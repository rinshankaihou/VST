(* Extended the original CompCert's correctness proof for supporting concurrency. *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for operators *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Cminor Cminor_op_footprint.
Require Import Op Op_fp.
Require Import CminorSel CminorSel_local.
Require Import SelectOp SelectOpproof. 

Local Open Scope cminorsel_scope.

Require Import Footprint.
Ltac EvalOpFP :=
  eauto;
  match goal with
  | [ |- eval_exprlist_fp _ _ _ _ _ Enil _ ] => constructor
  | [ |- eval_exprlist_fp _ _ _ _ _ (_:::_) _ ] => econstructor; EvalOpFP
  | [ |- eval_expr_fp _ _ _ _ _ (Eletvar _) _ ] => econstructor; simpl; eauto
  | [ |- eval_expr_fp _ _ _ _ _ (Elet _ _) _ ] => econstructor; EvalOpFP
  | [ |- eval_expr_fp _ _ _ _ _ (lift _) _ ] => apply eval_lift_fp; EvalOpFP
  | [ |- eval_expr_fp _ _ _ _ _ _ _ ] => eapply eval_Eop_fp; [EvalOp | EvalOpFP | simpl; eauto | simpl; eauto | eauto]
  | _ => idtac
  end.

Ltac InvEvalFP1:=
  match goal with
  | [ H: (eval_expr_fp _ _ _ _ _ (Eop _ Enil) _) |- _ ] =>
    inv H; InvEvalFP1
  | [ H: (eval_expr_fp _ _ _ _ _ (Eop _ (_ ::: Enil)) _) |- _ ] =>
    inv H; InvEvalFP1
  | [ H: (eval_expr_fp _ _ _ _ _ (Eop _ (_ ::: _ ::: Enil)) _) |- _ ] =>
    inv H; InvEvalFP1
  | [ H: (eval_exprlist_fp _ _ _ _ _ Enil _) |- _ ] =>
    inv H; InvEvalFP1
  | [ H: (eval_exprlist_fp _ _ _ _ _ (_ ::: _) _) |- _ ] =>
    inv H; InvEvalFP1
  | _ =>
    idtac
  end.

Ltac InvEvalFP2 :=
  match goal with
  | [ H: (eval_operation_fp _ _ _ nil _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation_fp _ _ _ (_ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation_fp _ _ _ (_ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation_fp _ _ _ (_ :: _ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | _ =>
      idtac
  end.

Ltac InvEmpFP :=
  match goal with
  | [ H: eval_operation_fp _ _ _ ?vl _ = Some _ |- _ ] => simpl in H; destruct vl; inv H; InvEmpFP
  | [ H: match ?vl with _ => _ end = Some _ |- _ ] => destruct vl; inv H; InvEmpFP
  | _ => idtac
  end.

Ltac InvEvalFP := InvEvalFP1; InvEvalFP2; InvEvalFP2; subst.

Ltac TrivFP := repeat rewrite (FP.fp_union_emp); repeat rewrite (FP.emp_union_fp); auto;
               match goal with
               | [ |- FP.subset ?fp ?fp ] => apply FP.subset_refl; auto
               | [ |- FP.subset FP.emp ?fp ] => apply FP.subset_emp
               | [ |- FP.subset ?fp (FP.union ?fp _) ] => apply FP.union_subset
               | [ |- FP.subset (FP.union ?fp1 ?fp2) (FP.union ?fp2 ?fp1) ] =>
                 rewrite FP.union_comm_eq; apply FP.subset_refl
               | [ |- FP.subset ?fp (FP.union _ ?fp) ] => rewrite FP.union_comm_eq; apply FP.union_subset
               | [ H: FP.subset ?fp1 ?fp2 |- FP.subset ?fp1 (FP.union ?fp2 _) ] => apply FP.subset_union_subset; auto
               | [ H: FP.subset ?fp1 ?fp2 |- FP.subset ?fp1 (FP.union _ ?fp2) ] =>
                 rewrite FP.union_comm_eq; apply FP.subset_union_subset; auto
               | _ => idtac
               end.

Ltac Triv := eexists; split; [repeat econstructor; eauto | TrivFP].


(** TODO: move to ? *)
Lemma subset_trans:
  forall fp1 fp2 fp3,
    FP.subset fp1 fp2 -> FP.subset fp2 fp3 -> FP.subset fp1 fp3.
Proof.
  intros. inv H; inv H0; constructor; eapply Locs.subset_trans; eauto.
Qed.

Lemma subset2_union:
  forall fp1 fp2 fp,
    FP.subset fp1 fp -> FP.subset fp2 fp -> FP.subset (FP.union fp1 fp2) fp.
Proof.
  intros. inv H; inv H0; constructor; eapply Locs.union_subset; eauto.
Qed.

Section CMCONSTR.

Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

Definition unary_constructor_fp_sound (cstr: expr -> expr) : Prop :=
  forall le a x fp,
    eval_expr ge sp e m le a x ->
    eval_expr_fp ge sp e m le a fp ->
    exists fp', eval_expr_fp ge sp e m le (cstr a) fp' /\ FP.subset fp' fp.

Definition binary_constructor_fp_sound (cstr: expr -> expr -> expr) : Prop :=
  forall le a x fpx b y fpy,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->  
  exists fp, eval_expr_fp ge sp e m le (cstr a b) fp /\ FP.subset fp (FP.union fpx fpy).

Theorem eval_addrsymbol_fp:
  forall le id ofs,
  eval_expr_fp ge sp e m le (addrsymbol id ofs) FP.emp. 
Proof.
  intros. unfold addrsymbol. 
  destruct (symbol_is_external id).
  predSpec Ptrofs.eq Ptrofs.eq_spec ofs Ptrofs.zero.
  subst. repeat econstructor. repeat econstructor. repeat econstructor.
Qed.

Theorem eval_addrstack_fp:
  forall le ofs,
  eval_expr_fp ge sp e m le (addrstack ofs) FP.emp.
Proof. intros. unfold addrstack. repeat econstructor. Qed.

Theorem eval_notint_fp: unary_constructor_fp_sound notint.
Proof. unfold notint; red; intros until x. case (notint_match a); intros; InvEval; InvEvalFP; Triv. Qed.

Theorem eval_addimm_fp: forall n, unary_constructor_fp_sound (addimm n).
Proof.
  red; unfold addimm; intros until x.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. intros. Triv.
- case (addimm_match a); intros; InvEval; InvEvalFP; InvEval; try (Triv; fail).
  inv H0. inv H1. Triv. simpl. erewrite eval_offset_addressing_total_32 by eauto. rewrite Int.repr_signed; auto.
  simpl. erewrite eval_offset_addressing_total_32 by eauto. auto.
Qed.

Theorem eval_add_fp: binary_constructor_fp_sound add.
Proof.
  red; intros until y.
  unfold add; case (add_match a b); intros; InvEval; try (InvEvalFP; InvEmpFP; Triv; fail).
  exploit eval_addimm_fp; try eassumption. intros [fp' [A B]]. exists fp'. split; eauto; TrivFP.
  exploit eval_addimm_fp; try eassumption. intros [fp' [A B]]. exists fp'. split; eauto; TrivFP.
Qed.  

Theorem eval_sub_fp: binary_constructor_fp_sound sub.
Proof.
  red; intros until fpy.
  unfold sub; case (sub_match a b); intros; InvEval; InvEvalFP;
    try match goal with
        | |- context[eval_expr_fp _ _ _ _ ?le (addimm ?e1 ?e2) ] =>
          exploit (eval_addimm_fp e1 le e2); try eassumption; try (repeat econstructor; eauto; fail); TrivFP
        end.
  - intros [fp' [A B]]. exists fp'. split; eauto. TrivFP.
  - replace (Int.repr (n1 - n2)) with (Int.sub (Int.repr n1) (Int.repr n2)). 
    intros [fp' [A B]]. exists fp'. split; [auto|TrivFP]. InvEmpFP; TrivFP. 
    apply Int.eqm_samerepr; auto with ints.
  - TrivFP. intros [fp' [A B]]. exists fp'. split;[auto|TrivFP]. InvEmpFP; TrivFP.
  - intros [fp' [A B]]. exists fp'. split;[auto|TrivFP]. InvEmpFP; TrivFP.
  - Triv.
Qed.

Theorem eval_negint_fp: unary_constructor_fp_sound negint.
Proof. red; intros until x. unfold negint. case (negint_match a); intros; InvEval; Triv. Qed.

Theorem eval_shlimm_fp: forall n, unary_constructor_fp_sound (fun a => shlimm a n).
Proof.
  red; intros until fp. unfold shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. Triv. 
  destruct (Int.ltu n Int.iwordsize) eqn:LT; simpl.
  destruct (shlimm_match a); intros; InvEval.
  - Triv.
  - destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?; InvEvalFP; InvEmpFP; Triv.
  - destruct (shift_is_scale n); InvEvalFP; InvEmpFP; Triv.
  - destruct (shift_is_scale n); InvEvalFP; InvEmpFP; Triv.
  - Triv.
Qed.

Theorem eval_shruimm_fp: forall n, unary_constructor_fp_sound (fun a => shruimm a n).
Proof.
  red; intros until x.  unfold shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. Triv. 
  destruct (Int.ltu n Int.iwordsize) eqn:LT; simpl; try (Triv; fail).
  destruct (shruimm_match a); intros; InvEval; try (Triv; fail).
  destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?; InvEvalFP; Triv.
Qed.

Theorem eval_shrimm_fp: forall n, unary_constructor_fp_sound (fun a => shrimm a n).
Proof.
  red; intros until x.  unfold shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. Triv.
  destruct (Int.ltu n Int.iwordsize) eqn:LT; simpl; try (Triv; fail).
  destruct (shrimm_match a); intros; InvEval; try (Triv; fail).
  destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?; InvEvalFP; InvEmpFP; Triv.
Qed.

Lemma eval_mulimm_base_fp: forall n, unary_constructor_fp_sound (mulimm_base n).
Proof.
  intros; red; intros; unfold mulimm_base.
  generalize (Int.one_bits_decomp n) (Int.one_bits_range n); intros D R.
  destruct (Int.one_bits n) as [ | i l]. Triv.
  destruct l as [ | j l ].
  replace (Val.mul x (Vint n)) with (Val.shl x (Vint i)). exploit eval_shlimm_fp; eauto.
  destruct x; auto; simpl. rewrite D; simpl; rewrite Int.add_zero.
  rewrite R by auto with coqlib. rewrite Int.shl_mul. auto.
  destruct l as [ | k l ].
  exploit (eval_shlimm ge sp e m i (x :: le) (Eletvar 0) x). constructor; auto. intros [v1 [A1 B1]].
  exploit (eval_shlimm_fp i (x :: le) (Eletvar 0) x). constructor; auto. econstructor; simpl; eauto. intros [fp1 [A1' B1']].
  exploit (eval_shlimm ge sp e m j (x :: le) (Eletvar 0) x). constructor; auto. intros [v2 [A2 B2]].
  exploit (eval_shlimm_fp j (x :: le) (Eletvar 0) x). constructor; auto. econstructor; simpl; eauto. intros [fp2 [A2' B2']].
  exploit eval_add. eexact A1. eexact A2. intros [v3 [A3 B3]].
  exploit eval_add_fp. eexact A1. eexact A1'. eexact A2. eexact A2'. intros [fp3 [A3' B3']].
  exists (FP.union fp fp3); split. econstructor; eauto.
  rewrite FP.union_comm_eq. rewrite <- (FP.emp_union_fp fp) at 2. 
  apply FP.union2_subset. apply subset_trans with (FP.union fp1 fp2); auto.  apply subset2_union; auto.
  Triv.
Qed.

Theorem eval_mulimm_fp: forall n, unary_constructor_fp_sound (mulimm n).
Proof.
  intros; red; intros until x; unfold mulimm.
  predSpec Int.eq Int.eq_spec n Int.zero. Triv. 
  predSpec Int.eq Int.eq_spec n Int.one. Triv.
  case (mulimm_match a); intros; InvEval; InvEvalFP; InvEmpFP; try (Triv; fail).

  exploit eval_mulimm_base; eauto. instantiate (1 := n). intros [v' [A1 B1]].
  exploit (eval_addimm ge sp e m (Int.mul n (Int.repr n2)) le (mulimm_base n t2) v'). auto. intros [v'' [A2 B2]].
  exploit eval_mulimm_base_fp. exact H3. eauto. intros [fp' [A1' B1']].
  exploit (eval_addimm_fp (Int.mul n (Int.repr n2)) le (mulimm_base n t2) v'). auto. eauto. intros [fp'' [A2' B2']].
  Triv. eapply subset_trans; eauto.
  exploit eval_mulimm_base_fp; eauto.
Qed.

Theorem eval_mul_fp: binary_constructor_fp_sound mul.
Proof.
  red; intros until y.
  unfold mul; case (mul_match a b); intros; InvEval; InvEvalFP.
  exploit eval_mulimm_fp; eauto. intros [fp' [A B]]. Triv.
  exploit eval_mulimm_fp; eauto. intros [fp' [A B]]. Triv.
  Triv.
Qed.

Theorem eval_andimm_fp: forall n, unary_constructor_fp_sound (andimm n).
Proof.
  intros; red; intros until x. unfold andimm.
  predSpec Int.eq Int.eq_spec n Int.zero. Triv.
  predSpec Int.eq Int.eq_spec n Int.mone. Triv.
  case (andimm_match a); intros; InvEval; InvEvalFP; Triv.
Qed.

Theorem eval_and_fp: binary_constructor_fp_sound and.
Proof.
  red; intros until y; unfold and; case (and_match a b); intros; InvEval.
- exploit eval_andimm_fp; eauto. intros [fp' [A B]]. Triv.
- exploit eval_andimm_fp; eauto. intros [fp' [A B]]. Triv.
- Triv.
Qed.

Theorem eval_orimm_fp: forall n, unary_constructor_fp_sound (orimm n).
Proof.
  intros; red; intros until x. unfold orimm. 
  predSpec Int.eq Int.eq_spec n Int.zero. Triv.
  predSpec Int.eq Int.eq_spec n Int.mone. Triv.
  destruct (orimm_match a); intros; InvEval; InvEvalFP; Triv.
Qed.

Remark eval_same_expr_fp:
  forall a1 a2 le v1 v2,
  same_expr_pure a1 a2 = true ->
  eval_expr_fp ge sp e m le a1 v1 ->
  eval_expr_fp ge sp e m le a2 v2 ->
  a1 = a2 /\ v1 = v2.
Proof.
  intros until v2.
  destruct a1; simpl; try (intros; discriminate).
  destruct a2; simpl; try (intros; discriminate).
  case (ident_eq i i0); intros.
  subst i0. inversion H0. inversion H1. split. auto. congruence.
  discriminate.
Qed.

Lemma eval_or_fp: binary_constructor_fp_sound or.
Proof.
  red; intros until y; unfold or; case (or_match a b); intros.
- InvEval. exploit eval_orimm_fp; eauto. intros [fp' [A B]]. Triv.
- InvEval. exploit eval_orimm_fp; eauto. intros [fp' [A B]]. Triv.
- (* shlimm - shruimm *)
  predSpec Int.eq Int.eq_spec (Int.add n1 n2) Int.iwordsize. 
  destruct (same_expr_pure t1 t2) eqn:? .
  InvEval. exploit eval_same_expr; eauto. intros [EQ1 EQ2]; subst.
  InvEvalFP. exploit eval_same_expr_fp; eauto. intros [EQ1 EQ2]; subst.
  Triv. InvEmpFP. TrivFP.
  InvEval. InvEvalFP. InvEmpFP. Triv.
  InvEval. InvEvalFP. InvEmpFP. Triv.
- predSpec Int.eq Int.eq_spec (Int.add n1 n2) Int.iwordsize. 
  destruct (same_expr_pure t1 t2) eqn:?; InvEval.
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]; subst.
  InvEvalFP. exploit eval_same_expr_fp; eauto. intros [EQ1 EQ2]; subst.
  InvEmpFP. Triv.
  InvEvalFP. InvEmpFP. Triv.   InvEvalFP. InvEmpFP. Triv.
-  Triv.
Qed.

Theorem eval_xorimm_fp: forall n, unary_constructor_fp_sound (xorimm n).
Proof.
  intros; red; intros until x. unfold xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero. Triv.
  destruct (xorimm_match a); intros; InvEval; InvEvalFP; Triv.
Qed.

Theorem eval_xor_fp: binary_constructor_fp_sound xor.
Proof.
  red; intros until y; unfold xor; case (xor_match a b); intros; InvEval; InvEvalFP.
  exploit eval_xorimm_fp; eauto. intros [fp' [A B]]. Triv.
  exploit eval_xorimm_fp; eauto. intros [fp' [A B]]. Triv.
  Triv.
Qed.

Theorem eval_divs_base_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->    
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divs x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divs_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof. intros. unfold divs_base. Triv. simpl. rewrite H3. auto. Qed.

Theorem eval_divu_base_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divu_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof. intros. unfold divu_base. Triv. simpl. rewrite H3. auto. Qed.

Theorem eval_mods_base_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->  
  Val.mods x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (mods_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof. intros. unfold mods_base. Triv. simpl. rewrite H3. auto. Qed.

Theorem eval_modu_base_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.modu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (modu_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof. intros. unfold modu_base. Triv. simpl. rewrite H3. auto. Qed.

Theorem eval_shrximm_fp:
  forall le a n x fpx z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.shrx x (Vint n) = Some z ->
  exists fp, eval_expr_fp ge sp e m le (shrximm a n) fp /\ FP.subset fp fpx.
Proof.
  intros. unfold shrximm.
  predSpec Int.eq Int.eq_spec n Int.zero; Triv. simpl. rewrite H1. auto.
Qed.

Theorem eval_shl_fp: binary_constructor_fp_sound shl.
Proof.
  red; intros until y; unfold shl; case (shl_match b); intros; InvEval; InvEvalFP.
  exploit eval_shlimm_fp; eauto. intros [fp' [A B]]. Triv. Triv.
Qed.

Theorem eval_shr_fp: binary_constructor_fp_sound shr.
Proof.
  red; intros until y; unfold shr; case (shr_match b); intros; InvEval; InvEvalFP.
  exploit eval_shrimm_fp; eauto. intros [fp' [A B]]. Triv. Triv.
Qed.

Theorem eval_shru_fp: binary_constructor_fp_sound shru.
Proof.
  red; intros until y; unfold shru; case (shru_match b); intros.
  InvEval; InvEvalFP. exploit eval_shruimm_fp; eauto. intros [fp' [A B]]. Triv. Triv.
Qed.

Theorem eval_negf_fp: unary_constructor_fp_sound negf.
Proof. Triv. Qed.

Theorem eval_absf_fp: unary_constructor_fp_sound absf.
Proof. Triv. Qed.

Theorem eval_addf_fp: binary_constructor_fp_sound addf.
Proof. Triv. Qed.

Theorem eval_subf_fp: binary_constructor_fp_sound subf.
Proof. Triv. Qed.

Theorem eval_mulf_fp: binary_constructor_fp_sound mulf.
Proof. Triv. Qed.

Theorem eval_negfs_fp: unary_constructor_fp_sound negfs.
Proof. Triv. Qed.

Theorem eval_absfs_fp: unary_constructor_fp_sound absfs.
Proof. Triv. Qed.

Theorem eval_addfs_fp: binary_constructor_fp_sound addfs.
Proof. Triv. Qed.

Theorem eval_subfs_fp: binary_constructor_fp_sound subfs.
Proof. Triv. Qed.

Theorem eval_mulfs_fp: binary_constructor_fp_sound mulfs.
Proof. Triv. Qed.


Definition binary_constructor_fp_sound_opt (cstr: expr -> expr -> expr) (op: binary_operation) : Prop :=
  forall le a x fpx b y fpy z,
    eval_expr ge sp e m le a x ->
    eval_expr_fp ge sp e m le a fpx ->
    eval_expr ge sp e m le b y ->
    eval_expr_fp ge sp e m le b fpy ->
    eval_expr ge sp e m le (cstr a b) z ->
    exists fp, eval_expr_fp ge sp e m le (cstr a b) fp /\
          FP.subset fp (FP.union (FP.union fpx fpy)
                                 match (eval_binop_fp op x y m) with
                                 | Some fp' => fp' | None => FP.emp end).
  
(** TODO: move to Op_fp.v *)
Lemma eval_negate_condition_fp:
  forall c vl m,
    eval_condition_fp (negate_condition c) vl m = eval_condition_fp c vl m.
Proof.
  clear. destruct c; simpl; auto; (destruct vl as [|v vl]; [|destruct vl; try destruct vl]; auto).
  destruct c, v, v0; auto.
  destruct c, v; auto.
  destruct c, v; auto.
  destruct c, v; auto.
  destruct c, v, v0; auto.
  destruct c, v; auto.
  destruct c, v, v0; auto.
  destruct c, v, v0; auto.
  destruct c, v, v0; auto.
  destruct c, v, v0; auto.
  destruct v; auto.
  destruct v; auto.
Qed.

Lemma eval_compimm_opt_fp:
  forall (C: comparison -> int -> condition) c n sem le a x fpx z,
    eval_expr ge sp e m le a x ->
    eval_expr_fp ge sp e m le a fpx ->
    eval_expr ge sp e m le (compimm C sem c a n) z ->
    exists fp', eval_expr_fp ge sp e m le (compimm C sem c a n) fp' /\
           FP.subset fp' (FP.union fpx (match C c n with
                                        | Ccompuimm c0 n0 => cmpu_fp m c0 x (Vint n0)
                                        | _ => FP.emp
                                        end)).
Proof.
  intros C c n sem le a x fpx z EVAL EVALFP EVAL'.
  revert EVAL'. unfold compimm. case (compimm_match c a) eqn:CIM.
  - Triv.
  - case (Int.eq_dec n Int.zero) eqn:HN.
    + inv EVAL. inv EVALFP. inv H5. simpl in *. 
      case (eval_condition c vl0 m) eqn:EC; inv H0.
      eexists. split. repeat econstructor; eauto.
      simpl. rewrite eval_negate_condition, EC. simpl. eauto.
      simpl. rewrite eval_negate_condition_fp. eauto.
      TrivFP.
    + case (Int.eq_dec n Int.one) eqn:HN'; [|Triv].
      inv EVALFP. inv H3. simpl in *. Triv.
  - case (Int.eq_dec n Int.zero) eqn:HN;[|case (Int.eq_dec n Int.one) eqn:HN'];
      inv EVALFP; inv H3; simpl in *; try (Triv; fail).
    case (eval_condition c vl m) eqn:EC; inv H0.
    eexists. split. repeat econstructor; eauto; simpl.
    rewrite eval_negate_condition, EC. simpl; eauto.
    rewrite eval_negate_condition_fp. eauto. TrivFP.
  - case (Int.eq_dec n Int.zero) eqn:HN; inv EVALFP;
      inv H2; inv H5; repeat (destruct vl; try discriminate); try (Triv; fail).
    + inv H3. inv H0. inv H1. intro. inv EVAL'; simpl in *. repeat (destruct vl; try discriminate).
      inv H2. Triv; simpl. case (Val.maskzero_bool v n1) eqn:EC; auto; discriminate.
      rewrite <- FP.fp_union_assoc. TrivFP.
    + intro. inv EVAL'; simpl in *. inv H8. inv H10. inv H13. inv H8. inv H13. simpl in *.
      simpl in *. inv H14. Triv. simpl.
      destruct C, v3; simpl in *; try discriminate; auto.
      do 2 rewrite <- FP.fp_union_assoc. TrivFP.
  - case (Int.eq_dec n Int.zero) eqn:HN; inv EVALFP;
      inv H2; inv H5; repeat (destruct vl; try discriminate); try (Triv; fail).
    + intro. inv EVAL'; simpl in *. inv H8. inv H13. 
      inv H3. Triv; simpl. case (Val.maskzero_bool v2 n1) eqn:EC; auto; discriminate.
      do 2 rewrite <- FP.fp_union_assoc. TrivFP.
    + intro. inv EVAL'; simpl in *. inv H8. inv H10. inv H13. inv H8. inv H13. simpl in *.
      inv H14. Triv. simpl.
      destruct C, v3; simpl in *; try discriminate; auto.
      do 2 rewrite <- FP.fp_union_assoc. TrivFP.
  - intro; inv EVAL'. inv H2. inv H6. eqexpr.
    destruct C eqn:HC, v1; simpl in *; try discriminate; auto; try (Triv; simpl; auto; fail).
    destruct Archi.ptr64 eqn:A; try discriminate.
    destruct Int.eq eqn:B; try discriminate. simpl in H4.
    destruct (Mem.valid_pointer m b (Ptrofs.unsigned i) || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)) eqn:D;
      try discriminate.
    destruct Val.cmp_different_blocks eqn:E; try discriminate.
    eexists. split. repeat econstructor. eauto. eauto. eauto.
    simpl. rewrite A, B, D, E. eauto.
    simpl. rewrite A, B, E. eauto.
    TrivFP.
Qed.

Lemma cmpu_fp_swap:
  forall m c x y,
    cmpu_fp m (swap_comparison c) x y = cmpu_fp m c y x.
Proof. clear. destruct c eqn:HC, x eqn:Hx, y eqn:Hy; simpl; destruct Archi.ptr64 eqn:ARCHI; auto.
       destruct eq_block; destruct eq_block; try congruence; subst; apply FP.union_comm_eq.
       destruct eq_block; destruct eq_block; try congruence; subst; apply FP.union_comm_eq.
       destruct eq_block; destruct eq_block; try congruence; subst; apply FP.union_comm_eq.
       destruct eq_block; destruct eq_block; try congruence; subst; apply FP.union_comm_eq.
       destruct eq_block; destruct eq_block; try congruence; subst; apply FP.union_comm_eq.
       destruct eq_block; destruct eq_block; try congruence; subst; apply FP.union_comm_eq.
Qed.

Theorem eval_comp_opt_fp:
  forall c, binary_constructor_fp_sound_opt (comp c) (Cminor.Ocmp c).
Proof.
  intros c le a x fpx b y fpy z EVAL1 EVALFP1 EVAL2 EVALFP2.
  unfold comp; intro EVAL'. 
  case (comp_match a b) eqn:CM.
  exploit eval_compimm_opt_fp. exact EVAL2. eauto. eauto. TrivFP. intros [fp [A B]]. Triv.
  exploit eval_compimm_opt_fp. exact EVAL1. eauto. eauto. TrivFP. intros [fp [A B]]. Triv.
  inv EVAL'. inv H2. inv H6. inv H7. Triv. simpl in *.
  destruct Val.cmp_bool; auto. discriminate.
Qed.

Theorem eval_compu_opt_fp:
  forall c, binary_constructor_fp_sound_opt (compu c) (Cminor.Ocmpu c).
Proof.
  intros c le a x fpx b y fpy z EVAL1 EVALFP1 EVAL2 EVALFP2.
  unfold compu; intro EVAL'. 
  case (compu_match a b) eqn:CM.
  exploit eval_compimm_opt_fp. exact EVAL2. eauto. eauto. simpl in *. intros [fp [A B]]. Triv.
  rewrite cmpu_fp_swap in B. inv EVAL1. inv H2. inv H4. rewrite <- FP.fp_union_assoc, (FP.union_comm_eq fpx). TrivFP.
  exploit eval_compimm_opt_fp. exact EVAL1. eauto. eauto. simpl in *. intros [fp [A B]]. Triv.
  inv EVAL2. inv H2. inv H4. rewrite (FP.union_comm_eq fpx), <- FP.fp_union_assoc, (FP.union_comm_eq fpy). TrivFP.
  InvEval. eqexpr. simpl. unfold cmpu_fp, ValFP.cmpu_bool_fp_total, Val.cmpu_bool in *. 
  destruct Archi.ptr64 eqn:A, v1 , v0; try discriminate; simpl in *.
  Triv. simpl. auto.
  destruct Int.eq eqn:B; try discriminate.
  destruct (Mem.valid_pointer m b (Ptrofs.unsigned i0) || Mem.valid_pointer m b (Ptrofs.unsigned i0 - 1)) eqn:D;
    try discriminate.
  eexists. destruct (Val.cmp_different_blocks c) eqn:CD; try discriminate; simpl in *.
  split. repeat econstructor; eauto. simpl. rewrite A, B, D; eauto. rewrite CD. simpl. eauto.
  simpl. rewrite A, B, CD; eauto. 
  TrivFP.
  destruct Int.eq eqn:B; try discriminate.
  destruct (Mem.valid_pointer m b (Ptrofs.unsigned i) || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)) eqn:D;
    try discriminate.
  eexists. destruct (Val.cmp_different_blocks c) eqn:CD; try discriminate; simpl in *.
  split. repeat econstructor; eauto. simpl. rewrite A, B, D; eauto. rewrite CD. simpl. eauto.
  simpl. rewrite A, B, CD; eauto. 
  TrivFP.
  destruct (Val.cmp_different_blocks c) eqn:CD; try discriminate; simpl in *.
  destruct eq_block eqn:B; eexists; (split; [repeat econstructor; eauto; simpl|]).
  rewrite B. eauto. rewrite A, B. eauto. TrivFP.
  rewrite B, CD. eauto. rewrite A, B, CD. eauto. TrivFP.
  destruct eq_block eqn:B; eexists; (split; [repeat econstructor; eauto; simpl|]).
  rewrite B. eauto. rewrite A, B. eauto. TrivFP.
  destruct (Mem.valid_pointer m b _ && Mem.valid_pointer m b0 _); discriminate.
  destruct (Mem.valid_pointer m b _ && Mem.valid_pointer m b0 _); discriminate.
  destruct (Mem.valid_pointer m b _ && Mem.valid_pointer m b0 _); discriminate.
  Unshelve. TrivFP. TrivFP.
Qed.

Theorem eval_compf_opt_fp:
  forall c, binary_constructor_fp_sound_opt (compf c) (Cminor.Ocmpf c).
Proof.
  intros; red; unfold compf; intros. InvEval. eqexpr.
  Triv; simpl. destruct Val.cmpf_bool; auto. discriminate.
Qed.

Theorem eval_compfs_opt_fp:
  forall c, binary_constructor_fp_sound_opt (compfs c) (Cminor.Ocmpfs c).
Proof. intros; red; unfold compfs; intros. InvEval; eqexpr. Triv. simpl. destruct Val.cmpfs_bool; auto. discriminate. Qed.

Theorem eval_cast8signed_fp: unary_constructor_fp_sound cast8signed.
Proof. red; intros until x. unfold cast8signed. case (cast8signed_match a); intros; InvEval; Triv. Qed.

Theorem eval_cast8unsigned_fp: unary_constructor_fp_sound cast8unsigned.
Proof.
  red; intros until x. unfold cast8unsigned. destruct (cast8unsigned_match a); intros; InvEval; InvEvalFP; eqexpr.
  Triv. exploit eval_andimm_fp; eauto. intros [fp' [A B]]. Triv. Triv.
Qed.

Theorem eval_cast16signed_fp: unary_constructor_fp_sound cast16signed.
Proof.
  red; intros until x. unfold cast16signed. case (cast16signed_match a); intros; InvEval; InvEvalFP; eqexpr; Triv.
Qed.

Theorem eval_cast16unsigned_fp: unary_constructor_fp_sound cast16unsigned.
Proof.
  red; intros until x. unfold cast16unsigned. destruct (cast16unsigned_match a); intros; InvEval; InvEvalFP; eqexpr.
  Triv. exploit eval_andimm_fp; eauto. intros [fp' [A B]]. Triv. Triv.
Qed.

Theorem eval_singleoffloat_fp: unary_constructor_fp_sound singleoffloat.
Proof. red; intros. unfold singleoffloat. Triv. Qed.

Theorem eval_floatofsingle_fp: unary_constructor_fp_sound floatofsingle.
Proof. Triv. Qed.

Theorem eval_intoffloat_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.intoffloat x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (intoffloat a) fp /\ FP.subset fp fpx.
Proof. Triv. simpl. rewrite H1. auto. Qed.

Theorem eval_floatofint_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.floatofint x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (floatofint a) fp /\ FP.subset fp fpx.
Proof. intros until y; unfold floatofint. case (floatofint_match a); intros; Triv. simpl. rewrite H1; auto. Qed.

Theorem eval_intuoffloat_fp:
  forall le a x fpx y ,
    eval_expr ge sp e m le a x ->
    eval_expr_fp ge sp e m le a fpx ->
    Val.intuoffloat x = Some y ->
    exists fp, eval_expr_fp ge sp e m le (intuoffloat a) fp /\ FP.subset fp fpx.
Proof.
  intros. exploit eval_intuoffloat; eauto. 
  destruct x; simpl in H1; try discriminate.
  destruct (Float.to_intu f) as [n|] eqn:?; simpl in H1; inv H1.
  unfold intuoffloat. intros [v' [EVAL' A]]. inv A. 
  inv EVAL'. eqexpr. inv H6. inv H7. inv H8. InvEval. inv H5. inv H3. inv H4. inv H3. inv H7.
  destruct (Float.cmp Clt f (Float.of_intu Float.ox8000_0000)) eqn:A.
  - inv H9. inv H4. inv H8. inv H5. inv H3. inv H6.
    apply Float.to_intu_to_int_1 in Heqo; auto. rewrite Heqo in H2. inv H2.
    Triv; simpl; eauto; try rewrite A; simpl; eauto; repeat econstructor; eauto; simpl; eauto; try rewrite Heqo; simpl; eauto.
  - apply Float.to_intu_to_int_2 in Heqo; eauto.
    Triv; simpl; eauto; try erewrite A; eauto.
    repeat econstructor; eauto; simpl; try rewrite Heqo; simpl; eauto.
Qed.

Theorem eval_floatofintu_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.floatofintu x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (floatofintu a) fp /\ FP.subset fp fpx.
Proof.
  intros. exploit eval_floatofintu; eauto. unfold floatofintu. 
  case (floatofintu_match a) eqn:FM; intros [v' [A B]].
  InvEval; InvEvalFP. Triv.
  destruct x; simpl in H1; try discriminate. inv H1.
  inv B. inv A. eqexpr. inv H6. inv H7. inv H4. inv H9. inv H5. inv H3. inv H6.
  destruct Int.ltu eqn:A.
  inv H8. inv H4. inv H6. inv H8. inv H5. inv H4. inv H2. 
  Triv; simpl; eauto; try rewrite A; repeat econstructor; eauto.
  inv H8. inv H4; InvEval. 
  Triv; simpl; eauto; try rewrite A; repeat econstructor; eauto.
Qed.

Theorem eval_intofsingle_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.intofsingle x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (intofsingle a) fp /\ FP.subset fp fpx.
Proof. Triv. simpl. rewrite H1. auto. Qed.

Theorem eval_singleofint_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.singleofint x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (singleofint a) fp /\ FP.subset fp fpx.
Proof.
  intros until y; unfold singleofint. case (singleofint_match a); intros; InvEval; InvEvalFP; Triv.
  simpl. rewrite H1; auto.
Qed.

Theorem eval_intuofsingle_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.intuofsingle x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (intuofsingle a) fp /\ FP.subset fp fpx.
Proof.
  intros. destruct x; simpl in H1; try discriminate.
  destruct (Float32.to_intu f) as [n|] eqn:?; simpl in H1; inv H1.
  unfold intuofsingle.
  exploit (eval_intuoffloat_fp le (floatofsingle a)).
  unfold intuofsingle, floatofsingle; repeat econstructor; eauto. repeat econstructor; eauto.
  simpl. change (Float.of_single f) with (Float32.to_double f).
  erewrite Float32.to_intu_double; eauto. simpl. eauto. TrivFP.
Qed.

Theorem eval_singleofintu_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.singleofintu x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (singleofintu a) fp /\ FP.subset fp fpx.
Proof.
  intros until y; unfold singleofintu. case (singleofintu_match a); intros.
  Triv.
  destruct x; simpl in H1; try discriminate. inv H1.
  exploit eval_floatofintu_fp; eauto. simpl. reflexivity.
  exploit eval_floatofintu; eauto. simpl. reflexivity.
  intros (v & A & B). intros (fp & A' & B'). Triv.
Qed.

Theorem eval_addressing_fp:
  forall le chunk a v fp b ofs,
  eval_expr ge sp e m le a v ->
  eval_expr_fp ge sp e m le a fp ->
  v = Vptr b ofs ->
  match addressing chunk a with (mode, args) =>
    exists vl,
    eval_exprlist ge sp e m le args vl /\
    eval_exprlist_fp ge sp e m le args fp /\
    Op.eval_addressing ge sp mode vl = Some v
  end.
Proof.
  intros until ofs.
  assert (A: v = Vptr b ofs -> Op.eval_addressing ge sp (Aindexed 0) (v :: nil) = Some v).
  { intros. subst v. unfold Op.eval_addressing.
    destruct Archi.ptr64 eqn:SF; simpl; rewrite SF; rewrite Ptrofs.add_zero; auto. }
  assert (D: forall a,
             eval_expr ge sp e m le a v ->
             eval_expr_fp ge sp e m le a fp ->
             v = Vptr b ofs ->
             exists vl, eval_exprlist ge sp e m le (a ::: Enil) vl
                   /\ eval_exprlist_fp ge sp e m le (a ::: Enil) fp
                   /\ Op.eval_addressing ge sp (Aindexed 0) vl = Some v).
  { intros. exists (v :: nil); split. constructor; auto. constructor.
    split; auto. econstructor; eauto; try constructor. TrivFP. }
  unfold addressing; case (addressing_match a); intros.
- destruct (negb Archi.ptr64 && addressing_valid addr) eqn:E. 
+ inv H. InvBooleans. apply negb_true_iff in H. unfold Op.eval_addressing; rewrite H. 
  exists vl; split; auto. split; auto. inv H0. simpl in *.
  destruct (eval_addressing32 ge sp addr vl0) ;inv H10. TrivFP.
+ apply D; auto.
- destruct (Archi.ptr64 && addressing_valid addr) eqn:E. 
+ inv H. InvBooleans. unfold Op.eval_addressing; rewrite H. 
  exists vl; split; [|split]; auto. inv H0. simpl in *.
  destruct (eval_addressing64 ge sp addr vl0) ;inv H10. TrivFP.
+ apply D; auto.
- apply D; auto.
Qed.

Theorem eval_builtin_arg_fp:
  forall a v fp,
  eval_expr ge sp e m nil a v ->
  eval_expr_fp ge sp e m nil a fp ->    
  eval_builtin_arg_fp ge sp e m (builtin_arg a) fp.
Proof.
  intros until fp. unfold builtin_arg; case (builtin_arg_match a); intros;
                     InvEvalFP; InvEval; InvEmpFP; eqexpr; simpl in *; FuncInv; try (constructor; fail); TrivFP.
  - econstructor; eauto. 
  - econstructor; eauto.
  - inv H0. inv H. InvEvalFP; InvEval; eqexpr. rewrite eval_addressing_Aglobal in H6. inv H6.
    econstructor; eauto. TrivFP.
  - inv H0. inv H. InvEvalFP; InvEval; eqexpr. rewrite eval_addressing_Ainstack in H6. inv H6.
    econstructor; eauto. TrivFP.
  - econstructor; eauto.
Qed.

End CMCONSTR.
