(* Extended the original CompCert's correctness proof for supporting concurrency. *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for 64-bit integer operations *)

Require Import String Coqlib Maps Integers Floats Errors.
Require Archi.
Require Import AST Values Memory Globalenvs Events.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong SplitLongproof.
Require Import SelectLong SelectLongproof.


Require Import Blockset Footprint Op_fp CUAST helpers Cminor_local CminorSel_local
        selectop_proof splitlong_proof. 

Local Open Scope cminorsel_scope.
Local Open Scope string_scope.

(** * Correctness of the instruction selection functions for 64-bit operators *)

Section CMCONSTR.

Variable cu: cminorsel_comp_unit.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared cu hf.
Variable ge: genv.
Hypothesis GEINIT: globalenv_generic cu ge.

Variable sp: val.
Variable e: env.
Variable m: mem.

Definition unary_constructor_fp_sound (cstr: expr -> expr) : Prop :=
  forall le a x fpx v,
    eval_expr ge sp e m le a x ->
    eval_expr_fp ge sp e m le a fpx ->
    eval_expr ge sp e m le (cstr a) v ->
    exists fp, eval_expr_fp ge sp e m le (cstr a) fp /\ FP.subset fp fpx.

Definition binary_constructor_fp_sound (cstr: expr -> expr -> expr) : Prop :=
  forall le a x fpx b y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  eval_expr ge sp e m le (cstr a b) z ->
  exists fp, eval_expr_fp ge sp e m le (cstr a b) fp /\ FP.subset fp (FP.union fpx fpy).

Theorem eval_longconst_fp:
  forall le n, eval_expr_fp ge sp e m le (longconst n) FP.emp.
Proof. trivcons. Qed.

Theorem eval_intoflong_fp: unary_constructor_fp_sound intoflong.
Proof.
  unfold intoflong; destruct Archi.splitlong. apply eval_intoflong_fp.
  red; intros. destruct (is_longconst a) as [n|] eqn:C; Triv.
Qed.

Theorem eval_longofintu_fp: unary_constructor_fp_sound longofintu.
Proof.
  unfold longofintu; destruct Archi.splitlong. apply eval_longofintu_fp.
  red; intros. destruct (is_intconst a) as [n|] eqn:C; Triv.
Qed.

Theorem eval_longofint_fp: unary_constructor_fp_sound longofint.
Proof.
  unfold longofint; destruct Archi.splitlong. apply eval_longofint_fp.
  red; intros. destruct (is_intconst a) as [n|] eqn:C; Triv.
Qed.

Theorem eval_notl_fp: unary_constructor_fp_sound notl.
Proof.
  unfold notl; destruct Archi.splitlong. apply eval_notl_fp.
  red; intros. destruct (notl_match a); InvEvalFP; InvEval; eqexpr; Triv.
Qed.

Theorem eval_andlimm_fp: forall n, unary_constructor_fp_sound (andlimm n).
Proof.
  unfold andlimm; intros; red.
  predSpec Int64.eq Int64.eq_spec n Int64.zero. Triv.
  predSpec Int64.eq Int64.eq_spec n Int64.mone. Triv.
  intros. destruct (andlimm_match a); InvEvalFP; InvEval; eqexpr; subst; Triv.
Qed.

Theorem eval_andl_fp: binary_constructor_fp_sound andl.
Proof.
  unfold andl; destruct Archi.splitlong. apply eval_andl_fp.
  red; intros. destruct (andl_match a b); InvEvalFP; InvEval; eqexpr.
  - eapply eval_andlimm_fp; eauto. InvEmpFP; TrivFP. 
  - eapply eval_andlimm_fp; eauto. InvEmpFP; TrivFP.
  - Triv.
Qed.

Theorem eval_orlimm_fp: forall n, unary_constructor_fp_sound (orlimm n).
Proof.
  unfold orlimm; intros; red.
  predSpec Int64.eq Int64.eq_spec n Int64.zero. Triv.
  predSpec Int64.eq Int64.eq_spec n Int64.mone. Triv.
  intros. destruct (orlimm_match a); InvEvalFP; InvEval; subst; Triv.
Qed.

Theorem eval_orl_fp: binary_constructor_fp_sound orl.
Proof.
  unfold orl; destruct Archi.splitlong. apply eval_orl_fp.
  red; intros.
  destruct (orl_match a b).
  eapply eval_orlimm_fp; eauto. InvEvalFP; InvEval. inv H10. TrivFP.
  eapply eval_orlimm_fp; eauto. InvEvalFP; InvEval. inv H10. TrivFP.
  destruct andb.
  InvEvalFP; InvEval; simpl in *; eqexpr; FuncInv; subst. Triv.
  InvEvalFP; InvEval; simpl in *; eqexpr; FuncInv; subst. Triv.
  destruct andb.
  InvEvalFP; InvEval; simpl in *; eqexpr; FuncInv; subst. Triv.
  InvEvalFP; InvEval; simpl in *; eqexpr; FuncInv; subst. Triv.
  Triv.
Qed.

Theorem eval_xorlimm_fp: forall n, unary_constructor_fp_sound (xorlimm n).
Proof.
  unfold xorlimm; intros; red; intros. 
  destruct Int64.eq. Triv.
  destruct Int64.eq. eapply eval_notl_fp; eauto.
  destruct (xorlimm_match a); InvEvalFP; InvEval; eqexpr; subst; Triv.
Qed.

Theorem eval_xorl_fp: binary_constructor_fp_sound xorl.
Proof.
  unfold xorl; destruct Archi.splitlong. apply eval_xorl_fp. 
  red; intros. destruct (xorl_match a b). 
  - eapply eval_xorlimm_fp; eauto. InvEvalFP; InvEmpFP. TrivFP.
  - eapply eval_xorlimm_fp; eauto. InvEvalFP; InvEmpFP. TrivFP.
  - Triv.
Qed.

Ltac trivcases:=
  repeat match goal with [ |- context[match ?x with _ => _ end] ] => destruct x end; InvEvalFP; Triv.

Theorem eval_shllimm_fp: forall n, unary_constructor_fp_sound (fun e => shllimm e n).
Proof.
  intros; unfold shllimm. destruct Archi.splitlong eqn:SL. eapply eval_shllimm_fp; eauto.
  red; intros; trivcases.
Qed.

Theorem eval_shrluimm_fp: forall n, unary_constructor_fp_sound (fun e => shrluimm e n).
Proof.
  intros; unfold shrluimm. destruct Archi.splitlong eqn:SL. eapply eval_shrluimm_fp; eauto.
  red; intros; trivcases.
Qed.

Theorem eval_shrlimm_fp: forall n, unary_constructor_fp_sound (fun e => shrlimm e n).
Proof.
  intros; unfold shrlimm. destruct Archi.splitlong eqn:SL. eapply eval_shrlimm_fp; eauto.
  red; intros; trivcases.
Qed.

Theorem eval_shll_fp: binary_constructor_fp_sound shll.
Proof.
  unfold shll. destruct Archi.splitlong eqn:SL. eapply eval_shll_fp; eauto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
  exploit eval_shllimm_fp. exact H. exact H0. eauto. intros [fp [A B]]. Triv. Triv.
Qed.

Theorem eval_shrlu_fp: binary_constructor_fp_sound shrlu.
Proof.
  unfold shrlu. destruct Archi.splitlong eqn:SL. eapply eval_shrlu_fp; eauto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
  exploit eval_shrluimm_fp. exact H. exact H0. eauto. intros [fp [A B]]. Triv. Triv.
Qed.

Theorem eval_shrl_fp: binary_constructor_fp_sound shrl.
Proof.
  unfold shrl. destruct Archi.splitlong eqn:SL. eapply eval_shrl_fp; eauto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
  exploit eval_shrlimm_fp. exact H. eauto. eauto. intros [fp [A B]]. Triv. Triv.
Qed.

Theorem eval_negl_fp: unary_constructor_fp_sound negl.
Proof.
  unfold negl. destruct Archi.splitlong eqn:SL. eapply eval_negl_fp; eauto.
  red; intros; trivcases.
Qed.

Theorem eval_addlimm_fp: forall n, unary_constructor_fp_sound (addlimm n).
Proof.
  unfold addlimm; intros; red; intros.
  destruct Int64.eq. Triv.
  destruct (addlimm_match a); InvEvalFP; try (Triv; fail).
  inv H0. inv H1. Triv. simpl in *. rewrite H10. auto.
Qed.

Theorem eval_addl_fp: binary_constructor_fp_sound addl.
Proof.
  unfold addl. destruct Archi.splitlong eqn:SL.
  eapply eval_addl_fp. apply Archi.splitlong_ptr32; auto.
  red; intros; destruct (addl_match a b).
  exploit eval_addlimm_fp. exact H1. eauto. eauto. intros [fp [A B]]. Triv.
  exploit eval_addlimm_fp. exact H. eauto. eauto. intros [fp [A B]]. Triv.
  1-8: InvEvalFP; InvEmpFP; Triv. 
Qed.

Theorem eval_subl_fp: binary_constructor_fp_sound subl.
Proof.
  unfold subl. destruct Archi.splitlong eqn:SL.
  eapply eval_subl_fp. apply Archi.splitlong_ptr32; auto.
  red; intros; destruct (subl_match a b); InvEvalFP; InvEmpFP; InvEval; eqexpr; TrivFP;
    try (eapply eval_addlimm_fp; eauto; repeat econstructor; simpl; eauto; TrivFP; fail).
  Triv.
Qed.

Theorem eval_mullimm_base_fp: forall n, unary_constructor_fp_sound (mullimm_base n).
Proof.
  intros; unfold mullimm_base. red; intros.
  generalize (Int64.one_bits'_decomp n); intros D.
  destruct (Int64.one_bits' n) as [ | i [ | j [ | ? ? ]]] eqn:B.
  Triv. eapply eval_shllimm_fp; eauto.
  assert (eval_expr ge sp e m (x::le) (Eletvar 0) x) as A by (econstructor; simpl; eauto).
  assert (eval_expr_fp ge sp e m (x::le) (Eletvar 0) FP.emp) as A' by (econstructor; simpl; eauto).
  exploit eval_shllimm. 2:exacteval A. eauto. intros [vi [E F]]. evalge E.
  exploit (eval_shllimm_fp i). exact A. eauto. exact E. intros [fpi [E' F']].
  exploit eval_shllimm. 2:exacteval A. eauto. intros [vj [G I]]. evalge G.
  exploit (eval_shllimm_fp j). exact A. eauto. exact G. intros [fpj [G' I']].
  exploit (eval_addl). exacteval E. exacteval G. intros [v' [J K]]. evalge J.
  exploit (eval_addl_fp). eexact E. eauto. eexact G. eauto. eauto. intros [fp' [J' K']].
  Triv. apply subset2_union; TrivFP. apply subset_trans with (FP.union fpi fpj); auto.
  apply subset2_union; apply subset_trans with FP.emp; TrivFP.
  Triv.
Qed.

Theorem eval_mullimm_fp: forall n, unary_constructor_fp_sound (mullimm n).
Proof.
  unfold mullimm. intros; red; intros.
  destruct Archi.splitlong eqn:SL.
  eapply eval_mullimm_fp; eauto.
  destruct Int64.eq. Triv. destruct Int64.eq. Triv. destruct (mullimm_match a).
  Triv.
  InvEvalFP. exploit eval_mullimm_base. 2: exacteval H3. eauto. intros [v2 [A2 B2]]. evalge A2.
  exploit eval_mullimm_base_fp. exact H3. eauto. eauto. intros [fp2' [A2' B2']]. 
  exploit eval_addlimm. exacteval A2. intros [v3 [A3 B3]]. evalge A3.
  exploit eval_addlimm_fp. exact A2. eauto. eauto. intros [fp3 [A3' B3']].
  Triv. apply subset_trans with fp2'; TrivFP.
  eapply eval_mullimm_base_fp; eauto.
Qed.

Theorem eval_mull_fp: binary_constructor_fp_sound mull.
Proof.
  unfold mull. destruct Archi.splitlong eqn:SL. eapply eval_mull_fp; eauto.
  red; intros; destruct (mull_match a b); InvEvalFP; InvEmpFP; try eapply eval_mullimm_fp; eauto; TrivFP; Triv.
Qed.

Theorem eval_mullhu_fp: forall n, unary_constructor_fp_sound (fun a => mullhu a n).
Proof.
  unfold mullhu; intros. destruct Archi.splitlong eqn:SL. eapply eval_mullhu_fp; eauto. Triv.
Qed.

Theorem eval_mullhs_fp: forall n, unary_constructor_fp_sound (fun a => mullhs a n).
Proof.
  unfold mullhs; intros. destruct Archi.splitlong eqn:SL. eapply eval_mullhs_fp; eauto. Triv.
Qed.

Theorem eval_shrxlimm_fp:
  forall le a n x fpx z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->    
  Val.shrxl x (Vint n) = Some z ->
  exists fp, eval_expr_fp ge sp e m le (shrxlimm a n) fp /\ FP.subset fp fpx.
Proof.
  unfold shrxlimm; intros. destruct Archi.splitlong eqn:SL.
  eapply eval_shrxlimm_fp; eauto using Archi.splitlong_ptr32.
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. destruct x; simpl in H1; inv H1. Triv. Triv. simpl. rewrite H1. auto.
Qed.

Ltac UseHelper := decompose [Logic.and] i64_helpers_correct; eauto.
Ltac DeclHelper := red in HELPERS; decompose [Logic.and] HELPERS; eauto.

Theorem eval_divls_base_fp: binary_constructor_fp_sound divls_base.
Proof.
  unfold divls_base; red; intros. destruct Archi.splitlong eqn:SL; inv H3; InvEval; eqexpr.
  eexists; split. econstructor; try eassumption. 2,3: repeat econstructor; eauto. 
  DeclHelper. inv H12. eapply find_def_symbol in H23; eauto.
  destruct H23 as [b0' [FIND DEF]]. unfold fundef in *; simpl in *.
  rewrite H7 in FIND; inv FIND. unfold Genv.find_funct_ptr in H8. rewrite DEF in H8; inv H8; auto. constructor.
  TrivFP. Triv. simpl. rewrite H9. auto. 
Qed.

Theorem eval_modls_base_fp: binary_constructor_fp_sound modls_base.
Proof.
  unfold modls_base; red; intros. destruct Archi.splitlong eqn:SL; inv H3; InvEval; eqexpr.
  eexists; split. econstructor; try eassumption. 2,3: repeat econstructor; eauto. 
  DeclHelper. inv H15. eapply find_def_symbol in H23; eauto.
  destruct H23 as [b0' [FIND DEF]]. unfold fundef in *; simpl in *.
  rewrite H7 in FIND; inv FIND. unfold Genv.find_funct_ptr in H8. rewrite DEF in H8; inv H8; auto.
  constructor. TrivFP. Triv. simpl. rewrite H9. auto.
Qed.

Theorem eval_divlu_base_fp: binary_constructor_fp_sound divlu_base.
Proof.
  unfold divlu_base; red; intros. destruct Archi.splitlong eqn:SL; inv H3; InvEval; eqexpr.
  eexists; split. econstructor; try eassumption. 2,3: repeat econstructor; eauto. 
  DeclHelper. inv H14. eapply find_def_symbol in H23; eauto.
  destruct H23 as [b0' [FIND DEF]]. unfold fundef in *; simpl in *.
  rewrite H7 in FIND; inv FIND. unfold Genv.find_funct_ptr in H8. rewrite DEF in H8; inv H8; auto.
  constructor. TrivFP. Triv. simpl. rewrite H9. auto.
Qed.

Theorem eval_modlu_base_fp: binary_constructor_fp_sound modlu_base.
Proof.
  unfold modlu_base; red; intros. destruct Archi.splitlong eqn:SL; inv H3; InvEval; eqexpr.
  eexists; split. econstructor; try eassumption. 2,3: repeat econstructor; eauto. 
  DeclHelper. inv H16. eapply find_def_symbol in H23; eauto.
  destruct H23 as [b0' [FIND DEF]]. unfold fundef in *; simpl in *.
  rewrite H7 in FIND; inv FIND. unfold Genv.find_funct_ptr in H8. rewrite DEF in H8; inv H8; auto.
  constructor. TrivFP. Triv. simpl. rewrite H9. auto.
Qed.

Theorem eval_cmplu_fp:
  forall c le a x fpx b y fpy v fp,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.cmplu (Mem.valid_pointer m) c x y = Some v ->
  ValFP.cmplu_bool_fp m c x y = Some fp ->
  exists fp', eval_expr_fp ge sp e m le (cmplu c a b) fp' /\ FP.subset fp' (FP.union (FP.union fpx fpy) fp).
Proof.
  unfold cmplu; intros. destruct Archi.splitlong eqn:SL.
  exploit eval_cmplu_fp. eauto. exact H. exact H0. exact H1. exact H2. eauto. eauto. intros [fp' [A B]]. Triv.
  unfold Val.cmplu in H3. destruct (Val.cmplu_bool (Mem.valid_pointer m) c x y) as [vb|] eqn:C; simpl in H3; inv H3.
  destruct (is_longconst a) as [n1|] eqn:LC1; destruct (is_longconst b) as [n2|] eqn:LC2;
  try (assert (x = Vlong n1) by (eapply is_longconst_sound; try exacteval H; eauto));
  try (assert (y = Vlong n2) by (eapply is_longconst_sound; try exacteval H1; eauto));
  subst.
- simpl in C; inv C. Triv.
- Triv. simpl. rewrite Val.swap_cmplu_bool. rewrite C; simpl; auto. 
  rewrite <- FP.fp_union_assoc, (FP.union_comm_eq fpx). TrivFP.
- Triv. simpl. rewrite C; simpl; auto.
  rewrite (FP.union_comm_eq fpx fpy), <- FP.fp_union_assoc, (FP.union_comm_eq fpy). TrivFP.
- Triv. simpl; rewrite C; simpl; auto.
Qed.

Theorem eval_cmpl_fp:
  forall c le a x fpx b y fpy v,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.cmpl c x y = Some v ->
  exists fp', eval_expr_fp ge sp e m le (cmpl c a b) fp' /\ FP.subset fp' (FP.union fpx fpy).
Proof.
  unfold cmpl; intros. destruct Archi.splitlong eqn:SL.
  eapply eval_cmpl_fp; eauto.
  unfold Val.cmpl in H3.
  destruct (Val.cmpl_bool c x y) as [vb|] eqn:C; simpl in H3; inv H3.
  destruct (is_longconst a) as [n1|] eqn:LC1; destruct (is_longconst b) as [n2|] eqn:LC2;
  try (assert (x = Vlong n1) by (eapply is_longconst_sound; try exacteval H; eauto));
  try (assert (y = Vlong n2) by (eapply is_longconst_sound; try exacteval H1; eauto));
  subst.
- simpl in C; inv C. Triv.
- Triv. simpl. rewrite Val.swap_cmpl_bool. rewrite C; simpl; auto.
  simpl. rewrite Val.swap_cmpl_bool. rewrite C; simpl; auto.
- Triv; simpl; rewrite C; simpl; auto.
- Triv; simpl; rewrite C; simpl; auto.
Qed.

Ltac findhelper:= DeclHelper;
                  match goal with
                  | [H: context[Genv.find_symbol _ ?id],
                        H1: (helper_declared _ ?id _ _ ),
                            H2: context[Genv.find_funct_ptr _ _] |- _ ] =>
                    let b := fresh in
                    let A := fresh in
                    let B := fresh in
                    eapply find_def_symbol in H1; eauto; destruct H1 as [b [A B]];
                    unfold fundef, Genv.find_funct_ptr in *; simpl in *;
                    rewrite H in A; inv A; rewrite B in H2; inv H2
                  end.

Theorem eval_longoffloat_fp: unary_constructor_fp_sound longoffloat.
Proof.
  unfold longoffloat; red; intros. destruct Archi.splitlong eqn:SL; inv H1; InvEval; eqexpr. 
  eexists. split. econstructor; eauto. findhelper. constructor.
  repeat econstructor; eauto. repeat econstructor; eauto. TrivFP.
  Triv; simpl. rewrite H7. auto.
Qed.

Theorem eval_floatoflong_fp: unary_constructor_fp_sound floatoflong.
Proof.
  unfold floatoflong; red; intros. destruct Archi.splitlong eqn:SL; inv H1; InvEval; eqexpr. 
  eexists. split. econstructor; eauto. findhelper. constructor.
  repeat econstructor; eauto. repeat econstructor; eauto. TrivFP.
  Triv; simpl. rewrite H7. auto.
Qed.

Theorem eval_longofsingle_fp: unary_constructor_fp_sound longofsingle.
Proof.
  unfold longofsingle; red; intros. destruct Archi.splitlong eqn:SL; inv H1; InvEval; eqexpr.
  inv H4; InvEval; eqexpr. 
  eexists. split. econstructor; eauto. findhelper. constructor.
  repeat econstructor; simpl; eauto. repeat econstructor; eauto. TrivFP.
  Triv; simpl. rewrite H7. auto.
Qed.

Theorem eval_singleoflong_fp: unary_constructor_fp_sound singleoflong.
Proof.
  unfold singleoflong; red; intros. destruct Archi.splitlong eqn:SL; inv H1; InvEval; eqexpr.
  eexists. split. econstructor; eauto. findhelper. constructor.
  repeat econstructor; eauto. repeat econstructor; eauto. TrivFP.
  Triv; simpl. rewrite H7. auto.
Qed.

End CMCONSTR.
