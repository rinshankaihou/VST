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

(** * Correctness of the translation from Clight to C#minor. *)

Require Import Coqlib Errors Maps Integers Floats.
Require Import AST Linking.
Require Import Values Events Memory Globalenvs Smallstep.
Require Import Ctypes Cshmgen.


Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        Op_fp ClightLang Cminor_op_footprint cshmgen.

Require Import  Cop Clight Clight_local Cminor Cminor_local Csharpminor Csharpminor_local Cop_fp_local selection_proof.

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.
(** * Relational specification of the transformation *)
Ltac bexpr:=
  match goal with
  | H:_|- eval_constant _ = Some _ => simpl;eauto
  | H:_|- eval_unop _ _ = Some _ => simpl;eauto
  | H:_|- eval_binop _ _ _ _ = Some _ => simpl;eauto
  | H:_|- eval_binop_fp _ _ _ _ = Some _ => simpl;eauto
  | H:_|- eval_expr_fp _ _ _ _ _ _ => econstructor;eauto
  | H:_|- eval_expr _ _ _ _ _ _ => econstructor;eauto
  end.
Ltac empfp:=
  repeat rewrite FP.fp_union_emp;repeat rewrite FP.emp_union_fp;auto.
Ltac inv_eq:=
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; inversion H ;subst
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;subst;try contradiction;try discriminate.
Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Inductive match_fundef (p: clight_comp_unit) : Clight.fundef -> Csharpminor.fundef -> Prop :=
  | match_fundef_internal: forall f tf,
      transl_function p.(cu_comp_env) f = OK tf ->
      match_fundef p (Ctypes.Internal f) (AST.Internal tf)
  | match_fundef_external: forall ef args res cc,
      ef_sig ef = signature_of_type args res cc ->
      match_fundef p (Ctypes.External ef args res cc) (AST.External ef).

Definition match_varinfo (v: type) (tv: unit) := True.

Definition match_cu (scu: clight_comp_unit) (tcu: Csharpminor_local.comp_unit) :=
  match_comp_unit_gen (match_fundef scu) match_varinfo scu tcu.

Lemma transl_program_match:
  forall scu tcu, transl_program scu = OK tcu -> match_cu scu tcu.
Proof.
  unfold transl_program; intros.
  eapply match_transform_partial_cunit2.
  eexact H.
- intros. destruct f; simpl in H0.
+ monadInv H0. constructor; auto.
+ destruct (signature_eq (ef_sig e) (signature_of_type t t0 c)); inv H0.
  constructor; auto.
- intros; red; auto.
Qed.

(** * Properties of operations over types *)

Remark transl_params_types:
  forall params,
  map typ_of_type (map snd params) = typlist_of_typelist (type_of_params params).
Proof.
  induction params; simpl. auto. destruct a as [id ty]; simpl. f_equal; auto.
Qed.

Lemma transl_fundef_sig1:
  forall ce f tf args res cc,
  match_fundef ce f tf ->
  classify_fun (type_of_fundef f) = fun_case_f args res cc ->
  funsig tf = signature_of_type args res cc.
Proof.
  intros. inv H.
- monadInv H1. simpl. inversion H0.
  unfold signature_of_function, signature_of_type.
  f_equal. apply transl_params_types.
- simpl in H0. unfold funsig. congruence.
Qed.

Lemma transl_fundef_sig2:
  forall ce f tf args res cc,
  match_fundef ce f tf ->
  type_of_fundef f = Tfunction args res cc ->
  funsig tf = signature_of_type args res cc.
Proof.
  intros. eapply transl_fundef_sig1; eauto.
  rewrite H0; reflexivity.
Qed.

Lemma transl_sizeof:
  forall (cunit: clight_comp_unit) t sz,
  Cshmgen.sizeof cunit.(cu_comp_env) t = OK sz ->
  sz = Ctypes.sizeof cunit.(cu_comp_env) t.
Proof.
  intros. unfold Cshmgen.sizeof in H.
  destruct (complete_type (cu_comp_env cunit) t) eqn:C; inv H.
  symmetry. 
  apply Ctypes.sizeof_stable; auto.
Qed.

Lemma transl_alignof:
  forall (cunit: clight_comp_unit) t al,
  Cshmgen.alignof cunit.(cu_comp_env) t = OK al ->
  al = Ctypes.alignof cunit.(cu_comp_env) t.
Proof.
  intros.
  unfold alignof in H. destruct (complete_type (cu_comp_env cunit) t) eqn:C; inv H.
  symmetry. apply Ctypes.alignof_stable; auto.
Qed.

Lemma transl_alignof_blockcopy:
  forall (cunit:clight_comp_unit) t sz,
  sizeof cunit.(cu_comp_env) t = OK sz ->
  sz = Ctypes.sizeof cunit.(cu_comp_env) t /\
  alignof_blockcopy cunit.(cu_comp_env) t = alignof_blockcopy cunit.(cu_comp_env) t.
Proof.
  intros. 
  unfold sizeof in H. destruct (complete_type (cu_comp_env cunit) t) eqn:C; inv H.
  split.
- symmetry. apply Ctypes.sizeof_stable; auto.
- revert C. induction t; simpl; auto;
  destruct (prog_comp_env cunit)!i as [co|] eqn:X; try discriminate; erewrite H0 by eauto; auto.
Qed.

Lemma field_offset_stable:
  forall (cunit:clight_comp_unit) id co f,
  cunit.(cu_comp_env)!id = Some co ->
  cunit.(cu_comp_env)!id = Some co /\
  field_offset cunit.(cu_comp_env) f (co_members co) = field_offset cunit.(cu_comp_env) f (co_members co).
Proof.
  split;auto.
Qed.


(** * Properties of the translation functions *)

(** Transformation of expressions and statements. *)

Lemma transl_expr_lvalue:
  forall ge e le m a loc ofs ce ta,
  Clight.eval_lvalue ge e le m a loc ofs ->
  transl_expr ce a = OK ta ->
  (exists tb, transl_lvalue ce a = OK tb /\ make_load tb (typeof a) = OK ta).
Proof.
  intros until ta; intros EVAL TR. inv EVAL; simpl in TR.
  (* var local *)
  exists (Eaddrof id); auto.
  (* var global *)
  exists (Eaddrof id); auto.
  (* deref *)
  monadInv TR. exists x; auto.
  (* field struct *)
  monadInv TR. exists x0; split; auto. simpl; rewrite EQ; auto.
  (* field union *)
  monadInv TR. exists x0; split; auto. simpl; rewrite EQ; auto.
Qed.

(** Properties of labeled statements *)

Lemma transl_lbl_stmt_1:
  forall ce tyret nbrk ncnt n sl tsl,
  transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
  transl_lbl_stmt ce tyret nbrk ncnt (Clight.select_switch n sl) = OK (select_switch n tsl).
Proof.
  intros until n.
  assert (DFL: forall sl tsl,
    transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
    transl_lbl_stmt ce tyret nbrk ncnt (Clight.select_switch_default sl) = OK (select_switch_default tsl)).
  {
    induction sl; simpl; intros.
    inv H; auto.
    monadInv H. simpl. destruct o; eauto. simpl; rewrite EQ; simpl; rewrite EQ1; auto.
  }
  assert (CASE: forall sl tsl,
    transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
    match Clight.select_switch_case n sl with
    | None =>
        select_switch_case n tsl = None
    | Some sl' =>
        exists tsl',
           select_switch_case n tsl = Some tsl'
        /\ transl_lbl_stmt ce tyret nbrk ncnt sl' = OK tsl'
    end).
  {
    induction sl; simpl; intros.
    inv H; auto.
    monadInv H; simpl. destruct o. destruct (zeq z n).
    econstructor; split; eauto. simpl; rewrite EQ; simpl; rewrite EQ1; auto.
    apply IHsl; auto.
    apply IHsl; auto.
  }
  intros. specialize (CASE _ _ H). unfold Clight.select_switch, select_switch.
  destruct (Clight.select_switch_case n sl) as [sl'|].
  destruct CASE as [tsl' [P Q]]. rewrite P, Q. auto.
  rewrite CASE. auto.
Qed.

Lemma transl_lbl_stmt_2:
  forall ce tyret nbrk ncnt sl tsl,
  transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
  transl_statement ce tyret nbrk ncnt (seq_of_labeled_statement sl) = OK (seq_of_lbl_stmt tsl).
Proof.
  induction sl; intros.
  monadInv H. auto.
  monadInv H. simpl. rewrite EQ; simpl. rewrite (IHsl _ EQ1). simpl. auto.
Qed.

(** * Correctness of Csharpminor construction functions *)

Section CONSTRUCTORS.
Variable cunit: clight_comp_unit.
(*Variables cunit prog: Clight.program.
Hypothesis LINK: linkorder cunit prog.*)
  Variable ge: genv.
Lemma make_intconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_intconst n) (Vint n).
Proof.
  intros. unfold make_intconst. econstructor. reflexivity.
Qed.

Lemma make_intconst_fp_correct:
  forall n e le m,
    eval_expr_fp ge e le m (make_intconst n) empfp.
Proof. econstructor;simpl;eauto. Qed.

Lemma make_floatconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_floatconst n) (Vfloat n).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity.
Qed.

Lemma make_floatconst_fp_correct:
  forall n e le m,
    eval_expr_fp ge e le m (make_floatconst n) empfp.
Proof. econstructor;simpl;eauto. Qed.

Lemma make_singleconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_singleconst n) (Vsingle n).
Proof.
  intros. unfold make_singleconst. econstructor. reflexivity.
Qed.

Lemma make_singleconst_fp_correct:
  forall n e le m,
    eval_expr_fp ge e le m (make_singleconst n) empfp.
Proof. econstructor;simpl;eauto. Qed.

Lemma make_longconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_longconst n) (Vlong n).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity.
Qed.

Lemma make_longconst_fp_correct:
  forall n e le m,
    eval_expr_fp ge e le m (make_longconst n) empfp.
Proof. econstructor;simpl;eauto. Qed.

Lemma make_ptrofsconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_ptrofsconst n) (Vptrofs (Ptrofs.repr n)).
Proof.
  intros. unfold Vptrofs, make_ptrofsconst. destruct Archi.ptr64 eqn:SF.
- replace (Ptrofs.to_int64 (Ptrofs.repr n)) with (Int64.repr n).
  apply make_longconst_correct.
  symmetry; auto with ptrofs.
- replace (Ptrofs.to_int (Ptrofs.repr n)) with (Int.repr n).
  apply make_intconst_correct.
  symmetry; auto with ptrofs.
Qed.

Lemma make_ptrofsconst_fp_correct:
  forall n e le m,
    eval_expr_fp ge e le m (make_ptrofsconst n) empfp.
Proof. econstructor;simpl;eauto. Qed.

Lemma make_singleoffloat_correct:
  forall a n e le m,
  eval_expr ge e le m a (Vfloat n) ->
  eval_expr ge e le m (make_singleoffloat a) (Vsingle (Float.to_single n)).
Proof.
  intros. econstructor. eauto. auto.
Qed.

Lemma make_singleoffloat_fp_correct:
  forall a n e le m fp,
    eval_expr ge e le m a (Vfloat n)->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m (make_singleoffloat a) fp.
Proof. econstructor;simpl;eauto. Qed.

Lemma make_floatofsingle_correct:
  forall a n e le m,
  eval_expr ge e le m a (Vsingle n) ->
  eval_expr ge e le m (make_floatofsingle a) (Vfloat (Float.of_single n)).
Proof.
  intros. econstructor. eauto. auto.
Qed.

Lemma make_floatofsingle_fp_correct:
  forall a n e le m fp,
    eval_expr ge e le m a (Vsingle n)->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m (make_floatofsingle a) fp.
Proof. econstructor;simpl;eauto. Qed.

Lemma make_floatofint_correct:
  forall a n sg e le m,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_floatofint a sg) (Vfloat(cast_int_float sg n)).
Proof.
  intros. unfold make_floatofint, cast_int_float.
  destruct sg; econstructor; eauto.
Qed.


Lemma make_floatofint_fp_correct:
  forall a n sg e le m fp,
    eval_expr ge e le m a (Vint n)->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m (make_floatofint a sg) fp.
Proof.
  unfold make_floatofint,cast_int_float.
  intros.
  destruct sg;econstructor;simpl;eauto;simpl;eauto.
Qed.


Hint Resolve
     make_intconst_correct make_floatconst_correct make_longconst_correct
     make_singleconst_correct make_singleoffloat_correct make_floatofsingle_correct make_floatofint_correct
     make_intconst_fp_correct make_floatconst_fp_correct make_longconst_fp_correct
     make_singleconst_fp_correct make_singleoffloat_fp_correct make_floatofsingle_fp_correct make_floatofint_fp_correct
  : cshm.
Hint Constructors eval_expr eval_exprlist: cshm.
Hint Extern 2 (@eq trace _ _) => traceEq: cshm.

Lemma make_cmpu_ne_zero_correct:
  forall e le m a n,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_cmpu_ne_zero a) (Vint (if Int.eq n Int.zero then Int.zero else Int.one)).
Proof.
  intros.
  assert (DEFAULT: eval_expr ge e le m (Ebinop (Ocmpu Cne) a (make_intconst Int.zero))
                                       (Vint (if Int.eq n Int.zero then Int.zero else Int.one))).
  { econstructor; eauto with cshm. simpl. unfold Val.cmpu, Val.cmpu_bool.
    unfold Int.cmpu. destruct (Int.eq n Int.zero); auto. }
  assert (CMP: forall ob,
               Val.of_optbool ob = Vint n ->
               n = (if Int.eq n Int.zero then Int.zero else Int.one)).
  { intros. destruct ob; simpl in H0; inv H0. destruct b; inv H2.
    rewrite Int.eq_false. auto. apply Int.one_not_zero.
    rewrite Int.eq_true. auto. }
  destruct a; simpl; auto. destruct b; auto.
- inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. destruct (Val.cmp_bool) eqn:?; inv H6. destruct b; inv H0; eauto.
- inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. destruct (Val.cmpu_bool) eqn:?; inv H6. destruct b; inv H0; eauto. 
- inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. destruct (Val.cmpf_bool) eqn:?; inv H6. destruct b; inv H0; eauto. 
- inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. destruct (Val.cmpfs_bool) eqn:?; inv H6. destruct b; inv H0; eauto. 
- inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. unfold Val.cmpl in H6.
  destruct (Val.cmpl_bool c v1 v2) as [[]|]; inv H6; reflexivity.
- inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. unfold Val.cmplu in H6.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) as [[]|]; inv H6; reflexivity.
Qed.

Lemma make_cmpu_ne_zero_fp_correct:
  forall e le m a n fp,
    eval_expr ge e le m a (Vint n) ->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m (make_cmpu_ne_zero a) fp.
Proof.
  intros; destruct a;simpl;auto; try destruct b;simpl;auto with cshm; econstructor;eauto with cshm;simpl;eauto;repeat rewrite FP.fp_union_emp;auto.
Qed.

Lemma make_cmpu_ne_zero_correct_ptr:
  forall e le m a b i,
  eval_expr ge e le m a (Vptr b i) ->
  Archi.ptr64 = false ->
  Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true ->
  eval_expr ge e le m (make_cmpu_ne_zero a) Vone.
Proof.
  intros.
  assert (DEFAULT: eval_expr ge e le m (Ebinop (Ocmpu Cne) a (make_intconst Int.zero)) Vone).
  { econstructor; eauto with cshm. simpl. unfold Val.cmpu, Val.cmpu_bool.
    unfold Mem.weak_valid_pointer in H1. rewrite H0, H1.
    rewrite Int.eq_true; auto. }
  assert (OF_OPTBOOL: forall ob, Some (Val.of_optbool ob) <> Some (Vptr b i)).
  { intros. destruct ob as [[]|]; discriminate. }
  assert (OF_BOOL: forall ob, option_map Val.of_bool ob <> Some (Vptr b i)).
  { intros. destruct ob as [[]|]; discriminate. }
  destruct a; simpl; auto. destruct b0; auto.
  Ltac OMelim:=
    match goal with
    | H: option_map _ ?x = _ |- _ => destruct x eqn:?; inv H
    | _ => idtac
    end.
- inv H; eelim OF_OPTBOOL; eauto. simpl in H8. instantiate (1:= Some false). OMelim. destruct b0; inv H2.
- inv H; eelim OF_OPTBOOL; eauto. simpl in H8. instantiate (1:= Some false). OMelim. destruct b0; inv H2.
- inv H; eelim OF_OPTBOOL; eauto. simpl in H8. instantiate (1:= Some false). OMelim. destruct b0; inv H2.
- inv H; eelim OF_OPTBOOL; eauto. simpl in H8. instantiate (1:= Some false). OMelim. destruct b0; inv H2.
- inv H; eelim OF_BOOL; eauto.
- inv H; eelim OF_BOOL; eauto.
Qed.



Definition make_cmpu_ne_zero_ptr_fp:=
  fun e m b i fp =>
  match e with
  | Ebinop (Ocmp _) _ _ => fp
  | Ebinop (Ocmpu _) _ _ => fp
  | Ebinop (Ocmpf _) _ _ => fp
  | Ebinop (Ocmpfs _) _ _ => fp
  | Ebinop (Ocmpl _) _ _ => fp
  | Ebinop (Ocmplu _) _ _ => fp
  | _ => FP.union fp (MemOpFP.weak_valid_pointer_fp m b (Ptrofs.unsigned i))
end.
Lemma make_cmpu_ne_zero_ptr_fp_correct:
  forall ge e le a m b i fp,
    eval_expr ge e le m a (Vptr b i)->
    make_cmpu_ne_zero_ptr_fp a m b i fp = FP.union fp (MemOpFP.weak_valid_pointer_fp m b (Ptrofs.unsigned i)).
Proof.
  unfold make_cmpu_ne_zero_ptr_fp;intros.
  destruct a;auto;destruct b0 ;auto; inv H; inv H6;unfold option_map,Val.of_bool in H0;[destruct Val.cmp_bool|destruct Val.cmpu_bool|destruct Val.cmpf_bool|destruct Val.cmpfs_bool| |destruct Val.cmplu_bool];inv H0;try destruct b0;inv H1.
  unfold Val.cmpl in H0. unfold option_map,Val.of_bool,Val.cmpl_bool in H0.
  destruct v1;inv H0. destruct v2;inv H1.
  destruct (Int64.cmp) ;inv H0.
Qed.
Lemma make_cmpu_ne_zero_fp_correct_ptr:
  forall e le m a b i fp,
    eval_expr ge e le m a (Vptr b i) ->
    eval_expr_fp ge e le m a fp->
    Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true ->
    eval_expr_fp ge e le m (make_cmpu_ne_zero a)(make_cmpu_ne_zero_ptr_fp a m b i fp).
Proof.
  unfold Mem.weak_valid_pointer;intros.
  assert(Archi.ptr64 = false). auto. assert(Int.eq Int.zero Int.zero=true). auto.
  destruct a;simpl;auto;try destruct b0;simpl;auto with cshm;try(econstructor;eauto with cshm;simpl;eauto;try rewrite H1,H2,H3;simpl;eauto;rewrite H2,H3,FP.fp_union_emp;auto;fail).
Qed.
Lemma make_cast_int_correct:
  forall e le m a n sz si,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_cast_int a sz si) (Vint (cast_int_int sz si n)).
Proof.
  intros. unfold make_cast_int, cast_int_int.
  destruct sz.
  destruct si; eauto with cshm.
  destruct si; eauto with cshm.
  auto.
  apply make_cmpu_ne_zero_correct; auto.
Qed.

Lemma make_cast_int_fp_correct:
  forall e le m a n sz si fp,
    eval_expr ge e le m a (Vint n) ->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m (make_cast_int a sz si) fp.
Proof.
  intros; unfold make_cast_int,cast_int_int;  destruct sz;auto;destruct si;eauto with cshm;try econstructor;simpl;eauto;eapply make_cmpu_ne_zero_fp_correct;eauto.
Qed.

Lemma make_longofint_correct:
  forall e le m a n si,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_longofint a si) (Vlong (cast_int_long si n)).
Proof.
  intros. unfold make_longofint, cast_int_long. destruct si; eauto with cshm.
Qed.

Lemma make_longofint_fp_correct:
  forall e le m a n si fp,
    eval_expr ge e le m a (Vint n) ->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m (make_longofint a si) fp.
Proof.
  intros; unfold make_longofint, cast_int_long; destruct si;eauto with cshm;econstructor;eauto;simpl;eauto.
Qed.
Hint Resolve make_cast_int_correct make_longofint_correct make_cast_int_fp_correct make_longofint_fp_correct: cshm.

Ltac InvEval :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; InvEval
  | [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x eqn:?; InvEval
  | [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; InvEval
  | _ => idtac
  end.

Lemma make_cast_correct:
  forall e le m a b v ty1 ty2 v',
  make_cast ty1 ty2 a = OK b ->
  eval_expr ge e le m a v ->
  sem_cast v ty1 ty2 m = Some v' ->
  eval_expr ge e le m b v'.
Proof.
  intros. unfold make_cast, sem_cast in *;
  destruct (classify_cast ty1 ty2); inv H; destruct v; InvEval; eauto with cshm.
- (* single -> int *)
  unfold make_singleofint, cast_int_float. destruct si1; eauto with cshm.
- (* float -> int *)
  apply make_cast_int_correct.
  unfold cast_float_int in Heqo. unfold make_intoffloat.
  destruct si2; econstructor; eauto; simpl; rewrite Heqo; auto.
- (* single -> int *)
  apply make_cast_int_correct.
  unfold cast_single_int in Heqo. unfold make_intofsingle.
  destruct si2; econstructor; eauto with cshm; simpl; rewrite Heqo; auto.
- (* long -> float *)
  unfold make_floatoflong, cast_long_float. destruct si1; eauto with cshm.
- (* long -> single *)
  unfold make_singleoflong, cast_long_single. destruct si1; eauto with cshm.
- (* float -> long *)
  unfold cast_float_long in Heqo. unfold make_longoffloat.
  destruct si2; econstructor; eauto; simpl; rewrite Heqo; auto.
- (* single -> long *)
  unfold cast_single_long in Heqo. unfold make_longofsingle.
  destruct si2; econstructor; eauto with cshm; simpl; rewrite Heqo; auto.
- (* int -> bool *)
  apply make_cmpu_ne_zero_correct; auto.
- (* pointer (32 bits) -> bool *)
  eapply make_cmpu_ne_zero_correct_ptr; eauto.
- (* long -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmplu, Val.cmplu_bool, Int64.cmpu.
  destruct (Int64.eq i Int64.zero); auto.
- (* pointer (64 bits) -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmplu, Val.cmplu_bool. unfold Mem.weak_valid_pointer in Heqb1.
  rewrite Heqb0, Heqb1. rewrite Int64.eq_true. reflexivity.
- (* float -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmpf, Val.cmpf_bool. rewrite Float.cmp_ne_eq.
  destruct (Float.cmp Ceq f Float.zero); auto.
- (* single -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmpfs, Val.cmpfs_bool. rewrite Float32.cmp_ne_eq.
  destruct (Float32.cmp Ceq f Float32.zero); auto.
- (* struct *)
  destruct (ident_eq id1 id2); inv H1; auto.
- (* union *)
  destruct (ident_eq id1 id2); inv H1; auto.
Qed.
    
Lemma make_cast_fp_correct:
  forall e le m a b v ty1 ty2 v' fp fp',
  make_cast ty1 ty2 a = OK b ->
  eval_expr ge e le m a v ->
  sem_cast v ty1 ty2 m = Some v' ->
  Cop_fp_local.sem_cast_fp v ty1 ty2 m = Some fp'->
  eval_expr_fp ge e le m a fp ->
  eval_expr_fp ge e le m b (FP.union fp fp').
Proof.
  intros.
  unfold Cop_fp_local.sem_cast_fp,make_cast, sem_cast in *;
    destruct (classify_cast ty1 ty2) eqn:?; inv H; destruct v; InvEval; eauto with cshm; try rewrite FP.fp_union_emp;auto;eauto with cshm.
  - unfold make_singleofint.  destruct si1; econstructor;eauto; simpl;eauto.
  - eapply make_cast_int_fp_correct;eauto with cshm;destruct si2; inv Heqo;econstructor;eauto;simpl;eauto;rewrite H1;simpl;eauto.
  - eapply make_cast_int_fp_correct;eauto with cshm;destruct si2; inv Heqo;econstructor;eauto;simpl;eauto;rewrite H1;simpl;eauto.
  - eapply make_cast_int_fp_correct;eauto with cshm;econstructor;eauto;simpl;eauto.
  - unfold make_floatoflong. destruct si1;econstructor;eauto;simpl;eauto.
  - unfold make_singleoflong. destruct si1;econstructor;eauto;simpl;eauto.
  - unfold make_longoffloat. destruct si2;econstructor;eauto;simpl;eauto; inv Heqo;rewrite H1;simpl;eauto.
  - unfold make_longofsingle. destruct si2;econstructor;eauto;simpl;eauto;inv Heqo;rewrite H1;simpl;eauto.
  - eapply make_cmpu_ne_zero_fp_correct;eauto.
  - eapply make_cmpu_ne_zero_fp_correct_ptr in Heqb1;eauto.
    erewrite<- make_cmpu_ne_zero_ptr_fp_correct;eauto.
  - econstructor;eauto with cshm;simpl;eauto;repeat rewrite FP.fp_union_emp;auto.
  - assert(Archi.ptr64 = false). auto.
    rewrite H in Heqb0. inv Heqb0.
  - econstructor;eauto with cshm;simpl;eauto;repeat rewrite FP.fp_union_emp;auto.
  - econstructor;eauto with cshm;simpl;eauto;repeat rewrite FP.fp_union_emp;auto.
  - destruct (ident_eq id1 id2) eqn:?;inv H1;inv H2. rewrite FP.fp_union_emp;auto.
  - destruct (ident_eq id1 id2) eqn:?;inv H1;inv H2. rewrite FP.fp_union_emp;auto.
Qed.
Lemma make_boolean_correct:
 forall e le m a v ty b,
  eval_expr ge e le m a v ->
  bool_val v ty m = Some b ->
  exists vb,
    eval_expr ge e le m (make_boolean a ty) vb
    /\ Val.bool_of_val vb b.
Proof.
  intros. unfold make_boolean. unfold bool_val in H0.
  destruct (classify_bool ty); destruct v; InvEval.
- (* int *)
  econstructor; split. apply make_cmpu_ne_zero_correct with (n := i); auto.
  destruct (Int.eq i Int.zero); simpl; constructor.
- (* ptr 32 bits *)
  exists Vone; split. eapply make_cmpu_ne_zero_correct_ptr; eauto. constructor.
- (* long *)
  econstructor; split. econstructor; eauto with cshm. simpl. unfold Val.cmplu. simpl. eauto.
  destruct (Int64.eq i Int64.zero); simpl; constructor.
- (* ptr 64 bits *)
  exists Vone; split.
  econstructor; eauto with cshm. simpl. unfold Val.cmplu, Val.cmplu_bool.
  unfold Mem.weak_valid_pointer in Heqb0. rewrite Heqb0, Heqb1, Int64.eq_true. reflexivity.
  constructor.
- (* float *)
  econstructor; split. econstructor; eauto with cshm. simpl. eauto.
  unfold Val.cmpf, Val.cmpf_bool. simpl. rewrite <- Float.cmp_ne_eq.
  destruct (Float.cmp Cne f Float.zero); constructor.
- (* single *)
  econstructor; split. econstructor; eauto with cshm. simpl. eauto.
  unfold Val.cmpfs, Val.cmpfs_bool. simpl. rewrite <- Float32.cmp_ne_eq.
  destruct (Float32.cmp Cne f Float32.zero); constructor.
Qed.
Lemma make_boolean_fp_correct:
 forall e le m a v ty b vb fp fp',
   eval_expr ge e le m a v ->
   eval_expr_fp ge e le m a fp ->
   bool_val v ty m = Some b ->
   Cop_fp_local.bool_val_fp v ty m = Some fp'->
   Val.bool_of_val vb b ->
   eval_expr_fp ge e le m (make_boolean a ty) (FP.union fp fp').
Proof.
  intros.
  unfold bool_val,make_boolean,Cop_fp_local.bool_val_fp in *.
  destruct (classify_bool ty) eqn:?;destruct v;inv H1;inv H2;try rewrite FP.fp_union_emp;auto.
  { eapply make_cmpu_ne_zero_fp_correct;eauto. }
  { assert(Archi.ptr64 = false). auto.
    rewrite H1 in *.
    destruct (Mem.weak_valid_pointer) eqn:?;inv H5.
    enough(FP.union fp (MemOpFP.weak_valid_pointer_fp m b0 (Ptrofs.unsigned i))= make_cmpu_ne_zero_ptr_fp a m b0 i fp).
    rewrite H2;auto. eapply make_cmpu_ne_zero_fp_correct_ptr;eauto.
    erewrite<- make_cmpu_ne_zero_ptr_fp_correct;eauto. }
  all: econstructor;eauto with cshm;simpl;eauto;rewrite ! FP.fp_union_emp;auto.
Qed.
Lemma make_neg_correct:
  forall a tya c va v e le m,
  sem_neg va tya = Some v ->
  make_neg a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_neg, make_neg; intros until m; intros SEM MAKE EV1;
  destruct (classify_neg tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
Qed.
Lemma make_neg_fp_correct:
  forall a tya c va v e le m fp,
  sem_neg va tya = Some v ->
  make_neg a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr_fp ge e le m a fp->
  eval_expr_fp ge e le m c fp.
Proof.
  unfold sem_neg, make_neg;intros until fp;intros SEM MAKE EV1 FP.
  destruct (classify_neg tya);inv MAKE;destruct va;inv SEM; eauto with cshm;econstructor;eauto;simpl;eauto.
Qed.
Lemma make_absfloat_correct:
  forall a tya c va v e le m,
  sem_absfloat va tya = Some v ->
  make_absfloat a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_absfloat, make_absfloat; intros until m; intros SEM MAKE EV1;
  destruct (classify_neg tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
  unfold make_floatoflong, cast_long_float. destruct s.
  econstructor. econstructor; simpl; eauto. simpl; eauto. simpl; eauto.
  econstructor. econstructor; simpl; eauto. simpl; eauto. simpl; eauto.
Qed.
Lemma make_absfloat_fp_correct:
  forall a tya c va v e le m fp,
  sem_absfloat va tya = Some v ->
  make_absfloat a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr_fp ge e le m a fp->
  eval_expr_fp ge e le m c fp.
Proof.
  unfold sem_absfloat, make_absfloat;intros until fp; intros SEM MAKE EV1 FP.
  destruct (classify_neg tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
  1-3:  econstructor;eauto with cshm;simpl;eauto.
  unfold make_floatoflong. destruct s;  econstructor;eauto with cshm;simpl;eauto; econstructor;eauto;simpl;eauto.
Qed.
Lemma make_notbool_correct:
  forall a tya c va v e le m,
  sem_notbool va tya m = Some v ->
  make_notbool a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_notbool, bool_val, make_notbool; intros until m; intros SEM MAKE EV1.
  destruct (classify_bool tya); inv MAKE; destruct va; simpl in SEM; InvEval.
- econstructor; eauto with cshm. simpl. unfold Val.cmpu, Val.cmpu_bool, Int.cmpu.
  destruct (Int.eq i Int.zero); auto.
- destruct Archi.ptr64 eqn:SF; inv SEM.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) eqn:V; simpl in H0; inv H0.
  econstructor; eauto with cshm. simpl. unfold Val.cmpu, Val.cmpu_bool.
  unfold Mem.weak_valid_pointer in V. rewrite SF, V, Int.eq_true. auto.
- econstructor; eauto with cshm. simpl. unfold Val.cmplu, Val.cmplu_bool, Int64.cmpu.
  destruct (Int64.eq i Int64.zero); auto.
- destruct Archi.ptr64 eqn:SF; inv SEM.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) eqn:V; simpl in H0; inv H0.
  econstructor; eauto with cshm. simpl. unfold Val.cmplu, Val.cmplu_bool.
  unfold Mem.weak_valid_pointer in V. rewrite SF, V, Int64.eq_true. auto.
- econstructor; eauto with cshm. simpl. unfold Val.cmpf, Val.cmpf_bool.
  destruct (Float.cmp Ceq f Float.zero); auto.
- econstructor; eauto with cshm. simpl. unfold Val.cmpfs, Val.cmpfs_bool.
  destruct (Float32.cmp Ceq f Float32.zero); auto.
Qed.
Lemma make_notbool_fp_correct:
  forall a tya c va v e le m fp fp',
    sem_notbool va tya m= Some v ->
    Cop_fp_local.sem_notbool_fp va tya m = Some fp'->
    make_notbool a tya = OK c ->
    eval_expr ge e le m a va ->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m c (FP.union fp fp').
Proof.
  unfold Cop_fp_local.sem_notbool_fp, sem_notbool,Cop_fp_local.bool_val_fp, bool_val, make_notbool; intros until fp'; intros SEM SEMFP MAKE EV1 FP.
  destruct (classify_bool tya) eqn:?; inv MAKE; destruct va; simpl in SEM,SEMFP; InvEval.
  all: try(econstructor;eauto with cshm;simpl;eauto;repeat rewrite FP.fp_union_emp;auto;fail);try discriminate.
  destruct Archi.ptr64 eqn:?;inv SEM;try discriminate.
  destruct Mem.weak_valid_pointer eqn:?;inv H0.
  unfold Mem.weak_valid_pointer in Heqb2.
  assert(Int.eq Int.zero Int.zero = true). auto.
  econstructor;eauto with cshm;simpl;eauto.
  rewrite Heqb1,Heqb2,H;eauto. simpl;eauto.
  rewrite! FP.fp_union_emp;auto.
Qed.
Lemma make_notint_correct:
  forall a tya c va v e le m,
  sem_notint va tya = Some v ->
  make_notint a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_notint, make_notint; intros until m; intros SEM MAKE EV1;
  destruct (classify_notint tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
Qed.

Lemma make_notint_fp_correct:
  forall a tya c va  e le m fp,
  make_notint a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr_fp ge e le m a fp->
  eval_expr_fp ge e le m c fp.
Proof.
  unfold sem_notint, make_notint; intros until fp; intros  MAKE EV1 FP.
  destruct (classify_notint tya); inv MAKE; destruct va; eauto with cshm;econstructor;eauto;simpl;eauto.
Qed.
  
Definition binary_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> type -> val -> type -> mem -> option val): Prop :=
  forall a tya b tyb c va vb v e le m,
  sem va tya vb tyb m = Some v ->
  make a tya b tyb = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.    

Definition binary_fp_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> type -> val -> type -> mem -> option val)
    (semfp: val -> type -> val -> type -> mem -> option footprint): Prop :=
  forall a tya b tyb c va vb v e le m fpa fpb fpc,
  sem va tya vb tyb m = Some v->
  semfp va tya vb tyb m = Some fpc ->
  make a tya b tyb = OK c ->
  eval_expr ge e le m a va ->
  eval_expr_fp ge e le m a fpa->
  eval_expr ge e le m b vb ->
  eval_expr_fp ge e le m b fpb->
  eval_expr ge e le m c v->
  eval_expr_fp ge e le m c (FP.union (FP.union fpa fpb) fpc).
Definition shift_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> type -> val -> type -> option val): Prop :=
  forall a tya b tyb c va vb v e le m,
  sem va tya vb tyb = Some v ->
  make a tya b tyb = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.
Definition shift_fp_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> type -> val -> type  -> option val)
    (semfp: val -> type -> val -> type -> option footprint): Prop :=
  forall a tya b tyb c va vb v e le m fpa fpb fpc,
  sem va tya vb tyb  = Some v->
  semfp va tya vb tyb  = Some fpc ->
  make a tya b tyb = OK c ->
  eval_expr ge e le m a va ->
  eval_expr_fp ge e le m a fpa->
  eval_expr ge e le m b vb ->
  eval_expr_fp ge e le m b fpb->
  eval_expr ge e le m c v->
  eval_expr_fp ge e le m c (FP.union (FP.union fpa fpb) fpc).
Section MAKE_BIN.

Variable sem_int: signedness -> int -> int -> option val.
Variable sem_long: signedness -> int64 -> int64 -> option val.
Variable sem_float: float -> float -> option val.
Variable sem_single: float32 -> float32 -> option val.

Variables iop iopu fop sop lop lopu: binary_operation.


Hypothesis iop_ok:
  forall x y m, eval_binop iop (Vint x) (Vint y) m = sem_int Signed x y.
Hypothesis iopu_ok:
  forall x y m, eval_binop iopu (Vint x) (Vint y) m = sem_int Unsigned x y.
Hypothesis lop_ok:
  forall x y m, eval_binop lop (Vlong x) (Vlong y) m = sem_long Signed x y.
Hypothesis lopu_ok:
  forall x y m, eval_binop lopu (Vlong x) (Vlong y) m = sem_long Unsigned x y.
Hypothesis fop_ok:
  forall x y m, eval_binop fop (Vfloat x) (Vfloat y) m = sem_float x y.
Hypothesis sop_ok:
  forall x y m, eval_binop sop (Vsingle x) (Vsingle y) m = sem_single x y.

Hypothesis iopfp_ok:
  forall x y v m, eval_binop iop (Vint x)(Vint y) m = Some v ->eval_binop_fp iop (Vint x) (Vint y) m = Some empfp.
Hypothesis iopufp_ok:
  forall x y v m, eval_binop iopu (Vint x)(Vint y) m = Some v -> eval_binop_fp iopu (Vint x) (Vint y) m = Some empfp.
Hypothesis lopfp_ok:
  forall x y v m, eval_binop lop (Vlong x)(Vlong y) m = Some v ->eval_binop_fp lop (Vlong x) (Vlong y) m = Some empfp.
Hypothesis lopufp_ok:
  forall x y v m, eval_binop lopu (Vlong x)(Vlong y) m = Some v -> eval_binop_fp lopu (Vlong x) (Vlong y) m = Some empfp.
Hypothesis fopfp_ok:
  forall x y v m,eval_binop fop (Vfloat x)(Vfloat y) m = Some v -> eval_binop_fp fop (Vfloat x) (Vfloat y) m = Some empfp.
Hypothesis sopfp_ok:
  forall x y v m, eval_binop sop (Vsingle x)(Vsingle y) m = Some v ->eval_binop_fp sop (Vsingle x) (Vsingle y) m = Some empfp.
Lemma fp_parallel_union_comm:
  forall a b c d, FP.union (FP.union a b)(FP.union c d) = FP.union (FP.union a c)(FP.union b d).
Proof.
  intros;do 2 rewrite<- FP.fp_union_assoc; f_equal.
  rewrite FP.union_comm_eq, <- FP.fp_union_assoc;f_equal.   rewrite FP.union_comm_eq;auto.
Qed.
Ltac ok:= try rewrite iop_ok;try rewrite iopu_ok;try rewrite lop_ok;try rewrite lopu_ok;try rewrite fop_ok;try rewrite sop_ok;eauto.
Ltac fpok:= ok;try erewrite iopfp_ok;try erewrite iopufp_ok;
            try erewrite lopfp_ok;try erewrite lopufp_ok;
            try erewrite fopfp_ok;try erewrite sopfp_ok;
            eauto;ok.
Ltac fpu:= try rewrite ! FP.fp_union_emp;try eapply fp_parallel_union_comm.
Ltac match_sem_cast_fp:=
  let x:=fresh in
  let y:=fresh in
  match goal with
    H: context [ match sem_cast_fp ?va ?tya ?ty ?m with _ => _ end] |- _ =>
    destruct (sem_cast_fp va tya ty m) as [x|] eqn:y;try discriminate;
      eapply make_cast_fp_correct in y;eauto
  end.
Ltac match_sem_cast:=
  let x:=fresh in
  let y:=fresh in
  match goal with
    H: context [ match sem_cast ?va ?tya ?ty ?m with _ => _ end] |- _ =>
    destruct (sem_cast va tya ty m) as [x|] eqn:y;try discriminate;
    try match_sem_cast_fp;
    eapply make_cast_correct in y;eauto
  end.
Ltac solv_sem:= do 2 match_sem_cast;intros;inv_eq;econstructor;eauto;fpok;fpu.
Lemma make_binarith_correct:
  binary_constructor_correct
    (make_binarith iop iopu fop sop lop lopu)
    (sem_binarith sem_int sem_long sem_float sem_single).
Proof.
  red; unfold make_binarith, sem_binarith;intros until m; intros SEM  MAKE EV1 EV2; monadInv MAKE; solv_sem.
Qed.

Lemma make_binarith_fp_correct:
  binary_fp_constructor_correct
    (make_binarith iop iopu fop sop lop lopu)
    (sem_binarith sem_int sem_long sem_float sem_single)
    (Cop_fp_local.sem_binarith_fp sem_int sem_long sem_float sem_single).
Proof with apply fp_parallel_union_comm.
  red;unfold make_binarith, Cop_fp_local.sem_binarith_fp;intros until fpc;intros SEM' SEM  MAKE EV1 FP1 EV2 FP2;  monadInv MAKE. solv_sem.
Qed.
Lemma make_binarith_int_correct:
  binary_constructor_correct
    (make_binarith_int iop iopu lop lopu)
    (sem_binarith sem_int sem_long (fun x y => None) (fun x y => None)).
Proof.
  red; unfold make_binarith_int, sem_binarith; intros until m; intros SEM MAKE EV1 EV2;  monadInv MAKE. solv_sem.
Qed.
Lemma make_binarith_int_fp_correct:
  binary_fp_constructor_correct
    (make_binarith_int iop iopu lop lopu)
    (sem_binarith sem_int sem_long (fun x y => None)(fun x y => None))
    (Cop_fp_local.sem_binarith_fp sem_int sem_long (fun x y => None) (fun x y => None)).
Proof.
  red; unfold make_binarith_int, Cop_fp_local.sem_binarith_fp;intros until fpc;intros SEM' SEM MAKE EV1 FP1 EV2 FP2 EV3;  monadInv MAKE. solv_sem.
Qed.  
End MAKE_BIN.
Hint Extern 2 (@eq (option val) _ _) => (simpl; reflexivity) : cshm.
Lemma make_add_correct: binary_constructor_correct (make_add cunit.(cu_comp_env)) (sem_add cunit.(cu_comp_env)).
Proof.
  assert (A: forall ty si a b c e le m va vb v,
             make_add_ptr_int cunit.(cu_comp_env) ty si a b = OK c ->
             eval_expr ge e le m a va -> eval_expr ge e le m b vb ->
             sem_add_ptr_int (cu_comp_env cunit) ty si va vb = Some v ->
             eval_expr ge e le m c v).
  { unfold make_add_ptr_int, sem_add_ptr_int; intros until v; intros MAKE EV1 EV2 SEM; monadInv MAKE.
    destruct Archi.ptr64 eqn:SF; inv EQ0; rewrite (transl_sizeof _ _ _  EQ).
  - destruct va; InvEval; destruct vb; inv SEM.
  + eauto with cshm.
  + econstructor; eauto with cshm.
    simpl. rewrite SF. f_equal. f_equal. f_equal.
    assert (Ptrofs.agree64 (ptrofs_of_int si i0) (cast_int_long si i0)).
    { destruct si; simpl; apply Ptrofs.agree64_repr; auto. }
    auto with ptrofs.
  - destruct va; InvEval; destruct vb; inv SEM.
  + eauto with cshm.
  + econstructor; eauto with cshm.
    simpl. rewrite SF. f_equal. f_equal. f_equal.
    assert (Ptrofs.agree32 (ptrofs_of_int si i0) i0) by (destruct si; simpl; auto with ptrofs).
    auto with ptrofs.
  }
  assert (B: forall ty a b c e le m va vb v,
             make_add_ptr_long cunit.(cu_comp_env) ty a b = OK c ->
             eval_expr ge e le m a va -> eval_expr ge e le m b vb ->
             sem_add_ptr_long (cu_comp_env cunit) ty va vb = Some v ->
             eval_expr ge e le m c v).
  { unfold make_add_ptr_long, sem_add_ptr_long; intros until v; intros MAKE EV1 EV2 SEM; monadInv MAKE.
    destruct Archi.ptr64 eqn:SF; inv EQ0; rewrite (transl_sizeof _ _ _ EQ).
  - destruct va; InvEval; destruct vb; inv SEM.
  + eauto with cshm.
  + econstructor; eauto with cshm.
    simpl. rewrite SF. f_equal. f_equal. f_equal. auto with ptrofs.
  - destruct va; InvEval; destruct vb; inv SEM.
  + eauto with cshm.
  + econstructor; eauto with cshm.
    simpl. rewrite SF. f_equal. f_equal. f_equal.
    assert (Ptrofs.agree32 (Ptrofs.of_int64 i0) (Int64.loword i0)) by (apply Ptrofs.agree32_repr; auto).
    auto with ptrofs.
  }
  red; unfold make_add, sem_add;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_add tya tyb); eauto.
- eapply make_binarith_correct; eauto; intros; auto.
Qed.

Lemma make_add_fp_correct:
  binary_fp_constructor_correct (make_add cunit.(cu_comp_env))(sem_add cunit.(cu_comp_env))(Cop_fp_local.sem_add_fp cunit.(cu_comp_env)).
Proof.
  red; unfold make_add, Cop_fp_local.sem_add_fp.
  intros until fpc;intros SEM' SEM MAKE EV1 FP1 EV2 FP2 EV3.
  destruct (classify_add tya tyb) eqn:?;eauto.
  1,3: destruct sem_add_ptr_int eqn:?;inv SEM;
    unfold make_add_ptr_int,sem_add_ptr_int in *;monadInv MAKE;
      destruct Archi.ptr64 eqn:?;try discriminate;inv EQ0; repeat bexpr;empfp;rewrite FP.union_comm_eq;auto.
  1,2: destruct sem_add_ptr_long eqn:?;inv SEM;
    unfold make_add_ptr_long,sem_add_ptr_long in *;monadInv MAKE;
      destruct Archi.ptr64 eqn:?;try discriminate;inv EQ0;repeat bexpr;empfp;rewrite FP.union_comm_eq;auto.
  eapply make_binarith_fp_correct;eauto;intros;auto.
  unfold sem_add in SEM'. rewrite Heqc0 in SEM'; auto.
Qed.    

Lemma make_sub_correct: binary_constructor_correct (make_sub cunit.(cu_comp_env)) (sem_sub cunit.(cu_comp_env)).
Proof.
  red; unfold make_sub, sem_sub;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_sub tya tyb); try (monadInv MAKE).
- destruct Archi.ptr64 eqn:SF; inv EQ0; rewrite (transl_sizeof _ _ _  EQ).
+ destruct va; InvEval; destruct vb; inv SEM; eauto with cshm.
  econstructor; eauto with cshm.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal.
  assert (Ptrofs.agree64 (ptrofs_of_int si i0) (cast_int_long si i0)).
  { destruct si; simpl; apply Ptrofs.agree64_repr; auto. }
  auto with ptrofs.
+ destruct va; InvEval; destruct vb; inv SEM; eauto with cshm.
  econstructor; eauto with cshm. simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal.
  assert (Ptrofs.agree32 (ptrofs_of_int si i0) i0) by (destruct si; simpl; auto with ptrofs).
  auto with ptrofs.
- rewrite (transl_sizeof _ _ _  EQ) in EQ0. clear EQ.
  set (sz := Ctypes.sizeof (cu_comp_env cunit) ty) in *.
  destruct va; InvEval; destruct vb; InvEval.
  destruct (eq_block b0 b1); try discriminate.
  destruct (zlt 0 sz); try discriminate.
  destruct (zle sz Ptrofs.max_signed); simpl in SEM; inv SEM.
  assert (E1: Ptrofs.signed (Ptrofs.repr sz) = sz).
  { apply Ptrofs.signed_repr. generalize Ptrofs.min_signed_neg; Lia.lia. }
  destruct Archi.ptr64 eqn:SF; inversion EQ0; clear EQ0; subst c.
+ assert (E: Int64.signed (Int64.repr sz) = sz).
  { apply Int64.signed_repr.
    replace Int64.max_signed with Ptrofs.max_signed.
    generalize Int64.min_signed_neg; Lia.lia.
    unfold Ptrofs.max_signed, Ptrofs.half_modulus; rewrite Ptrofs.modulus_eq64 by auto. reflexivity. }
  econstructor; eauto with cshm.
  rewrite SF, dec_eq_true. simpl.
  predSpec Int64.eq Int64.eq_spec (Int64.repr sz) Int64.zero.
  rewrite H in E; rewrite Int64.signed_zero in E; lia.
  predSpec Int64.eq Int64.eq_spec (Int64.repr sz) Int64.mone.
  rewrite H0 in E; rewrite Int64.signed_mone in E; lia.
  rewrite andb_false_r; simpl. unfold Vptrofs; rewrite SF. apply f_equal.
  apply f_equal. symmetry. auto with ptrofs.
+ assert (E: Int.signed (Int.repr sz) = sz).
  { apply Int.signed_repr.
    replace Int.max_signed with Ptrofs.max_signed.
    generalize Int.min_signed_neg; Lia.lia.
    unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize. rewrite SF. reflexivity.
  }
  econstructor; eauto with cshm. rewrite SF, dec_eq_true. simpl.
  predSpec Int.eq Int.eq_spec (Int.repr sz) Int.zero.
  rewrite H in E; rewrite Int.signed_zero in E; lia.
  predSpec Int.eq Int.eq_spec (Int.repr sz) Int.mone.
  rewrite H0 in E; rewrite Int.signed_mone in E; lia.
  rewrite andb_false_r; simpl. unfold Vptrofs; rewrite SF. apply f_equal. apply f_equal.
  symmetry. auto with ptrofs.
- destruct Archi.ptr64 eqn:SF; inv EQ0; rewrite (transl_sizeof _ _ _  EQ).
+ destruct va; InvEval; destruct vb; inv SEM; eauto with cshm.
  econstructor; eauto with cshm.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal.
  auto with ptrofs.
+ destruct va; InvEval; destruct vb; inv SEM; eauto with cshm.
  econstructor; eauto with cshm. simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal.
  assert (Ptrofs.agree32 (Ptrofs.of_int64 i0) (Int64.loword i0)) by (apply Ptrofs.agree32_repr; auto).
  auto with ptrofs.
- eapply make_binarith_correct; eauto; intros; auto.
Qed.


Lemma make_sub_fp_correct: binary_fp_constructor_correct (make_sub cunit.(cu_comp_env))(sem_sub cunit.(cu_comp_env)) (Cop_fp_local.sem_sub_fp cunit.(cu_comp_env)).
Proof.
  red; unfold make_sub,sem_sub,Cop_fp_local.sem_sub_fp.
  intros until fpc;intros SEM' SEM MAKE EV1 FP1 EV2 FP2 EV3.
  destruct Archi.ptr64 eqn:?;try discriminate.
  destruct (classify_sub tya tyb) eqn:?;eauto;  try monadInv MAKE.
  destruct va;inversion SEM;destruct vb;inversion SEM;subst  ;repeat bexpr;empfp.
  destruct va;inv SEM. destruct vb;inv H0.
  destruct (eq_block) eqn:?;inv H1. destruct (zlt 0 (Ctypes.sizeof (cu_comp_env cunit) ty) && zle (Ctypes.sizeof (cu_comp_env cunit) ty) Ptrofs.max_signed) ;inv H0.
  rewrite<- FP.fp_union_emp with(fp:=(FP.union fpa fpb)).
  inv EV3.
  econstructor;eauto. econstructor;eauto;simpl;eauto;  empfp.
  econstructor;eauto;simpl;eauto.
  unfold eval_binop,Cminor.eval_binop in H5. simpl. rewrite H5. auto.
  destruct va;inv SEM; destruct vb;inv H0; repeat bexpr;empfp.
  eapply make_binarith_fp_correct;eauto;intros;auto.
Qed.
Lemma make_mul_correct: binary_constructor_correct make_mul sem_mul.
Proof. apply make_binarith_correct; intros; auto. Qed.
Lemma make_mul_fp_correct: binary_fp_constructor_correct make_mul sem_mul Cop_fp_local.sem_mul_fp.
Proof. apply make_binarith_fp_correct; intros; auto. Qed.
Lemma make_div_correct: binary_constructor_correct make_div sem_div.
Proof. apply make_binarith_correct; intros; auto. Qed.
Lemma make_div_fp_correct: binary_fp_constructor_correct make_div sem_div Cop_fp_local.sem_div_fp.
Proof. apply make_binarith_fp_correct; intros; auto;simpl in *;inv_eq;auto. Qed.
Lemma make_mod_correct: binary_constructor_correct make_mod sem_mod.
Proof.  apply make_binarith_int_correct; intros; auto. Qed.
Lemma make_mod_fp_correct: binary_fp_constructor_correct make_mod sem_mod sem_mod_fp.
Proof. apply make_binarith_int_fp_correct; intros; auto;simpl in *;inv_eq;auto. Qed.
Lemma make_and_correct: binary_constructor_correct make_and sem_and.
Proof. apply make_binarith_int_correct; intros; auto. Qed.
Lemma make_and_fp_correct: binary_fp_constructor_correct make_and sem_and sem_and_fp.
Proof. apply make_binarith_int_fp_correct; intros; auto. Qed.
Lemma make_or_correct: binary_constructor_correct make_or sem_or.
Proof. apply make_binarith_int_correct; intros; auto. Qed.
Lemma make_or_fp_correct: binary_fp_constructor_correct make_or sem_or sem_or_fp.
Proof. apply make_binarith_int_fp_correct; intros; auto. Qed.
Lemma make_xor_correct: binary_constructor_correct make_xor sem_xor.
Proof. apply make_binarith_int_correct; intros; auto. Qed.
Lemma make_xor_fp_correct: binary_fp_constructor_correct make_xor sem_xor sem_xor_fp.
Proof. apply make_binarith_int_fp_correct; intros; auto. Qed.
Ltac comput val :=
  let x := fresh in set val as x in *; vm_compute in x; subst x.
Remark small_shift_amount_1:
  forall i,
  Int64.ltu i Int64.iwordsize = true ->
  Int.ltu (Int64.loword i) Int64.iwordsize' = true
  /\ Int64.unsigned i = Int.unsigned (Int64.loword i).
Proof.
  intros. apply Int64.ltu_inv in H. comput (Int64.unsigned Int64.iwordsize).
  assert (Int64.unsigned i = Int.unsigned (Int64.loword i)).
  { unfold Int64.loword. rewrite Int.unsigned_repr; auto.
    comput Int.max_unsigned; Lia.lia. }
  split; auto. unfold Int.ltu. apply zlt_true. rewrite <- H0. tauto.
Qed.

Remark small_shift_amount_2:
  forall i,
  Int64.ltu i (Int64.repr 32) = true ->
  Int.ltu (Int64.loword i) Int.iwordsize = true.
Proof.
  intros. apply Int64.ltu_inv in H. comput (Int64.unsigned (Int64.repr 32)).
  assert (Int64.unsigned i = Int.unsigned (Int64.loword i)).
  { unfold Int64.loword. rewrite Int.unsigned_repr; auto.
    comput Int.max_unsigned; Lia.lia. }
  unfold Int.ltu. apply zlt_true. rewrite <- H0. tauto.
Qed.

Lemma small_shift_amount_3:
  forall i,
  Int.ltu i Int64.iwordsize' = true ->
  Int64.unsigned (Int64.repr (Int.unsigned i)) = Int.unsigned i.
Proof.
  intros. apply Int.ltu_inv in H. comput (Int.unsigned Int64.iwordsize').
  apply Int64.unsigned_repr. comput Int64.max_unsigned; Lia.lia.
Qed.

Lemma make_shl_correct: shift_constructor_correct make_shl sem_shl.
Proof.
  red; unfold make_shl, sem_shl, sem_shift;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_shift tya tyb); inv MAKE;
  destruct va; try discriminate; destruct vb; try discriminate.
- destruct (Int.ltu i0 Int.iwordsize) eqn:E; inv SEM.
  econstructor; eauto. simpl; rewrite E; auto.
- destruct (Int64.ltu i0 Int64.iwordsize) eqn:E; inv SEM.
  exploit small_shift_amount_1; eauto. intros [A B].
  econstructor; eauto with cshm. simpl. rewrite A.
  f_equal; f_equal. unfold Int64.shl', Int64.shl. rewrite B; auto.
- destruct (Int64.ltu i0 (Int64.repr 32)) eqn:E; inv SEM.
  econstructor; eauto with cshm. simpl. rewrite small_shift_amount_2; auto.
- destruct (Int.ltu i0 Int64.iwordsize') eqn:E; inv SEM.
  econstructor; eauto with cshm. simpl. rewrite E.
  unfold Int64.shl', Int64.shl. rewrite small_shift_amount_3; auto.
Qed.

Lemma make_shr_correct: shift_constructor_correct make_shr sem_shr.
Proof.
  red; unfold make_shr, sem_shr, sem_shift;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_shift tya tyb); inv MAKE;
  destruct va; try discriminate; destruct vb; try discriminate.
- destruct (Int.ltu i0 Int.iwordsize) eqn:E; inv SEM.
  destruct s; inv H0; econstructor; eauto; simpl; rewrite E; auto.
- destruct (Int64.ltu i0 Int64.iwordsize) eqn:E; inv SEM.
  exploit small_shift_amount_1; eauto. intros [A B].
  destruct s; inv H0; econstructor; eauto with cshm; simpl; rewrite A;
  f_equal; f_equal.
  unfold Int64.shr', Int64.shr; rewrite B; auto.
  unfold Int64.shru', Int64.shru; rewrite B; auto.
- destruct (Int64.ltu i0 (Int64.repr 32)) eqn:E; inv SEM.
  destruct s; inv H0; econstructor; eauto with cshm; simpl; rewrite small_shift_amount_2; auto.
- destruct (Int.ltu i0 Int64.iwordsize') eqn:E; inv SEM.
  destruct s; inv H0; econstructor; eauto with cshm; simpl; rewrite E.
  unfold Int64.shr', Int64.shr; rewrite small_shift_amount_3; auto.
  unfold Int64.shru', Int64.shru; rewrite small_shift_amount_3; auto.
Qed.

Lemma make_cmp_ptr_correct:
  forall cmp e le m a va b vb v,
  cmp_ptr m cmp va vb = Some v ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m (make_cmp_ptr cmp a b) v.
Proof. unfold cmp_ptr, make_cmp_ptr; intros; destruct Archi.ptr64 eqn:?;try discriminate;econstructor; eauto. Qed.


Lemma cmpu_bool_cmp_ptr_fp_correct:
  forall cmp e le m a va b vb v fp fpa fpb,
    option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) cmp va vb) = Some v ->
    ValFP.cmpu_bool_fp m cmp va vb = Some fp->
    eval_expr ge e le m a va ->
    eval_expr_fp ge e le m a fpa->
    eval_expr ge e le m b vb ->
    eval_expr_fp ge e le m b fpb->
    eval_expr_fp ge e le m (make_cmp_ptr cmp a b)(FP.union(FP.union fpa fpb) fp).
Proof.
  unfold cmp_ptr, make_cmp_ptr,cmp_ptr_fp;intros.
  destruct Archi.ptr64 eqn:?;try discriminate.
  econstructor;eauto. simpl. f_equal.
  unfold cmpu_fp,ValFP.cmpu_bool_fp_total,Val.cmpu_bool,ValFP.cmpu_bool_fp in *; inv_eq;auto.
Qed.
Lemma make_cmp_ptr_fp_correct:
  forall cmp e le m a va b vb v fp fpa fpb,
    cmp_ptr m cmp va vb = Some v ->
    cmp_ptr_fp m cmp va vb = Some fp->
    eval_expr ge e le m a va ->
    eval_expr_fp ge e le m a fpa->
    eval_expr ge e le m b vb ->
    eval_expr_fp ge e le m b fpb->
    eval_expr_fp ge e le m (make_cmp_ptr cmp a b)(FP.union(FP.union fpa fpb) fp).
Proof.
  unfold cmp_ptr, make_cmp_ptr,cmp_ptr_fp;intros.  destruct Archi.ptr64 eqn:?;try discriminate.  eapply cmpu_bool_cmp_ptr_fp_correct;eauto.
Qed.
Remark make_ptrofs_of_int_correct:
  forall e le m a i si,
  eval_expr ge e le m a (Vint i) ->
  eval_expr ge e le m (if Archi.ptr64 then make_longofint a si else a) (Vptrofs (ptrofs_of_int si i)).
Proof.
  intros. unfold Vptrofs, ptrofs_of_int. destruct Archi.ptr64 eqn:SF.
- unfold make_longofint. destruct si.
+ replace (Ptrofs.to_int64 (Ptrofs.of_ints i)) with (Int64.repr (Int.signed i)).
  eauto with cshm.
  apply Int64.eqm_samerepr. rewrite Ptrofs.eqm64 by auto. apply Ptrofs.eqm_unsigned_repr.
+ replace (Ptrofs.to_int64 (Ptrofs.of_intu i)) with (Int64.repr (Int.unsigned i)).
  eauto with cshm.
  apply Int64.eqm_samerepr. rewrite Ptrofs.eqm64 by auto. apply Ptrofs.eqm_unsigned_repr.
- destruct si.
+ replace (Ptrofs.to_int (Ptrofs.of_ints i)) with i. auto.
  symmetry. auto with ptrofs.
+ replace (Ptrofs.to_int (Ptrofs.of_intu i)) with i. auto.
  symmetry. auto with ptrofs.
Qed.

Remark make_ptrofs_of_int64_correct:
  forall e le m a i,
  eval_expr ge e le m a (Vlong i) ->
  eval_expr ge e le m (if Archi.ptr64 then a else Eunop Ointoflong a) (Vptrofs (Ptrofs.of_int64 i)).
Proof.
  intros. unfold Vptrofs. destruct Archi.ptr64 eqn:SF.
- replace (Ptrofs.to_int64 (Ptrofs.of_int64 i)) with i. auto.
  symmetry. auto with ptrofs.
- econstructor; eauto. simpl. apply f_equal. apply f_equal.
  apply Int.eqm_samerepr. rewrite Ptrofs.eqm32 by auto. apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma make_cmp_correct: forall cmp, binary_constructor_correct (make_cmp cmp) (sem_cmp cmp).
Proof.
  red; unfold sem_cmp, make_cmp; intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_cmp tya tyb).
- inv MAKE. eapply make_cmp_ptr_correct; eauto.
- inv MAKE. destruct vb; InvEval; eauto using make_cmp_ptr_correct, make_ptrofs_of_int_correct.
- inv MAKE. destruct va; InvEval; eauto using make_cmp_ptr_correct, make_ptrofs_of_int_correct.
- inv MAKE. destruct vb; InvEval; eauto using make_cmp_ptr_correct, make_ptrofs_of_int64_correct.
- inv MAKE. destruct va; InvEval; eauto using make_cmp_ptr_correct, make_ptrofs_of_int64_correct.
- eapply make_binarith_correct; eauto; intros; auto.
Qed.
Lemma make_cmp_fp_correct: forall cmp, binary_fp_constructor_correct (make_cmp cmp) (sem_cmp cmp)(sem_cmp_fp cmp).
Proof.
  red. unfold sem_cmp, sem_cmp_fp, make_cmp;intros until fpc;intros SEM SEMFP MAKE EV1 FP1 EV2 FP2 EV3.
  destruct (classify_cmp tya tyb) eqn:?;inv MAKE.
  * eapply make_cmp_ptr_fp_correct;eauto.
  * unfold cmp_ptr,cmp_ptr_fp,Vptrofs in *;
      destruct vb;try discriminate;
        destruct Archi.ptr64 eqn:?;try discriminate;
        eapply cmpu_bool_cmp_ptr_fp_correct;eauto.
    eapply make_ptrofs_of_int_correct with(si:=si) in EV2 as ?;eauto.
  * unfold cmp_ptr, cmp_ptr_fp, Vptrofs in *;
      destruct va;try discriminate;
        destruct Archi.ptr64 eqn:?;try discriminate;
        eapply cmpu_bool_cmp_ptr_fp_correct;eauto.
    eapply make_ptrofs_of_int_correct with(si:=si) in EV1 as ?;eauto.
  * destruct vb ;inv SEM.
    destruct Archi.ptr64 eqn:?;try discriminate.
    eapply make_ptrofs_of_int64_correct in EV2 as ?;eauto.
    rewrite Heqb0 in H.
    repeat bexpr. rewrite Heqb0. simpl. f_equal.
    apply ValFP.cmpu_bool_fp_cmpu_bool_fp_total;auto.
  * destruct va;inv SEM.
    destruct Archi.ptr64 eqn:?;try discriminate.
    eapply make_ptrofs_of_int64_correct in EV1 as ?;eauto.
    rewrite Heqb0 in H.
    repeat bexpr. rewrite Heqb0. simpl. f_equal.
    apply ValFP.cmpu_bool_fp_cmpu_bool_fp_total;auto.
  * eapply make_binarith_fp_correct;eauto;intros;auto.
Qed.
Lemma transl_unop_correct:
  forall op a tya c va v e le m,
  transl_unop op a tya = OK c ->
  sem_unary_operation op va tya m = Some v ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_notbool_correct; eauto.
  eapply make_notint_correct; eauto.
  eapply make_neg_correct; eauto.
  eapply make_absfloat_correct; eauto.
Qed.
Lemma transl_unop_fp_correct:
  forall op a tya c va e le v m fp fp',
    transl_unop op a tya = OK c ->
    sem_unary_operation op va tya m = Some v->
    sem_unary_operation_fp op va tya m = Some fp'->
    eval_expr ge e le m a va ->
    eval_expr_fp ge e le m a fp->
    eval_expr_fp ge e le m c (FP.union fp fp').
Proof.
  intros. destruct op; simpl in *; [eapply make_notbool_fp_correct|eapply make_notint_fp_correct|eapply make_neg_fp_correct|eapply make_absfloat_fp_correct]; eauto;inv_eq;empfp.
Qed.
Lemma transl_binop_correct:
  forall op a tya b tyb c va vb v e le m,
  transl_binop cunit.(cu_comp_env) op a tya b tyb = OK c ->
  sem_binary_operation cunit.(cu_comp_env) op va tya vb tyb m = Some v ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_add_correct; eauto.
  eapply make_sub_correct; eauto.
  eapply make_mul_correct; eauto.
  eapply make_div_correct; eauto.
  eapply make_mod_correct; eauto.
  eapply make_and_correct; eauto.
  eapply make_or_correct; eauto.
  eapply make_xor_correct; eauto.
  eapply make_shl_correct; eauto.
  eapply make_shr_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
Qed.

Lemma transl_binop_fp_correct:
  forall op a tya b tyb c va vb v e le m fpa fpb fpc,
  transl_binop cunit.(cu_comp_env) op a tya b tyb = OK c ->
  sem_binary_operation cunit.(cu_comp_env) op va tya vb tyb m = Some v ->
  sem_binary_operation_fp cunit.(cu_comp_env) op va tya vb tyb m = Some fpc->
  eval_expr ge e le m a va ->
  eval_expr_fp ge e le m a fpa->
  eval_expr ge e le m b vb ->
  eval_expr_fp ge e le m b fpb->
  eval_expr ge e le m c v->
  eval_expr_fp ge e le m c (FP.union (FP.union fpa fpb) fpc).
Proof.
  intros.
  destruct op; simpl in *;[eapply make_add_fp_correct|eapply make_sub_fp_correct|eapply make_mul_fp_correct|eapply make_div_fp_correct|eapply make_mod_fp_correct|eapply make_and_fp_correct|eapply make_or_fp_correct|eapply make_xor_fp_correct| | | | | | | |];eauto.
  1,2:unfold make_shl,make_shr in H;inv_eq;repeat bexpr;empfp.
  all: eapply make_cmp_fp_correct;eauto.
Qed.
Lemma make_load_correct:
  forall addr ty code b ofs v e le m,
  make_load addr ty = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  deref_loc ty m b ofs v ->
  eval_expr ge e le m code v.
Proof.
  unfold make_load; intros until m; intros MKLOAD EVEXP DEREF.
  inv DEREF.
  (* scalar *)
  rewrite H in MKLOAD. inv MKLOAD.  apply Csharpminor.eval_Eload with (Vptr b ofs); auto.
  (* by reference *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
  (* by copy *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
Qed.

Lemma make_load_fp_correct:
  forall addr ty code b ofs v e le m fpa fpb,
  make_load addr ty = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  eval_expr_fp ge e le m addr fpa ->
  deref_loc ty m b ofs v ->
  deref_loc_fp ty  b ofs fpb ->
  eval_expr_fp ge e le m code (FP.union fpa fpb).
Proof.
  unfold make_load;intros until fpb;intros MKLOAD EV EVFP DEREF DEREFFP.
  inv DEREF;inv DEREFFP.
  all: try rewrite H in H1;try inv H1;try rewrite H in H0;try inv H0;rewrite H in MKLOAD;inv MKLOAD;empfp;econstructor;eauto.
Qed.

Lemma make_store_correct:
  forall addr ty rhs code e le m b ofs v m' f k fp1 fp2 fp3,
  make_store cunit.(cu_comp_env) addr ty rhs = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  eval_expr ge e le m rhs v ->
  eval_expr_fp ge e le m addr fp1 ->
  eval_expr_fp ge e le m rhs fp2 ->
  assign_loc cunit.(cu_comp_env) ty m b ofs v m' ->
  assign_loc_fp cunit.(cu_comp_env) ty b ofs v fp3->
  step ge (Core_State f code k e le) m (FP.union (FP.union fp1 fp2) fp3) (Core_State f Sskip k e le ) m'.
Proof.
  unfold make_store. intros until fp3; intros MKSTORE EV1 EV2 FP1 FP2 ASSIGN FP3.
  inversion ASSIGN; subst.
  inv FP3.
  rewrite H1 in H;inv H.
  (* nonvolatile scalar *)
  rewrite H1 in MKSTORE; inv MKSTORE.
  econstructor; eauto.
Qed.
End CONSTRUCTORS.

(** * Basic preservation invariants *)

Section CORRECTNESS.

Variable prog: clight_comp_unit.
Variable tprog: Csharpminor_local.comp_unit.
Variable ge : Clight.genv.
Variable tge : Csharpminor.genv.
Variable pge: Genv.t Clight.fundef type.
Hypothesis SGEINIT: Clight_local.init_genv prog pge ge.
Hypothesis TGEINIT: globalenv_generic tprog tge.
Hypothesis TRANSL:  match_cu  prog tprog.
Hypothesis S_EQ: ge.(Genv.genv_next) = tge.(Genv.genv_next).
Lemma ge_match: ge_match_strict ge tge.
Proof. eapply match_cu_ge_match_strict; eauto. inv SGEINIT;auto. Qed.
Lemma genv_match: Genv.match_genvs (match_globdef (fun f tf => match_fundef prog f tf) (fun _ _ => True)) ge tge.
Proof. eapply match_cu_match_genv; eauto. inv SGEINIT;auto. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. destruct genv_match. auto. Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. eapply match_cu_senv_preserved; eauto. inv SGEINIT;auto. Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Clight.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ match_fundef prog f tf.
Proof.
  destruct genv_match.
  unfold Clight.fundef, fundef in *. simpl in *.
  unfold Genv.find_funct_ptr, Genv.find_def; intros.
  specialize (mge_defs b). inv mge_defs.
  rewrite <- H1 in H. discriminate.
  rewrite <- H0 in H. destruct x; inv H.
  inv H2. eauto.
Qed.

Lemma functions_translated:
  forall v v' f,
    Genv.find_funct ge v = Some f ->
    Val.lessdef v v' ->
    exists tf, Genv.find_funct tge v' = Some tf /\ match_fundef prog f tf.
Proof.
  destruct v; simpl; intros; try discriminate. inv H0. simpl.
  destruct Ptrofs.eq_dec; [|discriminate]. 
  apply function_ptr_translated; auto.
Qed.

(** * Matching between environments *)

(** In this section, we define a matching relation between
  a Clight local environment and a Csharpminor local environment. *)

Record match_env (e: Clight.env) (te: Csharpminor.env) : Prop :=
  mk_match_env {
    me_local:
      forall id b ty,
      e!id = Some (b, ty) -> te!id = Some(b, Ctypes.sizeof ge ty);
    me_local_inv:
      forall id b sz,
      te!id = Some (b, sz) -> exists ty, e!id = Some(b, ty)
  }.

Lemma match_env_globals:
  forall e te id,
  match_env e te ->
  e!id = None ->
  te!id = None.
Proof.
  intros. destruct (te!id) as [[b sz] | ] eqn:?; auto.
  exploit me_local_inv; eauto. intros [ty EQ]. congruence.
Qed.

Lemma match_env_same_blocks:
  forall e te,
  match_env e te ->
  blocks_of_env te = Clight.blocks_of_env ge e.
Proof.
  intros.
  set (R := fun (x: (block * type)) (y: (block * Z)) =>
         match x, y with
         | (b1, ty), (b2, sz) => b2 = b1 /\ sz = Ctypes.sizeof ge ty
         end).
  assert (list_forall2
            (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
            (PTree.elements e) (PTree.elements te)).
  apply PTree.elements_canonical_order.
  intros id [b ty] GET. exists (b, Ctypes.sizeof ge ty); split. eapply me_local; eauto. red; auto.
  intros id [b sz] GET. exploit me_local_inv; eauto. intros [ty EQ].
  exploit me_local; eauto. intros EQ1.
  exists (b, ty); split. auto. red; split; congruence.

  unfold blocks_of_env, Clight.blocks_of_env.
  generalize H0. induction 1. auto.
  simpl. f_equal; auto.
  unfold block_of_binding, Clight.block_of_binding.
  destruct a1 as [id1 [blk1 ty1]]. destruct b1 as [id2 [blk2 sz2]].
  simpl in *. destruct H1 as [A [B C]]. congruence.
Qed.

Lemma match_env_free_blocks:
  forall e te m m',
  match_env e te ->
  Mem.free_list m (Clight.blocks_of_env ge e) = Some m' ->
  Mem.free_list m (blocks_of_env te) = Some m'.
Proof.
  intros. rewrite (match_env_same_blocks _ _ H). auto.
Qed.

Lemma match_env_empty:
  match_env Clight.empty_env Csharpminor.empty_env.
Proof.
  unfold Clight.empty_env, Csharpminor.empty_env.
  constructor.
  intros until ty. repeat rewrite PTree.gempty. congruence.
  intros until sz. rewrite PTree.gempty. congruence.
Qed.

(** The following lemmas establish the [match_env] invariant at
  the beginning of a function invocation, after allocation of
  local variables and initialization of the parameters. *)
Lemma transl_sizeof':
  forall (prog:clight_comp_unit) pge (ge:Clight.genv) ty,
    Clight_local.init_genv prog pge ge->
    Ctypes.sizeof ge ty = Ctypes.sizeof (cu_comp_env prog) ty.
Proof. clear;inversion 1;subst;simpl;auto. Qed.
Lemma match_env_alloc_variables:
  forall e1 m1 vars e2 m2, Clight.alloc_variables ge e1 m1 vars e2 m2 ->
  forall tvars te1,
  mmap (transl_var prog.(cu_comp_env)) vars = OK tvars ->
  match_env e1 te1 ->
  exists te2,
  Csharpminor.alloc_variables te1 m1 tvars te2 m2
  /\ match_env e2 te2.
Proof.
  induction 1; simpl; intros.
- inv H. exists te1; split. constructor. auto.
- monadInv H1. monadInv EQ. simpl in *.
  exploit transl_sizeof. eexact EQ0. eauto. intros SZ; rewrite SZ.
  exploit (IHalloc_variables x0 (PTree.set id (b1, Ctypes.sizeof ge ty) te1)).
  auto.
  constructor.
    (* me_local *)
    intros until ty0. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros. congruence. eapply me_local; eauto.
    (* me_local_inv *)
    intros until sz. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros. exists ty; congruence. eapply me_local_inv; eauto.
  intros [te2 [ALLOC MENV]].
  exists te2; split;auto.
  erewrite transl_sizeof' in *;eauto.
  econstructor;eauto.
Qed.
Lemma match_env_alloc_variables_fp:
  forall vars e1 m1 e2 m2, Clight.alloc_variables ge e1 m1 vars e2 m2 ->
  forall fp,Clight_local.alloc_variables_fp ge m1 vars fp->
  forall tvars,
  mmap (transl_var prog.(cu_comp_env)) vars = OK tvars ->
  Csharpminor_local.alloc_variables_fp m1 tvars fp.
Proof.
  induction vars;simpl;intros.
  - inv H. inv H0. inv H1. constructor.
  - inv H.
    monadInv H1.
    monadInv EQ. 
    inv H0. rewrite H6 in H4;inv H4.
    eapply IHvars in H8;eauto. 
    inv EQ1. inv H0. inv SGEINIT. simpl in *.
    unfold sizeof in EQ0. destruct complete_type;try discriminate.
    inversion EQ0;clear EQ0.
    econstructor 2;eauto.
Qed.
Lemma create_undef_temps_match:
  forall temps,
  create_undef_temps (map fst temps) = Clight.create_undef_temps temps.
Proof.
  induction temps; simpl. auto.
  destruct a as [id ty]. simpl. decEq. auto.
Qed.

Lemma bind_parameter_temps_match:
  forall vars vals le1 le2,
  Clight.bind_parameter_temps vars vals le1 = Some le2 ->
  bind_parameters (map fst vars) vals le1 = Some le2.
Proof.
  induction vars; simpl; intros.
  destruct vals; inv H. auto.
  destruct a as [id ty]. destruct vals; try discriminate. auto.
Qed.

Lemma transl_vars_names:
  forall ce vars tvars,
  mmap (transl_var ce) vars = OK tvars ->
  map fst tvars = var_names vars.
Proof.
  intros. exploit mmap_inversion; eauto. generalize vars tvars. induction 1; simpl.
- auto.
- monadInv H0. simpl; congruence.
Qed.

(** * Proof of semantic preservation *)

(** ** Semantic preservation for expressions *)

(** The proof of semantic preservation for the translation of expressions
  relies on simulation diagrams of the following form:
<<
         e, le, m, a ------------------- te, le, m, ta
            |                                |
            |                                |
            |                                |
            v                                v
         e, le, m, v ------------------- te, le, m, v
>>
  Left: evaluation of r-value expression [a] in Clight.
  Right: evaluation of its translation [ta] in Csharpminor.
  Top (precondition): matching between environments [e], [te],
    plus well-typedness of expression [a].
  Bottom (postcondition): the result values [v]
    are identical in both evaluations.

  We state these diagrams as the following properties, parameterized
  by the Clight evaluation. *)

Section EXPR.
Variable e: Clight.env.
Variable le: temp_env.
Variable m: mem.
Variable te: Csharpminor.env.
Hypothesis MENV: match_env e te.
Lemma transl_expr_lvalue_correct:
  (forall a v,
   Clight.eval_expr ge e le m a v ->
   forall ta (TR: transl_expr prog.(cu_comp_env) a = OK ta) ,
   Csharpminor.eval_expr tge te le m ta v)
/\(forall a b ofs,
   Clight.eval_lvalue ge e le m a b ofs ->
   forall ta (TR: transl_lvalue prog.(cu_comp_env) a = OK ta),
   Csharpminor.eval_expr tge te le m ta (Vptr b ofs)).
Proof.
  apply eval_expr_lvalue_ind; intros; try (monadInv TR).
- (* const int *)
  apply make_intconst_correct.
- (* const float *)
  apply make_floatconst_correct.
- (* const single *)
  apply make_singleconst_correct.
- (* const long *)
  apply make_longconst_correct.
- (* temp var *)
  constructor; auto.
- (* addrof *)
  simpl in TR. auto.
- (* unop *)
  eapply transl_unop_correct; eauto.
- (* binop *)
  eapply transl_binop_correct; eauto.
  inv SGEINIT;auto.
- (* cast *)
  eapply make_cast_correct; eauto.
- (* sizeof *)
  rewrite (transl_sizeof _ _ _  EQ).
  inv SGEINIT;auto.
  apply make_ptrofsconst_correct.
- (* alignof *)
  rewrite (transl_alignof _ _ _  EQ).
  inv SGEINIT;auto.
  apply make_ptrofsconst_correct.
- (* rvalue out of lvalue *)
  exploit transl_expr_lvalue; eauto. intros [tb [TRLVAL MKLOAD]].
  eapply make_load_correct; eauto.
- (* var local *)
  exploit (me_local _ _ MENV); eauto. intros EQ.
  econstructor. eapply eval_var_addr_local. eauto.
- (* var global *)
  econstructor. eapply eval_var_addr_global.
  eapply match_env_globals; eauto.
  rewrite symbols_preserved. auto.
- (* deref *)
  simpl in TR. eauto.
- (* field struct *)
  unfold make_field_access in EQ0. rewrite H1 in EQ0.
  destruct (cu_comp_env prog)!id as [co'|] eqn:CO; monadInv EQ0.
  inv SGEINIT.
  simpl in *. rewrite CO in H2.
  inversion H2;clear H2;subst co'.
  rewrite EQ1 in H3. inversion H3;clear H3;subst x0.
  destruct Archi.ptr64 eqn:SF.
+ eapply Csharpminor.eval_Ebinop; eauto using make_longconst_correct.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal. auto with ptrofs.
+ eapply Csharpminor.eval_Ebinop; eauto using make_intconst_correct.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal. auto with ptrofs.
- (* field union *)
  unfold make_field_access in EQ0; rewrite H1 in EQ0; monadInv EQ0.
  auto.
Qed.

Lemma transl_expr_correct:
   forall a v,
   Clight.eval_expr ge e le m a v ->
   forall ta, transl_expr prog.(cu_comp_env) a = OK ta ->
   Csharpminor.eval_expr tge te le m ta v.
Proof (proj1 transl_expr_lvalue_correct).

Lemma transl_lvalue_correct:
   forall a b ofs,
   Clight.eval_lvalue ge e le m a b ofs ->
   forall ta, transl_lvalue prog.(cu_comp_env) a = OK ta ->
   Csharpminor.eval_expr tge te le m ta (Vptr b ofs).
Proof (proj2 transl_expr_lvalue_correct).


Lemma transl_expr_lvalue_fp_correct:
  (forall a fp,
      Clight_local.eval_expr_fp ge e le m a fp->
   forall v ta (TR: transl_expr prog.(cu_comp_env) a = OK ta)(EV:Clight.eval_expr ge e le m a v) , 
   Csharpminor_local.eval_expr_fp tge te le m ta fp)
  /\(forall a fp,
      Clight_local.eval_lvalue_fp ge e le m a fp ->
      forall b ofs ta (TR: transl_lvalue prog.(cu_comp_env) a = OK ta)(EV:Clight.eval_lvalue ge e le m a b ofs),
   
   Csharpminor_local.eval_expr_fp tge te le m ta fp).
Proof.
  apply eval_expr_lvalue_fp_ind; intros; try monadInv TR.
  all : try (econstructor;eauto;simpl;eauto;fail);try( simpl in *;eauto;fail).
  - (*addrof*)
    simpl in TR;inv EV;[eapply H0 in TR;eauto|inv H1].
  - (*uop*)
    eapply H1 in EQ as ?;eauto.
    eapply transl_expr_correct in H as ?;eauto.
    eapply transl_unop_correct in EQ0 as ?;eauto.
    eapply transl_unop_fp_correct in EQ0 as ?;eauto.
    congruence.
  - (*bop*)
    eapply H1 in EQ as ?;eauto.
    eapply transl_expr_correct in H as ?;eauto.
    eapply transl_expr_correct in H2 as ?;eauto.
    eapply H4 in EQ1 as ?;eauto.
    inv SGEINIT.
    eapply transl_binop_correct in EQ2 as ?;eauto.
    eapply transl_binop_fp_correct in EQ2 as ?;eauto.
  - (*cast*)
    rewrite <- H4. eapply make_cast_fp_correct;eauto;eapply transl_expr_correct;eauto.
  - (*deref*)
    destruct a;try(inv H;fail);simpl in *; unfold make_load in TR.
    + destruct access_mode eqn:?;inv TR;inv H3;rewrite Heqm0 in H4;inv H4; inv H2;rewrite Heqm0 in H3;inv H3; eapply H1 in H as ?;eauto; inv H;repeat bexpr;empfp.
      econstructor ;eapply me_local;eauto.
      econstructor 2. eapply match_env_globals;eauto. rewrite symbols_preserved;eauto.
    + monadInv TR; destruct access_mode eqn:?;inv EQ0;inv H3;rewrite Heqm0 in H4;inv H4; inv H2;rewrite Heqm0 in H3;inv H3; eapply H1 in H as ?;eauto; inv H;repeat bexpr;empfp. eapply transl_expr_correct;eauto.
    + monadInv TR.
      unfold bind in H1. rewrite EQ in H1. rewrite EQ1 in H1.
      eapply transl_lvalue_correct in H as R0;eauto.
      Focus 2. simpl. unfold bind. rewrite EQ. eauto.
      eapply H1 in H as R;eauto.
      destruct (access_mode t)eqn:?;inv EQ2.
      * inv H3;rewrite Heqm0 in H4;inv H4;inv H2;rewrite Heqm0 in H3; inv H3.
        pose proof EQ1 as R2.
        unfold make_field_access in EQ1.
        destruct (typeof a) eqn:?;try discriminate.
        destruct (cu_comp_env prog)!i0 eqn:?;inv EQ1.
        destruct Archi.ptr64 eqn:?;try discriminate.
        monadInv H3.
        eapply eval_Eload;eauto.
        econstructor;eauto.
      * inv H3;rewrite Heqm0 in H4;inv H4;inv H2;rewrite Heqm0 in H3; inv H3;empfp.
      * inv H3;rewrite Heqm0 in H4;inv H4;inv H2;rewrite Heqm0 in H3; inv H3;empfp.
  - (*addrof*)
    inv EV. eapply me_local in MENV as ?;eauto.
    econstructor;eauto. econstructor;eauto.
    eapply match_env_globals in MENV as ?;eauto.
    erewrite<- symbols_preserved in H4.
    econstructor. econstructor 2;eauto. 
  - (*field*)
    eapply H1 in EQ as ?;eauto.
    unfold make_field_access in EQ0.
    destruct (typeof a) eqn:?;inv EQ0;auto.
    destruct (cu_comp_env prog) ! i0 eqn:?;inv H4.
    monadInv H5. destruct Archi.ptr64 eqn:?;try discriminate.
    eapply transl_expr_correct in H as ?;eauto.
    repeat bexpr;empfp.
Qed.

Lemma transl_expr_fp_correct:
  forall a fp,
    Clight_local.eval_expr_fp ge e le m a fp->
    forall v ta (TR: transl_expr prog.(cu_comp_env) a = OK ta)(EV:Clight.eval_expr ge e le m a v) , 
      Csharpminor_local.eval_expr_fp tge te le m ta fp.
Proof. pose proof(proj1 transl_expr_lvalue_fp_correct);auto. Qed.
Lemma transl_lvalue_fp_correct:
  forall a fp,
    Clight_local.eval_lvalue_fp ge e le m a fp ->
    forall b ofs ta (TR: transl_lvalue prog.(cu_comp_env) a = OK ta)(EV:Clight.eval_lvalue ge e le m a b ofs),
      Csharpminor_local.eval_expr_fp tge te le m ta fp.
Proof. pose (proj2 transl_expr_lvalue_fp_correct);auto. Qed.

Lemma eval_expr_det:
  forall ge p e m a v v',
    eval_expr ge p e m a v->
    eval_expr ge p e m a v'->
    v = v'.
Proof.
  clear;induction a;intros;auto;  inv H;inv H0;inv_eq;auto;try congruence.
  inv H1;inv H2;try congruence.
  eapply IHa in H3;eauto;congruence. 
  eapply IHa1 in H4;eauto. eapply IHa2 in H6;eauto. congruence.
  eapply IHa in H3;eauto. congruence.
Qed.

Lemma transl_exprlist_correct:
  forall al tyl vl,
    Clight.eval_exprlist ge e le m al tyl vl->
    forall bl (TR:transl_arglist prog.(cu_comp_env) al tyl= OK bl),
      eval_exprlist tge te le m bl vl.
Proof.
  induction al;intros;inv H;monadInv TR. constructor.
  eapply IHal in H6;eauto. eapply transl_expr_correct in H2;eauto.
  econstructor;eauto. eapply make_cast_correct;eauto.
Qed.

Lemma transl_exprlist_fp_correct:
  forall al tyl vl fp,
    Clight.eval_exprlist ge e le m al tyl vl->
    Clight_local.eval_exprlist_fp ge e le m al tyl fp->
    forall bl (TR:transl_arglist prog.(cu_comp_env) al tyl= OK bl),
      eval_exprlist_fp tge te le m bl fp.
Proof.
  induction al;intros;inv H0; monadInv TR. constructor.
  eapply transl_expr_fp_correct in EQ as ?;eauto.
  eapply make_cast_fp_correct in EQ1 as ?;eauto.
  econstructor;eauto. inv H. eapply IHal;eauto.  eapply transl_expr_correct;eauto.
Qed.  

End EXPR.

    (** ** Semantic preservation for statements *)

(** The simulation diagram for the translation of statements and functions
  is a "plus" diagram of the form
<<
           I
     S1 ------- R1
     |          |
   t |        + | t
     v          v
     S2 ------- R2
           I                         I
>>

The invariant [I] is the [match_states] predicate that we now define.
*)


Inductive match_transl: stmt -> cont -> stmt -> cont -> Prop :=
  | match_transl_0: forall ts tk,
      match_transl ts tk ts tk
  | match_transl_1: forall ts tk,
      match_transl (Sblock ts) tk ts (Kblock tk).

Lemma match_transl_step:
  forall ts tk ts' tk' f te le m,
  match_transl (Sblock ts) tk ts' tk' ->
  star (step tge) (Core_State f ts' tk' te le) m empfp (Core_State f ts (Kblock tk) te le) m.
Proof.
  intros. inv H.
  apply star_one. constructor.
  apply star_refl.
Qed.
Definition tenv_lessdef (le1 le2:temp_env):Prop:=
  forall id v, le1!id = Some v-> exists v', le2!id=Some v' /\ Val.lessdef v v'.
Inductive match_cont: composite_env -> type -> nat -> nat -> Clight.cont -> Csharpminor.cont -> Prop :=
  | match_Kstop: forall ce tyret nbrk ncnt,
      match_cont tyret ce nbrk ncnt Clight.Kstop Kstop
  | match_Kseq: forall ce tyret nbrk ncnt s k ts tk,
      transl_statement ce tyret nbrk ncnt s = OK ts ->
      match_cont ce tyret nbrk ncnt k tk ->
      match_cont ce tyret nbrk ncnt
                 (Clight.Kseq s k)
                 (Kseq ts tk)
  | match_Kloop1: forall ce tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
      transl_statement ce tyret 1%nat 0%nat s1 = OK ts1 ->
      transl_statement ce tyret 0%nat (S ncnt) s2 = OK ts2 ->
      match_cont ce tyret nbrk ncnt k tk ->
      match_cont ce tyret 1%nat 0%nat
                 (Clight.Kloop1 s1 s2 k)
                 (Kblock (Kseq ts2 (Kseq (Sloop (Sseq (Sblock ts1) ts2)) (Kblock tk))))
  | match_Kloop2: forall ce tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
      transl_statement ce tyret 1%nat 0%nat s1 = OK ts1 ->
      transl_statement ce tyret 0%nat (S ncnt) s2 = OK ts2 ->
      match_cont ce tyret nbrk ncnt k tk ->
      match_cont ce tyret 0%nat (S ncnt)
                 (Clight.Kloop2 s1 s2 k)
                 (Kseq (Sloop (Sseq (Sblock ts1) ts2)) (Kblock tk))
  | match_Kswitch: forall ce tyret nbrk ncnt k tk,
      match_cont ce tyret nbrk ncnt k tk ->
      match_cont ce tyret 0%nat (S ncnt)
                 (Clight.Kswitch k)
                 (Kblock tk)
  | match_Kcall: forall ce tyret nbrk ncnt nbrk' ncnt' f e k id tf te le le' tk,
      transl_function prog.(cu_comp_env) f = OK tf ->
      match_env e te ->
      match_cont prog.(cu_comp_env) (Clight.fn_return f) nbrk' ncnt' k tk ->
      tenv_lessdef le le'->
      match_cont ce tyret nbrk ncnt
                 (Clight.Kcall id f e le k)
                 (Kcall id tf te le' tk).
Inductive match_states: ClightLang.core*mem -> Csharpminor_local.core*mem -> Prop :=
  | match_state:
      forall f nbrk ncnt s k e le le' m m' tf ts tk te ts' tk'
          (TRF: transl_function prog.(cu_comp_env) f = OK tf)
          (TR: transl_statement prog.(cu_comp_env) (Clight.fn_return f) nbrk ncnt s = OK ts)
          (MTR: match_transl ts tk ts' tk')
          (MENV: match_env e te)
          (MK: match_cont prog.(cu_comp_env) (Clight.fn_return f) nbrk ncnt k tk)
          (MEXT: Mem.extends m m')
          (TENV:tenv_lessdef le le'),
      match_states (ClightLang.Core_State f s k e le,m)
                   (Csharpminor_local.Core_State tf ts' tk' te le',m')
  | match_callstate:
      forall fd args args' k m m' tfd tk targs tres cconv ce
          (TR: match_fundef prog fd tfd)
          (MK: match_cont ce Tvoid 0%nat 0%nat k tk)
          (ISCC: Clight.is_call_cont k)
          (TY: type_of_fundef fd = Tfunction targs tres cconv)
          (MEXT:Mem.extends m m')
          (LD:Val.lessdef_list args args'),
      match_states (ClightLang.Core_Callstate fd args k,m)
                   (Csharpminor_local.Core_Callstate tfd args' tk,m')
  | match_returnstate:
      forall res k m m' tk ce res'
        (MK: match_cont ce Tvoid 0%nat 0%nat k tk)
        (LD:Val.lessdef res res')
        (MEXT:Mem.extends m m'),
      match_states (ClightLang.Core_Returnstate res k,m)
                   (Csharpminor_local.Core_Returnstate res' tk,m').

Lemma tenv_lessdef_refl:
  forall le, tenv_lessdef le le.
Proof. unfold tenv_lessdef;intros. exists v. split;auto. Qed.
Remark match_states_skip:
  forall f e le te nbrk ncnt k tf tk m ,
  transl_function prog.(cu_comp_env) f = OK tf ->
  match_env e te ->
  match_cont prog.(cu_comp_env) (Clight.fn_return f) nbrk ncnt k tk ->
  match_states (ClightLang.Core_State f Clight.Sskip k e le,m) (Csharpminor_local.Core_State tf Sskip tk te le,m).
Proof.
  intros. econstructor; eauto. simpl; reflexivity. constructor.
  apply Mem.extends_refl.
  apply tenv_lessdef_refl.
Qed.

(** Commutation between label resolution and compilation *)

Section FIND_LABEL.
Variable ce: composite_env.
Variable lbl: label.
Variable tyret: type.

Lemma transl_find_label:
  forall s nbrk ncnt k ts tk
  (TR: transl_statement ce tyret nbrk ncnt s = OK ts)
  (MC: match_cont ce tyret nbrk ncnt k tk),
  match Clight.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label lbl ts tk = Some (ts', tk')
      /\ transl_statement ce tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont ce tyret nbrk' ncnt' k' tk'
  end

with transl_find_label_ls:
  forall ls nbrk ncnt k tls tk
  (TR: transl_lbl_stmt ce tyret nbrk ncnt ls = OK tls)
  (MC: match_cont ce tyret nbrk ncnt k tk),
  match Clight.find_label_ls lbl ls k with
  | None => find_label_ls lbl tls tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label_ls lbl tls tk = Some (ts', tk')
      /\ transl_statement ce tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont ce tyret nbrk' ncnt' k' tk'
  end.

Proof.
* intro s; case s; intros; try (monadInv TR); simpl.
- (* skip *)
  auto.
- (* assign *)
  unfold make_store, make_memcpy in EQ3.
  destruct (access_mode (typeof e)); monadInv EQ3; auto.
- (* set *)
  auto.
- (* call *)
  simpl in TR. destruct (classify_fun (typeof e)); monadInv TR. auto.
- (* builtin *)
  auto.
- (* seq *)
  exploit (transl_find_label s0 nbrk ncnt (Clight.Kseq s1 k)); eauto. constructor; eauto.
  destruct (Clight.find_label lbl s0 (Clight.Kseq s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
- (* ifthenelse *)
  exploit (transl_find_label s0); eauto.
  destruct (Clight.find_label lbl s0 k) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
- (* loop *)
  exploit (transl_find_label s0 1%nat 0%nat (Kloop1 s0 s1 k)); eauto. econstructor; eauto.
  destruct (Clight.find_label lbl s0 (Kloop1 s0 s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label; eauto. econstructor; eauto.
- (* break *)
  auto.
- (* continue *)
  auto.
- (* return *)
  simpl in TR. destruct o; monadInv TR. auto. auto.
- (* switch *)
  assert (exists b, ts = Sblock (Sswitch b x x0)).
  { destruct (classify_switch (typeof e)); inv EQ2; econstructor; eauto. }
  destruct H as [b EQ3]; rewrite EQ3; simpl.
  eapply transl_find_label_ls with (k := Clight.Kswitch k); eauto. econstructor; eauto.
- (* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists nbrk; exists ncnt; auto.
  eapply transl_find_label; eauto.
- (* goto *)
  auto.

* intro ls; case ls; intros; monadInv TR; simpl.
- (* nil *)
  auto.
- (* cons *)
  exploit (transl_find_label s nbrk ncnt (Clight.Kseq (seq_of_labeled_statement l) k)); eauto.
  econstructor; eauto. apply transl_lbl_stmt_2; eauto.
  destruct (Clight.find_label lbl s (Clight.Kseq (seq_of_labeled_statement l) k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label_ls; eauto.
Qed.

End FIND_LABEL.

(** Properties of call continuations *)

Lemma match_cont_call_cont:
  forall ce' tyret' nbrk' ncnt' ce tyret nbrk ncnt k tk,
  match_cont ce tyret nbrk ncnt k tk ->
  match_cont ce' tyret' nbrk' ncnt' (Clight.call_cont k) (call_cont tk).
Proof. induction 1; simpl; auto; econstructor; eauto. Qed.

Lemma match_cont_is_call_cont:
  forall ce tyret nbrk ncnt k tk ce' tyret' nbrk' ncnt',
  match_cont ce tyret nbrk ncnt k tk ->
  Clight.is_call_cont k ->
  match_cont ce' tyret' nbrk' ncnt' k tk /\ is_call_cont tk.
Proof. intros. inv H; simpl in H0; try contradiction; simpl;  split; auto; econstructor ;eauto. Qed.

Definition MS (b:bool) mu fp fp' cm cm' :Prop:=
  match_states cm cm' /\
  Injections.FPMatch' mu fp fp' /\
  let (c, m) := cm in
  let (c', m') := cm' in
  (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
  (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
  (proper_mu ge tge inject_id mu) /\
  (MemClosures_local.unmapped_closed mu m m').
Lemma freelist_valid_block:
  forall a m m' l,
    Mem.free_list m a = Some m'->
    (forall b, Bset.belongsto l b -> Mem.valid_block m b)->
    forall b,Bset.belongsto l b ->Mem.valid_block m' b.
Proof.
  induction a;intros; inv H;auto;inv_eq.
  exploit IHa;eauto;intros. apply H0 in H.
  eapply Mem.valid_block_free_1; eauto.
Qed.

Ltac invMS :=
  match goal with
  | H: MS _ _ _ _  ?cm1 ?cm2 |- _ =>
    destruct cm1 as [sc Hm]; destruct cm2 as [tc Lm];
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU RCPRESV]]]]]
  | H: MS _ _ _ _  ?cm1 ?cm2 |- _ =>
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU RCPRESV]]]]]
  end.

Ltac resolvfp:=
  match goal with
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; auto; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) ?fp1' => 
    eapply Injections.fp_match_union_S'; auto; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union ?fp1 _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union (FP.union ?fp1 _) _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union (FP.union ?fp1' _) _) (FP.union (FP.union ?fp1 _) _)=> 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp1 ?fp') =>
    rewrite FP.union_comm_eq; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp' _) =>
    apply FP.subset_union_subset; auto
  | |- Injections.FPMatch' _ _ empfp => apply Injections.fp_match_emp'
  | H: FP.subset ?fp1 ?fp2 |- Injections.FPMatch' _ ?fp2 ?fp1 =>
    apply Injections.fp_match_subset_T' with fp2; try exact H; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) ?fp2 =>
    apply Injections.fp_match_union_S'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union ?fp2 _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union'; resolvfp                                          
  | H: (forall b, Bset.belongsto (FP.blocks ?fp2) _ -> ~ Injections.SharedTgt ?mu _)
    |- Injections.FPMatch' _ _ ?fp2 =>
    apply Injections.fp_match_local_block; auto                                          
  | |- FP.subset ?fp ?fp => apply FP.subset_refl
  | H: fp_inject _ ?fp ?fp', H': proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp' =>
    eapply fp_inject_fp_match; inv H'; eauto
  | H: fp_inject inject_id ?fp ?fp'|- FP.subset ?fp' ?fp =>
    apply fp_inject_id_fp_subset
  | H: proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp => inv H; eapply fp_match_id; eauto
  | _ => idtac
  end.

Ltac eresolvfp:= resolvfp; eauto.

Ltac resvalid:=
  match goal with
  (** valid blocks *)
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.free ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_free_1; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.free_list ?m1 _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    =>  eapply freelist_valid_block; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.alloc ?m1 _ _ = (?m2,_)
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_alloc; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.store _ ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.store_valid_block_1; eauto
  (** Mem inv *)
  | H1: Mem.store _ ?m1 _ _ _ = Some ?m2,
        H2: Mem.store _ ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.store_val_inject_unmapped_closed_preserved;
       try (rewrite Z.add_0_r);  try eassumption;
       try (compute; eauto; fail); try Lia.lia
  | H1: Mem.free ?m1 _ _ _ = Some ?m2,
        H2: Mem.free ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.alloc ?m1 _ _ = (?m2, _),
        H2: Mem.alloc ?m1' _ _ = (?m2', _),
            H3: proper_mu _ _ _ _
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto;
      try (eapply Mem.alloc_unchanged_on; eauto; fail)
  | _ => idtac
  end.

Lemma freelist_unmapped_closed:
  forall mu a m m' Lm x,
    Mem.free_list m a = Some m' ->
    Mem.free_list Lm a = Some x ->
    (forall b : block,
        Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) ->
    (forall b : block,
        Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block Lm b) ->
    MemClosures_local.unmapped_closed mu m Lm ->
    Mem.extends m Lm ->
    Mem.extends m' x ->
    proper_mu ge tge inject_id mu -> MemClosures_local.unmapped_closed mu m' x.
Proof.
  induction a;intros;inv H;inv H0;auto.
  destruct a,p. destruct (Mem.free m b z0 z) eqn:?;try discriminate.
  eapply Mem.free_parallel_extends in Heqo as ?;eauto.
  Hsimpl. rewrite H in H7.
  eapply IHa;eauto;resvalid.
Qed.

Ltac Right := do 4 eexists; [apply plus_one|resolvfp].
Ltac FP:= match goal with |- ?P /\ _ => assert P; [eresolvfp| try (split;[auto; fail|])] end.
Ltac splitMS :=
  constructor;
  [econstructor; eresolvfp |
   split; [eresolvfp|
           split; [try resvalid; auto |
                   split; [try resvalid; auto
                          |split; [auto|
                                   try resvalid; eauto]]]]].
Lemma args_type_translated:
  forall mu args args' f0 tf t t0 c,
    LDSimDefs.arg_rel (Injections.inj mu) args args'->
    transl_function (cu_comp_env prog) f0 = OK tf->
    type_of_function f0 = Tfunction t t0 c->
    val_casted_list_func args t =true ->
    tys_nonvoid t =true->
    vals_defined args = true->
    val_has_type_list_func args' (sig_args (funsig (AST.Internal tf))) = true /\ vals_defined args'=true.
Proof.
  intros. apply match_fundef_internal in H0 as ?; eapply transl_fundef_sig2 in H5;try apply H1;rewrite H5.
  clear f0 tf H0 H1 H5;revert args' t t0 c H H2 H3 H4;induction args;intros.
  inv H;inv H2; inv_eq;auto.
  unfold LDSimDefs.arg_rel in *;inv H;simpl in H2,H4.     
  destruct t eqn:?;inv H2.
  apply andb_true_iff in H0 as [];simpl in *.
  assert(t1 <> Tvoid /\ tys_nonvoid t2 = true).
  split;destruct t1 eqn:?;inv H3;auto;try (intro R;inv R;fail).
  clear H3;destruct H1.
  assert(a<>Vundef /\ vals_defined args = true).
  split;destruct a eqn:?;inv H4;auto;try(intro R;inv R;fail).
  clear H4;destruct H3.
  specialize (IHargs vl' t2 t0 c H7 H0 H2 H4).
  rewrite H,H0;simpl in *.
  destruct IHargs.
  rewrite H6,H8;split.
  apply andb_true_iff;split;auto.
  inv H5;simpl;auto;unfold val_casted_func in H;inv_eq;auto.
  inv H5;simpl;auto;unfold val_casted_func in H;inv_eq;auto.
Qed.
Lemma arg_rel_length_eq:
  forall mu args args',
    LDSimDefs.arg_rel (Injections.inj mu) args args'->
    Zlength args = Zlength args'.
Proof.
  unfold Zlength;intros until args. generalize 0.
  induction args;intros; inv H;auto.  eapply IHargs in H4;eauto.
Qed.
Lemma eval_expr_extends:
  forall a ge p e e' m v fp m',
    eval_expr ge p e m a v ->
    eval_expr_fp ge p e m a fp ->
    Mem.extends m m'->
    tenv_lessdef e e'->
    exists  v' fp',
      eval_expr ge p e' m' a v' /\ Val.lessdef v v' /\
      eval_expr_fp ge p e' m' a fp' /\ FP.subset fp' fp.
Proof.
  clear;induction a;intros;inv H0;inv H.
  eapply H2 in H3;Hsimpl. Esimpl;eauto. econstructor;eauto. econstructor;eauto. apply FP.subset_refl.
  1-2:Esimpl;eauto;econstructor;eauto;unfold empfp;simpl;apply Locs.subset_refl.
  eapply eval_expr_det in H4;try apply H5;eauto;subst.
  inv_eq. inv H9.
  eapply IHa in H5;eauto;Hsimpl.
  eapply eval_unop_lessdef in H8 as ?;eauto;Hsimpl.
  Esimpl;eauto. econstructor;eauto. econstructor;eauto.
  eapply eval_expr_det in H5;try apply H6;eauto;subst.
  eapply eval_expr_det in H8;try apply H13;eauto;subst.
  inv_eq. inv H14.
  eapply IHa1 in H6 as ?;eauto.
  eapply IHa2 in H13 as ?;eauto;Hsimpl.
  eapply eval_binop_lessdef in H10 as ?;eauto.
  eapply eval_binop_lessdef_fp in H12 as ?;eauto;Hsimpl.
  Esimpl;eauto. econstructor;eauto. econstructor;eauto.
  do 2 try eapply FP.subset_parallel_union;eauto.
  eapply eval_expr_det in H5;eauto;subst.
  inv_eq. inv H9.
  eapply IHa in H4 as ?;eauto;Hsimpl.
  eapply Mem.loadv_extends in H7 as ?;eauto;Hsimpl.
  Esimpl;eauto. econstructor;eauto. econstructor;eauto.
  eapply FP.subset_parallel_union;eauto.
  unfold FMemOpFP.loadv_fp. inv H0;auto. apply FP.subset_refl. inv H7.
Qed.

Lemma eval_exprlist_extends:
  forall a ge p e e' m v fp m',
    eval_exprlist ge p e m a v ->
    eval_exprlist_fp ge p e m a fp ->
    Mem.extends m m'->
    tenv_lessdef e e'->
    exists  v' fp',
      eval_exprlist ge p e' m' a v' /\ Val.lessdef_list v v' /\
      eval_exprlist_fp ge p e' m' a fp' /\ FP.subset fp' fp.
Proof.
  clear;induction a;intros;inv H;inv H0.
  Esimpl;eauto;try constructor;try apply Locs.subset_refl.
  eapply eval_expr_extends in H5;eauto.
  eapply IHa in H7;eauto;  Hsimpl.
  Esimpl;eauto. econstructor;eauto. econstructor;eauto.
  eapply FP.subset_parallel_union;eauto.
Qed.
Lemma eval_expr_extends':
  forall a ge p e m v fp m',
    eval_expr ge p e m a v ->
    eval_expr_fp ge p e m a fp ->
    Mem.extends m m'->
    exists v' fp',
      eval_expr ge p e m' a v' /\ Val.lessdef v v' /\
      eval_expr_fp ge p e m' a fp' /\ FP.subset fp' fp.
Proof. intros;eapply eval_expr_extends;eauto;apply tenv_lessdef_refl. Qed.
Lemma tenv_lessdef_set:
  forall le le' v v' id,
    tenv_lessdef le le'->
    Val.lessdef v v'->
    tenv_lessdef (PTree.set id v le)(PTree.set id v' le').
Proof.
  unfold tenv_lessdef;intros.
  rewrite PTree.gsspec;destruct peq;subst.
  rewrite PTree.gss in H1;inv H1; Esimpl;eauto.
  rewrite PTree.gso in H1;auto.
Qed.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Definition transl_fundef (ce: composite_env) (f: AST.fundef Clight.function) : res fundef :=
  match f with
  | AST.Internal g =>
      do tg <- transl_function ce g; OK(AST.Internal tg)
  | AST.External ef  =>
      OK(AST.External ef)
  end.
Lemma genv_match_trans: Genv.match_genvs (match_globdef (fun f tf => transl_fundef (cu_comp_env prog) f = OK tf) (fun _ _ => True)) (trans_ge ge) tge.
Proof.
  unfold trans_ge;pose proof genv_match as H; inv H.
  econstructor;eauto;simpl; intros.
  specialize (mge_defs b).
  unfold trans_genv_defs,option_map;rewrite PTree.gmap.
  inv mge_defs;auto;constructor;  inv H1;constructor;auto;  inv H2;unfold transl_fundef,trans_c_fundef_ast;auto;  rewrite H1; auto.
Qed.
Lemma ge_match_invert_symbol_preserved:
  forall name f,
    invert_symbol_from_string ge name = Some f->
    CUAST.invert_symbol_from_string tge name = Some f.
Proof.
  intros;erewrite invert_symbol_trans_preserved in H;eauto.
  erewrite CUAST.match_genvs_invert_symbol_from_string_preserved;eauto using genv_match_trans.
  intros;inv H0;auto. induction f1;auto;monadInv H1;auto.
Qed.

Lemma bind_parameter_temps_lessdef:
  forall f al t e t',
    bind_parameter_temps f al t = Some e->
    tenv_lessdef t t'->
    forall bl,
      Val.lessdef_list al bl->
      exists e',bind_parameter_temps f bl t' = Some e' /\ tenv_lessdef e e'.
Proof.
  induction f;intros;simpl in *;inv H1;inv H. exists t';split;auto.
  1,2:destruct a;try discriminate.
  eapply IHf in H4;eauto.  eapply tenv_lessdef_set;eauto.
Qed.
Lemma freelist_extends:
  forall  l m m',
    Mem.free_list m l = Some m'->
    forall em,
      Mem.extends m em->
      exists em', Mem.free_list em l = Some em' /\ Mem.extends m' em'.
Proof.
  induction l;intros;inv H. simpl. Esimpl;eauto.
  destruct a,p,(Mem.free) eqn:?;try discriminate.
  eapply Mem.free_parallel_extends in Heqo;eauto;Hsimpl.
  eapply IHl in H2;eauto;Hsimpl.
  Esimpl;eauto. simpl. rewrite H. auto.
Qed.
Ltac triv:= Esimpl; [constructor;econstructor;eauto|eresolvfp|splitMS];simpl;eauto;try(econstructor;eauto;fail).

Lemma TRANSF_local_ldsim:
  @local_ldsim Clight_IS_2_local Csharpminor_IS ge tge ge tge.
Proof.
  econstructor.
  instantiate(1:= fun b (i:nat)=>MS b).
  instantiate(1:=lt).
  assert(GEMATCH:ge_match_strict ge tge).
  apply ge_match.
  constructor.
  apply lt_wf.
  intros;invMS;eapply proper_mu_inject; eauto.
  intros;invMS;eapply proper_mu_ge_init_inj;eauto.
  auto.
  { (*init*)
    intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    unfold init_core_local in *. simpl in *.
    unfold init_core in *.
    
    unfold Clight_local.init_core in INITCORE.
    unfold generic_init_core in INITCORE |- *.
    erewrite symbols_preserved.
    destruct Genv.find_symbol eqn:?;[|inv INITCORE].
    destruct (Genv.find_funct_ptr ge b) eqn:?;[|inv INITCORE].
    
    apply function_ptr_translated in Heqo0 as ?.
    destruct H as [tf[Heqo' FUNDEFMATCH]].
    rewrite Heqo'.
    destruct f eqn:?;[|inv INITCORE].
    unfold type_of_fundef in INITCORE.
    destruct (type_of_function f0) eqn:?;try (inv INITCORE;fail).
    destruct (val_casted_list_func args t && tys_nonvoid t && vals_defined args && zlt (4 * (2 * Zlength args)) Int.max_unsigned) eqn:?;inv INITCORE.

    unfold fundef_init.
    inv FUNDEFMATCH. rename H0 into FUNCTRANS.
    apply andb_true_iff in Heqb0 as [Heqb0 ZLT].
    apply andb_true_iff in Heqb0 as [Heqb0 VALSDEF].
    apply andb_true_iff in Heqb0 as [VALCASTED TYSNOVOID].
    edestruct args_type_translated as(A1&A2);eauto.
    erewrite A1,A2,<- arg_rel_length_eq with(args':=args'),ZLT;eauto;simpl.
    eexists;split;eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists O.
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. induction args; intros args' REL G MEMREL; inv REL.
      auto. inv G. f_equal. inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. }
    subst.
    splitMS.
    econstructor;eauto.
    apply match_Kstop.
    constructor.
    {
      inv MEMINITINJ; inv HRELY; inv LRELY.
      eapply inject_implies_extends;eauto.
      intros b0 A. unfold Mem.valid_block in A; rewrite EQNEXT, <- dom_eq_src in A. eapply Bset.inj_dom in A; eauto.
      destruct A as [b' A]. unfold Bset.inj_to_meminj. rewrite A. eauto.
      inv GE_INIT_INJ. rewrite mu_shared_src in dom_eq_src. rewrite mu_shared_tgt in dom_eq_tgt. rewrite S_EQ in dom_eq_src.
      assert (forall b, Plt b (Mem.nextblock sm0) <-> Plt b (Mem.nextblock tm0)).
      intro. rewrite <- dom_eq_src, <- dom_eq_tgt. tauto.
      rewrite EQNEXT, EQNEXT0.
      destruct (Pos.lt_total (Mem.nextblock sm0) (Mem.nextblock tm0)) as [LT | [EQ | LT]]; auto; generalize H3 LT; clear; intros; exfalso; apply H3 in LT; eapply Pos.lt_irrefl; eauto.
    }
    { clear; induction args;auto. }
    inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_src; auto.
    inv MEMINITINJ. inv LRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto.
    inv MEMINITINJ; econstructor; eauto. simpl. intro.
    intros ? ? ? ? ? . exploit inj_inject_id. exact H. intro. inv H0.
    intro A. inv A. auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
  }
  { (*tau*)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP. simpl in STEP.
    revert i mu Hfp Lfp Lcore Lm MS.
    pose proof STEP as STEP_bk.
    induction STEP;intros;invMS; inv MS; right;exists 0%nat;simpl.
    { (*assign*)
      monadInv TR.
      eapply transl_lvalue_correct in H as EV1;eauto.
      eapply transl_lvalue_fp_correct in H3 as FP1;eauto.
      eapply transl_expr_correct in H0 as EV2;eauto.
      eapply transl_expr_fp_correct in H4 as FP2;eauto.

      eapply make_cast_correct in EV2 as EV2';eauto.
      eapply make_cast_fp_correct in FP2 as FP2';eauto.
      eapply eval_expr_extends in EV1 as ?;eauto.
      eapply eval_expr_extends in EV2' as ?;eauto.
      Hsimpl.
      inv H12. inv H2.
      eapply Mem.storev_extends in H15 as ?;eauto; Hsimpl.
      eapply assign_loc_value in H2 ;eauto.
      inv H6.
      assert(R1:FP.subset ( (FP.union x5 x3))( (FP.union (FP.union fp1 fp2) fp3))).
      rewrite <- FP.fp_union_assoc with(fp1:=fp1).
      eapply FP.subset_parallel_union;eauto.
      assert(R2:Injections.FPMatch' mu (FP.union Hfp (FP.union (FP.union (FP.union fp1 fp2) fp3)(FMemOpFP.storev_fp chunk0 (Vptr loc ofs)))) (FP.union Lfp (FP.union (FP.union x5 x3) (FMemOpFP.storev_fp chunk0 (Vptr loc ofs))))).
      resolvfp.
      assert(R3:Injections.FPMatch' mu (FP.union (FP.union (FP.union fp1 fp2) fp3)(FMemOpFP.storev_fp chunk0 (Vptr loc ofs))) (FP.union (FP.union x5 x3) (FMemOpFP.storev_fp chunk0 (Vptr loc ofs)))).
      resolvfp.
      inv SGEINIT.
      eapply make_store_correct with(f:=tf)(k:=tk) in EQ3 as ?;try apply H8;eauto;[|econstructor;eauto].
      exists   (FP.union (FP.union x5 x3) (FMemOpFP.storev_fp chunk0 (Vptr loc ofs))),
      (Core_State tf Sskip tk te le') ,x4.
      Esimpl;auto.
      + inversion MTR.
        subst ts0 tk0 ts' tk';econstructor;eauto. 
        subst tk0 ts0 ts tk'.
        inversion H19.
        contradict H32. clear. intro.
        induction tk;inv H. auto.
      + splitMS.
        simpl;eauto. constructor.
        unfold Mem.storev in H15;resvalid.
        inversion H2;subst x2 x4;unfold Mem.storev in H21; resvalid.
        rewrite H6;auto.
        inversion H2;subst x2 x4;unfold Mem.storev in *.
        rewrite H17 in H12;inversion H12;subst chunk0.
        rewrite H17 in H20;inversion H20;subst chunk1.
        rewrite <- H6 in *;resvalid.
    }
    { (*Sset*)
      monadInv TR;inv MTR.
      eapply transl_expr_correct in H as EV1;eauto.
      eapply transl_expr_fp_correct in H0 as FP1;eauto.
      eapply eval_expr_extends in EV1 as ?;eauto.
      Hsimpl. triv.
      eapply tenv_lessdef_set;eauto.
    }
    { (*call*)
      simpl in TR.  unfold bind in TR. inv_eq. inv H8. inv H.
      eapply transl_expr_correct in H0 as EV1;eauto.
      eapply transl_exprlist_correct in H1 as EVL1;eauto.
      eapply transl_expr_fp_correct in H4 as FP1;eauto.
      eapply transl_exprlist_fp_correct in H5 as FPL2;eauto.
      eapply eval_expr_extends in EV1 as EV1';eauto.
      eapply eval_exprlist_extends in EVL1 as EVL1';eauto.
      Hsimpl;inv MTR.
      eapply functions_translated in H2 as F1;eauto; Hsimpl.
      eapply transl_fundef_sig2 in H3 as ?;eauto.
      triv.
      unfold signature_of_type in H15. rewrite H15. f_equal.
      revert H1. clear; revert tyargs vargs.
      induction al;intros. inv H1;simpl;auto.
      inv H1.  eapply IHal in H6.
      simpl. f_equal. auto.
    }
      monadInv TR;inv MTR;triv.
      monadInv TR;inv MTR;inv MK;triv.
      monadInv TR;inv MTR;inv MK;triv.
      monadInv TR;inv MTR;inv MK;triv.
    { (*ifthenelse*)
      monadInv TR;inv MTR.
      eapply transl_expr_correct in H as EV1;eauto.
      eapply transl_expr_fp_correct in H1 as FP1;eauto.
      eapply make_boolean_correct in H0 as R;eauto.
      destruct R as [?[EV2 ?]].
      eapply make_boolean_fp_correct in H2 as FP2;eauto.
      eapply eval_expr_extends in EV1 as EV1';eauto.
      eapply eval_expr_extends in EV2 as EV2';eauto.
      Hsimpl. destruct b eqn:?;triv;try(rewrite Heqb0;constructor;fail);try(inv H5;eauto; inv H3;constructor).
    }
    { (*loop*)
      monadInv TR;inv MTR.
      Esimpl. econstructor 2. constructor. econstructor 2. constructor.
      econstructor 2. constructor. constructor. constructor.
      eresolvfp. splitMS.  econstructor;eauto.  econstructor;eauto.

      Esimpl;eauto. econstructor 2. constructor. econstructor 2. constructor.  constructor.  constructor.
      eresolvfp. splitMS. econstructor;eauto. econstructor;eauto.
    }
    { (*loop continue*)
      destruct H;subst;monadInv TR;inv MTR;inv MK;Esimpl;eauto.
      econstructor 2. econstructor. constructor. econstructor. 
      eresolvfp. splitMS; econstructor;eauto.
      econstructor 2. constructor. econstructor;constructor.
      eresolvfp. splitMS; econstructor;eauto.
    }
    { (*loop break*)
      monadInv TR;inv MTR;inv MK.
      Esimpl;eauto.
      econstructor 2;eauto. constructor. econstructor 2. constructor.  econstructor 2. constructor. constructor. constructor.
      eresolvfp. splitMS;simpl;eauto. econstructor.
    }
    { (*loop skip*)
      monadInv TR;inv MTR;inv MK;triv;rewrite H6,H8;auto.
    }
    { (*loop2 break*)
      monadInv TR;inv MTR;inv MK;Esimpl;eauto.
      econstructor 2;constructor. constructor.
      eresolvfp. splitMS. simpl. eauto. constructor.
    }
    { (*return*)
      monadInv TR;inv MTR.
      pose proof H as R. erewrite <-match_env_free_blocks,R in H;eauto.
      symmetry in H.
      eapply freelist_extends in H as ?;eauto;Hsimpl.
      triv.
      erewrite match_env_same_blocks;eauto;eresolvfp.
      eapply match_cont_call_cont;eauto.
      erewrite match_env_same_blocks;eauto;eresolvfp.
      eapply freelist_unmapped_closed;eauto.
    }
    { (*return*)
      monadInv TR. inv MTR.
      eapply transl_expr_correct in H as EV1;eauto.
      eapply transl_expr_fp_correct in H2 as FP1;eauto.
      eapply make_cast_fp_correct in FP1;eauto.
      eapply make_cast_correct in EV1;eauto.
      eapply eval_expr_extends in EV1 as ?;eauto.
      Hsimpl.
      eapply freelist_extends in H1 as ?;eauto;Hsimpl.
      erewrite<- match_env_same_blocks in *;eauto.
      triv.
      eapply match_cont_call_cont;eauto.
      eapply freelist_unmapped_closed;eauto.
    }
    { (*skip return*)
      monadInv TR;inv MTR.
      pose proof H0 as R.
      erewrite <-match_env_free_blocks in H0;eauto.
      rewrite R in H0. symmetry in H0.
      eapply freelist_extends in H0 as ?;eauto.
      Hsimpl. 
      Esimpl;eauto.
      econstructor. constructor;eauto.
      inv MK;simpl in *;auto.
      erewrite match_env_same_blocks;eauto. eresolvfp.
      erewrite match_env_same_blocks;eauto.
      splitMS. eapply match_cont_is_call_cont;eauto.
      eapply freelist_unmapped_closed;eauto.
    }
    { (*switch*)
      pose proof TR as TR'.
      monadInv TR.
      eapply transl_expr_correct in H as EV1;eauto.
      eapply transl_expr_fp_correct in H0 as FP1;eauto.
      eapply eval_expr_extends in EV1 as ?;eauto.
      Hsimpl.
      unfold sem_switch_arg in H1.
      destruct (classify_switch (typeof a)) eqn:?;inv EQ2;
        destruct v eqn:?;inv H1;
        inv H3;inv MTR;
          eapply transl_lbl_stmt_1 in EQ1 as ?;eauto;
          eapply transl_lbl_stmt_2 in H1;eauto;
            Esimpl;eauto.
      1,7:  econstructor 2;econstructor; econstructor;eauto;econstructor.
      3,8: econstructor;econstructor;eauto;econstructor.
      all: try eresolvfp;try  splitMS;econstructor;eauto.
    }
      destruct H;subst;monadInv TR;inv MTR;inv MK;triv.
      monadInv TR;inv MTR;inv MK;triv.
      monadInv TR;inv MTR;triv.
    { (*goto*)
      monadInv TR;inv MTR.
      generalize TRF. unfold transl_function. intro TRF'.
      monadInv TRF'.
      exploit (transl_find_label (cu_comp_env prog) lbl). eexact EQ. eapply match_cont_call_cont. eauto.
      rewrite H; intros [ts' [tk'' [nbrk' [ncnt' [A [B C]]]]]].
      triv.
    }
    { (*internal*)
      inv H. inv TR. monadInv H6. inv H0.
      exploit match_cont_is_call_cont; eauto. intros [A B].
      exploit match_env_alloc_variables; eauto.
      apply match_env_empty.

      intros [te1 [C D]].
      eapply match_env_alloc_variables_fp in H;eauto.
      eapply alloc_variables_extends in C as ?;eauto.
      eapply bind_parameter_temps_lessdef in H5;eauto;try apply tenv_lessdef_refl.
      Hsimpl.
      Esimpl;simpl;try assumption.
      apply plus_one;eapply step_internal_function.
      erewrite transl_vars_names by eauto. assumption.
      all:try(simpl;eauto). 
      rewrite create_undef_temps_match. eapply bind_parameter_temps_match; eauto.
      eresolvfp.
      splitMS; unfold transl_function,bind.
      rewrite EQ,EQ1;auto.
      constructor.
      revert SVALID H4; clear;
        induction 2;auto; apply IHalloc_variables; resvalid.
      revert TVALID H0; clear;
        induction 2;auto; apply IHalloc_variables; resvalid.
      revert SVALID TVALID C H0 AGMU RCPRESV MEXT H8;clear;revert m m1 Lm x2 te1.
      generalize empty_env.
      induction x0;intros;inv C;inv H0;auto.
      eapply Mem.alloc_extends with(lo2:=0)(hi2:=sz) in H4 as ?;eauto;try Lia.lia.
      Hsimpl. rewrite H in H10;inv H10.
      assert(MemClosures_local.unmapped_closed mu m2 m3). resvalid.
      eapply IHx0 in H1;eauto;resvalid.
    }
    { (*return*)
      inv MK. Esimpl;eauto.  constructor. econstructor. eresolvfp.
      splitMS. simpl;eauto.
      constructor; unfold set_opttemp,set_optvar.
      destruct optid;auto. eapply tenv_lessdef_set;eauto.
    }
  }
  { (*at_ext*)
    simpl; intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MS ATEXT RC GARG.
    exists 0%nat; unfold Clight_local.at_external,at_external in *.
    destruct Hcore; try discriminate. destruct f0; try discriminate. destruct e; try discriminate. destruct vals_defined eqn:?;try discriminate.
    destruct (invert_symbol_from_string) eqn:SYMBNAME;try discriminate.
    destruct peq; try discriminate.
    destruct peq; try discriminate.
    simpl in *. inv ATEXT; invMS; inv MS; inv TR; inv TY.
    simpl in H4;subst.
    erewrite ge_match_invert_symbol_preserved;eauto.
    destruct peq; try contradiction.
    destruct peq; try contradiction.
    simpl.
    exists args'; Esimpl;auto.
    { simpl in *. unfold LDSimDefs.arg_rel.
      revert args' AGMU GARG LD  ; clear.
      (** should be extracted as a lemma ... *)
      induction argSrc; intros args' AGMU GARG LD. simpl. inv LD. auto. inv LD. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto. destruct v2; auto.
      simpl in H2. eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H; eauto.
      intro. inv H0. econstructor. unfold Bset.inj_to_meminj; rewrite H. eauto. rewrite Ptrofs.add_zero; auto. }
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    splitMS; constructor;simpl;eauto.
  }
  { (*aft-ext*)
    simpl;unfold after_external_local,Clight_IS_local,Csharpminor_IS.
    unfold Clight_local.after_external,after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    destruct Hcore; try discriminate. destruct f; try discriminate. destruct e;try discriminate.
    invMS. inv MS.
    assert(oresSrc = oresTgt).
    { destruct oresSrc, oresTgt; try contradiction; auto. simpl in RESREL.
      inv RESREL; simpl in GRES; auto; try contradiction.
      inv AGMU. apply proper_mu_inject_incr in H. inv H. rewrite Ptrofs.add_zero. auto.  }
    subst.
    assert (Hcore' = ClightLang.Core_Returnstate (match oresTgt with Some v => v | None => Vundef end) c).
    { destruct oresTgt; inv AFTEXT; auto; inv_eq;auto. }
    rename H into AFTEXT'. simpl in *. inv TY. inv TR.
    exists (Core_Returnstate (match oresTgt with Some v=> v| None => Vundef end)  tk).
    split. destruct oresTgt;auto;inv_eq;auto.
    intros Hm' Lm' [HRELY LRELY INV]. subst. exists 0%nat.
    splitMS; inv AGMU;try eapply extends_rely_extends; eauto.
    econstructor; eauto.
    intros ? S. apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT; auto.
    intros ? T. apply TVALID in T. unfold Mem.valid_block in *. inv LRELY. rewrite EQNEXT; auto.
    inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
  }
  { (*halt*)
    simpl. unfold Clight_local.halted,halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES.
    destruct Hcore; try discriminate.
    destruct c;try discriminate.
    destruct (vals_defined) eqn:?;try discriminate.
    inv HALT.
    invMS. inv MS.
    inv MK. simpl in Heqb. assert(resSrc = res').
    inv LD;auto. inv Heqb.
    subst res'. clear Heqb.
    exists resSrc. Esimpl;eauto.
    { revert LD GRES AGMU. clear;intros.
      destruct resSrc; try constructor. econstructor. simpl in GRES. inv AGMU.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. inv A. unfold Bset.inj_to_meminj; rewrite INJ; eauto. rewrite Ptrofs.add_zero; auto. }
    inv AGMU; eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto.
    eresolvfp. inv AGMU; eapply extends_reach_closed_implies_inject; eauto.
  }
  Unshelve.
  all: apply (cu_comp_env prog).
Qed.
End CORRECTNESS.