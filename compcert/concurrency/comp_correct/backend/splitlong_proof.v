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

(** Correctness of instruction selection for integer division *)

Require Import String.
Require Import Coqlib Maps.
Require Import AST Errors Integers Floats.
Require Import Values Memory Globalenvs Events Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong.

Require Import Blockset Footprint Op_fp CUAST helpers Cminor_local CminorSel_local SplitLongproof
selectop_proof. 

Local Open Scope cminorsel_scope.
Local Open Scope string_scope.

(** * Characterizing the helper functions *)
Definition helper_declared {F V: Type} (cu: comp_unit_generic (AST.fundef F) V) (id: ident) (name: string) (sg: signature) : Prop :=
  (comp_unit_defmap cu)!id = Some (Gfun (External (EF_runtime name sg))).

Definition helper_functions_declared {F V: Type} (p: comp_unit_generic (AST.fundef F) V) (hf: helper_functions) : Prop :=
     helper_declared p i64_dtos "__i64_dtos" sig_f_l
  /\ helper_declared p i64_dtou "__i64_dtou" sig_f_l
  /\ helper_declared p i64_stod "__i64_stod" sig_l_f
  /\ helper_declared p i64_utod "__i64_utod" sig_l_f
  /\ helper_declared p i64_stof "__i64_stof" sig_l_s
  /\ helper_declared p i64_utof "__i64_utof" sig_l_s
  /\ helper_declared p i64_sdiv "__i64_sdiv" sig_ll_l
  /\ helper_declared p i64_udiv "__i64_udiv" sig_ll_l
  /\ helper_declared p i64_smod "__i64_smod" sig_ll_l
  /\ helper_declared p i64_umod "__i64_umod" sig_ll_l
  /\ helper_declared p i64_shl "__i64_shl" sig_li_l
  /\ helper_declared p i64_shr "__i64_shr" sig_li_l
  /\ helper_declared p i64_sar "__i64_sar" sig_li_l
  /\ helper_declared p i64_umulh "__i64_umulh" sig_ll_l
  /\ helper_declared p i64_smulh "__i64_smulh" sig_ll_l.

(** * Correctness of the instruction selection functions for 64-bit operators *)

Ltac exacteval H:=
  eapply eval_expr_preserved; try eexact H; try gegen; eauto with gegen.
Ltac evalge H:=
  eapply eval_expr_preserved in H; try (try gegen; eauto with gegen; fail).
Ltac swapeq fp0 fp5:=
  match goal with
  | |- context[(FP.union (FP.union ?fp4 fp0) (FP.union fp5 ?fp1))] =>
    rewrite <- (FP.fp_union_assoc fp4 fp0), (FP.fp_union_assoc fp0 fp5), (FP.union_comm_eq fp0 fp5);
    rewrite <- (FP.fp_union_assoc fp5 fp0), (FP.fp_union_assoc fp4 fp5)
  end.
Ltac rffp := repeat rewrite FP.fp_union_assoc.
Ltac trivcons := repeat econstructor; eauto with evalexpr evalexprfp; simpl; eauto.


Section CMCONSTR.

Variable prog: cminorsel_comp_unit.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared prog hf.

Variable ge : genv.
Hypothesis GE_INIT: globalenv_generic prog ge.

Variable sp: val.
Variable e: env.
Variable m: mem.

Ltac UseHelper := decompose [Logic.and] i64_helpers_correct; eauto.
Ltac DeclHelper := red in HELPERS; decompose [Logic.and] HELPERS; eauto.

Lemma eval_helper_fp:
  forall le id name sg args vargs fp vres (Hi64ext: i64ext (EF_runtime name sg)),
  eval_exprlist ge sp e m le args vargs ->
  eval_exprlist_fp ge sp e m le args fp ->    
  helper_declared prog id name sg  ->
  external_implements name sg vargs vres ->
  eval_expr_fp ge sp e m le (Eexternal id sg args) fp.
Proof.
  intros.
  red in H1. eapply find_def_symbol in H1; eauto. destruct H1 as (b & P & Q).
  rewrite <- Genv.find_funct_ptr_iff in Q. 
  econstructor; eauto.
Qed.

Corollary eval_helper_fp_1:
  forall le id name sg arg1 varg1 fp vres (Hi64ext: i64ext (EF_runtime name sg)),
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr_fp ge sp e m le arg1 fp ->    
  helper_declared prog id name sg  ->
  external_implements name sg (varg1::nil) vres ->
  eval_expr_fp ge sp e m le (Eexternal id sg (arg1 ::: Enil)) fp.
Proof.
  intros. eapply eval_helper_fp; eauto. constructor; auto. constructor.
  econstructor; eauto. econstructor. econstructor. rewrite FP.fp_union_emp; auto.
Qed.

Corollary eval_helper_fp_2:
  forall le id name sg arg1 arg2 varg1 fp1 varg2 fp2 vres (Hi64ext: i64ext (EF_runtime name sg)),
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr_fp ge sp e m le arg1 fp1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  eval_expr_fp ge sp e m le arg2 fp2 ->
  helper_declared prog id name sg  ->
  external_implements name sg (varg1::varg2::nil) vres ->
  eval_expr_fp ge sp e m le (Eexternal id sg (arg1 ::: arg2 ::: Enil)) (FP.union fp1 fp2).
Proof.
  intros. eapply eval_helper_fp; eauto. constructor; auto. constructor; auto. constructor.
  econstructor; eauto. econstructor; eauto. econstructor. econstructor; eauto. econstructor. econstructor.
  rewrite FP.fp_union_emp; auto.
Qed.

Remark eval_builtin_fp_1:
  forall le id sg arg1 varg1 fp1 vres (Hi64ext: i64ext (EF_builtin id sg)),
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr_fp ge sp e m le arg1 fp1 ->    
  builtin_implements id sg (varg1::nil) vres ->
  eval_expr_fp ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: Enil)) fp1.
Proof.
  intros. econstructor; eauto. econstructor. eauto. constructor.
  econstructor; eauto. constructor. constructor. rewrite FP.fp_union_emp; auto.
Qed.

Remark eval_builtin_2:
  forall le id sg arg1 arg2 varg1 fp1 varg2 fp2 vres (Hi64ext: i64ext (EF_builtin id sg)),
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr_fp ge sp e m le arg1 fp1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  eval_expr_fp ge sp e m le arg2 fp2 ->
  builtin_implements id sg (varg1::varg2::nil) vres ->
  eval_expr_fp ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: arg2 ::: Enil)) (FP.union fp1 fp2).
Proof.
  intros. econstructor; eauto. constructor; eauto. constructor; eauto. constructor.
  econstructor; eauto. econstructor; eauto. constructor. econstructor; eauto. constructor. constructor.
  rewrite FP.fp_union_emp; auto.
Qed.



(** cstr won't introduce additional footprint *)
Definition unary_constructor_fp_sound (cstr: expr -> expr) : Prop :=
  forall le a x fp z,
    eval_expr ge sp e m le a x ->
    eval_expr_fp ge sp e m le a fp ->
    eval_expr ge sp e m le (cstr a) z ->
    exists fp', eval_expr_fp ge sp e m le (cstr a) fp' /\ FP.subset fp' fp.

Definition binary_constructor_fp_sound (cstr: expr -> expr -> expr) : Prop :=
  forall le a x fp1 b y fp2 z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fp1 ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fp2 ->
  eval_expr ge sp e m le (cstr a b) z ->
  exists fp, eval_expr_fp ge sp e m le (cstr a b) fp /\ FP.subset fp (FP.union fp1 fp2).


(** Theorems about cstr *)
Theorem eval_intoflong_fp: unary_constructor_fp_sound intoflong.
Proof.
  intros le a x fp. intros.
  unfold intoflong, lowlong.
  case (lowlong_match a) eqn:? ; InvEvalFP; InvEmpFP; Triv.
Qed.

Theorem eval_longofintu_fp: unary_constructor_fp_sound longofintu.
Proof.
  intros le a x fp. intros. unfold longofintu, makelong. Triv.
Qed.
  
Theorem eval_longofint_fp: unary_constructor_fp_sound longofint.
Proof. 
  intros le a x fp. intros. unfold longofint.
  case (longofint_match a) eqn:? ; InvEvalFP; InvEmpFP; Triv.
Qed.

Lemma eval_longconst_fp:
  forall le n, eval_expr_fp ge sp e m le (longconst n) FP.emp.
Proof. intros. EvalOpFP. repeat econstructor; eauto. Qed.

Theorem eval_negl_fp: unary_constructor_fp_sound negl.
Proof.
  intros le a x fp. intros. unfold negl.
  case (is_longconst a) eqn:? ; InvEvalFP; Triv. UseHelper. eapply H8.
Qed.

Lemma eval_splitlong_fp:
  forall le a f v fp v',  
  (forall le a b x y fpx fpy z,
      eval_expr ge sp e m le a x ->
      eval_expr_fp ge sp e m le a fpx ->        
      eval_expr ge sp e m le b y ->
      eval_expr_fp ge sp e m le b fpy ->
      eval_expr ge sp e m le (f a b) z ->
      exists fp',
        eval_expr_fp ge sp e m le (f a b) fp' /\
        FP.subset fp' (FP.union fpx fpy)) ->
  eval_expr ge sp e m le a v ->
  eval_expr_fp ge sp e m le a fp ->
  eval_expr ge sp e m le (splitlong a f) v' ->
  exists fp',
    eval_expr_fp ge sp e m le (splitlong a f) fp' /\ FP.subset fp' fp.
Proof.
  intros until v'; intros EXEC.
  unfold splitlong. case (splitlong_match a) eqn:SM; intros EVAL EVALFP EVAL'.
  - InvEval; InvEvalFP; InvEmpFP; InvEval; eqexpr.
    exploit EXEC. exact H3. exact H8. exact H2. exact H10. eauto. intros [fp' [A B]]. Triv.
  - inv EVAL'; eqexpr.
    exploit (EXEC (v1 :: le) (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))); eauto.
    EvalOp. repeat econstructor; eauto. simpl. eauto.  repeat econstructor; eauto.
    EvalOp. repeat econstructor; eauto. simpl. eauto.  repeat econstructor; eauto.
    TrivFP. intros [fp' [A B]]. Triv.
    rewrite FP.union_comm_eq. rewrite <- (FP.emp_union_fp fp) at 2. apply FP.union2_subset; auto.
Qed.

Lemma eval_splitlong2_fp:
  forall le a b f va vb fpa fpb v,
  (forall le a1 a2 b1 b2 x1 x2 fpx1 fpx2 y1 y2 fpy1 fpy2 v,
   eval_expr ge sp e m le a1 x1 ->
   eval_expr ge sp e m le a2 x2 ->
   eval_expr_fp ge sp e m le a1 fpx1 ->
   eval_expr_fp ge sp e m le a2 fpx2 ->
   eval_expr ge sp e m le b1 y1 ->
   eval_expr ge sp e m le b2 y2 ->
   eval_expr_fp ge sp e m le b1 fpy1 ->
   eval_expr_fp ge sp e m le b2 fpy2 ->
   eval_expr ge sp e m le (f a1 a2 b1 b2) v ->
   exists fp, eval_expr_fp ge sp e m le (f a1 a2 b1 b2) fp /\
         FP.subset fp (FP.union (FP.union fpx1 fpx2) (FP.union fpy1 fpy2))) ->
  eval_expr ge sp e m le a va ->
  eval_expr_fp ge sp e m le a fpa ->
  eval_expr ge sp e m le b vb ->
  eval_expr_fp ge sp e m le b fpb ->
  eval_expr ge sp e m le (splitlong2 a b f) v ->
  exists fp, eval_expr_fp ge sp e m le (splitlong2 a b f) fp /\ FP.subset fp (FP.union fpa fpb).
Proof.
  intros until v; intros EXEC.
  unfold splitlong2. case (splitlong2_match a b); intros.
- InvEvalFP; InvEval; eqexpr. simpl in *. FuncInv. subst.
  exploit (EXEC le h1 l1 h2 l2); eauto. intros [fp [A B]]. Triv.
- inv H3. InvEvalFP; InvEval; eqexpr. simpl in *. FuncInv. subst.
  exploit (EXEC (v1 :: le) (lift h1) (lift l1)
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil)));
    try eauto with evalexpr; try eauto with evalexprfp.
  EvalOp. repeat econstructor. simpl; eauto. EvalOp. repeat econstructor. simpl; eauto.
  repeat econstructor; eauto. repeat econstructor; eauto.
  TrivFP. intros [fp [A B]]. Triv. rewrite (FP.union_comm_eq fpb). apply FP.union2_subset; auto.
- inv H3. InvEvalFP;InvEval; eqexpr; simpl in *; FuncInv; subst.
  exploit (EXEC (v1 :: le)
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))
                (lift h2) (lift l2)); try eauto with evalexpr evalexprfp.
  repeat econstructor; eauto. repeat econstructor; eauto.
  repeat econstructor; eauto. repeat econstructor; eauto.
  TrivFP. intros [fp [A B]]. Triv. do 2 rewrite (FP.union_comm_eq fpa). apply FP.union2_subset; auto.
- inv H3. inv H9. InvEvalFP;InvEval; eqexpr; simpl in *; FuncInv; subst.
  exploit (EXEC (vb :: v1 :: le)
                (Eop Ohighlong (Eletvar 1 ::: Enil)) (Eop Olowlong (Eletvar 1 ::: Enil))
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil)));
    try eauto with evalexpr evalexprfp; try (repeat econstructor; eauto; fail).
  eapply eval_lift in H1. instantiate (1:= v1) in H1. eqexpr. eauto.
  TrivFP. intros [fp [A B]]. eexists. split.
  eapply eval_lift in H1. instantiate (1:= v1) in H1. eqexpr. 
  repeat econstructor; eauto with evalexpr evalexprfp.
  rewrite FP.fp_union_assoc, FP.union_comm_eq. rewrite <- (FP.emp_union_fp (FP.union fpa fpb)) at 2.
  apply FP.union2_subset; auto.
Qed.

Theorem eval_notl_fp: unary_constructor_fp_sound notl.
Proof.
  intros le a x fp. unfold notl. intros. 
  exploit (eval_splitlong_fp le a (fun h l => makelong (notint h) (notint l))).
  clear; unfold makelong; intros. InvEval.
  exploit eval_notint_fp; try exact H; eauto. intros [fpa [A1 B1]].
  exploit eval_notint_fp; try exact H1; eauto. intros [fpb [A2 B2]].
  Triv. apply subset2_union; TrivFP.
  eauto. eauto. eauto. eauto.
Qed.

Theorem eval_longoffloat_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.longoffloat x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (longoffloat a) fp /\ FP.subset fp fpx.
Proof. 
  intros; unfold longoffloat. econstructor; split. 
  eapply eval_helper_fp_1; eauto. 2: DeclHelper. constructor. UseHelper; auto. TrivFP.
Qed.

Theorem eval_longuoffloat_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.longuoffloat x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (longuoffloat a) fp /\ FP.subset fp fpx.
Proof.
  intros; unfold longuoffloat. econstructor; split.
  eapply eval_helper_fp_1; eauto. 2: DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_floatoflong_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.floatoflong x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (floatoflong a) fp /\ FP.subset fp fpx.
Proof.
  intros; unfold floatoflong. econstructor; split.
  eapply eval_helper_fp_1; eauto. 2:DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_floatoflongu_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.floatoflongu x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (floatoflongu a) fp /\ FP.subset fp fpx.
Proof.
  intros; unfold floatoflongu. econstructor; split.
  eapply eval_helper_fp_1; eauto. 2:DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_longofsingle_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.longofsingle x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (longofsingle a) fp /\ FP.subset fp fpx.
Proof.
  intros; unfold longofsingle.
  destruct x; simpl in H1; inv H1. destruct (Float32.to_long f) as [n|] eqn:EQ; simpl in H3; inv H3.
  exploit eval_floatofsingle; eauto. intros (v' & A' & B'). inv B'.
  exploit eval_floatofsingle_fp. exact H. eauto. intros (fp & A & B).
  exploit eval_longoffloat_fp; try exact A; eauto. 
  simpl. apply Float32.to_long_double in EQ.
  change (Float.of_single f) with (Float32.to_double f). rewrite EQ; simpl; eauto.
  intros (fp' & A'' & B''). exists fp'. split; auto. apply subset_trans with fp; auto.
Qed.

Theorem eval_longuofsingle_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.longuofsingle x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (longuofsingle a) fp /\ FP.subset fp fpx.
Proof.
  intros; unfold longuofsingle.
  destruct x; simpl in H1; inv H1. destruct (Float32.to_longu f) as [n|] eqn:EQ; simpl in H3; inv H3.
  exploit eval_floatofsingle; eauto. intros (v & A & B). simpl in B. inv B.
  exploit eval_floatofsingle_fp; try exact H; eauto. intros (fp & A' & B').
  apply Float32.to_longu_double in EQ.
  exploit eval_longuoffloat_fp; eauto. simpl.
  change (Float.of_single f) with (Float32.to_double f); rewrite EQ; simpl; eauto.
  intros (fp' & A'' & B''). exists fp'; split; auto. apply subset_trans with fp; auto.
Qed.

Theorem eval_singleoflong_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.singleoflong x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (singleoflong a) fp /\ FP.subset fp fpx.
Proof.
  intros; unfold singleoflong. econstructor; split.
  eapply eval_helper_fp_1; eauto. 2:DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_singleoflongu_fp:
  forall le a x fpx y,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  Val.singleoflongu x = Some y ->
  exists fp, eval_expr_fp ge sp e m le (singleoflongu a) fp /\ FP.subset fp fpx.
Proof.
  intros; unfold singleoflongu. econstructor; split.
  eapply eval_helper_fp_1; eauto. 2:DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_andl_fp: binary_constructor_fp_sound andl.
Proof.
  red; intros. unfold andl.
  exploit (eval_splitlong2_fp le a b (fun h1 l1 h2 l2 => makelong (and h1 h2) (and l1 l2))); eauto.
  clear; unfold makelong; intros. InvEval.
  exploit eval_and_fp. eexact H. eauto. eexact H3. eauto. intros [fp1 [A B]].
  exploit eval_and_fp. eexact H0. eauto. eexact H4. eauto. intros [fp2 [C D]].
  Triv. rewrite <- FP.fp_union_assoc.
  rewrite (FP.fp_union_assoc fpx2), (FP.union_comm_eq fpx2),
  <- (FP.fp_union_assoc fpy1). rewrite (FP.fp_union_assoc fpx1).
  apply subset2_union; TrivFP.
Qed.

Theorem eval_orl_fp: binary_constructor_fp_sound orl.
Proof.
  red; intros. unfold orl.
  eapply eval_splitlong2_fp; eauto.
  clear; unfold makelong; intros. inv H7. InvEval.
  exploit eval_or_fp. eexact H. eauto. eexact H3. eauto. intros [fp1 [A B]].
  exploit eval_or_fp. eexact H0. eauto. eexact H4. eauto. intros [fp2 [C D]].
  Triv. rewrite <- FP.fp_union_assoc.
  rewrite (FP.fp_union_assoc fpx2), (FP.union_comm_eq fpx2),
  <- (FP.fp_union_assoc fpy1). rewrite (FP.fp_union_assoc fpx1).
  apply subset2_union; TrivFP.
Qed.

Theorem eval_xorl_fp: binary_constructor_fp_sound xorl.
Proof.
  red; intros. unfold xorl. eapply eval_splitlong2_fp; eauto.
  clear; unfold makelong; intros. InvEval.
  exploit eval_xor_fp. eexact H. eauto. eexact H3. eauto. intros [fp1 [A B]].
  exploit eval_xor_fp. eexact H0. eauto. eexact H4. eauto. intros [fp2 [C D]].
  Triv.
  rewrite <- FP.fp_union_assoc.
  rewrite (FP.fp_union_assoc fpx2), (FP.union_comm_eq fpx2),
  <- (FP.fp_union_assoc fpy1). rewrite (FP.fp_union_assoc fpx1).
  apply subset2_union; TrivFP.
Qed.

Lemma eval_lowlong_fp: unary_constructor_fp_sound lowlong.
Proof.
  unfold lowlong; red. intros until x. destruct (lowlong_match a); intros.
  InvEvalFP; InvEval; eqexpr; simpl in *; FuncInv; subst. Triv. Triv.
Qed.

Lemma eval_highlong_fp: unary_constructor_fp_sound highlong.
Proof.
  unfold highlong; red. intros until x. destruct (highlong_match a); intros.
  InvEvalFP; InvEval; eqexpr; simpl in *; FuncInv; subst. Triv. Triv.
Qed.

Lemma eval_shllimm_fp:
  forall n, unary_constructor_fp_sound (fun e => shllimm e n).
Proof.
  unfold shllimm; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end.
  - eqexpr. Triv.
  - match goal with | |- context[splitlong ?a ?f] => exploit (eval_splitlong_fp le a f) end; eauto.
    clear; unfold makelong; intros.
    InvEval.
    exploit eval_shlimm_fp. exact H. exact H0. instantiate (1:= n); intros [fp1 [A1 B1]].
    exploit eval_shlimm. exact H. instantiate (1:= n); intros [v1' [A1' B1']].
    exploit eval_shruimm_fp. exact H1. exact H2. instantiate (1:= (Int.sub Int.iwordsize n)); intros [fp2 [A2 B2]].
    exploit eval_shruimm. exact H1. instantiate (1:= (Int.sub Int.iwordsize n)); intros [v2' [A2' B2']].
    exploit eval_or_fp. exact A1'. exact A1. exact A2'. exact A2. intros [fp12 [A12 B12]].
    exploit eval_shlimm_fp. exact H1. exact H2. intros [fp22 [A22 B22]].
    Triv. apply subset2_union; TrivFP. apply subset_trans with (FP.union fp1 fp2); auto.
    apply subset2_union; TrivFP.
  - unfold makelong in *.
    exploit globalenv_generic_senv_eq'; eauto.
    exploit globalenv_generic_senv_eq; eauto.
    generalize (globalenv_generic_find_symbol_eq _ _ prog ge GE_INIT).
    generalize (globalenv_generic_find_funct_ptr_eq _ _ prog ge GE_INIT).
    intros SENV SENV' SYMB FPTR.
    exploit eval_lowlong. eapply eval_expr_preserved; try exact H; eauto.
    intros [v [A B]]. eapply eval_expr_preserved in A; eauto.
    exploit eval_lowlong_fp; try exact H; eauto. intros [fp' [A' B']].
    exploit eval_shlimm; eauto. intros [v' [C D]].
    exploit eval_shlimm_fp; try exact A; eauto. intros [fp'' [C' D']].
    Triv. apply subset_trans with fp'; auto.
  - eexists. split. eapply eval_helper_fp_2; try (repeat econstructor; eauto; fail). 
    DeclHelper. UseHelper. TrivFP.
Qed.

Lemma eval_shrlimm_fp:
  forall n, unary_constructor_fp_sound (fun e => shrlimm e n).
Proof.
  unfold shrlimm; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end.
  - eqexpr. Triv.
  - match goal with | |- context[splitlong ?a ?f] => exploit (eval_splitlong_fp le a f) end; eauto.
    clear; unfold makelong; intros.
    InvEval.
    exploit eval_shlimm_fp. exact H. exact H0. instantiate (1:= (Int.sub Int.iwordsize n)); intros [fp1 [A1 B1]].
    exploit eval_shlimm. exact H. instantiate (1:= (Int.sub Int.iwordsize n)); intros [v1' [A1' B1']].
    exploit eval_shruimm_fp. exact H1. exact H2. instantiate (1:= n); intros [fp2 [A2 B2]].
    exploit eval_shruimm. exact H1. instantiate (1:= n); intros [v2' [A2' B2']].
    exploit eval_or_fp. exact A2'. exact A2. exact A1'. exact A1. intros [fp12 [A12 B12]].
    exploit eval_shrimm_fp. exact H. exact H0. intros [fp22 [A22 B22]].
    Triv. apply subset2_union; TrivFP. apply subset_trans with (FP.union fp2 fp1); auto.
    apply subset2_union; TrivFP.
  - unfold makelong in *.
    exploit globalenv_generic_senv_eq'; eauto.
    exploit globalenv_generic_senv_eq; eauto.
    generalize (globalenv_generic_find_symbol_eq _ _ prog ge GE_INIT).
    generalize (globalenv_generic_find_funct_ptr_eq _ _ prog ge GE_INIT).
    intros SENV SENV' SYMB FPTR.
    exploit eval_highlong. eapply eval_expr_preserved; try exact H; eauto.
    intros [v [A B]]. eapply eval_expr_preserved in A; eauto.
    exploit eval_highlong_fp; try exact H; eauto. intros [fp' [A' B']].
    exploit eval_shrimm. instantiate (3:=(v :: le)). instantiate (2:= Eletvar 0).
    econstructor; simpl; eauto. intros [v' [C D]].
    exploit eval_shrimm_fp. instantiate (3:=(v :: le)). instantiate (2:= Eletvar 0).
    econstructor; simpl; eauto. econstructor; simpl; eauto. intros [fp'' [C' D']].
    Triv. apply subset2_union; auto. apply subset_trans with FP.emp; TrivFP. 
  - eexists. split. eapply (eval_helper_fp_2 le i64_sar "__i64_sar"); try (repeat econstructor; eauto; fail). 
    DeclHelper. UseHelper. TrivFP.
Qed.

Lemma eval_shrluimm_fp:
  forall n,
  unary_constructor_fp_sound (fun e => shrluimm e n).
Proof.
  unfold shrluimm; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end.
  - eqexpr. Triv.
  - match goal with | |- context[splitlong ?a ?f] => exploit (eval_splitlong_fp le a f) end; eauto.
    clear; unfold makelong; intros.
    InvEval.
    exploit eval_shlimm_fp. exact H. exact H0. instantiate (1:= (Int.sub Int.iwordsize n)); intros [fp1 [A1 B1]].
    exploit eval_shlimm. exact H. instantiate (1:= (Int.sub Int.iwordsize n)); intros [v1' [A1' B1']].
    exploit eval_shruimm_fp. exact H1. exact H2. instantiate (1:= n); intros [fp2 [A2 B2]].
    exploit eval_shruimm. exact H1. instantiate (1:= n); intros [v2' [A2' B2']].
    exploit eval_or_fp. exact A2'. exact A2. exact A1'. exact A1. intros [fp12 [A12 B12]].
    exploit eval_shruimm_fp. exact H. exact H0. intros [fp22 [A22 B22]].
    Triv. apply subset2_union; TrivFP. apply subset_trans with (FP.union fp2 fp1); auto.
    apply subset2_union; TrivFP.
  - unfold makelong in *.
    exploit globalenv_generic_senv_eq'; eauto.
    exploit globalenv_generic_senv_eq; eauto.
    generalize (globalenv_generic_find_symbol_eq _ _ prog ge GE_INIT).
    generalize (globalenv_generic_find_funct_ptr_eq _ _ prog ge GE_INIT).
    intros SENV SENV' SYMB FPTR.
    exploit eval_highlong. eapply eval_expr_preserved; try exact H; eauto.
    intros [v [A B]]. eapply eval_expr_preserved in A; eauto.
    exploit eval_highlong_fp; try exact H; eauto. intros [fp' [A' B']].
    exploit eval_shruimm; eauto. intros [v' [C D]].
    exploit eval_shruimm_fp; try exact A; eauto. intros [fp'' [C' D']].
    Triv. apply subset_trans with fp'; auto.
  - eexists. split. eapply (eval_helper_fp_2 le i64_shr "__i64_shr"); try (repeat econstructor; eauto; fail). 
    DeclHelper. UseHelper. TrivFP.
Qed.

Theorem eval_shll_fp: binary_constructor_fp_sound shll.
Proof.
  unfold shll; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end.
  - exploit eval_shllimm_fp. exact H. exact H0. exact H3. intros [fp [A B]]. Triv.
  - econstructor; split. eapply eval_helper_fp_2; eauto. 2: DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_shrlu_fp: binary_constructor_fp_sound shrlu.
Proof.
  unfold shrlu; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end.
  - exploit eval_shrluimm_fp. exact H. exact H0. exact H3. intros [fp [A B]]. Triv.
  - econstructor; split. eapply eval_helper_fp_2; eauto. 2: DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_shrl_fp: binary_constructor_fp_sound shrl.
Proof.
  unfold shrl; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end.
  - exploit eval_shrlimm_fp. exact H. exact H0. exact H3. intros [fp [A B]]. Triv.
  - econstructor; split. eapply eval_helper_fp_2; eauto. 2: DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_addl_fp: Archi.ptr64 = false -> binary_constructor_fp_sound addl.
Proof.
  unfold addl; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end; Triv;
    inv H4; InvEval; eqexpr; eauto.
Qed.

Theorem eval_subl_fp: Archi.ptr64 = false -> binary_constructor_fp_sound subl.
Proof.
  unfold subl; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end;
    try (Triv; inv H4; InvEval; eqexpr; eauto; fail).
  exploit eval_negl_fp. exact H2. exact H3. exact H4. intros [fp' [A B]]. Triv.
Qed.

Lemma eval_mull_base_fp: binary_constructor_fp_sound mull_base.
Proof.
  unfold mull_base; red; intros.
  eapply eval_splitlong2_fp; eauto.
  clear. intros.
  inv H7. inv H11. inv H13. InvEval; eqexpr. 
  exploit eval_mul. eapply eval_lift. exact H. eapply eval_lift. exact H4. instantiate (1:= v1); intros [vm [A B]].
  exploit eval_mul_fp. eapply eval_lift. exact H. eapply eval_lift_fp. exact H1.
  eapply eval_lift. exact H4. eapply eval_lift_fp. exact H6. instantiate (1:= v1); intros [fpm [A' B']].  
  exploit eval_mul. eapply eval_lift. exact H0. eapply eval_lift. exact H3. instantiate (1:= v1); intros [vm' [C D]].
  exploit eval_mul_fp. eapply eval_lift. exact H0. eauto with evalexprfp. eapply eval_lift. exact H3. eauto with evalexprfp.
  instantiate (1:= v1); intros [fpm' [C' D']].
  exploit eval_add. 2: exact C. instantiate (2:= Eop Ohighlong (Eletvar 0 ::: Enil)).
  repeat econstructor. intros [va [E F]].
  exploit eval_add_fp. 3: exact C. 3: exact C'. instantiate (2:= Eop Ohighlong (Eletvar 0 ::: Enil)).
  repeat econstructor. repeat econstructor. TrivFP. intros [fpa [E' F']].
  exploit eval_add. exact E. exact A. intros [va' [G I]].
  exploit eval_add_fp. exact E. exact E'. exact A. exact A'. intros [fpa' [G' I']].
  Triv. repeat apply subset2_union; TrivFP.
  apply FP.subset_union_subset. TrivFP.
  rewrite (FP.union_comm_eq). apply FP.subset_union_subset. TrivFP.
  
  apply subset_trans with (FP.union fpa fpm); auto.
  apply subset2_union.
  apply subset_trans with fpm'; auto.
  repeat rewrite <- FP.fp_union_assoc. rewrite FP.union_comm_eq. apply FP.subset_union_subset.
  repeat rewrite FP.fp_union_assoc. apply FP.subset_union_subset. auto.
  
  repeat rewrite FP.fp_union_assoc. rewrite FP.union_comm_eq.
  rewrite FP.fp_union_assoc. apply FP.subset_union_subset.
  rewrite FP.fp_union_assoc. apply FP.subset_union_subset.
  rewrite FP.union_comm_eq. auto.
Qed.

Lemma eval_mullimm_fp: forall n, unary_constructor_fp_sound (mullimm n).
Proof.
  unfold mullimm; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end;
    try (Triv; inv H4; InvEval; eqexpr; eauto; fail).
  exploit eval_shllimm_fp. exact H. exact H0. exact H1. intros [fp' [A B]]. Triv.
  exploit eval_mull_base_fp. exact H. exact H0. instantiate (2:= longconst n).
  repeat econstructor. repeat econstructor. exact H1. TrivFP.
Qed.

Theorem eval_mull_fp: binary_constructor_fp_sound mull.
Proof.
  unfold mull; red; intros.
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end.
  Triv. 
  exploit eval_mullimm_fp. exact H1. exact H2. exact H3. intros [fp' [A B]]. Triv.
  exploit eval_mullimm_fp. exact H. exact H0. exact H3. intros [fp' [A B]]. Triv.
  exploit eval_mull_base_fp. exact H. exact H0. exact H1. exact H2. exact H3. intros [fp' [A B]]. Triv.
Qed.

Theorem eval_mullhu_fp: forall n, unary_constructor_fp_sound (fun a => mullhu a n).
Proof.
  unfold mullhu; intros; red; intros. eexists. split.
  eapply eval_helper_fp_2; eauto. 4:DeclHelper; eauto. constructor.
  repeat econstructor. repeat econstructor. UseHelper. TrivFP.
Qed.

Theorem eval_mullhs_fp: forall n, unary_constructor_fp_sound (fun a => mullhs a n).
Proof.
  unfold mullhs; intros; red; intros. econstructor; split.
  eapply eval_helper_fp_2; eauto. 4:DeclHelper; eauto. constructor.
  repeat econstructor. repeat econstructor. UseHelper. TrivFP.
Qed.

Theorem eval_shrxlimm_fp:
  forall le a n x fpx z,
  Archi.ptr64 = false ->
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->  
  Val.shrxl x (Vint n) = Some z ->
  exists fp, eval_expr_fp ge sp e m le (shrxlimm a n) fp /\ FP.subset fp fpx.
Proof.
  intros. unfold shrxlimm.
  apply Val.shrxl_shrl_2 in H2. 
  repeat match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:? end. Triv.
  assert (SplitLongproof.helper_functions_declared (mkprogram (cu_defs prog) (cu_public prog) 1%positive) hf) by auto.
  edestruct (eval_shrlimm (mkprogram (cu_defs prog) (cu_public prog) 1%positive)
                          hf H3 sp e m (Int.repr 63) (x :: le) (Eletvar 0)) as (v1 & A1 & B1).
  constructor; reflexivity. 
  edestruct (eval_shrlimm_fp (Int.repr 63) (x :: le) (Eletvar 0)) as (fp1 & A1' & B1').
  constructor; reflexivity. econstructor; reflexivity. simpl.
  eapply eval_expr_preserved; try eassumption; eauto with gegen.
  edestruct (eval_shrluimm _ hf H3 sp e m (Int.sub (Int.repr 64) n) (x :: le)) as (v2 & A2 & B2). exact A1.
  edestruct (eval_shrluimm_fp (Int.sub (Int.repr 64) n) (x :: le)) as (fp2 & A2' & B2').
  eapply eval_expr_preserved; try exact A1; eauto with gegen. exact A1'.
  simpl. eapply eval_expr_preserved; try exact A2; eauto with gegen.
  edestruct (eval_addl (mkprogram (cu_defs prog) (cu_public prog) 1%positive) sp e m H (x :: le) (Eletvar 0)) as (v3 & A3 & B3).
  constructor. reflexivity. eexact A2.
  edestruct (eval_addl_fp H (x :: le) (Eletvar 0)) as (fp3 & A3' & B3').
  constructor. reflexivity. econstructor. reflexivity.
  eapply eval_expr_preserved; try eexact A2; eauto with gegen. exact A2'.
  eapply eval_expr_preserved; try eexact A3; eauto with gegen. 
  edestruct (eval_shrlimm _ hf H3 sp e m n (x :: le)) as (v4 & A4 & B4). eexact A3.
  edestruct (eval_shrlimm_fp n (x :: le)) as (fp4 & A4' & B4').
  eapply eval_expr_preserved; try eexact A3; eauto with gegen. exact A3'.
  simpl.  eapply eval_expr_preserved; try eexact A4; eauto with gegen.
  eapply eval_expr_preserved in A1; eauto with gegen. eapply eval_expr_preserved in A2; eauto with gegen.
  eapply eval_expr_preserved in A3; eauto with gegen. eapply eval_expr_preserved in A4; eauto with gegen.
  Triv. apply subset2_union; TrivFP. apply subset_trans with fp3; auto.
  apply subset_trans with (FP.union FP.emp fp2); auto.
  TrivFP. apply subset_trans with fp1; TrivFP. rewrite <- (FP.emp_union_fp fpx).
  apply FP.subset_union_subset; auto.
Qed.

Theorem eval_divlu_base_fp:
  forall le a b x y fpx fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divlu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divlu_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof. intros; unfold divlu_base. econstructor; split. eapply eval_helper_fp_2; eauto.
       2:DeclHelper. constructor. UseHelper. TrivFP. Qed.

Theorem eval_modlu_base_fp:
  forall le a b x y fpx fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->  
  Val.modlu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (modlu_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof. intros; unfold modlu_base. econstructor; split.
       eapply eval_helper_fp_2; eauto. 2: DeclHelper. constructor. UseHelper. TrivFP. Qed.

Theorem eval_divls_base_fp:
  forall le a b x y fpx fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divls x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divls_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  intros; unfold divls_base. econstructor; split. eapply eval_helper_fp_2; eauto.
  2:DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Theorem eval_modls_base_fp:
  forall le a b x y fpx fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.modls x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (modls_base a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  intros; unfold modls_base. econstructor; split. eapply eval_helper_fp_2; eauto.
  2:DeclHelper. constructor. UseHelper. TrivFP.
Qed.

Lemma eval_cmpl_eq_zero_fp:
  forall le a x fpx,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr_fp ge sp e m le a fpx ->    
  exists fp, eval_expr_fp ge sp e m le (cmpl_eq_zero a) fp /\ FP.subset fp fpx.
Proof.
  intros. unfold cmpl_eq_zero.
  exploit eval_cmpl_eq_zero. exacteval H. intro C. evalge C.
  unfold cmpl_eq_zero in *.
  exploit eval_splitlong_fp. 4: exact C. 2,3: eauto.
  clear. simpl. intros. 
  exploit eval_or. exact H. exact H1. intros [v [A B]]. 
  exploit eval_or_fp. exact H. eauto. exact H1. eauto. intros [fp1 [A' B']]. 
  exploit eval_comp_opt_fp. exact A. eauto. 
  instantiate (2:= (Eop (Ointconst Int.zero) Enil)). trivcons. trivcons. eauto.
  simpl. TrivFP. intros [fp' [C D]].
  Triv. apply subset_trans with fp1; auto.
  intros [fp' [E F]]. Triv.
Qed.

Lemma eval_cmpl_ne_zero_fp:
  forall le a x fpx,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr_fp ge sp e m le a fpx ->
  exists fp, eval_expr_fp ge sp e m le (cmpl_ne_zero a) fp /\ FP.subset fp fpx.
Proof.
  intros. unfold cmpl_eq_zero.
  exploit eval_cmpl_ne_zero. exacteval H. intro C. evalge C.
  unfold cmpl_ne_zero in *.
  exploit eval_splitlong_fp. 4: exact C. 2,3: eauto.
  clear. simpl. intros. 
  exploit eval_or. exact H. exact H1. intros [v [A B]]. 
  exploit eval_or_fp. exact H. eauto. exact H1. eauto. intros [fp1 [A' B']]. 
  exploit eval_comp_opt_fp. exact A. eauto. 
  instantiate (2:= (Eop (Ointconst Int.zero) Enil)). trivcons. trivcons. eauto.
  simpl. TrivFP. intros [fp' [C D]].
  Triv. apply subset_trans with fp1; auto.
  intros [fp' [E F]]. Triv.
Qed.

Lemma eval_cmpl_gen_fp:
  forall ch cl a b le x fpx y fpy,
    eval_expr ge sp e m le a (Vlong x) ->
    eval_expr_fp ge sp e m le a fpx ->    
    eval_expr ge sp e m le b (Vlong y) ->
    eval_expr_fp ge sp e m le b fpy ->
    exists fp, eval_expr_fp ge sp e m le (cmpl_gen ch cl a b) fp /\
          FP.subset fp (FP.union fpx fpy).
Proof.
  intros. unfold cmpl_gen.
  exploit eval_cmpl_gen. exacteval H. exacteval H1. instantiate (1:= ch). instantiate (1:= cl). intro A. evalge A.
  unfold cmpl_gen in *. unfold splitlong2 in *.
  case (splitlong2_match a b) eqn:SL; clear SL; inv A; InvEvalFP; InvEval; eqexpr; simpl in *; FuncInv; subst.
  ++ destruct v11, v12; inv H; destruct v13, v14; inv H0.
     inv H8; InvEval; eqexpr; simpl in *; FuncInv; subst.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|]).
     TrivFP. swapeq fp0 fp5. TrivFP.
     TrivFP. apply subset2_union; swapeq fp0 fp5; TrivFP.
  ++ destruct v6, v7; inv H. inv H8. inv H9. InvEval; simpl in *; eqexpr.
     pose proof (eval_lift ge sp e m le h1 _ (Vlong y) H4). eqexpr. inv H5. inv H3. simpl in H8. inv H8.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|TrivFP]).
     rewrite (FP.union_comm_eq fpy). apply FP.union2_subset. apply subset2_union; TrivFP.
  ++ destruct v6, v7; inv H1. inv H8. inv H9. InvEval; simpl in *; eqexpr.
     pose proof (eval_lift ge sp e m le h2 _ (Vlong x) H4). eqexpr. inv H6. inv H3. simpl in H8. inv H8.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|TrivFP]).
     repeat apply subset2_union; TrivFP; rewrite FP.union_comm_eq, <- FP.fp_union_assoc; TrivFP. 
  ++ inv H8. pose proof (eval_lift _ _ _ _ _ _ _ (Vlong x) H1). eqexpr. inv H9. inv H10.
     InvEval; eqexpr. inv H8. inv H7. inv H5. inv H8. simpl in H9. inv H9.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|TrivFP]).
Qed.

Theorem eval_cmpl_fp:
  forall c le a x fpx b y fpy v,
    eval_expr ge sp e m le a x ->
    eval_expr_fp ge sp e m le a fpx ->
    eval_expr ge sp e m le b y ->
    eval_expr_fp ge sp e m le b fpy ->
    Val.cmpl c x y = Some v ->
    exists fp, eval_expr_fp ge sp e m le (cmpl c a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold cmpl. intros. unfold Val.cmpl in H3.
  destruct x; simpl in H3; try discriminate. destruct y; inv H3.
  rename i into x. rename i0 into y.
  destruct c; simpl. 
  - (* Ceq *)
    exploit eval_xorl. exacteval H. exacteval H1. intros [v1 [A B]]. simpl in B; inv B. evalge A.
    exploit eval_xorl_fp. eexact H. eexact H0. eexact H1. eexact H2. exact A. intros [fp1 [A' B']].
    exploit eval_cmpl_eq_zero_fp; eauto. intros [fp' [C D]]. Triv. apply subset_trans with fp1; TrivFP.
  - (* Cne *)
    exploit eval_xorl. exacteval H. exacteval H0. intros [v1 [A B]]. simpl in B; inv B. evalge A.
    exploit eval_xorl_fp. exact H. eauto. exact H1. eauto. exact A. intros [fp1 [A' B']].
    exploit eval_cmpl_ne_zero_fp; eauto. intros [fp' [C D]]. Triv. apply subset_trans with fp1; TrivFP.
  - (* Clt *)
    destruct (is_longconst_zero b) eqn:LC.
    + exploit eval_highlong. exacteval H. intros [v1 [A1 B1]]. simpl in B1. inv B1. evalge A1.
      exploit eval_highlong_fp. exact H. eauto. eauto. intros [fp1 [A1' B1']]. 
      exploit eval_comp_opt. eexact A1.
      instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp. simpl; auto. simpl. eauto.
      instantiate (1 := Clt). intros [v2 [A2 B2]].
      exploit eval_comp_opt_fp. 5: exact A2. eauto. eauto. trivcons. trivcons.
      simpl. TrivFP. intros [fp' [C D]].
      Triv. apply subset_trans with fp1; auto. TrivFP.
    + eapply eval_cmpl_gen_fp; eauto.
  - (* Cle *)
    eapply eval_cmpl_gen_fp; eauto.
  - (* Cgt *)
    eapply (eval_cmpl_gen_fp Cgt Cgt); eauto.
  - (* Cge *)
    destruct (is_longconst_zero b) eqn:LC.
    + exploit eval_highlong. exacteval H. intros [v1 [A1 B1]]. simpl in B1; inv B1. evalge A1.
      exploit eval_highlong_fp. exact H. eauto. eauto. intros [fp1 [A1' B1']]. 
      exploit eval_comp_opt. eexact A1.
      instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp. simpl; auto. simpl. eauto.
      instantiate (1 := Cge). intros [v2 [A2 B2]].
      exploit eval_comp_opt_fp. 5: exact A2. eauto. eauto. trivcons. trivcons.
      simpl. TrivFP. intros [fp' [C D]].
      Triv. apply subset_trans with fp1; TrivFP.
    + eapply (eval_cmpl_gen_fp Cgt Cge);eauto.
Qed.

Lemma eval_cmplu_gen_fp:
  forall ch cl a b le x fpx y fpy,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr_fp ge sp e m le a fpx ->    
  eval_expr ge sp e m le b (Vlong y) ->
  eval_expr_fp ge sp e m le b fpy ->  
  exists fp, eval_expr_fp ge sp e m le (cmplu_gen ch cl a b) fp /\
        FP.subset fp (FP.union fpx fpy).
Proof.
  intros. unfold cmplu_gen.
  exploit eval_cmplu_gen. exacteval H. exacteval H1. instantiate (1:= ch). instantiate (1:= cl). intro A. evalge A.
  unfold cmplu_gen in *. unfold splitlong2 in *.
  case (splitlong2_match a b) eqn:SL; clear SL; inv A; InvEvalFP; InvEval; eqexpr; simpl in *; FuncInv; subst.
  ++ destruct v11, v12; inv H; destruct v13, v14; inv H0.
     inv H8; InvEval; eqexpr; simpl in *; FuncInv; subst.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|]).
     TrivFP. swapeq fp0 fp5. TrivFP.
     TrivFP. apply subset2_union; swapeq fp0 fp5; TrivFP.
  ++ destruct v6, v7; inv H. inv H8. inv H9. InvEval; simpl in *; eqexpr.
     pose proof (eval_lift ge sp e m le h1 _ (Vlong y) H4). eqexpr. inv H5. inv H3. simpl in H8. inv H8.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|TrivFP]).
     rewrite (FP.union_comm_eq fpy). apply FP.union2_subset. apply subset2_union; TrivFP.
  ++ destruct v6, v7; inv H1. inv H8. inv H9. InvEval; simpl in *; eqexpr.
     pose proof (eval_lift ge sp e m le h2 _ (Vlong x) H4). eqexpr. inv H6. inv H3. simpl in H8. inv H8.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|TrivFP]).
     repeat apply subset2_union; TrivFP; rewrite FP.union_comm_eq, <- FP.fp_union_assoc; TrivFP. 
  ++ inv H8. pose proof (eval_lift _ _ _ _ _ _ _ (Vlong x) H1). eqexpr. inv H9. inv H10.
     InvEval; eqexpr. inv H8. inv H7. inv H5. inv H8. simpl in H9. inv H9.
     destruct Int.eq eqn:IEQ; eexists; (split; [trivcons; try rewrite IEQ; simpl; eauto; trivcons|TrivFP]).
Qed.

Theorem eval_cmplu_fp:
  forall c le a x fpx b y fpy v,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->  
  Val.cmplu (Mem.valid_pointer m) c x y = Some v ->
  Archi.ptr64 = false ->
  exists fp, eval_expr_fp ge sp e m le (cmplu c a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  intros. unfold Val.cmplu, Val.cmplu_bool in H3. rewrite H4 in H3. simpl in H3.
  destruct x; simpl in H3; try discriminate H3; destruct y; inv H3.
  rename i into x. rename i0 into y. destruct c; simpl.
 - (* Ceq *)
   exploit eval_xorl. exacteval H. exacteval H1. intros [v1 [A B]]. simpl in B; inv B. evalge A.
   exploit eval_xorl_fp. eexact H. eexact H0. eexact H1. eexact H2. exact A. intros [fp1 [A' B']].
   exploit eval_cmpl_eq_zero_fp; eauto. intros [fp' [C D]]. Triv. apply subset_trans with fp1; TrivFP.
 - (* Cne *)
   exploit eval_xorl. exacteval H. exacteval H0. intros [v1 [A B]]. simpl in B; inv B. evalge A.
   exploit eval_xorl_fp. exact H. eauto. exact H1. eauto. exact A. intros [fp1 [A' B']].
   exploit eval_cmpl_ne_zero_fp; eauto. intros [fp' [C D]]. Triv. apply subset_trans with fp1; TrivFP.
 - (* Clt *)
   eapply eval_cmplu_gen_fp; eauto.
 - (* Cle *)
   eapply eval_cmplu_gen_fp; eauto.
 - (* Cgt *)
   eapply (eval_cmplu_gen_fp Cgt Cgt); eauto.
 - (* Cge *)
   eapply eval_cmplu_gen_fp; eauto.
Qed.

End CMCONSTR.

