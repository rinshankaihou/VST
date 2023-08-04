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

Require Import Zquot Coqlib.
Require Import AST Integers Floats Values Memory Globalenvs Events.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong SplitLongproof SelectLong SelectLongproof SelectDiv.


Require Import Blockset Footprint Op_fp CUAST helpers Cminor_local CminorSel_local
        selectop_proof splitlong_proof selectlong_proof SelectDivproof. 
Local Open Scope cminorsel_scope.

(** * Correctness of the smart constructors for division and modulus *)

Section CMCONSTRS.

Variable cu: cminorsel_comp_unit.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared cu hf.
Variable ge: genv.
Hypothesis GEINIT: globalenv_generic cu ge.
Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma subset_emp_emp:
  forall fp, FP.subset fp FP.emp -> fp = FP.emp.
Proof.
  clear.
  intros; destruct fp; unfold FP.emp; inv H; simpl in *; f_equal;
    do 2 (apply Axioms.functional_extensionality; intros); 
    match goal with
      [H: context[?x] |- ?x _ _ = Locs.emp _ _ ] =>
      destruct x eqn:A; auto ; apply H in A; discriminate
    end.
Qed.

Lemma eval_divu_mul_fp:
  forall le x y p M,
  divu_mul_params (Int.unsigned y) = Some(p, M) ->
  nth_error le O = Some (Vint x) ->
  eval_expr_fp ge sp e m le (divu_mul p M) FP.emp.
Proof.
  intros. unfold divu_mul.
  assert (exists v, eval_expr ge sp e m le (Eop Omulhu (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil)) v).
  repeat econstructor; eauto. destruct H1.
  assert (eval_expr_fp ge sp e m le (Eop Omulhu (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil)) FP.emp).
  repeat econstructor; eauto. 
  exploit eval_shruimm_fp. eexact H1. eauto. intros [fp' [A B]].
  apply subset_emp_emp in B. subst. eauto.
Qed.

Theorem eval_divuimm_fp:
  forall le e1 x fpx n2 z,
    eval_expr ge sp e m le e1 x ->
    eval_expr_fp ge sp e m le e1 fpx ->
    Val.divu x (Vint n2) = Some z ->
    exists fp, eval_expr_fp ge sp e m le (divuimm e1 n2) fp /\ FP.subset fp fpx.
Proof.
  unfold divuimm; intros. generalize H1; intros DIV.
  destruct x; simpl in DIV; try discriminate.
  destruct (Int.eq n2 Int.zero) eqn:Z2; inv DIV.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
- eapply eval_shruimm_fp; eauto.
- destruct (Compopts.optim_for_size tt). Triv. simpl. rewrite Z2. auto.
  destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
  exploit eval_divu_mul; eauto. instantiate (2:= (Vint i) :: le). simpl. eauto. intro. evalge H2. 2: eauto with gegen.
  exploit eval_divu_mul_fp; eauto. instantiate (2:= (Vint i) :: le). simpl. eauto. intro. Triv.
  exploit eval_divu_base_fp. exact H. exact H0. instantiate (2:= Eop (Ointconst n2) Enil).
  repeat econstructor; eauto.   repeat econstructor; eauto. eauto. TrivFP. 
Qed.

Theorem eval_divu_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divu a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold divu; intros until b. destruct (divu_match b); intros.
  - InvEvalFP; InvEval; InvEmpFP; eapply eval_divuimm_fp; eauto; TrivFP; auto.
  - eapply eval_divu_base_fp; eauto.
Qed.

Lemma eval_mod_from_div_fp:
  forall le a n x y fpy,
    eval_expr ge sp e m le a (Vint y) ->
    eval_expr_fp ge sp e m le a fpy ->
    nth_error le O = Some (Vint x) ->
    exists fp, eval_expr_fp ge sp e m le (mod_from_div a n) fp /\ FP.subset fp fpy.
Proof.
  unfold mod_from_div; intros.
  exploit eval_mulimm; eauto. instantiate (1 := n). intros [v [A B]].
  exploit eval_mulimm_fp; try exact H; eauto. instantiate (1 := n). intros [fp' [A' B']]. Triv.
Qed.

Theorem eval_moduimm_fp:
  forall le e1 x fpx n2 z,
    eval_expr ge sp e m le e1 x ->
    eval_expr_fp ge sp e m le e1 fpx ->    
    Val.modu x (Vint n2) = Some z ->
    exists fp, eval_expr_fp ge sp e m le (moduimm e1 n2) fp /\ FP.subset fp fpx.
Proof.
  unfold moduimm; intros. generalize H1; intros MOD.
  destruct x; simpl in MOD; try discriminate.
  destruct (Int.eq n2 Int.zero) eqn:Z2; inv MOD.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2. 
  -  eapply eval_andimm_fp; eauto.
  - destruct (Compopts.optim_for_size tt).
    exploit eval_modu_base_fp. exact H. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
    EvalOp. simpl. eauto. repeat econstructor; eauto. rewrite H1. eauto. TrivFP.
    destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
    exploit eval_divu_mul. eauto. instantiate (2:= Vint i :: le). simpl. eauto. intro. evalge H2; try eauto with gegen.
    exploit eval_divu_mul_fp. eauto. instantiate (2:= Vint i :: le). simpl. eauto. intro.
    exploit eval_mod_from_div; try exacteval H2; simpl; eauto. intros A. evalge A; try eauto with gegen.
    exploit eval_mod_from_div_fp; try exact H2; simpl; eauto. intros [t [A' B]]; apply subset_emp_emp in B; subst.
    eexists; split. econstructor; eauto. TrivFP.
    exploit eval_modu_base_fp. exact H. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
    repeat econstructor; eauto. repeat econstructor; eauto. eauto. TrivFP.
Qed.

Theorem eval_modu_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.modu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (modu a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold modu; intros until b. destruct (modu_match b); intros. 
  InvEvalFP; InvEval; eqexpr.
  exploit eval_moduimm; try exacteval H; eauto. intros [v [A B]]. evalge A; eauto with gegen.
  exploit eval_moduimm_fp. exact H. eauto. eauto. intros [fp [A' B']]. Triv.
  eapply eval_modu_base_fp; eauto.
Qed.

Lemma eval_divs_mul_fp:
  forall le x y p M,
  divs_mul_params (Int.signed y) = Some(p, M) ->
  nth_error le O = Some (Vint x) ->
  eval_expr_fp ge sp e m le (divs_mul p M) FP.emp.
Proof.
  intros. unfold divs_mul.
  destruct (zlt M Int.half_modulus);
    unfold add, shrimm, shruimm; simpl.
  destruct Int.eq;[|destruct negb]; (destruct Int.eq;[|destruct negb]); simpl; repeat econstructor; eauto.
  destruct Int.eq;[|destruct negb]; (destruct Int.eq;[|destruct negb]); simpl; repeat econstructor; eauto.
Qed.

Theorem eval_divsimm_fp:
  forall le e1 x fpx n2 z,
  eval_expr ge sp e m le e1 x ->
  eval_expr_fp ge sp e m le e1 fpx ->
  Val.divs x (Vint n2) = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divsimm e1 n2) fp /\ FP.subset fp fpx.
Proof.
  unfold divsimm; intros. generalize H1; intros DIV.
  destruct x; simpl in DIV; try discriminate.
  destruct (Int.eq n2 Int.zero
            || Int.eq i (Int.repr Int.min_signed) && Int.eq n2 Int.mone) eqn:Z2; inv DIV.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
  destruct (Int.ltu l (Int.repr 31)) eqn:LT31. 
  eapply eval_shrximm_fp; eauto. eapply Val.divs_pow2; eauto.
  exploit eval_divs_base_fp. exact H. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
  repeat econstructor; eauto. repeat econstructor; eauto. eauto. TrivFP.
  destruct (Compopts.optim_for_size tt).
  exploit eval_divs_base_fp. exact H. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
  repeat econstructor; eauto. repeat econstructor; eauto. eauto. TrivFP.
  destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
  exploit eval_divs_mul. eauto. instantiate (2:= Vint i :: le). simpl. eauto.
  intro A. evalge A; eauto with gegen. 
  exploit eval_divs_mul_fp. eauto. instantiate (2:= Vint i :: le). simpl. eauto. intro A'. Triv.
  exploit eval_divs_base_fp. eauto. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
  repeat econstructor; eauto. repeat econstructor; eauto. eauto. TrivFP.
Qed.

Theorem eval_divs_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divs x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divs a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold divs; intros until b. destruct (divs_match b); intros. 
  InvEvalFP; InvEval; InvEmpFP; eqexpr; TrivFP; eapply eval_divsimm_fp; eauto.
  eapply eval_divs_base_fp; eauto.
Qed.

Theorem eval_modsimm_fp:
  forall le e1 x fpx n2 z,
  eval_expr ge sp e m le e1 x ->
  eval_expr_fp ge sp e m le e1 fpx ->
  Val.mods x (Vint n2) = Some z ->
  exists fp, eval_expr_fp ge sp e m le (modsimm e1 n2) fp /\ FP.subset fp fpx.
Proof.
  unfold modsimm; intros.
  exploit Val.mods_divs; eauto. intros [y [A B]].
  generalize A; intros DIV.
  destruct x; simpl in DIV; try discriminate.
  destruct (Int.eq n2 Int.zero
            || Int.eq i (Int.repr Int.min_signed) && Int.eq n2 Int.mone) eqn:Z2; inv DIV.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
  destruct (Int.ltu l (Int.repr 31)) eqn:LT31.
  exploit (eval_shrximm ge sp e m (Vint i :: le) (Eletvar O)).
  constructor. simpl; eauto. eapply Val.divs_pow2; eauto.
  intros [v1 [X LD]]. inv LD.
  exploit (eval_shrximm_fp ge sp e m (Vint i :: le) (Eletvar 0)); eauto .
  econstructor; simpl; eauto. econstructor. simpl. eauto. eapply Val.divs_pow2; eauto.
  intros [fp1 [X' LD']]. apply subset_emp_emp in LD'; subst.
  exploit eval_mod_from_div. exacteval X. simpl; eauto. intros Y. evalge Y; eauto with gegen.
  exploit eval_mod_from_div_fp. eexact X. eauto. simpl; eauto. intros [fp' [Y' Z]]. apply subset_emp_emp in Z; subst.
  eexists. split. econstructor; eauto. TrivFP.
  exploit eval_mods_base_fp. exact H. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
  repeat econstructor; eauto. repeat econstructor; eauto. eauto. TrivFP.
  destruct (Compopts.optim_for_size tt).
  exploit eval_mods_base_fp. exact H. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
  repeat econstructor; eauto. repeat econstructor; eauto. eauto. TrivFP.
  destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
  exploit eval_divs_mul; eauto. instantiate (2:= Vint i:: le). simpl. eauto. intro B. evalge B; eauto with gegen.
  exploit eval_divs_mul_fp; eauto. instantiate (2:= Vint i:: le). simpl. eauto. intro B'. 
  exploit eval_mod_from_div. exacteval B. simpl; eauto. intros Y. evalge Y; eauto with gegen.
  exploit eval_mod_from_div_fp. eexact B. eauto. simpl; eauto. intros [fp' [Y' Z]]. apply subset_emp_emp in Z; subst.
  eexists. split. econstructor; eauto. TrivFP.
  exploit eval_mods_base_fp. exact H. eauto. instantiate (2:= Eop (Ointconst n2) Enil).
  repeat econstructor; eauto. repeat econstructor; eauto. eauto. TrivFP.
Qed.

Theorem eval_mods_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->    
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.mods x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (mods a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold mods; intros until b. destruct (mods_match b); intros.
  InvEvalFP; InvEmpFP; InvEval; eqexpr.
  exploit eval_modsimm. exacteval H. eauto. intros [v [A B]].
  exploit eval_modsimm_fp. exact H. eauto. eauto. intros [fp1 [A' B']]. Triv.
  eapply eval_mods_base_fp; eauto.
Qed.

Lemma eval_modl_from_divl_fp:
  forall le a n x y fpy,
  eval_expr ge sp e m le a (Vlong y) ->
  eval_expr_fp ge sp e m le a fpy ->
  nth_error le O = Some (Vlong x) ->
  exists fp, eval_expr_fp ge sp e m le (modl_from_divl a n) fp /\ FP.subset fp fpy.
Proof.
  unfold modl_from_divl; intros.
  exploit eval_mullimm. 2: exacteval H. eauto. instantiate (1 := n). intros (v1 & A1 & B1). evalge A1; eauto with gegen.
  exploit eval_mullimm_fp; try exact H; eauto. intros [fp1 [A1' B1']]. 
  assert (A0: eval_expr ge sp e m le (Eletvar O) (Vlong x)) by (constructor; auto).
  exploit eval_subl; auto. exacteval A0. exacteval A1. intros (v2 & A2 & B2). evalge A2; eauto with gegen.
  exploit eval_subl_fp. exact A0. econstructor; eauto. exact A1. eauto. eauto. TrivFP. intros [fp [Y Z]].
  eexists; split; eauto. apply subset_trans with fp1; auto.
Qed.

Lemma eval_divlu_mull_fp:
  forall le x y p M,
  divlu_mul_params (Int64.unsigned y) = Some(p, M) ->
  nth_error le O = Some (Vlong x) ->
  eval_expr_fp ge sp e m le (divlu_mull p M) FP.emp.
Proof.
  intros. unfold divlu_mull. exploit (divlu_mul_shift x); eauto. intros [A B].
  assert (A0: eval_expr ge sp e m le (Eletvar O) (Vlong x)) by (constructor; auto).
  exploit eval_mullhu. 2: exacteval A0. eauto. instantiate (1 := Int64.repr M). intros (v1 & A1 & B1).
  evalge A1; eauto with gegen.
  exploit eval_mullhu_fp; try exact A0; eauto. econstructor; eauto. intros [fp1 [A1' B1']].
  apply subset_emp_emp in B1'; subst.
  exploit eval_shrluimm. 2:exacteval A1. eauto. instantiate (1 := Int.repr p). intros (v2 & A2 & B2).
  evalge A2; eauto with gegen.
  exploit eval_shrluimm_fp; try exact A1; eauto. intros (fp2 & A2' & B2').
  apply subset_emp_emp in B2'; subst. auto.
Qed.

Theorem eval_divlu_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->    
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divlu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divlu a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold divlu; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
  - assert (y = Vlong n2) by (eapply is_longconst_sound; try exacteval H1; eauto). subst y.
    destruct (is_longconst a) as [n1|] eqn:N1.
    assert (x = Vlong n1) by (eapply is_longconst_sound; try exacteval H; eauto). subst x.
    simpl in H3. destruct (Int64.eq n2 Int64.zero); inv H3.
    econstructor; split. apply eval_longconst_fp. TrivFP. 
    destruct (Int64.is_power2' n2) as [l|] eqn:POW.
    * exploit Val.divlu_pow2; eauto. intros EQ; subst z.
      exploit eval_shrluimm. 2: exacteval H. eauto. intros [vx [A B]]. evalge A.
      exploit eval_shrluimm_fp; try exact H; eauto. intros [fp [A' B']]. Triv.
    * destruct (Compopts.optim_for_size tt).
      exploit eval_divlu_base. 2: exacteval H. 2: exacteval H1. 1,2: eauto. intros [v' [C D]].
      evalge C. eapply eval_divlu_base_fp; eauto.
      destruct (divlu_mul_params (Int64.unsigned n2)) as [[p M]|] eqn:PARAMS. 
      destruct x; simpl in H3; try discriminate.
      destruct (Int64.eq n2 Int64.zero); inv H3.
      exploit eval_divlu_mull; eauto. 2:instantiate (2:=Vlong i :: le); simpl; eauto.
      instantiate (1:=mkprogram (cu_defs cu) (cu_public cu) 1%positive). simpl; eauto.
      exploit eval_divlu_mull_fp; eauto. instantiate (2:=Vlong i :: le); simpl; eauto. 
      intros. evalge H4. econstructor; split; eauto. econstructor; eauto. TrivFP.
      exploit eval_divlu_base. 2:exacteval H. 2:exacteval H1. eauto. eauto. intros [v [A B]].
      evalge A. eapply eval_divlu_base_fp; eauto.     
  - exploit eval_divlu_base. 2:exacteval H. 2:exacteval H1. eauto. eauto. intros [v [A B]].
    evalge A. eapply eval_divlu_base_fp; eauto.     
Qed.

Theorem eval_modlu_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.modlu x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (modlu a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold modlu; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
  - assert (y = Vlong n2) by (eapply is_longconst_sound; try exacteval H; eauto). subst y.
    destruct (is_longconst a) as [n1|] eqn:N1.
    + Triv.
    + destruct (Int64.is_power2 n2) as [l|] eqn:POW.
      exploit eval_andl; eauto. exacteval H.
      instantiate (2:= longconst (Int64.sub n2 Int64.one)). repeat econstructor. intros [v [A B]].
      exploit eval_andl_fp. exact H. eauto. instantiate (2:= longconst (Int64.sub n2 Int64.one)).
      repeat econstructor. repeat econstructor. evalge A. TrivFP. intros [fp [A' B']]. Triv.
      destruct (Compopts.optim_for_size tt).
      exploit eval_modlu_base. 2: exacteval H. eauto. exacteval H1. eauto. intros [v [A B]]. evalge A.
      eapply eval_modlu_base_fp; eauto.
      destruct (divlu_mul_params (Int64.unsigned n2)) as [[p M]|] eqn:PARAMS. 
      ** destruct x; simpl in H1; try discriminate.
         exploit eval_divlu_mull; eauto. 2: instantiate (2:= Vlong i :: le); simpl; eauto.
         instantiate (1:=mkprogram (cu_defs cu) (cu_public cu) 1%positive). simpl; eauto.
         exploit eval_divlu_mull_fp; eauto. instantiate (2:=Vlong i :: le); simpl; eauto. intros. evalge H5.
         exploit eval_modl_from_divl; try exacteval H5; simpl; eauto. intros; evalge H6.
         exploit eval_modl_from_divl_fp; try exact H5; simpl; eauto. intros [fp [A B]]. apply subset_emp_emp in B. subst.
         econstructor; split; eauto. econstructor; eauto. TrivFP.
      ** exploit eval_modlu_base. 2:exacteval H. 2:exacteval H1. eauto. eauto. intros [v [A B]].
         evalge A. eapply eval_modlu_base_fp; eauto.     
  - exploit eval_modlu_base. 2:exacteval H. 2:exacteval H1. eauto. eauto. intros [v [A B]].
    evalge A. eapply eval_modlu_base_fp; eauto.     
Qed.

Lemma eval_divls_mull_fp:
  forall le x y p M,
  divls_mul_params (Int64.signed y) = Some(p, M) ->
  nth_error le O = Some (Vlong x) ->
  eval_expr_fp ge sp e m le (divls_mull p M) FP.emp.
Proof.
  intros. unfold divls_mull.
  assert (A0: eval_expr ge sp e m le (Eletvar O) (Vlong x)) by (constructor; auto).
  exploit eval_mullhs. 2:exacteval A0. eauto. instantiate (1 := Int64.repr M).  intros (v1 & A1 & B1).
  exploit eval_mullhs_fp; eauto. econstructor; eauto. evalge A1. intros (fp1 & A1' & B1').
  exploit eval_addl; auto. exact A1. exacteval A0. intros (v2 & A2 & B2).
  exploit eval_addl_fp; auto. exacteval A1. eauto. exact A0. econstructor; eauto. exacteval A2. intros (fp2 & A2' & B2').
  exploit eval_shrluimm. 2:exacteval A0. eauto. instantiate (1 := Int.repr 63). intros (v3 & A3 & B3).
  exploit eval_shrluimm_fp; eauto. econstructor; eauto. exacteval A3. intros [fp3 [A3' B3']].
  set (a4 := if zlt M Int64.half_modulus
             then mullhs (Eletvar 0) (Int64.repr M)
             else addl (mullhs (Eletvar 0) (Int64.repr M)) (Eletvar 0)).
  set (v4 := if zlt M Int64.half_modulus then v1 else v2).
  evalge A1. evalge A2. evalge A3.
  assert (A4: eval_expr ge sp e m le a4 v4). 
  { unfold a4, v4; destruct (zlt M Int64.half_modulus); auto. }
  assert (exists fp4,  eval_expr_fp ge sp e m le a4 fp4 /\ FP.subset fp4 fp2) as [fp4 [A4' B4']].
  { unfold a4, v4; destruct (zlt M Int64.half_modulus); eexists; (split;[eauto|TrivFP]).
    apply subset_trans with FP.emp; TrivFP. }
  exploit eval_shrlimm. 2:exacteval A4. eauto. instantiate (1 := Int.repr p). intros (v5 & A5 & B5).
  exploit eval_shrlimm_fp; try exact A4; eauto. exacteval A5. intros (fp5 & A5' & B5').
  exploit eval_addl. exact A5. exacteval A3. intros [v6 [A6 B6]].
  exploit eval_addl_fp. exacteval A5. eauto. eexact A3. eauto. exacteval A6. intros [fp6 [A6' B6']].
  assert (fp6 = FP.emp).
  { apply subset_emp_emp. eapply subset_trans; try eexact B6'. apply subset_emp_emp in B3'. subst.
    TrivFP. eapply subset_trans; try eexact B5'. eapply subset_trans; try eexact B4'.
    eapply subset_trans; try eexact B2'. TrivFP. }
  subst. auto.
Qed.

Theorem eval_divls_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.divls x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (divls a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold divls; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
- assert (y = Vlong n2) by (eapply is_longconst_sound; try exacteval H1; eauto). subst y.
  destruct (is_longconst a) as [n1|] eqn:N1.
+ assert (x = Vlong n1) by (eapply is_longconst_sound; try exacteval H; eauto). subst x.
  simpl in H3. 
  destruct (Int64.eq n2 Int64.zero
         || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H3.
  econstructor; split. apply eval_longconst_fp. TrivFP.
+ destruct (Int64.is_power2' n2) as [l|] eqn:POW.
* destruct (Int.ltu l (Int.repr 63)) eqn:LT.
** exploit Val.divls_pow2; eauto. intros EQ. exploit eval_shrxlimm_fp; try exact H; eauto. intros [fp [A B]]. Triv.
** exploit eval_divls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]]. evalge A.
   eapply eval_divls_base_fp; eauto.
* destruct (Compopts.optim_for_size tt).
  exploit eval_divls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]]. evalge A.
  eapply eval_divls_base_fp; eauto.
  destruct (divls_mul_params (Int64.signed n2)) as [[p M]|] eqn:PARAMS. 
** destruct x; simpl in H3; try discriminate.
   destruct (Int64.eq n2 Int64.zero
             || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H3.
   exploit eval_divls_mull; eauto. 2:instantiate (2:= Vlong i :: le); simpl; eauto.
   instantiate (1:= mkprogram (cu_defs cu) (cu_public cu) 1%positive); eauto. intro A. evalge A.
   exploit eval_divls_mull_fp; eauto. instantiate (2:= Vlong i :: le); simpl; eauto. intro A'.
   econstructor; split; eauto. econstructor. eauto. eauto. eauto. eauto. TrivFP. TrivFP.
** exploit eval_divls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]]. evalge A.
   eapply eval_divls_base_fp; eauto.
- exploit eval_divls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]]. evalge A.
  eapply eval_divls_base_fp; eauto.
Qed.

Theorem eval_modls_fp:
  forall le a b x fpx y fpy z,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  Val.modls x y = Some z ->
  exists fp, eval_expr_fp ge sp e m le (modls a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  unfold modls; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
- assert (y = Vlong n2) by (eapply is_longconst_sound; try exacteval H1; eauto). subst y.
  destruct (is_longconst a) as [n1|] eqn:N1.
+ assert (x = Vlong n1) by (eapply is_longconst_sound; try exacteval H; eauto). subst x.
  simpl in H3. 
  destruct (Int64.eq n2 Int64.zero
         || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H3.
  econstructor; split. apply eval_longconst_fp. TrivFP.
+ destruct (Int64.is_power2' n2) as [l|] eqn:POW.
* destruct (Int.ltu l (Int.repr 63)) eqn:LT.
**destruct x; simpl in H3; try discriminate.
  destruct (Int64.eq n2 Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone) eqn:D; inv H3.
  assert (Val.divls (Vlong i) (Vlong n2) = Some (Vlong (Int64.divs i n2))).
  { simpl; rewrite D; auto. }
  exploit Val.divls_pow2; eauto. intros EQ.
  set (le' := Vlong i :: le).
  assert (A: eval_expr ge sp e m le' (Eletvar O) (Vlong i)) by (constructor; auto).
  assert (A': eval_expr_fp ge sp e m le' (Eletvar O) FP.emp) by (econstructor; simpl; eauto).
  exploit eval_shrxlimm. 2: exacteval A. eauto. eauto. intros (v1 & A1 & B1). inv B1.
  exploit eval_shrxlimm_fp; eauto. intros (fp1 & A1' & B1'). apply subset_emp_emp in B1'; subst.
  exploit eval_modl_from_divl. 2:exact A1. eauto. reflexivity. intro A2. evalge A2.
  exploit eval_modl_from_divl_fp. exacteval A1. eauto. reflexivity. intros [fp' [A2' B2']].
  apply subset_emp_emp in B2'; subst. econstructor; split. econstructor; eauto. TrivFP.
**exploit eval_modls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]].
  eapply eval_modls_base_fp; eauto. exacteval A.
* destruct (Compopts.optim_for_size tt).
  exploit eval_modls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]].
  eapply eval_modls_base_fp; eauto. exacteval A.
  destruct (divls_mul_params (Int64.signed n2)) as [[p M]|] eqn:PARAMS. 
** destruct x; simpl in H3; try discriminate.
   destruct (Int64.eq n2 Int64.zero
             || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H3.
   exploit eval_modl_from_divl. 2:eapply eval_divls_mull; eauto.
   instantiate (1:=mkprogram (cu_defs cu) (cu_public cu) 1%positive). eauto. eauto.
   instantiate (2:=Vlong i :: le). reflexivity. reflexivity. intro A. evalge A.
   exploit eval_modl_from_divl_fp. eapply eval_expr_preserved; try gegen.
   4:eapply eval_divls_mull. 1-3:try gegen; eauto with gegen. eauto. eauto.
   instantiate (2:=Vlong i :: le). reflexivity.
   eapply eval_divls_mull_fp; eauto; simpl; eauto. simpl; eauto. intros [fp [C D]].
   econstructor; split; eauto. econstructor; eauto. apply subset_emp_emp in D; subst. TrivFP.
** exploit eval_modls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]].
   eapply eval_modls_base_fp; eauto. exacteval A.
- exploit eval_modls_base. 2:exacteval H. eauto. exacteval H1. eauto. intros [v [A B]].
   eapply eval_modls_base_fp; eauto. exacteval A.
Qed.

(** * Floating-point division *)

Theorem eval_divf_fp:
  forall le a b x fpx y fpy,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  exists fp, eval_expr_fp ge sp e m le (divf a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  intros until y. unfold divf. destruct (divf_match b); intros.
- unfold divfimm. destruct (Float.exact_inverse n2) as [n2' | ] eqn:EINV.
  + InvEvalFP; InvEval; eqexpr; InvEmpFP; Triv.
  + Triv.
- Triv.
Qed.

Theorem eval_divfs_fp:
  forall le a b x fpx y fpy,
  eval_expr ge sp e m le a x ->
  eval_expr_fp ge sp e m le a fpx ->
  eval_expr ge sp e m le b y ->
  eval_expr_fp ge sp e m le b fpy ->
  exists fp, eval_expr_fp ge sp e m le (divfs a b) fp /\ FP.subset fp (FP.union fpx fpy).
Proof.
  intros until y. unfold divfs. destruct (divfs_match b); intros;[|Triv].
  unfold divfsimm. destruct (Float32.exact_inverse n2) as [n2' | ] eqn:EINV; [|Triv].
  InvEvalFP; InvEval; eqexpr; InvEmpFP; Triv.
Qed.

End CMCONSTRS.
