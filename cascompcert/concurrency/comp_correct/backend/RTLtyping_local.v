(* This file is adapted from [backend/RTLtyping.v] of CompCert,
   with support for our interaction semantics. *)

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


(** Typing rules and a type inference algorithm for RTL. *)

Require Import Coqlib.
Require Import Errors.
Require Import Unityping.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import Values.
Require Import Integers.
Require Import Memory.
Require Import Events.
Require Import RTL.
Require Import Conventions.
Require Import RTLtyping.

Require Import CUAST IS_local RTL_local.


Definition wt_cu (cu: RTL_comp_unit) : Prop :=
  forall i f, In (i, Gfun f) (cu_defs cu) -> wt_fundef f.

(** * Type preservation during evaluation *)
Inductive wt_stackframes: list stackframe -> signature -> Prop :=
  | wt_stackframes_nil: forall sg,
(*       sg.(sig_res) = Some Tint -> *)
      wt_stackframes nil sg
  | wt_stackframes_cons:
      forall s res f sp pc rs env sg,
      wt_function f env ->
      wt_regset env rs ->
      env res = proj_sig_res sg ->
      wt_stackframes s (fn_sig f) ->
      wt_stackframes (Stackframe res f sp pc rs :: s) sg.

Remark wt_stackframes_change_sig:
  forall s sg1 sg2,
  sg1.(sig_res) = sg2.(sig_res) -> wt_stackframes s sg1 -> wt_stackframes s sg2.
Proof.
  intros. inv H0.
- constructor; congruence.
- econstructor; eauto. rewrite H3. unfold proj_sig_res. rewrite H. auto.
Qed.

Inductive wt_core: core -> Prop :=
| wt_core_intro:
    forall s f sp pc rs env
      (WT_STK: wt_stackframes s (fn_sig f))
      (WT_FN: wt_function f env)
      (WT_RS: wt_regset env rs),
      wt_core (Core_State s f sp pc rs)
| wt_core_call:
    forall s f args,
      wt_stackframes s (funsig f) ->
      wt_fundef f ->
      Val.has_type_list args (sig_args (funsig f)) ->
      wt_core (Core_Callstate s f args)
| wt_core_return:
    forall s v sg,
      wt_stackframes s sg ->
      Val.has_type v (proj_sig_res sg) ->
      wt_core (Core_Returnstate s v).

Section SUBJECT_REDUCTION.

Variable cu: RTL_comp_unit.

Hypothesis wt_p: wt_cu cu.

Variable ge: genv.

Hypothesis HGE: globalenv_generic cu ge.

Lemma subject_reduction:
  forall st1 m1 fp st2 m2,
    step ge st1 m1 fp st2 m2 ->
    forall (WT: wt_core st1), wt_core st2.
Proof.
  induction 1; intros; inv WT;
    try (generalize (wt_instrs _ _ WT_FN pc _ H); intros WTI).
  (* Inop *)
  econstructor; eauto.
  (* Iop *)
  econstructor; eauto. eapply wt_exec_Iop; eauto.
  (* Iload *)
  econstructor; eauto. eapply wt_exec_Iload; eauto.
  (* Istore *)
  econstructor; eauto.
  (* Icall *)
  assert (wt_fundef fd).
  { destruct ros; simpl in H0.
    pattern fd. eapply find_funct_prop; eauto.
    destruct (Genv.find_symbol ge i); try discriminate.
    pattern fd. eapply find_funct_ptr_prop; eauto.
  }
  econstructor; eauto.
  econstructor; eauto. inv WTI; auto.
  inv WTI. rewrite <- H8. apply wt_regset_list. auto.
  (* Itailcall *)
  assert (wt_fundef fd).
    destruct ros; simpl in H0.
    pattern fd. eapply find_funct_prop; eauto.
    caseEq (Genv.find_symbol ge i); intros; rewrite H1 in H0.
    pattern fd. eapply find_funct_ptr_prop; eauto.
    discriminate.
  econstructor; eauto.
  inv WTI. apply wt_stackframes_change_sig with (fn_sig f); auto.
  inv WTI. rewrite <- H7. apply wt_regset_list. auto.
  (* Ibuiltin *)
  econstructor; eauto. eapply wt_exec_Ibuiltin; eauto.
  (* Icond *)
  econstructor; eauto.
  (* Ijumptable *)
  econstructor; eauto.
  (* Ireturn *)
  econstructor; eauto.
  inv WTI; simpl. auto. unfold proj_sig_res; rewrite H2. auto.
  (* internal function *)
  simpl in *. inv H5.
  econstructor; eauto.
  inv H1. apply wt_init_regs; auto. rewrite wt_params. auto.
  (* external function *)
  econstructor; eauto. simpl.
  eapply external_call_well_typed; eauto.
  (* return *)
  inv H1. econstructor; eauto.
  apply wt_regset_assign; auto. rewrite H10; auto.
Qed.

Lemma wt_initial_core:
  forall fid args c, init_core ge fid args = Some c -> wt_core c.
Proof.
  unfold init_core, generic_init_core, fundef_init, val_casted.wd_args. intros.
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ =>
           destruct x eqn:?; try discriminate
         end.
  inv H. constructor. constructor. 
  pattern (Internal f0). eapply find_funct_ptr_prop; eauto.
  repeat rewrite andb_true_iff in Heqb0. destruct Heqb0. destruct H.
  eapply val_casted.val_has_type_list_func_charact; eauto.
Qed.

Lemma wt_after_external:
  forall c ores c',
    wt_core c ->
    after_external c ores = Some c' ->
    wt_core c'.
Proof.
  unfold after_external.
  destruct c; try discriminate.
  destruct f; try discriminate.
  destruct e; try discriminate.
  intros. inv H.
  destruct ores, (sig_res sg) eqn:?; try discriminate.
  destruct (val_casted.val_has_type_func v t) eqn:?; inv H0.
  econstructor; eauto. apply val_casted.val_has_type_funcP. unfold proj_sig_res; simpl; rewrite Heqo. auto.
  inv H0. econstructor; eauto. simpl. auto.
Qed.
  
Lemma wt_instr_inv:
  forall s f sp pc rs i,
  wt_core (Core_State s f sp pc rs) ->
  f.(fn_code)!pc = Some i ->
  exists env, wt_instr f env i /\ wt_regset env rs.
Proof.
  intros. inv H. exists env; split; auto.
  inv WT_FN. eauto.
Qed.

End SUBJECT_REDUCTION.


