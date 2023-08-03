(* This file is adapted from [backend/Lineartyping.v] of CompCert,
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

(** Type-checking Linear code. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Events.
Require Import Op.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Linear CUAST Linear_local.
Require Import Lineartyping.


Lemma wt_set_arguments:
  forall ls rl args,
    (forall r, In r rl -> forall_rpair (fun l => match l with S _ _ _ => True | _ => False end) r) ->
    wt_locset ls ->
    wt_locset (val_casted.set_arguments rl args ls).
Proof.
  clear. induction rl; auto.
  intros; simpl.
  destruct args; auto.
  exploit (H a); simpl; auto.
  destruct a; simpl; intro.
  destruct r; try contradiction. apply wt_setstack.
  apply IHrl; auto. intros. apply H. simpl. auto.
  destruct rhi; try tauto; destruct rlo; try tauto. do 2 apply wt_setstack.
  apply IHrl; auto. intros. apply H. simpl. auto.
Qed.

Lemma wt_parent_locset0:
  forall rs0 s, wt_locset rs0 -> wt_callstack s -> wt_locset (parent_locset0 rs0 s).
Proof.
  induction 2; auto.
Qed.

Inductive wt_core: core -> Prop :=
| wt_regular_core: forall s f sp c rs rs0 f0
                      (WTSTK: wt_callstack s )
                      (WTF: wt_function f = true)
                      (WTC: wt_code f c = true)
                      (WTRS: wt_locset rs)
                      (WTRS0: wt_locset rs0),
    wt_core (Core_State s f sp c rs (mk_load_frame rs0 f0))
| wt_call_core: forall s fd rs rs0 f0
                   (WTSTK: wt_callstack s)
                   (WTFD: wt_fundef fd)
                   (WTRS: wt_locset rs)
                   (WTRS0: wt_locset rs0),
    wt_core (Core_Callstate s fd rs (mk_load_frame rs0 f0))
| wt_call_coreIn: forall fd rs rs0 f0
                     (WTFD: wt_fundef fd)
                     (WTRS: wt_locset rs)
                     (WTRS0: wt_locset rs0),
    wt_core (Core_CallstateIn nil fd rs (mk_load_frame rs0 f0))
| wt_return_core: forall s rs rs0 f0
                     (WTSTK: wt_callstack s)
                     (WTRS: wt_locset rs)
                     (WTRS0: wt_locset rs0),
    wt_core (Core_Returnstate s rs (mk_load_frame rs0 f0)).

(** Preservation of state typing by transitions *)

Section SOUNDNESS.

Variable cu: Linear_comp_unit.
Variable ge: genv.
Hypothesis GE_INIT: init_genv cu ge ge.

Hypothesis wt_prog:
  forall i fd, In (i, Gfun fd) cu.(cu_defs) -> wt_fundef fd.
Lemma cu_find_def_eq:
  forall F V (cu: comp_unit_generic F V) ge b,
    globalenv_generic cu ge ->
    Genv.find_def ge b =
    Genv.find_def (Genv.globalenv
                     {|
                       prog_defs := cu_defs cu;
                       prog_public := cu_public cu;
                       prog_main := 1%positive |}) b.
Proof. clear; intros. inv H. auto. Qed.

Theorem cu_find_def_inversion:
  forall F V (cu: comp_unit_generic F V) ge b g,
    globalenv_generic cu ge ->
    Genv.find_def ge b = Some g ->
    exists id, In (id, g) (cu_defs cu).
Proof.
  clear; intros F V cu0 ge0 b g HGE FIND.
  erewrite cu_find_def_eq in FIND; eauto. 
  exploit Genv.find_def_inversion; eauto.
Qed.

Lemma cu_find_funct_ptr_inversion:
  forall F V (cu: comp_unit_generic F V) ge b f,
    globalenv_generic cu ge ->
    Genv.find_funct_ptr ge b = Some f ->
    exists id, In (id, Gfun f) (cu_defs cu).
Proof.
  clear; intros. eapply cu_find_def_inversion; eauto.
  apply Genv.find_funct_ptr_iff; eauto.
Qed.

Lemma cu_find_funct_inversion:
  forall F V (cu: comp_unit_generic F V) ge v f,
    globalenv_generic cu ge ->
    Genv.find_funct ge v = Some f ->
    exists id, In (id, Gfun f) (cu_defs cu).
Proof.
  clear; intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H0.
  eapply cu_find_funct_ptr_inversion; eauto.
Qed.
Lemma wt_find_function:
  forall ros rs f, find_function ge ros rs = Some f -> wt_fundef f.
Proof.
  intros.
  assert (exists i, In (i, Gfun f) cu.(cu_defs)) as [i IN].
  {
    destruct ros as [r | s]; simpl in H.
    (** TODO: there should be a CUAST version of find_funct_inversion. *)
  

      
    eapply cu_find_funct_inversion; eauto. inv GE_INIT; auto.
    destruct (Genv.find_symbol ge s) as [b|]; try discriminate.
    eapply cu_find_funct_ptr_inversion; eauto. inv GE_INIT; auto.
  }
  eapply wt_prog; eauto.
Qed.

Theorem step_type_preservation:
  forall c1 m1 fp c2 m2, step ge c1 m1 fp c2 m2 -> wt_core c1 -> wt_core c2.
Proof.
Local Opaque mreg_type.
  induction 1; intros WTS; inv WTS.
- (* getstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_setreg; eauto. eapply Val.has_subtype; eauto. apply WTRS.
  apply wt_undef_regs; auto.
- (* setstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_setstack. apply wt_undef_regs; auto.
- (* op *)
  simpl in *. destruct (is_move_operation op args) as [src | ] eqn:ISMOVE.
  + (* move *)
    InvBooleans. exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst.
    simpl in H. inv H.
    econstructor; eauto. apply wt_setreg. eapply Val.has_subtype; eauto. apply WTRS.
    apply wt_undef_regs; auto.
  + (* other ops *)
    destruct (type_of_operation op) as [ty_args ty_res] eqn:TYOP. InvBooleans.
    econstructor; eauto.
    apply wt_setreg; auto. eapply Val.has_subtype; eauto.
    change ty_res with (snd (ty_args, ty_res)). rewrite <- TYOP. eapply type_of_operation_sound; eauto.
    red; intros; subst op. simpl in ISMOVE.
    destruct args; try discriminate. destruct args; discriminate.
    apply wt_undef_regs; auto.
- (* load *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_setreg. eapply Val.has_subtype; eauto.
  destruct a; simpl in H0; try discriminate. eapply Mem.load_type; eauto.
  apply wt_undef_regs; auto.
- (* store *)
  simpl in *; InvBooleans.
  econstructor. eauto. eauto. eauto.
  apply wt_undef_regs; auto. auto.
- (* call *)
  simpl in *; InvBooleans.
  econstructor; eauto. econstructor; eauto.
  eapply wt_find_function; eauto.
- (* tailcall *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_find_function; eauto.
  apply wt_return_regs; auto. apply wt_parent_locset0; auto.
- (* builtin *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_setres; eauto. eapply external_call_well_typed; eauto.
  apply wt_undef_regs; auto.
- (* label *)
  simpl in *. econstructor; eauto.
- (* goto *)
  simpl in *. econstructor; eauto. eapply wt_find_label; eauto.
- (* cond branch, taken *)
  simpl in *. econstructor. auto. auto. eapply wt_find_label; eauto.
  apply wt_undef_regs; auto. auto.
- (* cond branch, not taken *)
  simpl in *. econstructor. auto. auto. auto.
  apply wt_undef_regs; auto. auto.
- (* jumptable *)
  simpl in *. econstructor. auto. auto. eapply wt_find_label; eauto.
  apply wt_undef_regs; auto. auto.
- (* return *)
  simpl in *. InvBooleans.
  econstructor; eauto.
  apply wt_return_regs; auto. apply wt_parent_locset0; auto.
- (* internal function *)
  simpl in WTFD.
  econstructor. eauto. eauto. eauto.
  apply wt_undef_regs. apply wt_call_regs. auto. auto.
- (* internal0 *)
  econstructor. constructor. auto. auto. auto.
- (* external *)
  econstructor; auto. apply wt_setpair; auto.
  eapply external_call_well_typed; eauto.
- (* return *)
  inv WTSTK. econstructor; eauto.
Qed.

Theorem wt_initial_state:
  forall fid args c, init_core ge fid args = Some c -> wt_core c.
Proof.
  unfold init_core, generic_init_core, fundef_init.
  intros.
  repeat match goal with
         | H: context[match ?x with _ => _ end] |- _ =>
           destruct x eqn:?; try discriminate
         end.
  inv H. econstructor; eauto. 
  exploit cu_find_funct_ptr_inversion; eauto. inv GE_INIT; eauto.
  intros [id IN].  apply wt_prog with id; auto.
  apply wt_set_arguments. clear.
  unfold loc_arguments. destruct Archi.ptr64 eqn:C. inversion C.
  intros r H. apply loc_arguments_32_charact in H.
  unfold forall_rpair,loc_argument_32_charact in *.
  destruct r. destruct r; auto. destruct rhi, rlo; tauto.
  apply wt_init.
  apply wt_set_arguments. clear.
  unfold loc_arguments. destruct Archi.ptr64 eqn:C. inversion C.
  intros r H. apply loc_arguments_32_charact in H.
  unfold forall_rpair,loc_argument_32_charact in *.
  destruct r. destruct r; auto. destruct rhi, rlo; tauto.
  apply wt_init.
Qed.

End SOUNDNESS.

(** Properties of well-typed states that are used in [Stackingproof]. *)

Lemma wt_core_getstack:
  forall s f sp sl ofs ty rd c rs lf,
  wt_core (Core_State s f sp (Lgetstack sl ofs ty rd :: c) rs lf) ->
  slot_valid f sl ofs ty = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_core_setstack:
  forall s f sp sl ofs ty r c rs lf,
  wt_core (Core_State s f sp (Lsetstack r sl ofs ty :: c) rs lf) ->
  slot_valid f sl ofs ty = true /\ slot_writable sl = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. intuition.
Qed.

Lemma wt_core_tailcall:
  forall s f sp sg ros c rs lf,
  wt_core (Core_State s f sp (Ltailcall sg ros :: c) rs lf) ->
  size_arguments sg = 0.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_core_builtin:
  forall s f sp ef args res c rs m,
  wt_core (Core_State s f sp (Lbuiltin ef args res :: c) rs m) ->
  forallb (loc_valid f) (params_of_builtin_args args) = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_core_callstate_wt_regs:
  forall s f rs lf,
  wt_core (Core_Callstate s f rs lf) ->
  forall r, Val.has_type (rs (R r)) (mreg_type r).
Proof.
  intros. inv H. apply WTRS.
Qed.
