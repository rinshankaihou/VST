(** Restricted globalization for Clight.

    CompCert supplies a forward simulation from global [Clight_IS_2] steps to
    local [Clight_IS_2_local] steps. This file packages a converse for local
    steps that carry both a represented global witness and a uniqueness proof
    at the displayed local result. It does not claim that every local step can
    be globalized. *)

From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Globalenvs Values.
From compcert.common_cas Require Import Memory.
From compcert.concurrency.common
Require Import Blockset Footprint GMemory MemAux InteractionSemantics LDSimDefs.
From compcert.concurrency.comp_correct Require Import ClightLang.
From compcert.concurrency.comp_correct.cfrontend Require Import Clight_local.
From compcert.concurrency.comp_correct.localize
Require Import IS_local Localize ClightLocalize.

(** A local transition is deterministic at the displayed result.  Keeping
    this condition local to a transition makes the restricted converse
    independent of a separate language-wide determinism interface. *)
Definition local_step_unique_at
    (sem : sem_local) (Ge_local : G sem)
    (lc : core sem) (lm : mem)
    (lfp : FP.t) (lc' : core sem) (lm' : mem) : Prop :=
  forall lfp' lc'' lm'',
    step_local sem Ge_local lc lm lfp' lc'' lm'' ->
    lfp' = lfp /\ lc'' = lc' /\ lm'' = lm'.

Section GlobalizeSim.
  Context {L : Language} {sem : sem_local}.

  Context (bj : Bset.inj)
          (ge : Genv.t (InteractionSemantics.F L)
                       (InteractionSemantics.V L))
          (ge_local : Genv.t (F sem) (V sem))
          (Ge : InteractionSemantics.G L)
          (Ge_local : G sem)
          (match_state :
             Bset.inj -> freelist ->
             InteractionSemantics.core L -> gmem ->
             core sem -> mem -> Prop).

  Local Notation Shared :=
    (fun b : block => Plt b (Genv.genv_next ge)).

  (** The global witness in [representable_step] is constrained only at its
      source and by the two footprints.  In particular, the definition does
      not assume that the displayed local target already matches the global
      target; that is the conclusion supplied by [GlobalizeSim].  A
      bit-field-only local transition is not representable because
      [Clight_IS_2] has no source transition for it. *)
  Definition representable_step
      (fl : freelist)
      (gc : InteractionSemantics.core L) (gm : gmem)
      (lc : core sem) (lm : mem)
      (lfp : FP.t) (lc' : core sem) (lm' : mem) : Prop :=
    local_step_unique_at sem Ge_local lc lm lfp lc' lm' /\
    exists gfp gc' gm',
      InteractionSemantics.step L Ge fl gc gm gfp gc' gm' /\
      FPlocalize
        (construct_inj bj (Genv.genv_next ge) fl) gfp lfp /\
      fpG fl Shared gfp.

  (** A restricted reverse simulation.  The ordinary localization
      simulation supplies the matching invariant and all non-step clauses;
      [globalize_lockstep] adds the converse for precisely the local steps
      represented by the global semantics. *)
  Record GlobalizeSim : Prop := {
    globalize_localize :
      @LocalizeSim L sem bj ge ge_local Ge Ge_local match_state;

    globalize_lockstep :
      forall fl gc lc gm lm lfp lc' lm',
        match_state bj fl gc gm lc lm ->
        step_local sem Ge_local lc lm lfp lc' lm' ->
        representable_step fl gc gm lc lm lfp lc' lm' ->
        exists gfp gc' gm',
          InteractionSemantics.step L Ge fl gc gm gfp gc' gm' /\
          FPlocalize
            (construct_inj bj (Genv.genv_next ge) fl) gfp lfp /\
          fpG fl Shared gfp /\
          match_state bj fl gc' gm' lc' lm'
  }.
End GlobalizeSim.

(** Every forward localization simulation induces the restricted converse:
    replay the represented global step through localization, then use local
    uniqueness to identify its result with the displayed local transition. *)
Lemma localize_globalize_sim :
  forall (L : Language) (sem : sem_local)
         (bj : Bset.inj)
         (ge : Genv.t (InteractionSemantics.F L)
                      (InteractionSemantics.V L))
         (ge_local : Genv.t (F sem) (V sem))
         (Ge : InteractionSemantics.G L) (Ge_local : G sem)
         (match_state :
            Bset.inj -> freelist ->
            InteractionSemantics.core L -> gmem ->
            core sem -> mem -> Prop),
    @LocalizeSim L sem bj ge ge_local Ge Ge_local match_state ->
    @GlobalizeSim L sem bj ge ge_local Ge Ge_local match_state.
Proof.
  intros L sem bj ge ge_local Ge Ge_local match_state LOCALIZE.
  constructor.
  - exact LOCALIZE.
  - intros fl gc lc gm lm lfp lc' lm' MATCH LOCAL_STEP
      [LOCAL_UNIQUE (gfp & gc' & gm' & GLOBAL_STEP & FP_REL & FP_GLOBAL)].
    destruct
      (localize_lockstep
         bj ge ge_local Ge Ge_local match_state LOCALIZE
         fl gc lc gm lm gfp gc' gm' MATCH GLOBAL_STEP FP_GLOBAL)
      as (lfp' & lc'' & lm'' & LOCAL_STEP' & FP_REL' & MATCH').
    destruct (LOCAL_UNIQUE lfp' lc'' lm'' LOCAL_STEP')
      as [-> [-> ->]].
    exists gfp, gc', gm'.
    split; [exact GLOBAL_STEP |].
    split; [exact FP_REL |].
    split; [exact FP_GLOBAL | exact MATCH'].
Qed.

(** Language-level packaging, parallel to [LangLocalize], but exposing the
    restricted reverse simulation above. *)
Inductive LangGlobalize
    (comp_unit : Type) (wdcu : comp_unit -> Prop) :
    Language -> sem_local -> Prop :=
| LangGlobalize_intro :
    forall F0 V0 G0 core0
           f1 f2 f3 f4 f5 f6 f7 f8
           f1' f2' f3' f4' f5' f6' f7',
      (forall (cu : comp_unit) (Hwdcu : wdcu cu)
              (ge : Genv.t F0 V0) (Ge : G0),
          InteractionSemantics.init_genv
            (Build_Language F0 V0 G0 comp_unit core0
               f1 f2 f3 f4 f5 f6 f7 f8) cu ge Ge ->
          exists bj_ident ge_local Ge_local match_state,
            init_genv_local
              (Build_sem_local F0 V0 G0 comp_unit core0
                 f1' f2' f3' f4' f5' f6' f7')
              cu ge_local Ge_local /\
            ge_match_strict bj_ident ge ge_local /\
            (forall b b', bj_ident b = Some b' ->
               exists gd, Genv.find_def ge_local b = Some gd) /\
            (forall bj,
                inject_incr (Bset.inj_to_meminj bj_ident)
                            (Bset.inj_to_meminj bj) ->
                Bset.inject bj
                  (fun b => Plt b (Genv.genv_next ge_local))
                  (fun b => Plt b (Genv.genv_next ge)) ->
                @GlobalizeSim
                  (Build_Language F0 V0 G0 comp_unit core0
                     f1 f2 f3 f4 f5 f6 f7 f8)
                  (Build_sem_local F0 V0 G0 comp_unit core0
                     f1' f2' f3' f4' f5' f6' f7')
                  bj ge ge_local Ge Ge_local match_state)) ->
      LangGlobalize comp_unit wdcu
        (Build_Language F0 V0 G0 comp_unit core0
           f1 f2 f3 f4 f5 f6 f7 f8)
        (Build_sem_local F0 V0 G0 comp_unit core0
           f1' f2' f3' f4' f5' f6' f7').

(** Restricted reverse of [clight_localize]. *)
Theorem clight_globalize :
  LangGlobalize clight_comp_unit wdcu Clight_IS_2 Clight_IS_2_local.
Proof.
  constructor; simpl in *.
  intros cu WDCU ge Ge INIT_GE.
  pose proof
    (localize_localizesim
       _ _ _ _ _ _
       _ _ _ _ _ _ _ _
       _ _ _ _ _ _ _
       clight_localize cu WDCU ge Ge INIT_GE) as LOCALIZE.
  destruct LOCALIZE as
    (bj_ident & ge_local & Ge_local & match_state &
     INIT_LOCAL & GE_MATCH & DEFS & LOCALIZE).
  exists bj_ident, ge_local, Ge_local, match_state.
  split; [exact INIT_LOCAL |].
  split; [exact GE_MATCH |].
  split; [exact DEFS |].
  intros bj INCR INJECT.
  apply localize_globalize_sim.
  apply LOCALIZE; auto.
Qed.
