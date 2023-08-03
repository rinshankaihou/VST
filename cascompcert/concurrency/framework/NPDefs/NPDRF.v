Require Import Blockset Footprint GMemory InteractionSemantics GlobDefs GAST ETrace NPSemantics.
Require Import GlobSim.

(** * NP-DRF *)

(** This file defines a non-preemptive version of data-race-free property *)

Local Notation "'[[' thdp ',' t ',' m ',' b ']]'" :=
  ({| thread_pool:= thdp; cur_tid:= t; gm:= m; atom_bit:= b |})
    (at level 70, right associativity).

Local Notation "'[[' thdp ',' t ',' m ',' b ']]@' G " :=
  (Build_ProgConfig G thdp t m b) (at level 70, right associativity).

Local Notation " GE '|-' pc1 '=[' l '|' fp ']=>>' pc2 " :=
  (@np_step GE pc1 l fp pc2) (at level 80, right associativity).

Inductive np_ent_atom {GE} : ProgConfig -> tid -> ProgConfig -> Prop :=
| np_ent_atom_intro:
    forall thdp tid gm thdp' gm',
      GE |- [[thdp, tid, gm, O]] =[ tau | FP.emp]=>> [[thdp', tid, gm', I]] ->
           np_ent_atom ([[thdp, tid, gm, O]]) tid ([[thdp', tid, gm', I]]).
Corollary tau_step_bitchange_np_ent_atom :
  forall ge pc pc1,
    ge|- pc =[tau|FP.emp]=>>pc1 ->
    atom_bit pc <> atom_bit pc1 ->
    np_ent_atom pc pc.(cur_tid) pc1.
Proof.
  intros.
  inversion H;subst;try contradiction.
  constructor;auto.
Qed.
Corollary np_ent_atom_tau_step_bitchange:
  forall ge pc pc1 id,
    np_ent_atom pc id pc1->
    (ge|-pc =[tau|FP.emp]=>>pc1) /\ atom_bit pc <> atom_bit pc1 /\ id = cur_tid pc.
Proof.
  intros.
  inversion H;clear H;subst.
  split;auto.
  split;auto.
  compute.
  intro.
  inversion H.
Qed.
(** this relation [np_normal_tau pc t b fp pc'] states that 
    - [pc] could step to another configuration [pc'], with zero or more tau steps of thread [t]. 
    - All intermediate states has atomic bit [b],
    - and we accumulate the footprint of all step in [fp].
 *)

Inductive np_normal_tau {GE} : @ProgConfig GE -> tid -> Bit -> FP.t -> ProgConfig -> Prop :=
| predict_nil: forall thdp t gm b,
    np_normal_tau ([[thdp, t, gm, b]]) t b FP.emp ([[thdp, t, gm, b]])
| predict_cons: forall thdp t gm b fp thdp' gm' fp' pc',
    GE |- [[thdp, t, gm, b]] =[ tau | fp ]=>> [[thdp', t, gm', b]] ->
         np_normal_tau ([[thdp', t, gm', b]]) t b fp' pc' ->
         np_normal_tau ([[thdp, t, gm, b]]) t b (FP.union fp fp') pc'.
Lemma tau_step_bitpreservation_np_normal_tau :
  forall ge pc pc1 fp,
    @np_step ge pc tau fp pc1 ->
    atom_bit pc =atom_bit pc1 ->
    np_normal_tau pc pc.(cur_tid) pc.(atom_bit) fp pc1.
Proof.
  intros.
  destruct pc,pc1.
  compute [GlobDefs.atom_bit] in H0;subst.
  assert(cur_tid0=cur_tid).
  inversion H;subst;try contradiction;auto.
  subst.
  compute [GlobDefs.cur_tid].
  compute [atom_bit].
  eapply predict_cons in H;try constructor.
  rewrite FP.fp_union_emp in H.
  auto.
Qed.
Lemma tau_N_bitpreservation_np_normal_tau:
  forall i ge pc pc1 fp ,
    tau_N (@np_step ge) i pc fp pc1->
    atom_bit pc = atom_bit pc1 ->
    np_normal_tau pc pc.(cur_tid) pc.(atom_bit) fp pc1.
Proof.
  induction i.
  {
    intros.
    inversion H;subst.
    destruct pc1.
    constructor.
  }
  {
    intros.
    inversion H;clear H;subst.
    pose GlobSim.tau_N_tau_step_bit_rule.
    pose proof H2 as P1.
    eapply e in H2;eauto.
    rewrite H0 in H2. symmetry in H2.
    eapply IHi in H2;eauto.
    pose @predict_cons .
    destruct pc,pc1,s'.
    assert(cur_tid=cur_tid1). inversion P1;subst;auto.
    assert(atom_bit=atom_bit1).
    inversion P1;subst;try contradiction;auto.
    apply GlobSim.tau_N_bit_I_preservation in H3;auto.
    compute in H0,H3;rewrite <- H0 in H3; auto.
    subst.

    eapply n in P1;eauto.
  }
Qed.
Lemma np_normal_tau_N_exists:
   forall ge pc pc1 fp id bit,
     np_normal_tau pc id bit fp pc1 ->
     atom_bit pc = atom_bit pc1 /\ atom_bit pc = bit /\ cur_tid pc = id  /\ exists i, tau_N (@np_step ge) i pc fp pc1.
Proof.
  intros.
  induction H.
  {
    split;auto.
    split;auto.
    split;auto.
    exists 0;constructor.
  }
  {
    destruct IHnp_normal_tau as[eq[eq2[eq3 [i ] ] ] ].
    split;auto.
    split;auto.
    split;auto.
    exists (S i);  econstructor 2;eauto.
  }
Qed.
Corollary np_normal_iff_tau_star_bitpreservation :
    forall ge pc pc1 fp id bit,
     np_normal_tau pc id bit fp pc1 <->
     atom_bit pc = atom_bit pc1  /\ atom_bit pc = bit /\ cur_tid pc = id /\  tau_star (@np_step ge) pc fp pc1.
Proof.
  split;intros.
  apply np_normal_tau_N_exists in H as[eq1[eq2[eq3 ] ] ].
  apply tau_star_tau_N_equiv in H.
  auto.
  destruct H as[eq1[eq2[eq3] ] ].
  apply tau_star_tau_N_equiv in H as[].
  apply tau_N_bitpreservation_np_normal_tau in H;subst;auto.
Qed.

(** ** The non-preemptive "prediction"s *)

(** We do prediction on a program configuration for some thread [t] *)

(** [np_predict] is the non-preemptive version of [predict]. 
    We predict two sections of footprints, the former is predicted outside atomic blocks, the latter (if exists) is predicted inside the atomic blocks. 
    -- Note that np_normal_tau means one or multiple tau steps, so we may predict multiple steps in non-preemptive in one time.
 *)
Inductive np_predict {ge: GlobEnv.t}: @ProgConfig ge -> tid -> FP.t -> FP.t -> Prop :=
| np_predict_only_tau: forall thdp i' gm i fp0 pc',
    np_normal_tau ([[thdp, i, gm, O]]) i O fp0 pc'->
    np_predict ([[thdp, i', gm, O]]) i fp0 FP.emp
| np_predict_with_atom: forall thdp i' gm i fp0 pc' pc'' fp1 pc''',
    np_normal_tau ([[thdp, i, gm, O]]) i O fp0 pc' ->
    np_ent_atom pc' i pc'' ->
    np_normal_tau pc'' i I fp1 pc''' ->
    np_predict ([[thdp, i', gm, O]]) i fp0 fp1.


(** It is not conflicting if the footprints are both predicted inside atomic blocks.  *)
Inductive conflict_fps: FP.t * FP.t -> FP.t * FP.t -> Prop :=
| conflict_fps_00: forall fp10 fp11 fp20 fp21,
    FP.conflict fp10 fp20 -> conflict_fps (fp10, fp11) (fp20, fp21)
| conflict_fps_10: forall fp10 fp11 fp20 fp21,
    FP.conflict fp11 fp20 -> conflict_fps (fp10, fp11) (fp20, fp21)
| conflict_fps_01: forall fp10 fp11 fp20 fp21,
    FP.conflict fp10 fp21 -> conflict_fps (fp10, fp11) (fp20, fp21).

(** The definition of data-race in non-preemptive.
Configuration S is racy if two different threads of S are predicted to generated conflicting footprints and at least one thread is not predicted inside atomic block.
*)
Inductive np_race_config {ge: GlobEnv.t} : @ProgConfig ge -> Prop :=
  NP_Race_config: forall s t1 fp10 fp11 t2 fp20 fp21,
    t1 <> t2 ->
    np_predict s t1 fp10 fp11 ->
    np_predict s t2 fp20 fp21 ->
    conflict_fps (fp10, fp11) (fp20, fp21) ->
    np_race_config s.

(** [np_star_race_config] requires the prediction be made at switching points. *)
Inductive np_star_race_config {ge: GlobEnv.t} : @ProgConfig ge -> Prop :=
(* predict at switch point *)
| NP_Race_point: forall s l fp s',
    np_step s l fp s' ->
    l <> tau ->
    np_race_config s' ->
    np_star_race_config s
(* or progress *)
| NP_Race_progress: forall s l fp s',
    np_step s l fp s' ->
    np_star_race_config s' ->
    np_star_race_config s.

(** Either the prediction is made exactly after the initialization, or it is made after switching points. *)
Inductive np_race_prog {NL: nat} {L: @langs NL} : prog L -> Prop :=
(* race at initial program point *)
| NPRace_init: forall p gm ge s t,
    init_config p gm ge s t ->
    np_race_config s ->
    np_race_prog p
(* race at program point after some np_steps *)
| NPRace_plus: forall p gm ge s t,
    init_config p gm ge s t ->
    np_star_race_config s ->
    np_race_prog p.

Definition npdrf {NL} {L} p: Prop := ~ @np_race_prog NL L p.



  
    
