Require Import InteractionSemantics GAST GlobUSim NPSemantics NPDRF.
Require Import ETrace GlobDefs Footprint Injections GSimDefs GlobSim USimDRF Classical Init.
(** * Simulation implies Refinement *)

(** This file defines the lemma [USim_NPDRF], which says when 
    source program simulates target program ( [S > T] ), and
    source program is data-race-free ([NPDRF(S)]), then
    target program is data-race-free ([NPDRF(T)]). *)
Local Notation "'[[' thdp ',' t ',' m ',' b ']]'" :=
  ({| thread_pool:= thdp; cur_tid:= t; gm:= m; atom_bit:= b |})
    (at level 70, right associativity).

Local Notation "'[[' thdp ',' t ',' m ',' b ']]@' G " :=
  (Build_ProgConfig G thdp t m b) (at level 70, right associativity).

Definition npdrfpc {ge}(pc:@ProgConfig ge):Prop:=
  ~ np_race_config pc /\ ~ np_star_race_config pc.

(** * NPDRF Preservation(Lemma 6):
In the rule of data race, we always load the program P and the state \sigma to the world W first. Here spc is the source world and tpc is the target world. For convenience we write the load step explicitly.
 *)
Lemma USim_NPDRF_Config:
  forall NL L sprog tprog mu sgm sge spc t tgm tge tpc,
    (** Source program simulates and target program*)
    @GlobUSim NL L sprog tprog->
    (** initM(mu,GE,sgm,tgm) the relation of initial memory *)
    InitRel mu sge tge sgm tgm->
    (** load step: (sprog,sgm) ==load==> spc *)
    init_config sprog sgm sge spc t->
    (** load step: (tprog,tgm) ==load==> tpc *)
    init_config tprog tgm tge tpc t->
    (** source program configuration is data-race-free*)
    npdrfpc spc->
    (** Conclusion: target program configuration is data-race-free*)
    npdrfpc tpc.
Proof.
  unfold npdrfpc;intros.
  apply and_not_or in H3.
  apply not_or_and. intro. contradict H3.
  assert(ThreadPool.inv spc.(thread_pool)). inversion H1;subst;eapply ThreadPool.init_inv;eauto.
  assert(ThreadPool.inv tpc.(thread_pool)). inversion H2;subst;eapply ThreadPool.init_inv;eauto.
  assert(t=cur_tid tpc). inversion H2;auto. subst.
  destruct H4.
  + apply np_race_config_np_race_config_base_equiv in H4;auto.
    assert(@np_race_config_0 NL L tgm tge tprog tpc).
    split;auto. 
    eapply GUSim_nprace_preservation_2' in H6;eauto.
    destruct H6 as (_&?). eapply np_race_config_np_race_config_base_equiv in H6;eauto.
  + assert(wdtge:GlobEnv.wd tge).  inversion H2;subst. inversion H6;auto.
    eapply np_star_race_config_np_race_config_1_equiv in H4 as (l&fp&o&pc1&pc2&?&?);eauto.
    edestruct H as (I&ord&match_state&i&Usim&matched);eauto.
    eapply GUSim_star_progress in H4 as ?;eauto.
    destruct H7 as (?&?&?&?&?&?&?&?).
    eapply GUSim_nprace_preservation_1 in H7 as ?;try apply H6;eauto.
    destruct H9 as (?&?&?&?&?).
    right.
    eapply np_star_race_config_np_race_config_1_equiv ;eauto.
    inversion H1;subst. inversion H11;auto.
    eapply tau_star_to_star in H9 as [].
    eapply cons_star_star in H9;eauto.
    do 6 eexists;eauto.
Qed. 