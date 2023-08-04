Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics NPSemantics TypedSemantics.

Require Import DRF USimDRF NPDRF .

Require Import FPLemmas PRaceLemmas Init SmileReorder ConflictReorder Init DRFLemmas RefineEquiv.

Require Import Classical.

(** * Equivalence on safety and DRF definitions between preemptive and non-preemptive semantics *)

(** This file consists of results on np-semantics:
    - [Safe(S)] <=> [NPSafe(S)]
    - [Safe(S)] /\ [WD_langs(S)] => ([NPDRF(S)] <=> [DRF(S)]) *)

Lemma drf_drfpc:
  forall NL L p gm ge pc t,
    @init_config NL L p gm ge pc t->
    drf p ->
    drfpc pc.
Proof.
  unfold drf,drfpc;intros.
  intro. contradict H0.
  unfold race_prog.
  eexists;eauto.
Qed.

Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).

Lemma DRF_NP_Refine_Config:
  forall NL L mu su tu e sgm sge spc st tgm tge tpc tt,
    @wd_langs NL L su ->
    @wd_langs NL L tu ->
    (forall t : tid, DRFLemmas.pc_valid_tid tpc t -> np_safe_config ({-|tpc, t})) ->
    InitRel mu sge tge sgm tgm->
    init_config (su,e) sgm sge spc st->
    init_config (tu,e) tgm tge tpc tt->
    drf (su,e)->
    drfpc tpc->
    np_prog_refine (su,e)(tu,e)->
    config_refine tpc spc.
Proof.
  apply DRF_NP_Refine_Config_Proof;auto.
  apply init_free.
Qed.

(** ** Equivalence between preemptive and non-preemptive safety definition *)
Lemma Safe_NPSafe:
  forall NL L cus e,
    @wd_langs NL L cus -> 
    safe_prog (cus, e) ->
    np_safe_prog (cus, e).
Proof.
  intros.
  econstructor.
  intros.
  apply H0 in H1 as ?.
  apply Safe_eq.
  unfold safe_state in *.
  intros.
  intro.
  assert(t=cur_tid s). inversion H1;auto. subst.
  eapply star_abort_np_p in H4;eauto.
  Focus 2. econstructor;eauto.
  Esimpl;eauto.

  apply np_star_glob_star in H3 as [].
  eapply H2 in H3;eauto.
Qed.

Lemma NPSafe_Safe:
  forall NL L cus e,
    @wd_langs NL L cus ->
    np_safe_prog (cus, e) ->
    npdrf (cus, e) ->
    safe_prog (cus, e).
Proof.
  apply NPSafe_Safe';auto.
Qed.


Lemma NPDRF_config:
  forall NL L p gm ge pc t,
    npdrf p->
    @init_config NL L p gm ge pc t->
    (
      forall t,
        GSimDefs.pc_valid_tid pc t->
        npdrfpc ({-|pc,t})).
Proof.    
  intros.
  assert(t=cur_tid pc). inversion H0;auto. subst.
  eapply init_free in H0;eauto.
  unfold npdrf in H. unfold npdrfpc.
  apply not_or_and.
  intro.
  contradict H. destruct H2.
  econstructor;eauto.
  econstructor 2;eauto.
Qed.

(** ** Equivalence between DRF definitions between preemptive and non-preemptive program configurations *)
Lemma NPDRF_DRF_Config:
  forall NL L p gm ge pc t,
    @wd_langs NL L (fst p) ->
    init_config p gm ge pc t ->
    (forall t, GSimDefs.pc_valid_tid pc t-> np_safe_config ({-|pc,t})) ->
    (forall t, GSimDefs.pc_valid_tid pc t -> npdrfpc ({-|pc,t})) ->
    drfpc pc.
Proof.
  intros. assert(t=cur_tid pc). inversion H0;auto. subst.
  apply init_property_1_alt in H0 as ?.
  specialize (H1 (cur_tid pc) H3) as ?.
  unfold npdrfpc in H2. unfold drfpc.
  intro. 
  assert(invpc ge pc).
  inversion H0;subst. eapply ThreadPool.init_inv;eauto.
  assert(atom_bit pc = O).
  inversion H0;subst. auto.
  apply init_config_GE_wd in H0 as ?.
  specialize (@lang_wd_mod_wd _ _ _ _ _ _ _ H H0) as ?.
  
  apply p_star_race_np_star_race in H5;auto.
  destruct H5.
  eapply H2 in H3;eauto. destruct H3;auto.  rewrite pc_cur_tid in H3;auto.
  Hsimpl. apply swstar_l in H5.
  destruct H5. subst. eapply H2 in H3 as [];eauto. rewrite pc_cur_tid in H5;auto.
  destruct H5. assert(Init.pc_valid_tid pc (cur_tid x)). inversion H5;subst;split;auto.
  apply H2 in H12 as []. assert(({-|pc,cur_tid x}) = x). inversion H5;auto.
  rewrite H14 in H13;auto.
  split;auto. apply Safe_eq;auto. rewrite pc_cur_tid in H4;auto.
  intros.
  apply H1 in H10.
  eapply Safe_eq;eauto.
Qed.

Lemma DRF_NPDRF_Config:
  forall NL L p gm ge pc t,
    @wd_langs NL L (fst p) ->
    init_config p gm ge pc t ->
    drfpc pc ->
    npdrfpc pc.
Proof.
  unfold drfpc,npdrfpc.
  pose proof NPRace_Race_Config.
  intros.
  apply not_or_and.
  eauto.
Qed.
