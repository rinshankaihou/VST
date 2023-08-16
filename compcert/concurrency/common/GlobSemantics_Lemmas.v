Require Import Coqlib Maps AST Values Footprint GMemory InteractionSemantics GAST GlobDefs ETrace Blockset Injections Coq.Lists.Streams GlobSemantics MemAux.

Definition GE_mod_wd (GE: GlobEnv.t): Prop:=
  let: modules := GlobEnv.modules GE in
  forall i,
    let: Mod := modules i in
    let: lang := ModSem.lang Mod in
    wd lang.
Lemma get_top_in_cs:
  forall GE (thdp: @ThreadPool.t GE) i c,
    ThreadPool.get_top thdp i = Some c ->
    exists cs,
      ThreadPool.get_cs thdp i = Some cs /\
      CallStack.top cs = Some c.
Proof.
  intros.
  unfold ThreadPool.get_top in H.
  destruct (ThreadPool.get_cs thdp i); try discriminate.
  exists t; split; auto.
Qed.

Lemma GE_mod_wd_forward:
  forall GE pc l fp pc',
    GE_mod_wd GE ->
    @glob_step GE pc l fp pc' ->
    GMem.forward (gm pc) (gm pc').
Proof.
  inversion 2; subst; simpl in *; try apply GMem.forward_refl.
  destruct c; subst; simpl in *.
  specialize (H i).
  apply (step_forward _ H) in H_core_step; auto.
Qed.

Lemma GE_mod_wd_star_forward:
  forall GE (pc pc': @ProgConfig GE) fp,
    GE_mod_wd GE ->
    tau_star glob_step pc fp pc' ->
    GMem.forward (gm pc) (gm pc').
Proof.
  induction 2.
  apply GMem.forward_refl.
  eapply GMem.forward_trans; eauto.
  eapply GE_mod_wd_forward; eauto.
Qed.

Lemma GE_mod_wd_plus_forward:
  forall GE (pc pc': @ProgConfig GE) fp,
    GE_mod_wd GE ->
    tau_plus glob_step pc fp pc' ->
    GMem.forward (gm pc) (gm pc').
Proof.
  induction 2.
  eapply GE_mod_wd_forward; eauto.
  eapply GMem.forward_trans; eauto.
  eapply GE_mod_wd_forward; eauto.
Qed.

Lemma GE_mod_wd_tp_inv:
  forall GE pc l fp pc',
    GlobEnv.wd GE -> 
    ThreadPool.inv (thread_pool pc) ->
    @glob_step GE pc l fp pc' ->
    ThreadPool.inv (thread_pool pc').
Proof.
  intros; destruct pc, pc'.
  inversion H1; clear H1; subst; simpl in *.
  (* core step *)
  { eapply ThreadPool.upd_top_inv; eauto. }
  (* call ext *)
  { eapply ThreadPool.push_inv; eauto. }
  (* return *)
  { eapply ThreadPool.upd_top_inv.
    Focus 2. eauto.
    eapply ThreadPool.pop_inv; eauto. eauto. eauto. }
  (* thread halt *)
  { eapply ThreadPool.pop_inv; eauto. }
  (* primitives *)
  eapply ThreadPool.upd_top_inv; eauto.
  eapply ThreadPool.upd_top_inv; eauto.
  eapply ThreadPool.upd_top_inv; eauto.
  eauto.
Qed.

Lemma GE_mod_wd_plus_tp_inv:
  forall GE pc fp pc',
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    tau_plus (@glob_step GE) pc fp pc' ->
    ThreadPool.inv (thread_pool pc').
Proof.
  intros.
  induction H1. eapply GE_mod_wd_tp_inv; eauto.
  eapply GE_mod_wd_tp_inv in H1; eauto.
Qed.
Lemma GE_mod_wd_star_tp_inv:
  forall GE pc fp pc',
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    tau_star (@glob_step GE) pc fp pc' ->
    ThreadPool.inv (thread_pool pc').
Proof.
  intros.
  induction H1. auto.
  eapply GE_mod_wd_tp_inv in H1; eauto.
Qed.
Lemma GE_mod_wd_tp_inv_mem:
  forall GE pc l fp pc',
    GE_mod_wd GE ->
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    ThreadPool.inv_mem (thread_pool pc) (gm pc) ->
    @glob_step GE pc l fp pc' ->      
    ThreadPool.inv_mem (thread_pool pc') (gm pc').
Proof.
  intros.
  destruct H1,H2.
  inv H3;simpl in *;constructor;intros.
  {
    inversion H_tp_upd; destruct c; subst; simpl in *.
    pose proof H1. apply tp_valid_freelist_free in H1.
    
    (* / need lemma for blockset and no_overlap *)
    intros b n0 H'. specialize (H1 b n0 H').
    intro. apply H1.
    unfold Bset.belongsto in *.
    unfold valid_block_bset in *.
    specialize (cs_inv _ _ H2). destruct cs_inv.
    specialize (fid_valid {| Core.i := i0; Core.c := c; Core.sg := sg; Core.F := F |}).
    simpl in fid_valid. clear fid_disjoint.
    apply (step_local_eff _ (H i0)) in H_core_step.
    eapply LEffect_local_alloc in H_core_step; eauto.
    rename H_core_step into H_in_fl.
    destruct H_in_fl as (n0'&H_in_fl). subst b.

    unfold FLists.get_tfl in H_in_fl.
    assert (FLists.get_tfid (GlobEnv.freelists GE) i n <> F).
    { apply get_top_in_cs in H_tp_core.
      destruct H_tp_core as (cs0&H''&H''').
      rewrite H'' in H2. inversion H2. subst. clear H2.
      unfold CallStack.top in H'''. destruct cs; try discriminate.
      inversion H'''. subst. clear H'''.
      simpl in *. clear H_tp_upd H_core_upd fid_belongsto tp_valid_freelist_free H3.
      specialize (fid_valid (or_introl eq_refl)).
      destruct fid_valid as (nF&HnF&HF). subst F.
      destruct (peq i t).
      { subst. apply (FLists.thread_fl_norep _ (GlobEnv.wd_fl _ H0)); Lia.lia. }
      { apply (FLists.thread_fl_disj _ (GlobEnv.wd_fl _ H0)); auto. }
    }
    exfalso.
    pose proof (FLists.flist_disj _ (GlobEnv.wd_fl _ H0) _ _ H6).
    destruct H7. eapply H7; eauto.
  }
  (* call *)
  { apply tp_valid_freelist_free.
    unfold ThreadPool.push in H_tp_push.
    destruct ((ThreadPool.content thdp)!!t); try discriminate.
    inversion H_tp_push. subst. simpl in *.
    destruct peq; subst; Lia.lia. }
  (* *)
  { apply tp_valid_freelist_free.
    unfold ThreadPool.pop in H_tp_pop.
    destruct ((ThreadPool.content thdp)!!t); try discriminate.
    destruct (CallStack.pop t0); try discriminate.
    inversion H_tp_pop; inversion H_tp_upd. subst; simpl in *; auto.
  }
  { apply tp_valid_freelist_free.
    unfold ThreadPool.pop in H_tp_pop.
    destruct ((ThreadPool.content thdp) !! t); try discriminate.
    destruct (CallStack.pop t0); try discriminate.
    inversion H_tp_pop. subst. auto.
  }
  { apply tp_valid_freelist_free.
    inversion H_tp_upd; subst. auto.
  }
  { apply tp_valid_freelist_free.
    inversion H_tp_upd; subst. auto.
  }
  { apply tp_valid_freelist_free.
    inversion H_tp_upd; subst. auto.
  }
  eauto.
Qed.

Lemma GE_mod_wd_star_tp_inv_mem:
  forall GE pc fp pc',
    GE_mod_wd GE ->
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    ThreadPool.inv_mem (thread_pool pc) (gm pc) ->
    tau_star (@glob_step GE) pc fp pc' ->      
    ThreadPool.inv_mem (thread_pool pc') (gm pc').
Proof.
  intros.
  induction H3; auto.
  apply IHtau_star; auto.
  eapply GE_mod_wd_tp_inv; eauto.
  eapply GE_mod_wd_tp_inv_mem; eauto.
Qed.

Lemma GE_mod_wd_plus_tp_inv_mem:
  forall GE pc fp pc',
    GE_mod_wd GE ->
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    ThreadPool.inv_mem (thread_pool pc) (gm pc) ->
    tau_plus (@glob_step GE) pc fp pc' ->      
    ThreadPool.inv_mem (thread_pool pc') (gm pc').
Proof.
  intros.
  induction H3. eapply GE_mod_wd_tp_inv_mem; eauto.
  apply IHtau_plus; auto.
  eapply GE_mod_wd_tp_inv; eauto.
  eapply GE_mod_wd_tp_inv_mem; eauto.
Qed.
