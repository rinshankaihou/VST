Require Import EqdepFacts.
Require Import Axioms Coqlib Maps List.
Require Import Blockset Footprint GMemory MemAux InteractionSemantics
        ETrace GlobDefs NPSemantics
        Injections LDSimDefs LDSim AuxLDSim GSimDefs GlobDSim GDefLemmas.

Local Notation "'<<' i ',' c ',' sg ',' F '>>'" :=
  {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|}
    (at level 60, right associativity).

Local Notation "'[[' thdp ',' t ',' m ',' b ']]@' G " :=
  (Build_ProgConfig G thdp t m b) (at level 70, right associativity).

Local Notation "'[[' thdp ',' t ',' m ',' b ']]'" :=
  ({| thread_pool:= thdp; cur_tid:= t; gm:= m; atom_bit:= b |})
    (at level 70, right associativity).

Local Notation " GE '||-' pc1 '=<' l '|' fp '>=>>' pc2 " :=
  (@np_step GE pc1 l fp pc2) (at level 80, right associativity).

Lemma freelist_free_unchg_freelist:
  forall m m' fl,
    no_overlap fl (valid_block_bset m) ->
    no_overlap fl (valid_block_bset m') ->            
    unchg_freelist fl m m'.
Proof.
  clear. intros.
  constructor; intros.
  { inversion H1. split; intro; [exploit H| exploit H0]; eauto; try contradiction. }
  { exfalso. inversion H1. exploit H; eauto. }
  { exfalso. inversion H1. exploit H; eauto. eapply Memperm_validblock; eauto. }
Qed.

(** Well defined properties for GE *)
Definition GE_mod_wd (GE: GlobEnv.t): Prop:=
  let: modules := GlobEnv.modules GE in
  forall i,
    let: Mod := modules i in
    let: lang := ModSem.lang Mod in
    wd lang.

(** lemmas derived from GE_mod_wd *)
(** forward *)
Lemma GE_mod_wd_forward:
  forall GE pc l fp pc',
    GE_mod_wd GE ->
    GE ||- pc =<l|fp>=>> pc' ->
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
    ETrace.tau_star np_step pc fp pc' ->
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
    ETrace.tau_plus np_step pc fp pc' ->
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
    @np_step GE pc l fp pc' ->
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
  (* all halt *)
  { eapply ThreadPool.pop_inv; eauto. }
  (* primitives *)
  eapply ThreadPool.upd_top_inv; eauto.
  eapply ThreadPool.upd_top_inv; eauto.
  eapply ThreadPool.upd_top_inv; eauto.
Qed.

Lemma GE_mod_wd_plus_tp_inv:
  forall GE pc fp pc',
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    ETrace.tau_plus (@np_step GE) pc fp pc' ->
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
    ETrace.tau_star (@np_step GE) pc fp pc' ->
    ThreadPool.inv (thread_pool pc').
Proof.
  intros.
  induction H1. auto.
  eapply GE_mod_wd_tp_inv in H1; eauto.
Qed.

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

Lemma GE_mod_wd_tp_inv_mem:
  forall GE pc l fp pc',
    GE_mod_wd GE ->
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    ThreadPool.inv_mem (thread_pool pc) (gm pc) ->
    @np_step GE pc l fp pc' ->      
    ThreadPool.inv_mem (thread_pool pc') (gm pc').
Proof.
  intros. destruct H1, H2.
  destruct H3; subst; simpl in *; constructor; intros.
  (* core-step *)
  { inversion H_tp_upd; destruct c; subst; simpl in *.
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
      { subst. apply (FLists.thread_fl_norep _ (GlobEnv.wd_fl _ H0)); omega. }
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
    destruct peq; subst; omega. }
  (* *)
  { apply tp_valid_freelist_free.
    unfold ThreadPool.pop in H_tp_pop.
    destruct ((ThreadPool.content thdp)!!t); try discriminate.
    destruct (CallStack.pop t0); try discriminate.
    inversion H_tp_pop; inversion H_tp_upd. subst; simpl in *; auto.
  }
  (* *)
  { apply tp_valid_freelist_free.
    unfold ThreadPool.pop in H_tp_pop.
    destruct ((ThreadPool.content thdp) !! t); try discriminate.
    destruct (CallStack.pop t0); try discriminate.
    inversion H_tp_pop. subst. auto.
  }
  (* *)
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
Qed.

Lemma GE_mod_wd_star_tp_inv_mem:
  forall GE pc fp pc',
    GE_mod_wd GE ->
    GlobEnv.wd GE ->
    ThreadPool.inv (thread_pool pc) ->
    ThreadPool.inv_mem (thread_pool pc) (gm pc) ->
    ETrace.tau_star (@np_step GE) pc fp pc' ->      
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
    ETrace.tau_plus (@np_step GE) pc fp pc' ->      
    ThreadPool.inv_mem (thread_pool pc') (gm pc').
Proof.
  intros.
  induction H3. eapply GE_mod_wd_tp_inv_mem; eauto.
  apply IHtau_plus; auto.
  eapply GE_mod_wd_tp_inv; eauto.
  eapply GE_mod_wd_tp_inv_mem; eauto.
Qed.


Lemma GE_mod_wd_star_unchg:
  forall GE ix fl c m fp c' m',
    GE_mod_wd GE ->
    InteractionSemantics.star
      (step (ModSem.lang (GlobEnv.modules GE ix)) (ModSem.Ge (GlobEnv.modules GE ix)) fl)
      c m fp c' m' ->
    GMem.unchanged_on (fun b ofs => ~ Locs.belongsto (FP.locs fp) b ofs) m m'.
Proof.
  clear. induction 2.
  apply GMem.unchanged_on_refl.
  apply step_local_eff, LEffect_unchanged_on in H0; auto.
  eapply GMem.unchanged_on_trans with (m2:= m'); eauto.
  eapply GMem.unchanged_on_implies; eauto.
  clear. intros. simpl. intro. apply H; clear H. solv_belongsto.
  eapply GMem.unchanged_on_implies; eauto.
  clear. intros. simpl. intro. apply H; clear H. solv_belongsto.
Qed.

(** This section deals with invariants on global environments *)
Section GEInvs.
  Context (SGE TGE: GlobEnv.t).

  Definition mod_ldsim sMod tMod sfl tfl mu:=
    exists index index_order match_state,
      let: sl := ModSem.lang sMod in
      let: sge := ModSem.ge sMod in
      let: sGe := ModSem.Ge sMod in
      let: tl := ModSem.lang tMod in
      let: tge := ModSem.ge tMod in
      let: tGe := ModSem.Ge tMod in
      forall fnid argS argT score,
        G_args (SharedSrc mu) argS ->
        arg_rel (inj mu) argS argT ->
        init_core sl sGe fnid argS = Some score ->
        exists tcore,
          init_core tl tGe fnid argT = Some tcore /\
          (forall sm tm,
              init_gmem sl sge sm ->
              init_gmem tl tge tm ->
              local_init_rel mu sfl sm tfl tm ->
              (forall sm' tm',
                  HLRely sfl tfl mu sm sm' tm tm' ->
                  exists i,
                    config_ldsim_aux index index_order sfl tfl sGe tGe sge tge match_state /\
                    match_state true i mu FP.emp FP.emp (score, sm') (tcore, tm'))).
  
  Definition GE_mod_sim (mu: Mu): Prop :=
    forall fnid i_xs sfid tfid,
      GlobEnv.get_mod SGE fnid = Some i_xs ->
      exists i_xt,
        GlobEnv.get_mod TGE fnid = Some i_xt
        /\
        (let: sMod := (GlobEnv.modules SGE) i_xs in
         let: tMod := (GlobEnv.modules TGE) i_xt in
         let: sfl := (FLists.get_fl (GlobEnv.freelists SGE) sfid) in
         let: tfl := (FLists.get_fl (GlobEnv.freelists TGE) tfid) in
         mod_ldsim sMod tMod sfl tfl mu).

End GEInvs.



Section StateInvs.
  (* the initialized global environment *)
  Context (SGE TGE: GlobEnv.t).
  (* the initial memories and injection *)
  Context (sm_init tm_init: gmem).
  Context (mu: Mu).
  (* hypothesis on initial memories *)
  Hypothesis (H_init_sm: GlobEnv.init_mem SGE sm_init).
  Hypothesis (H_init_tm: GlobEnv.init_mem TGE tm_init).
  Hypothesis (H_wd_mu: Bset.inject_weak (inj mu) (SharedSrc mu) (SharedTgt mu)).
  Hypothesis (H_mem_inj: GMem.Binject_weak (inj mu) sm_init tm_init).
  Hypothesis (H_valid_SharedSrc: forall b, GMem.valid_block sm_init b <-> SharedSrc mu b).
  Hypothesis (H_valid_SharedTgt: forall b, GMem.valid_block tm_init b <-> SharedTgt mu b).
  Hypothesis (H_RC_init_sm: MemClosures.reach_closed sm_init (SharedSrc mu)).
  Hypothesis (H_RC_init_tm: MemClosures.reach_closed tm_init (SharedTgt mu)).
  (* modules are simulated *)
  Hypothesis (HGE_sim: GE_mod_sim SGE TGE mu).
  (* freelists disjoint with mu *)
  Hypothesis (Hfl_mu_disj_src: forall fi,
                 no_overlap (FLists.get_fl (GlobEnv.freelists SGE) fi) (SharedSrc mu)).
  Hypothesis (Hfl_mu_disj_tgt: forall fi,
                 no_overlap (FLists.get_fl (GlobEnv.freelists TGE) fi) (SharedTgt mu)).
  (* freelists are free in initial memory *)
  Hypothesis (Hfl_free_src: forall fi,
                 no_overlap (FLists.get_fl (GlobEnv.freelists SGE) fi) (valid_block_bset sm_init)).
  Hypothesis (Hfl_free_tgt: forall fi,
                 no_overlap (FLists.get_fl (GlobEnv.freelists TGE) fi) (valid_block_bset tm_init)).
  (* GEs are well-defined *)
  (* * Langauges are well-defined *)
  Hypothesis GE_mod_wd_src: GE_mod_wd SGE.
  Hypothesis GE_mod_wd_tgt: GE_mod_wd TGE.
  (* * GEs are properly initialized *)
  Hypothesis GE_wd_src: GlobEnv.wd SGE.
  Hypothesis GE_wd_tgt: GlobEnv.wd TGE.

  
  (** wrapping local config sim to sim on (Core.t * gmem) *)

  Record Core_sim_current (mu: Mu) (index: Type) (index_order: index -> index -> Prop)
         (i: index) (fpS fpT: FP.t)
         (sCore: @Core.t SGE) (sm:gmem) (tCore: @Core.t TGE) (tm: gmem) : Prop :=
    {
      core_config_sim_current:
        (* get lang, core, ge, Ge from Core and GE *)
        let: i_xs := Core.i sCore in
        let: score := Core.c sCore in
        let: sMod := GlobEnv.modules SGE i_xs in
        let: sl := ModSem.lang sMod in
        let: sG := ModSem.Ge sMod in
        let: sge := ModSem.ge sMod in
        
        let: i_xt := Core.i tCore in
        let: tcore := Core.c tCore in
        let: tMod := GlobEnv.modules TGE i_xt in
        let: tl := ModSem.lang tMod in
        let: tG := ModSem.Ge tMod in
        let: tge := ModSem.ge tMod in

        (* get freelists from Core and GE *)
        let: sfid := Core.F sCore in
        let: sfls := GlobEnv.freelists SGE in
        let: sfl := FLists.get_fl sfls sfid in

        let: tfid := Core.F tCore in
        let: tfls := GlobEnv.freelists TGE in
        let: tfl := FLists.get_fl tfls tfid in
        exists R, @config_ldsim_aux sl tl index index_order sfl tfl sG tG sge tge R /\
             R true i mu fpS fpT (score, sm) (tcore, tm)
      ;

      sg_eq_current:
        Core.sg sCore = Core.sg tCore
      ;
    }.

  Record Core_sim_block (mu: Mu) (index: Type) (index_order: index -> index -> Prop)
         (sm0 tm0: gmem)
         (sCore: @Core.t SGE) (sm: gmem) (tCore: @Core.t TGE) (tm: gmem) : Prop :=
    {
      core_config_sim_block:
        (* get lang, core, ge, Ge from Core and GE *)
        let: i_xs := Core.i sCore in
        let: score := Core.c sCore in
        let: sMod := GlobEnv.modules SGE i_xs in
        let: sl := ModSem.lang sMod in
        let: sG := ModSem.Ge sMod in
        let: sge := ModSem.ge sMod in
        
        let: i_xt := Core.i tCore in
        let: tcore := Core.c tCore in
        let: tMod := GlobEnv.modules TGE i_xt in
        let: tl := ModSem.lang tMod in
        let: tG := ModSem.Ge tMod in
        let: tge := ModSem.ge tMod in

        (* get freelists from Core and GE *)
        let: sfid := Core.F sCore in
        let: sfls := GlobEnv.freelists SGE in
        let: sfl := FLists.get_fl sfls sfid in

        let: tfid := Core.F tCore in
        let: tfls := GlobEnv.freelists TGE in
        let: tfl := FLists.get_fl tfls tfid in
        forall sm' tm', HLRely sfl tfl mu sm0 sm' tm0 tm' ->
                   exists R, @config_ldsim_aux sl tl index index_order sfl tfl sG tG sge tge R /\
                        exists i, R true i mu FP.emp FP.emp (score, sm') (tcore, tm');

      mem_rely_src_block:
        (* get freelists from Core and GE *)
        let: sfid := Core.F sCore in
        let: sfls := GlobEnv.freelists SGE in
        let: sfl := FLists.get_fl sfls sfid in
        GMem.forward sm0 sm /\
        unchg_freelist sfl sm0 sm
      ;
      
       mem_rely_tgt_block:
        (* get freelists from Core and GE *)
        let: tfid := Core.F tCore in
        let: tfls := GlobEnv.freelists TGE in
        let: tfl := FLists.get_fl tfls tfid in
        GMem.forward tm0 tm /\
        unchg_freelist tfl tm0 tm
      ;
                       
      sg_eq_block:
        Core.sg sCore = Core.sg tCore
      ;
    }.
      
         
  Record Core_sim_tail (beta: bool) (mu: Mu) (index: Type) (index_order: index -> index -> Prop)
         (i: index) (fpS fpT: FP.t) (sm0 tm0: gmem)
         (sCore: @Core.t SGE) (sm: gmem) (tCore: @Core.t TGE) (tm: gmem) 
    : Prop :=
    {
      (** The caller cores *)
      core_config_sim:
        beta = false ->
        (* get lang, core, ge, Ge from Core and GE *)
        let: i_xs := Core.i sCore in
        let: score := Core.c sCore in
        let: sMod := GlobEnv.modules SGE i_xs in
        let: sl := ModSem.lang sMod in
        let: sG := ModSem.Ge sMod in
        let: sge := ModSem.ge sMod in
        
        let: i_xt := Core.i tCore in
        let: tcore := Core.c tCore in
        let: tMod := GlobEnv.modules TGE i_xt in
        let: tl := ModSem.lang tMod in
        let: tG := ModSem.Ge tMod in
        let: tge := ModSem.ge tMod in

        (* get freelists from Core and GE *)
        let: sfid := Core.F sCore in
        let: sfls := GlobEnv.freelists SGE in
        let: sfl := FLists.get_fl sfls sfid in

        let: tfid := Core.F tCore in
        let: tfls := GlobEnv.freelists TGE in
        let: tfl := FLists.get_fl tfls tfid in
        
        (* R is a local simulation relation *)
        exists R, @config_ldsim_aux sl tl index index_order sfl tfl sG tG sge tge R /\
             R false i mu fpS fpT (score, sm0) (tcore, tm0)
      ;
      

      mem_rely_src:
        (* get freelists from Core and GE *)
        let: sfid := Core.F sCore in
        let: sfls := GlobEnv.freelists SGE in
        let: sfl := FLists.get_fl sfls sfid in
        GMem.forward sm0 sm /\
        unchg_freelist sfl sm0 sm
      ;
      
      mem_rely_tgt:
        (* get freelists from Core and GE *)
        let: tfid := Core.F tCore in
        let: tfls := GlobEnv.freelists TGE in
        let: tfl := FLists.get_fl tfls tfid in
        GMem.forward tm0 tm /\
        unchg_freelist tfl tm0 tm
      ;
      
      sg_eq:
        Core.sg sCore = Core.sg tCore
      ;
    }.
  

  Inductive CallStack_sim_tail (mu: Mu):
            @CallStack.t SGE -> gmem -> @CallStack.t TGE -> gmem -> Prop :=
  | sim_emp: forall sm tm, CallStack_sim_tail mu CallStack.emp_cs sm CallStack.emp_cs tm
  | sim_cons: forall sm0 tm0 sm tm scs tcs index index_order i sCore tCore,
      Core_sim_tail false mu index index_order i FP.emp FP.emp sm0 tm0 sCore sm tCore tm ->
      CallStack_sim_tail mu scs sm tcs tm ->
      CallStack_sim_tail mu (sCore::scs) sm (tCore::tcs) tm.
  
  Inductive CallStack_sim_cur (index: Type) (index_order: index -> index -> Prop) (i: index)
            (mu: Mu) :
    FP.t -> FP.t -> @CallStack.t SGE -> gmem -> @CallStack.t TGE -> gmem -> Prop :=
  | cur_emp:
      forall sm tm (Hwf: well_founded index_order),
        CallStack_sim_cur index index_order i mu FP.emp FP.emp nil sm nil tm
  | top_sim:
      forall fpS fpT sCore sm tCore tm scs tcs,
        Core_sim_current mu index index_order i fpS fpT sCore sm tCore tm ->
        CallStack_sim_tail mu scs sm tcs tm ->
        CallStack_sim_cur index index_order i mu fpS fpT (sCore::scs) sm (tCore::tcs) tm.

  Inductive CallStack_sim_other (mu: Mu) :
    @CallStack.t SGE -> gmem -> @CallStack.t TGE -> gmem -> Prop :=
  | other_emp:
      forall sm tm,
      CallStack_sim_other mu nil sm nil tm
  | other_sim:
      forall index index_order sm0 tm0 sCore sm tCore tm scs tcs,
        Core_sim_block mu index index_order sm0 tm0 sCore sm tCore tm ->
        CallStack_sim_tail mu scs sm tcs tm ->
        CallStack_sim_other mu (sCore::scs) sm (tCore::tcs) tm.
      
  Lemma CallStack_sim_cur_order_wf:
    forall mu index index_order i fpS fpT scs sm tcs tm,
      CallStack_sim_cur index index_order i mu fpS fpT scs sm tcs tm ->
      well_founded index_order.
  Proof.
    intros. inversion H. auto.
    inversion H0.
    destruct core_config_sim_current0 as (R&Hsim&Hmatch).
    destruct Hsim; auto.
  Qed.

  
  (** The global index *)
  Inductive glob_index: Type :=
  | i_wrap : forall (index: Type) (order: index -> index -> Prop) (wf: well_founded order),
      index -> glob_index.

  Inductive glob_order: glob_index -> glob_index -> Prop :=
  | g_order: forall (index: Type) (order: index -> index -> Prop) (wf: well_founded order) i1 i2,
      order i1 i2 ->
      glob_order (i_wrap index order wf i1) (i_wrap index order wf i2).

  Lemma glob_order_eq:
    forall i1 i2,
      glob_order i1 i2 ->
      let (index, order, wf, i2') := i2 in
      exists i1',
        i1 = i_wrap index order wf i1' /\
        order i1' i2'.
  Proof.
    clear. intros. inversion H.
    repeat eexists ; eauto.
  Qed.
      
  Lemma glob_order_wf: well_founded glob_order.
  Proof.
    clear. intros i.
    constructor. intros j Horder.
    inversion Horder; subst.
    apply wf in H. clear Horder.
    induction H.
    constructor; intros.
    destruct (glob_order_eq _ _ H1) as (y' & Hy' & Horder).
    subst. apply H0. auto.
  Qed.
  



  (** Global invariant *)
  (** fp0 are the accumulated footprints since the last switch point, 
      and fp are footprints recorded by current module local simulation *)
  Record Config_sim (i: glob_index)
         (fpS fpT fpS0 fpT0: FP.t) (spc: @ProgConfig SGE) (tpc: @ProgConfig TGE) : Prop :=
    {
      (** mem_forward *)
      curmem_forward_src:
        let: sm := gm spc in
        GMem.forward sm_init sm;
      curmem_forward_tgt:
        let: tm := gm tpc in
        GMem.forward tm_init tm;
      
      (** freelists are free in current memory *)
      fl_inv_src:
        let: stp := thread_pool spc in
        let: sm := gm spc in        
        ThreadPool.inv_mem stp sm;
      fl_inv_tgt:
        let: ttp := thread_pool tpc in
        let: tm := gm tpc in
        ThreadPool.inv_mem ttp tm;

      (** thread-pool domain matches, tid and atombit are eq *)
      tp_match:
        thrddom_eq spc tpc /\
        atombit_eq spc tpc /\
        tid_eq spc tpc;
      (** recorded fps are matched *)
      fp_match:
        let: Build_ProgConfig _ ttid _ _ := tpc in
        LFPG mu TGE ttid fpS0 fpT0 /\
        FP.subset fpS fpS0 /\
        FP.subset fpT fpT0
      ;
          
      (** thread-pools are well-formed *)
      tp_inv_src:
        let: Build_ProgConfig stp stid sm sbit := spc in
        ThreadPool.inv stp;
      tp_inv_tgt:
        let: Build_ProgConfig ttp ttid tm tbit := tpc in        
        ThreadPool.inv ttp;
      (** cores in call-stacks are simulated *)
      tp_cur_sim:
        let: Build_ProgConfig stp stid sm sbit := spc in
        let: Build_ProgConfig ttp ttid tm tbit := tpc in
        let: i_wrap index index_order _ i' := i in
        forall scs,
          ThreadPool.get_cs stp stid = Some scs ->
          exists tcs,
            ThreadPool.get_cs ttp ttid = Some tcs /\
            CallStack_sim_cur index index_order i' mu fpS fpT scs sm tcs tm
      ;
      tp_other_sim:
        let: Build_ProgConfig stp stid sm sbit := spc in
        let: Build_ProgConfig ttp ttid tm tbit := tpc in        
        forall t scs tcs,
          t <> stid ->
          ThreadPool.get_cs stp t = Some scs ->
          ThreadPool.get_cs ttp t = Some tcs ->
          CallStack_sim_other mu scs sm tcs tm;
    }.

  Lemma sim_final:
    forall i fpS fpT fpS0 fpT0 spc tpc,
      Config_sim i fpS fpT fpS0 fpT0 spc tpc ->
      final_state spc ->
      exists (tpc' : ProgConfig) (fpT' : FP.t),
        ETrace.tau_star np_step tpc fpT' tpc' /\
        atom_bit tpc = atom_bit tpc' /\
        LFPG mu TGE (cur_tid tpc) fpS0 (FP.union fpT0 fpT') /\ final_state tpc'.
  Proof.
    intros.
    exists tpc, FP.emp.
    split. constructor.
    split. auto.
    split.
    (* LFPG *)
    { pose proof (fp_match _ _ _ _ _ _ _ H). 
      destruct tpc. simpl in *. inversion H1. inversion H2.
      constructor. eapply eq_fp_match'; eauto.
      constructor; eauto with locs.
      apply FP.eq_sym. apply FP.union_emp.
      apply fpG_union; auto. apply fpG_emp.
    }
    destruct spc, tpc; simpl in *.
    (* final state *)
    inversion H0. econstructor; eauto. simpl.
    intro t; specialize (H2 t).
    
    pose proof (tp_match _ _ _ _ _ _ _ H) as Htp.
    pose proof (tp_inv_src _ _ _ _ _ _ _ H) as Hinvs.
    pose proof (tp_inv_tgt _ _ _ _ _ _ _ H) as Hinvt.
    destruct Htp as (Htp & junk); clear junk.
    subst; simpl in *.
    generalize H2 Htp Hinvs Hinvt. clear; intros.

    inversion Htp. specialize (H3 t). simpl in *; subst.
    generalize H2 Hinvs Hinvt H H3. clear; intros.
    inversion H3.
    { exfalso. inversion Hinvt. apply tp_valid in H. destruct H.
      unfold ThreadPool.get_cs in H4. rewrite H in H4. discriminate. }
    { assert (ThreadPool.valid_tid thread_pool t).
      unfold ThreadPool.valid_tid.
      destruct (plt t (ThreadPool.next_tid thread_pool)); auto.
      inversion Hinvs.
      unfold ThreadPool.get_cs in H0.
      rewrite tp_finite in H0; auto. discriminate.
      specialize (H2 H5).
      inversion H2. rewrite <- H0 in H6. inversion H6; subst.
      econstructor; eauto.
      inversion H4; auto.
      inversion H7. congruence. }
  Qed.

  Lemma sim_tau_step:
    forall i fpS fpT fpS0 fpT0 spc tpc,
      Config_sim i fpS fpT fpS0 fpT0 spc tpc ->
      forall (spc' : ProgConfig) (fpS' : FP.t),
        np_step spc ETrace.tau fpS' spc' ->
        atom_bit spc = atom_bit spc' ->
        (exists (tpc' : ProgConfig) (fpT' : FP.t) (i' : glob_index) fpS'' fpT'',
            ETrace.tau_plus np_step tpc fpT' tpc' /\
            LFPG mu TGE (cur_tid tpc) (FP.union fpS0 fpS') (FP.union fpT0 fpT') /\
            Config_sim i' fpS'' fpT'' (FP.union fpS0 fpS') (FP.union fpT0 fpT') spc' tpc')
        \/
        (exists i', glob_order i' i /\ Config_sim i' (FP.union fpS fpS') fpT (FP.union fpS0 fpS') fpT0 spc' tpc).
  Proof.
    intros i fpS fpT fpS0 fpT0 spc tpc H spc' fpS' H0 Hatom.
    destruct spc as [sthdp stid sm sbit].
    destruct spc' as [sthdp' stid' sm' sbit'].
    destruct tpc as [tthdp ttid tm tbit].
    pose proof (tp_match _ _ _ _ _ _ _ H) as Htp.
    destruct Htp as [Htp H'].
    destruct H'.
    inversion H1. simpl in *. subst tbit. clear pc1 pc2 H4 H5 H1.
    inversion H2. simpl in *. subst ttid. clear pc1 pc2 H3 H4 H2.
    inversion Htp. subst; simpl in *. clear Htp.
    rename H3 into Htp. rename H0 into Hsstep.
    
    inversion Hsstep; subst; simpl in *.
    (* core-step *)
    {
      assert (exists scs,
                 ThreadPool.get_cs sthdp stid' = Some scs /\
                 CallStack.top scs = Some c) as H_tp_scs.
      { apply get_top_in_cs; auto. }
      destruct H_tp_scs as ( scs & H_tp_scs & H_scs_c).
      
      assert (exists tc,
                 ThreadPool.get_top tthdp stid' = Some tc) as H_tp_core_tgt.
      { eapply ocs_match_top_exists; eauto. }
      destruct H_tp_core_tgt as (tc & H_tp_core_tgt).

      assert (exists tcs,
                 ThreadPool.get_cs tthdp stid' = Some tcs /\
                 CallStack.top tcs = Some tc) as H_tp_tcs.
      { repeat solv_thread. 
        destruct ((ThreadPool.content tthdp) !! stid'); [eexists; split; eauto|discriminate]. }
      destruct H_tp_tcs as (tcs & H_tp_tcs & H_tcs_tc).
      
      destruct i as [index index_order Hwf i].
      pose proof (tp_cur_sim _ _ _ _ _ _ _ H scs H_tp_scs) as Hlsim_cur;
        simpl in Hlsim_cur.
      destruct Hlsim_cur as (tcs' & H_tp_tcs' & Hlsim_cur).
      rewrite H_tp_tcs in H_tp_tcs'. inversion H_tp_tcs'. subst tcs'. clear H_tp_tcs'.
      
      inversion Hlsim_cur. solv_thread'. subst. clear Hlsim_cur.
      inversion H0.
      destruct core_config_sim_current0 as (R&Hlsim_top&Hmatch).

      inversion H_scs_c. subst. inversion H_tcs_tc. subst.
      eapply (AuxLDSim.match_tau_step _ _ _ _ _ _ _ _ _ Hlsim_top) in Hmatch; eauto.
      destruct Hmatch as [Hnostep | Hplus].
      
      { (* * no step, index decrease *)
        right.
        destruct Hnostep as (i'&Hdecr&Hmatch).
        exists (i_wrap _ _ Hwf i'). split. constructor; auto.
        constructor; simpl in *.
        (* ** src_fwd *)
        generalize H H_core_step GE_mod_wd_src. clear. intros.
        specialize (GE_mod_wd_src (Core.i c)).
        inversion GE_mod_wd_src.
        apply step_forward in H_core_step. eapply GMem.forward_trans; eauto.
        inversion H; auto.
        (* ** tgt_fwd *)
        inversion H; auto.
        (* ** src mem inv *)
        { eapply GE_mod_wd_tp_inv_mem in Hsstep; eauto.
          inversion H; auto.
          inversion H; auto. }
        (* ** tgt mem inv *)
        { inversion H; auto. }
        (* ** tp_match *)
        { split; [|split; constructor; auto].
          econstructor; eauto; simpl. subst.
          intro. generalize H_tp_upd Htp H_tp_scs. clear. intros.
          eapply stp_upd_ocs_match; eauto.
        }
        (* ** LFPG *)
        { pose proof (fp_match _ _ _ _ _ _ _ H).
          destruct H2 as (HLFPG&Hfpsubs&Hfpsubt).
          split.
          apply LFPG_union_S. inversion H. destruct fp_match0; auto.
          split; auto. apply FP.union2_subset. auto. }
        (* ** tp_inv src *)
        { (* /need lemma for np_step and threadpool inv *)
          eapply GE_mod_wd_tp_inv in Hsstep; inversion H; eauto. }
        (* ** tp_inv tgt *)
        { inversion H; auto. }
        (* ** sim_invs cur *)
        { intros. exists (tc :: tcs0). split; auto.
          destruct scs.
          exfalso. eapply thdp_upd_get_nil_false; eauto.
          constructor.
          (* current top sim *)
          { (* /need lemma for upd and get *)
            assert (c' = t).
            { apply thdp_upd_get in H_tp_upd.
              destruct H_tp_upd as (c0&cs&H'&H'').
              solv_eq. }
            subst t.
            constructor.
            (* dealing with dependent types... *)
            inversion H_core_upd. simpl in *; subst. exists R. auto.
            rewrite <- sg_eq_current0.
            inversion H_core_upd; subst; auto.
          }
          (* current tail sim *)
          {
            assert (scs0 = scs).
            { apply thdp_upd_get in H_tp_upd.
              destruct H_tp_upd as (?&?&?&?).
              solv_eq. }
            subst.

            assert (GMem.forward sm sm').
            { eapply  GE_mod_wd_forward in Hsstep; auto. }
            (* /by step and HG we know forward and unchg_on *)
            assert (forall fi,
                       let: fl := (FLists.get_fl (GlobEnv.freelists SGE) fi) in
                       fi <> (Core.F c) ->
                       unchg_freelist fl sm sm').
            {
              apply step_local_eff, LEffect_unchanged_on in H_core_step.
              intros. eapply GMem.unchanged_on_implies; eauto.
              intros. simpl. intro.
              eapply match_HG in Hmatch; eauto.
              destruct Hmatch. destruct H7. unfold LDSimDefs.fpG in H7.
              specialize (H7 b).
              assert (Bset.belongsto (FP.blocks (FP.union fpS fpS')) b).
              { generalize H6; clear; intro.
                exists ofs. solv_belongsto. }

              specialize (H7 H9); clear H8 H9.
              destruct H7.

              (* b in S *)
              unfold no_overlap in Hfl_mu_disj_src.
              unfold in_fl in H5. destruct H5.
              specialize (Hfl_mu_disj_src _ _ _ H5).
              apply Hfl_mu_disj_src. auto.
              (* b in F *)
              destruct H7, H5. rewrite <- H5 in H7.
              eapply (FLists.flist_disj _ (GlobEnv.wd_fl _ GE_wd_src)) in H4; eauto.
              destruct H4. eapply H4; eauto. 

              eapply GE_mod_wd_src; eauto.
            }
            
            assert (ThreadPool.inv sthdp').
            { apply GE_mod_wd_tp_inv in Hsstep; auto. inversion H; auto. }
            
            assert (forall score', In score' scs ->
                                   Core.F score' <> Core.F c).
            {
              apply ThreadPool.cs_inv in H_tp_scs.
              destruct H_tp_scs.
              intros. intro.
              apply In_nth_error in H6. destruct H6. symmetry in H7.
              specialize (fid_disjoint 0%nat (S x) c score' eq_refl H6 H7).
              inversion fid_disjoint.
              inversion H; auto.
            }
            
            generalize H1 H3 H4 H5 H6 GE_wd_src. clear; intros.
            induction H1. constructor.
            specialize (IHCallStack_sim_tail H3 H4).
            econstructor; eauto.
            inversion H. econstructor; eauto.
            destruct mem_rely_src0. split; auto. eapply GMem.forward_trans; eauto.
            eapply GMem.unchanged_on_trans; eauto.
            apply H4.
            (* /by wd GE *)
            apply H6; simpl; auto.

            apply IHCallStack_sim_tail. intros.
            apply H6. 
            apply in_cons. auto.
          }
        }
        
        (* ** sim_invs other *)
        { intros.
          (* /by step and HG we know forward and unchg_on *)
          assert (GMem.forward sm sm').
          { eapply  GE_mod_wd_forward in Hsstep; auto. }
          assert (forall fi,
                       let: fl := (FLists.get_fl (GlobEnv.freelists SGE) fi) in
                       fi <> (Core.F c) ->
                       unchg_freelist fl sm sm').
            {
              apply step_local_eff, LEffect_unchanged_on in H_core_step.
              intros. eapply GMem.unchanged_on_implies; eauto.
              intros. simpl. intro.
              eapply match_HG in Hmatch; eauto.
              destruct Hmatch. destruct H9. unfold LDSimDefs.fpG in H9.
              specialize (H9 b).
              assert (Bset.belongsto (FP.blocks (FP.union fpS fpS')) b).
              { exists ofs. solv_belongsto. }

              specialize (H9 H11); clear H10 H11.
              destruct H9.

              (* b in S *)
              unfold no_overlap in Hfl_mu_disj_src.
              unfold in_fl in H7. destruct H7.
              specialize (Hfl_mu_disj_src _ _ _ H7).
              apply Hfl_mu_disj_src. auto.
              (* b in F *)
              destruct H7, H9. rewrite <- H9 in H7.
              eapply (FLists.flist_disj _ (GlobEnv.wd_fl _ GE_wd_src)) in H6; eauto.
              destruct H6. eapply H6; eauto. 

              eapply GE_mod_wd_src; eauto.
            }
            
            assert (ThreadPool.inv sthdp').
            { eapply ThreadPool.upd_top_inv; eauto. inversion H; auto. }
            
            assert (forall score', In score' scs ->
                                   Core.F score' <> Core.F c).
            {
              intros. destruct H7. apply cs_inv in H3. destruct H3.
              apply fid_belongsto in H8.
              assert (In c (c :: scs0)) by (simpl; auto).
              eapply ThreadPool.fid_belongsto in H3.
              Focus 2. apply ThreadPool.cs_inv; eauto. inversion H; eauto. 
              unfold FLists.fbelongsto in *.
              destruct H8, H3. 
              rewrite <- H7, <- H3.
              eapply FLists.thread_fl_disj in H2; eauto.
              eapply GlobEnv.wd_fl; eauto.
            }

            assert (ThreadPool.get_cs sthdp t = Some scs).
            { generalize H2 H_tp_upd H3. clear. intros.
              solv_thread. destruct peq; congruence. }

            pose proof (tp_other_sim _ _ _ _ _ _ _ H t scs tcs H2 H9 H4).

            generalize H10 H5 H6 H7 H8. clear; intros.

            destruct H10; econstructor. 
            inversion H. econstructor; eauto.
            clear core_config_sim_block0 mem_rely_tgt_block0.
            destruct mem_rely_src_block0.
            split.
            eapply GMem.forward_trans; eauto.
            eapply unchg_freelist_trans; eauto.
            apply H6, H8. simpl; auto.

            clear H. induction H0. constructor.
            inversion H. econstructor; eauto. econstructor; eauto.
            destruct mem_rely_src0. split.
            eapply GMem.forward_trans; eauto.
            eapply unchg_freelist_trans; eauto.
            apply H6, H8; simpl; auto.
            apply IHCallStack_sim_tail; auto.
            intros. apply H8. destruct H1; simpl; auto.
        }
      }      

      { (* * step case *)
        left.
        destruct Hplus as (i'&fpT'&tcc'&tm'&Hplus&HLfpG&Hmatch).
        
        assert (exists tc', Core.update tc tcc' tc') as H_tcore_upd.
        { clear. destruct tc; simpl in *.
          exists (Core.Build_t i tcc' sg F). constructor; auto. }
        destruct H_tcore_upd as (tc'&H_tcore_upd).

        assert (exists tthdp', ThreadPool.update tthdp stid' tc' tthdp') as H_tp_upd_tgt.
        { generalize H_tp_core_tgt H_tcore_upd. clear; intros.
          unfold ThreadPool.get_top in H_tp_core_tgt.
          
          assert (exists cs, ThreadPool.get_cs tthdp stid' = Some cs).
          { destruct ThreadPool.get_cs; eauto. discriminate. }
          destruct H as [cs H]. rewrite H in H_tp_core_tgt.
          
          assert (exists cs', CallStack.update cs tc' cs'). 
          { destruct cs; inversion H_tp_core_tgt. subst.
            exists (tc'::cs). econstructor; eauto. }
          destruct H0 as [cs' H0].

          eexists. econstructor; eauto. }
        destruct H_tp_upd_tgt as [tthdp' H_tp_upd_tgt].

        exists {| thread_pool:=tthdp'; cur_tid:= stid'; gm:= tm'; atom_bit:= sbit'|},
        fpT', (i_wrap index index_order Hwf i'), (FP.union fpS fpS'), (FP.union fpT fpT').
        
        (* * plus step *)
        (* /lemma, core plus step -> glob plus tau step *)
        assert (ETrace.tau_plus np_step
                                {| thread_pool := tthdp; cur_tid := stid'; gm := tm; atom_bit := sbit' |} fpT'
                                {| thread_pool := tthdp'; cur_tid := stid'; gm := tm'; atom_bit := sbit' |})
               as Htstep.
        {
          generalize H_tp_tcs Hplus H_tcore_upd H_tp_upd_tgt H_tp_core_tgt. clear.
          destruct tc. do 3 intro . inversion H_tcore_upd. subst; simpl in *.
          generalize dependent H_tcore_upd.
          generalize dependent tcs0.
          generalize dependent tthdp.
          induction Hplus; intros. 
          constructor. econstructor; eauto.
          eapply core_step_np_step in H. destruct H as (?&?&?). 
          eapply ETrace.tau_plus_cons. eauto.
          eapply IHHplus; eauto; clear IHHplus.
          solv_thread.
          econstructor; eauto.
          econstructor; eauto. solv_thread. econstructor; eauto. econstructor; eauto. 
          solv_thread. rewrite PMap.set2. solv_thread.
          solv_thread.
          eauto. 
        }
        split. auto.

        split.
        (* * LFPG *)
        destruct (fp_match _ _ _ _ _ _ _ H). destruct H3.
        apply LFPG_union_T. apply LFPG_union_S. auto.
        apply LfpG'_subset_T with (fpT':=fpT') in HLfpG.
        inversion HLfpG.
        apply LFPG_subset_S with (fpS := FP.union fpS fpS').
        split; auto.
        (* /lemma LDSimDefs.fpG -> fpG *)
        constructor. intros. specialize (H6 b).
        (* /lemma locs belongsto bset belongsto *)
        assert (Blockset.Bset.belongsto (FP.blocks fpT') b).
        { exists ofs. solv_belongsto. }
        apply H6 in H8. destruct H8; auto. destruct H8.
        right. unfold FLists.bbelongsto.
        unfold FLists.get_tfblock, FLists.get_block, FLists.get_tfl in *.
        (* /lemma by wd GE, ..*)
        assert (exists n,
                   FLists.get_tfid (GlobEnv.freelists TGE) stid' n = Core.F tc).
        {
          eapply ThreadPool.fid_belongsto.
          eapply ThreadPool.cs_inv.
          inversion H; eauto.
          eauto. simpl; auto.
        }
        destruct H9.
        exists x0, x. rewrite H9. auto.
        apply FP.union2_subset. auto.
        (* /lemma eq subset *)
        { clear. constructor; simpl; intros b ofs H; solv_belongsto. }
        (* * match state *)
        assert (GMem.forward sm sm').
        { eapply GE_mod_wd_forward in Hsstep; eauto. }
        assert (GMem.forward tm tm').
        { generalize Htstep GE_mod_wd_tgt; clear; intros.
          eapply GE_mod_wd_plus_forward in Htstep; eauto.
        }
        
        constructor; simpl in *.
        (* ** src_fwd *)
        eapply GMem.forward_trans; eauto.
        inversion H; auto.
        (* ** tgt_fwd *)
        eapply GMem.forward_trans; eauto.
        inversion H; auto.
        (* ** src mem inv *)
        { eapply GE_mod_wd_tp_inv_mem in Hsstep; eauto.
          inversion H; auto.
          inversion H; auto.
        }
        (* ** tgt mem inv *)
        { eapply GE_mod_wd_plus_tp_inv_mem in Htstep; eauto.
          inversion H; auto.
          inversion H; auto.
        }
        (* ** tp_match *)
        { split.
          (* /need lemma for upd and dom_eq/ *)
          econstructor; eauto; simpl.
          intro. eapply sttp_upd_ocs_match; eauto.
          
          split; constructor; auto.
        }
        (* ** LFPG *)
        { pose proof (fp_match _ _ _ _ _ _ _ H). destruct H4 as (HLFPG&Hfpsubs&Hfpsubt).
          split.
          
          apply LFPG_union_T; auto.
          apply LFPG_union_S; auto.
          split. destruct HLfpG.
          eapply fp_match_subset_T'.
          eapply fp_match_subset_S'. eapply H4.
          apply FP.union2_subset. auto.
          
          (* / lemma x subset (x U y) *)
          { clear. constructor; simpl; intros b ofs H; solv_belongsto. }
          destruct HLfpG.
          (* / need lemma for local fpG to glob fpG *)
          unfold LDSimDefs.fpG in H5.
          constructor. intros. specialize (H5 b).
          assert (Bset.belongsto (FP.blocks (FP.union fpT fpT')) b) by (exists ofs; solv_belongsto).
          specialize (H5 H7).
          destruct H5; auto.
          destruct H5. right.
          unfold FLists.bbelongsto.
          assert (In tc (tc::tcs0)) by (simpl; auto).
          eapply ThreadPool.fid_belongsto in H8. unfold FLists.fbelongsto in H8.
          destruct H8.
          exists x0, x. rewrite <- H8 in H5. rewrite <- H5.
          unfold FLists.get_tfblock, FLists.get_block, FLists.get_tfl. eauto.
          eapply ThreadPool.cs_inv. inversion H; eauto. auto.

          (* *** fp subsets *)
          split; apply FP.union2_subset; auto. }
        (* ** tp_inv src *)
        { eapply GE_mod_wd_tp_inv in Hsstep; eauto. inversion H; auto. }
        (* ** tp_inv tgt *)
        { eapply GE_mod_wd_plus_tp_inv in Htstep; eauto. inversion H; auto. }
        (* ** sim_invs cur *)
        {
          intros. exists (tc' :: tcs0). split; auto.
          inversion H_tp_upd_tgt. subst. unfold ThreadPool.get_cs.
          simpl. rewrite PMap.gsspec. destruct peq; try congruence.
          inversion H6. subst. rewrite H_tp_tcs in H5. inversion H5. auto.
          
          destruct scs.
          (* /need lemma for upd and thread pool dom *)
          exfalso. inversion H_tp_upd. subst.
          unfold ThreadPool.get_cs in H4. simpl in H4.
          rewrite PMap.gsspec in H4.
          destruct peq; try congruence. inversion H4. subst.
          inversion H6.
          
          constructor.
          (* current top sim *)
          { (* /need lemma for upd and get *)
            assert (c' = t).
            { inversion H_tp_upd. subst.
              unfold ThreadPool.get_cs in H4. simpl in H4.
              rewrite Maps.PMap.gsspec in H4.
              destruct peq; try congruence. inversion H4. subst.
              inversion H6. auto. }
            subst t.
            (* dealing with dependent types... *)
            inversion H_core_upd; inversion H_tcore_upd. simpl in *; subst.
            constructor.
            exists R. auto.
            simpl. auto.
          }
          (* current tail sim *)
          {
            assert (scs0 = scs).
            { inversion H_tp_upd. subst.
              unfold ThreadPool.get_cs in H4. simpl in H4.
              rewrite Maps.PMap.gsspec in H4.
              destruct peq; try congruence. inversion H4. subst.
              destruct cs. inversion H6.
              inversion H6. subst. rewrite H_tp_scs in H5. inversion H5. auto. }
            subst.

            (* /by step and HG we know forward and unchg_on *)
            assert (forall fi,
                       let: fl := (FLists.get_fl (GlobEnv.freelists SGE) fi) in
                       fi <> (Core.F c) ->
                       unchg_freelist fl sm sm').
            {
              apply step_local_eff, LEffect_unchanged_on in H_core_step.
              intros. eapply GMem.unchanged_on_implies; eauto.
              intros. simpl. intro.
              eapply match_HG in Hmatch; eauto.
              destruct Hmatch. destruct H8. unfold LDSimDefs.fpG in H8.
              specialize (H8 b).
              assert (Bset.belongsto (FP.blocks (FP.union fpS fpS')) b).
              { exists ofs. solv_belongsto. }

              specialize (H8 H10); clear H10 H9.
              destruct H8.

              (* b in S *)
              unfold no_overlap in Hfl_mu_disj_src.
              unfold in_fl in H6. destruct H6.
              specialize (Hfl_mu_disj_src _ _ _ H6).
              apply Hfl_mu_disj_src. auto.
              (* b in F *)
              destruct H8, H6. rewrite <- H6 in H8.
              eapply (FLists.flist_disj _ (GlobEnv.wd_fl _ GE_wd_src)) in H5; eauto.
              destruct H5. eapply H5; eauto. 

              eapply GE_mod_wd_src; eauto.
            }
            
            assert (forall fi,
                       let: fl := (FLists.get_fl (GlobEnv.freelists TGE) fi) in
                       fi <> (Core.F tc) ->
                       unchg_freelist fl tm tm').
            {
              (* / lemma for plus-step local-effect *)
              assert (GMem.unchanged_on (fun b ofs => ~ Locs.belongsto (FP.locs fpT') b ofs) tm tm') as Htleffect.
              { generalize Hplus GE_mod_wd_tgt; clear; intros.
                induction Hplus.
                apply step_local_eff, LEffect_unchanged_on in H; auto.
                
                eapply GMem.unchanged_on_trans with (m2:= m'); eauto.
                eapply GMem.unchanged_on_implies; eauto.
                apply step_local_eff, LEffect_unchanged_on in H; eauto.
                clear. intros. intro. apply H. clear H. solv_belongsto.
                eapply GMem.unchanged_on_implies; eauto.
                clear. intros. intro. apply H. clear H. solv_belongsto.
              }
              
              intros. eapply GMem.unchanged_on_implies; eauto.
              intros. simpl. intro.
              generalize HLfpG H6 H7 H8 GE_wd_tgt Hfl_mu_disj_tgt. clear ; intros.
              destruct HLfpG. clear H. unfold LDSimDefs.fpG in H0.
              specialize (H0 b).
              assert (Bset.belongsto (FP.blocks (FP.union fpT fpT')) b).
              { exists ofs; solv_belongsto. }

              specialize (H0 H); clear H H8.
              destruct H7.
              destruct H0.
              (* b in S *)
              unfold no_overlap in Hfl_mu_disj_tgt.
              specialize (Hfl_mu_disj_tgt _ _ _ H).
              apply Hfl_mu_disj_tgt. auto.
              (* b in F *)
              destruct H0. rewrite <- H0 in H.
              eapply (FLists.flist_disj _ (GlobEnv.wd_fl _ GE_wd_tgt)) in H6; eauto.
              destruct H6. eapply H1; eauto. 
            }
            
            assert (forall score', In score' scs ->
                                   Core.F score' <> Core.F c).
            {
              apply ThreadPool.cs_inv in H_tp_scs.
              destruct H_tp_scs.
              intros. intro.
              apply In_nth_error in H7. destruct H7. symmetry in H8.
              specialize (fid_disjoint 0%nat (S x) c score' eq_refl H7 H8).
              inversion fid_disjoint.
              inversion H; auto.
            }

            assert (forall tcore', In tcore' tcs0 ->
                                   Core.F tcore' <> Core.F tc).
            {
              apply ThreadPool.cs_inv in H_tp_tcs.
              destruct H_tp_tcs.
              intros. intro.
              apply In_nth_error in H8. destruct H8. symmetry in H9.
              specialize (fid_disjoint 0%nat (S x) tc tcore' eq_refl H8 H9).
              inversion fid_disjoint.
              inversion H; auto.
            }

            assert (ThreadPool.inv sthdp').
            { apply GE_mod_wd_tp_inv in Hsstep; auto.
              inversion H; auto. }
            assert (ThreadPool.inv tthdp').
            { apply GE_mod_wd_plus_tp_inv in Htstep; auto.
              inversion H; auto. }
            
            generalize H1 H2 H3 H5 H6 H7 H8 H9 H10 GE_wd_src. clear; intros.
            induction H1. constructor.
            specialize (IHCallStack_sim_tail H2 H3 H5 H6).
            econstructor; eauto.
            inversion H. econstructor; eauto.

            destruct mem_rely_src0. split; auto. eapply GMem.forward_trans; eauto.
            eapply GMem.unchanged_on_trans; eauto.
            specialize (H7 sCore (or_introl eq_refl)).
            apply H5. auto.

            destruct mem_rely_tgt0. split; auto. eapply GMem.forward_trans; eauto.
            eapply GMem.unchanged_on_trans; eauto.
            specialize (H8 tCore (or_introl eq_refl)).
            apply H6. auto.

            apply IHCallStack_sim_tail; intros.
            apply H7. apply in_cons. auto.
            apply H8. apply in_cons. auto.
          }
        }
        
        (* ** sim_invs other *)
        { intros.
          (* /by step and HG we know forward and unchg_on *)
          assert (forall fi,
                       let: fl := (FLists.get_fl (GlobEnv.freelists SGE) fi) in
                       fi <> (Core.F c) ->
                       unchg_freelist fl sm sm').
            {
              apply step_local_eff, LEffect_unchanged_on in H_core_step.
              intros. eapply GMem.unchanged_on_implies; eauto.
              intros. simpl. intro.
              eapply match_HG in Hmatch; eauto.
              destruct Hmatch. destruct H10. unfold LDSimDefs.fpG in H10.
              specialize (H10 b).
              assert (Bset.belongsto (FP.blocks (FP.union fpS fpS')) b).
              { exists ofs; solv_belongsto. }

              specialize (H10 H12); clear H11 H12.
              destruct H10.

              (* b in S *)
              unfold no_overlap in Hfl_mu_disj_src.
              unfold in_fl in H8. destruct H8.
              specialize (Hfl_mu_disj_src _ _ _ H8).
              apply Hfl_mu_disj_src. auto.
              (* b in F *)
              destruct H10, H8. rewrite <- H8 in H10.
              eapply (FLists.flist_disj _ (GlobEnv.wd_fl _ GE_wd_src)) in H7; eauto.
              destruct H7. eapply H7; eauto. 

              eapply GE_mod_wd_src; eauto.
            }
            
            assert (forall fi,
                       let: fl := (FLists.get_fl (GlobEnv.freelists TGE) fi) in
                       fi <> (Core.F tc) ->
                       unchg_freelist fl tm tm').
            {
              (* / lemma for plus-step local-effect *)
              assert (GMem.unchanged_on (fun b ofs => ~ Locs.belongsto (FP.locs fpT') b ofs) tm tm') as Htleffect.
              { generalize Hplus GE_mod_wd_tgt; clear; intros.
                induction Hplus.
                apply step_local_eff, LEffect_unchanged_on in H; auto.
                eapply GMem.unchanged_on_trans with (m2:= m'); eauto.
                eapply GMem.unchanged_on_implies; eauto.
                apply step_local_eff, LEffect_unchanged_on in H; eauto.
                clear. intros. intro. apply H. clear H.
                solv_belongsto.
                eapply GMem.unchanged_on_implies; eauto.
                clear. intros. intro. apply H. clear H.
                solv_belongsto.
              }
              intros. eapply GMem.unchanged_on_implies; eauto.
              intros. simpl. intro.
              generalize HLfpG H8 H9 H10 GE_wd_tgt Hfl_mu_disj_tgt. clear ; intros.
              destruct HLfpG. clear H. unfold LDSimDefs.fpG in H0.
              specialize (H0 b).
              assert (Bset.belongsto (FP.blocks (FP.union fpT fpT')) b).
              { exists ofs. solv_belongsto. }
              
              specialize (H0 H); clear H.
              destruct H9. destruct H0.
              (* b in S *)
              eapply Hfl_mu_disj_tgt; eauto.
              (* b in F *)
              destruct H0. solv_eq.
              eapply FLists.flist_disj; eauto.
              inversion GE_wd_tgt; eauto.
            }
            
            assert (forall score', In score' scs ->
                                   Core.F score' <> Core.F c).
            {
              intros. apply ThreadPool.cs_inv in H5.
              apply ThreadPool.cs_inv in H_tp_scs.
              destruct H5, H_tp_scs.
              apply fid_belongsto in H9.
              assert (In c (c :: scs0)) by (simpl; auto).
              apply fid_belongsto0 in H5.
              unfold FLists.fbelongsto in *.
              destruct H9, H5.
              rewrite <- H9, <- H5.
              eapply FLists.thread_fl_disj in H4; eauto.
              eapply GlobEnv.wd_fl; eauto.
              inversion H; auto.
              apply GE_mod_wd_tp_inv in Hsstep; auto.
              inversion H; auto.
            }

            assert (forall tcore', In tcore' tcs ->
                                   Core.F tcore' <> Core.F tc).
            {
              intros. apply ThreadPool.cs_inv in H6.
              apply ThreadPool.cs_inv in H_tp_tcs.
              destruct H6, H_tp_tcs.
              apply fid_belongsto in H10.
              assert (In tc (tc :: tcs0)) by (simpl; auto).
              apply fid_belongsto0 in H6.
              unfold FLists.fbelongsto in *.
              destruct H10, H6.
              rewrite <- H10, <- H6.
              eapply FLists.thread_fl_disj in H4; eauto.
              eapply GlobEnv.wd_fl; eauto.
              inversion H; auto.
              apply GE_mod_wd_plus_tp_inv in Htstep; auto.
              inversion H; auto.
            }

            assert (ThreadPool.get_cs sthdp t = Some scs).
            {
              generalize H_tp_upd H4 H5. clear. intros.
              unfold ThreadPool.get_cs in *.
              inversion H_tp_upd; subst; simpl in *.
              rewrite PMap.gsspec in *.
              destruct peq; congruence.
            }
            
            assert (ThreadPool.get_cs tthdp t = Some tcs).
            {
              generalize H_tp_upd_tgt H4 H6. clear. intros.
              unfold ThreadPool.get_cs in *.
              inversion H_tp_upd_tgt; subst; simpl in *.
              rewrite PMap.gsspec in *.
              destruct peq; congruence.
            }
            
            pose proof (tp_other_sim _ _ _ _ _ _ _ H t _ _ H4 H11 H12).

            generalize H2 H3 H4 H7 H8 H9 H10 H13. clear; intros.

            destruct H13; econstructor.
            inversion H. econstructor; eauto.
            destruct mem_rely_src_block0. split.
            eapply GMem.forward_trans; eauto. 
            eapply unchg_freelist_trans; eauto.
            apply H7, H9. simpl; auto.

            destruct mem_rely_tgt_block0. split.
            eapply GMem.forward_trans; eauto. 
            eapply unchg_freelist_trans; eauto.
            apply H8, H10. simpl; auto.

            clear H. induction H0. constructor.
            econstructor; eauto.
            inversion H. econstructor; eauto.
            destruct mem_rely_src0. split.
            eapply GMem.forward_trans; eauto. 
            eapply unchg_freelist_trans; eauto.
            apply H7, H9. simpl; auto.

            destruct mem_rely_tgt0. split.
            eapply GMem.forward_trans; eauto. 
            eapply unchg_freelist_trans; eauto.
            apply H8, H10; simpl; auto.
            
            apply IHCallStack_sim_tail; auto.
            intros. apply H9. destruct H1; simpl; auto.
            intros. apply H10. destruct H1; simpl; auto.
        }
      }  
    }

    
    (* call ext *)
    { left. destruct i eqn:Hi.
      (* arguments related arg_rel (inj mu) args args' *)
      assert (exists scs, ThreadPool.get_cs sthdp stid' = Some (c :: scs)) as H_tp_cs.
      { generalize H_tp_core; clear; intro.
        unfold ThreadPool.get_top in H_tp_core.
        destruct ThreadPool.get_cs; inversion H_tp_core.
        unfold CallStack.top in H0. destruct t; inversion H0.
        eauto. }
      decompose_ex H_tp_cs.
      destruct (tp_cur_sim _ _ _ _ _ _ _ H _ H_tp_cs) as (tcs & H_tp_cs' & Hsim_cur_cs).

      destruct tcs as [ | tc ]; [ inversion Hsim_cur_cs | ].

      inversion Hsim_cur_cs; subst.
      rename H9 into Hsim_cur_other.
      clear Hsim_cur_cs.

      assert (ThreadPool.get_top tthdp stid' = Some tc) as H_tp_core'.
      { unfold ThreadPool.get_top. rewrite H_tp_cs'; auto. }

      destruct H8 as [core_config_sim Hsg].
      destruct core_config_sim as [R_top [Hldsim_top Hmatch_top] ].

      pose proof Hldsim_top as Hldsim_top'.
      eapply match_at_external in Hldsim_top; eauto.
      destruct Hldsim_top as [GARG [i0' [args' Hldsim_top] ] ].
      destruct Hldsim_top as (H_core_atext' & Hargs & HLG & match_top').

      destruct tc eqn:Htc; simpl in *.

      (* by simulation on modules in SGE and TGE, 
         we could init a related target core *)
      set (ThreadPool.next_fmap sthdp stid') as sfnum.
      set (FLists.get_tfid (GlobEnv.freelists SGE) stid' sfnum) as sfid.
      set (ThreadPool.next_fmap tthdp stid') as tfnum.
      set (FLists.get_tfid (GlobEnv.freelists TGE) stid' tfnum) as tfid.
      destruct (HGE_sim funid new_ix sfid tfid H_mod_id) as
          (new_ix' & H_mod_id' & Hmod_sim_new).

      destruct Hmod_sim_new as (index' & index_order' & R_new & Hmod_sim_new).
      edestruct (Hmod_sim_new funid args args') as (tcc'' & H_new_core' & Htmp); eauto.
      exploit (Htmp sm_init tm_init).
      { inversion H_init_sm. eauto. }
      { inversion H_init_tm. eauto. }
      { constructor; auto.
        eapply FLists.freelist_norepeat; eauto. eapply GlobEnv.wd_fl; eauto.
        eapply FLists.freelist_norepeat; eauto. eapply GlobEnv.wd_fl; eauto. }
      { instantiate (2:= sm'). instantiate (1:= tm).
        inversion HLG. inversion H0.
        constructor; auto.
        constructor; auto.
        inv H; auto.
        (** TODO: lemma : freelist free -> unchg_freelist *)
        
        apply freelist_free_unchg_freelist; auto. inv H. inv fl_inv_src0. eauto. 
        eapply match_HG in Hmatch_top; eauto. destruct Hmatch_top. destruct H5. auto.
        constructor; auto.
        inv H; auto.
        apply freelist_free_unchg_freelist; auto. inv H. inv fl_inv_tgt0. eauto. 
      }
      intros (i0'' & Hsim_new & Hmatch_new).

      (*eapply match_init
      inversion H. eapply ThreadPool.tp_valid_freelist_free; eauto.
        inversion H. eapply ThreadPool.tp_valid_freelist_free; eauto.
        eapply FLists.freelist_norepeat; eauto. eapply GlobEnv.wd_fl; eauto.
        eapply FLists.freelist_norepeat; eauto. eapply GlobEnv.wd_fl; eauto.
        
        eapply match_HG; eauto. }
            
      H_init_sm H_init_tm).   sm' tm) as (index' & index_order' & R_new & i0'' &
                         Hsim_new & Hmatch_new); eauto.
       *)
      clear Htmp.
      
      assert (exists tthdp'', ThreadPool.push tthdp stid' new_ix' tcc'' sg = Some tthdp'')
        as H_tp_push'.
      { generalize H_tp_core'. clear. intro.
        repeat solv_thread'. }
      destruct H_tp_push' as [tthdp'' H_tp_push''].

      exists ([[ tthdp'', stid', tm, O ]]), FP.emp.
      unshelve eexists (i_wrap index' index_order' _ i0'').
      { eapply AuxLDSim.index_wf; eauto. }
      exists FP.emp, FP.emp.

      assert ( tau_plus np_step
                        {| thread_pool := tthdp; cur_tid := stid'; gm := tm; atom_bit := O |}
                        FP.emp
                        {| thread_pool := tthdp''; cur_tid := stid'; gm := tm; atom_bit := O |}) as Htplus.
      { eapply tau_plus_1. eapply Call with (c1:= (<< i, c0, sg0, F >>)); eauto. }
      
      split; auto.
      split.
      { 
        (* * LFPG *)
        destruct (fp_match _ _ _ _ _ _ _ H). destruct H1.
        apply LFPG_union. auto.
        clear. constructor.
        constructor; constructor; intros; inversion H0.
        apply fpG_emp.
      }
      {
        constructor; simpl in *.
        (* ** src_fwd *)
        inversion H; auto.
        (* ** tgt_fwd *)
        inversion H; auto.
        (* ** src mem inv *)
        { eapply GE_mod_wd_tp_inv_mem in Hsstep; eauto.
          inversion H; auto.
          inversion H; auto.
        }
        (* ** tgt mem inv *)
        { eapply GE_mod_wd_plus_tp_inv_mem in Htplus; eauto.
          simpl. inversion H; auto.
          simpl. inversion H; auto.
        }
        (* ** tp_match *)
        { split; [| split; constructor; auto].
          (* /need lemma for upd and dom_eq/ *)
          econstructor; eauto; simpl. intro t.
          generalize H_tp_push, H_tp_push'', H. clear; intros.
          apply tp_match in H. destruct H as [? _]. inversion H; subst.
          unfold ThreadPool.get_cs in *; simpl in *. specialize (H2 t).
          eapply tp_push_ocs_match in H2; eauto.
        }
        (* ** LFPG *)
        { pose proof (fp_match _ _ _ _ _ _ _ H). destruct H0 as (HLFPG&Hfpsubs&Hfpsubt).
          split.
          apply LFPG_union. auto.
          clear. constructor. constructor; constructor; intros; inversion H0. apply fpG_emp.
          clear. split; constructor; intros b ofs H; solv_belongsto.
        }
        (* ** tp_inv src *)
        { eapply GE_mod_wd_tp_inv in Hsstep; eauto. inversion H; auto. }
        (* ** tp_inv tgt *)
        { eapply GE_mod_wd_plus_tp_inv in Htplus; eauto. inversion H; auto. }
        (* ** sim_invs cur *)
        { intros. 
          inversion H_tp_push. unfold ThreadPool.push in H2.
          unfold ThreadPool.get_cs in H_tp_cs, H0.
          rewrite H_tp_cs in H2. inversion H2; subst; clear H2; simpl in *.
          rewrite PMap.gsspec in H0. destruct peq; [|contradiction].
          inversion H0; clear H0; subst. unfold CallStack.push.
          unfold ThreadPool.push in H_tp_push''.
          exists ({| Core.c:=tcc''; Core.sg:= sg;
                Core.F:= FLists.get_tfid (GlobEnv.freelists TGE) stid'
                                         (ThreadPool.next_fmap tthdp stid') |}
               :: {| Core.c:=c0; Core.sg:=Core.sg c; Core.F:= F |} :: tcs). split.
          { generalize H_tp_push'', H_tp_cs'. clear. intros.
            solv_thread'. solv_pmap. auto. discriminate. }

          constructor.
          (* current top sim *)
          { constructor; simpl in *; auto.
            eexists; eauto. }
          (* current tail sim *)
          {
            (* caller core *)
            econstructor; eauto.
            econstructor. eexists. eauto.
            split;[apply GMem.forward_refl|apply GMem.unchanged_on_refl].
            split;[apply GMem.forward_refl|apply GMem.unchanged_on_refl].
            auto.
          }
        }
        
        (* ** sim_invs other *)
        { intros.
          (* /by step and HG we know forward and unchg_on *)
          assert (ThreadPool.get_cs sthdp t = Some scs0).
          { generalize H_tp_push H0 H1. clear. intros.
            solv_thread'. solv_pmap. auto. }
            
          assert (ThreadPool.get_cs tthdp t = Some tcs0).
          { generalize H_tp_push'' H0 H2. clear. intros.
            solv_thread'; solv_pmap; auto. }
          
          pose proof (tp_other_sim _ _ _ _ _ _ _ H t _ _ H0 H3 H4).

          generalize H1 H2 H5. clear; intros.

          destruct H5; econstructor; eauto.
        }
      }  
    }

    (* return *)
    { left.
      assert (exists scs,
                 ThreadPool.get_cs sthdp stid' = Some (c :: c' :: scs)) as H_tp_scs.
      { apply get_top_in_cs in H_tp_core; auto.
        destruct H_tp_core as (cs & Htpcs & Htop).
        destruct cs; inversion Htop. subst.
        unfold ThreadPool.pop in H_tp_pop.
        unfold ThreadPool.get_cs in Htpcs.
        rewrite Htpcs in H_tp_pop; simpl in *.
        inversion H_tp_pop; subst.
        unfold ThreadPool.get_top, ThreadPool.get_cs in H_tp_caller; simpl in *.
        rewrite PMap.gsspec in H_tp_caller. destruct peq; [|contradiction].
        destruct cs; inversion H_tp_caller; subst.
        exists cs; auto.
      }
      destruct H_tp_scs as (scs & H_tp_scs).
      
      assert (exists tc tc' tcs,
                 ThreadPool.get_cs tthdp stid' = Some (tc :: tc' :: tcs)) as H_tp_tcs.
      { apply tp_match in H. destruct H as [H _].
        inversion H; subst. specialize (H2 stid'); inversion H2.
        congruence.
        solv_eq; subst;
          repeat match goal with
                 | H: cs_match (cons _ _) _ |- _ => inversion H; subst; clear H
                 | H: CallStack.is_emp (cons _ _) |- _ => inversion H
                 end.
        repeat eexists; eauto. }
      destruct H_tp_tcs as (tc & tc' & tcs & H_tp_tcs).
      
      destruct i as [index index_order Hwf i].
      
      pose proof (tp_cur_sim _ _ _ _ _ _ _ H _ H_tp_scs) as Hlsim_cur;
        simpl in Hlsim_cur.
      
      destruct Hlsim_cur as (tcs' & H_tp_tcs' & Hlsim_cur).
      rewrite H_tp_tcs in H_tp_tcs'. inversion H_tp_tcs'. subst tcs'. clear H_tp_tcs'.
      
      inversion Hlsim_cur as
          [|sCore sm tCore tm0 scs0 tcs0 H0 H1' Hsim_cur_top Hsim_cur_other H3 H2'].
      subst. clear Hlsim_cur.
      
      inversion Hsim_cur_top. 
      destruct core_config_sim_current0 as (R&Hlsim_top&Hmatch).
      pose proof Hmatch as Hmatch'.

      eapply (AuxLDSim.match_halt _ _ _ _ _ _ _ _ _ Hlsim_top) in Hmatch; eauto.

      destruct tc as [tix_top tcc sg F] eqn:Htc; simpl in *.
      destruct Hmatch as (H_res_src & resT & H_core_halt' &  Hres_rel & HLG).

      inversion Hsim_cur_other as
          [|sm0 tm0 sm tm1 scs0 tcs0 index0 index_order0 i0
                sCore tCore Hsim_caller Hsim_cur_other' H0 H1' H3 H2'].
      subst. clear Hsim_cur_other.
      (* construct return step  in target *)
      inversion Hsim_caller. clear Hsim_caller.
      destruct core_config_sim0 as (R_caller & Hsim_caller & Hmatch_caller). auto.
      pose proof Hsim_caller as Hcaller_after_sim.
      eapply match_after_external in Hcaller_after_sim; eauto.
      instantiate (1:= res_sg (Core.sg c) resT) in Hcaller_after_sim.
      Focus 2. destruct (res_sg _ res) eqn:Htmp; simpl; auto.
      inversion Htmp. unfold res_sg in H1. destruct AST.sig_res; congruence.

      destruct Hcaller_after_sim as (tcc'' & H_core_aftext' & Hmatch_after).
      
      (* TODO: 
         1. is signature preserved across all compilation passes ?
         A: propably yes, at leat for Selection.v

         2. if so, need additional condition in Config_sim for eq_sig 
         
         3. what about the entry signature? main_sg? 
         A: seems it does not matter what signature is recoreded in the bottom core,
         both source and target program could initialize the core with [ sg_main ].

         4. Do we need additional conditions in mod_lsim?
         A: no, signature checks only return values when a core halts. mod_lsim
         deals with core initialization, has nothing to do with sg.
       *)

      (* TODO:
         It seems that the has_type relation is not preserved by value injection ...
         Sol:
         1. we could add condition on returning type? 
         i.e. 
         halted c = Some (v, typ) -> has_type v typ /\
         check typ when returning in globsem /\
         require return type matches in simulation

         need lemma for:
         res_has_type res ty ->
         val_inj res res' ->
         res_has_type res' ty *)

      (* Solved: 
         additional type information in interaction semantics *)

      assert (exists tthdp', ThreadPool.pop tthdp stid' = Some tthdp').
      { generalize H_tp_tcs. clear. intros. solv_thread'. }
      destruct H0 as [tthdp' H_tp_pop'].
      assert (exists tthdp'',
                 ThreadPool.update tthdp' stid'
                                   {| Core.c:= tcc''; Core.sg := Core.sg tc';
                                      Core.F := Core.F tc' |}
                                   tthdp'').
      { generalize H_tp_pop' H_tp_tcs. clear. intros. solv_thread'.
        eexists. econstructor; eauto. solv_thread. repeat (econstructor; eauto). }
      destruct H0 as [tthdp'' H_tp_upd'].
      
      assert (np_step {| thread_pool := tthdp; cur_tid := stid'; gm := tm; atom_bit := O|}
                      tau FP.emp
                      {| thread_pool := tthdp''; cur_tid := stid'; gm := tm; atom_bit := O|}
             ) as Htreturn.
      { inversion H_tp_upd' as [cs cs' thdp'0 H0' H1' H2' H3']. 
        inversion H1' as [c0 cs0 cc c'0 H0'' H1'' H2'' H3''].
        subst; simpl in *.

        eapply Return with (c1:=(<<tix_top, tcc, Core.sg c, F>>)); eauto.
        { find_relatives tthdp. clear. intros. solv_thread'. }
        { find_relatives tthdp'. clear; intros. solv_thread'. solv_pmap. congruence. }
        { simpl.
          (* dependent types....... *)
          assert (tc' = c0).
          { generalize H0' H_tp_pop' H_tp_tcs. clear. intros.
            solv_thread'. solv_pmap. congruence. }
          subst c0. constructor. auto.
        }
      }
      
      assert (well_founded index_order0) as wf0.
      { inversion Hsim_caller; auto. }

      destruct (Hmatch_after sm' tm) as (i0' & Hmatch_caller').
      { eapply match_HG in Hlsim_top; eauto.
        generalize Hlsim_top HLG mem_rely_src0 mem_rely_tgt0; clear; intros.
        destruct mem_rely_src0, mem_rely_tgt0, HLG, Hlsim_top.
        destruct H3, H6.
        constructor; auto; constructor; auto. }
      clear Hmatch_after.

      eexists _, FP.emp, (i_wrap _ _ wf0 i0'), FP.emp, FP.emp.
      split. econstructor; eauto. 
      split. do 2 rewrite fp_union_emp_r. apply fp_match in H. destruct H. auto.

      (* sim *)
      do 2 rewrite fp_union_emp_r.
      constructor; simpl.
      { inversion H; auto. }
      { inversion H; auto. }
      { inversion H; eapply GE_mod_wd_tp_inv_mem in Hsstep; eauto. }
      { inversion H; eapply GE_mod_wd_tp_inv_mem in Htreturn; eauto. }
      { (** match tp dom *)
        split; [| split; constructor; auto].
        econstructor; eauto; simpl.
        apply tp_match in H; destruct H as [H _].

        generalize H H_tp_pop H_tp_upd H_tp_pop' H_tp_upd' H_tp_scs H_tp_tcs;
          clear; intros.
        inversion H; simpl in *; subst.
        eapply sttp_upd_ocs_match; [|eauto|eauto].
        eapply tp_pop_ocs_match in H2; eauto.
      }
      { (** LFPG *)
        (** ??? the same routine with the caller sim case *)
        split; [|clear; split; constructor; intros b ofs H; inversion H].
        apply fp_match in H. destruct H; auto.
      }
      (** tp invs *)
      { eapply GE_mod_wd_tp_inv in Hsstep; inversion H; eauto. }
      { inversion H; eapply GE_mod_wd_tp_inv in Htreturn; eauto;
          eapply GE_mod_wd_star_tp_inv in Htstar'; eauto. }
      (** sim cur *)
      { intros. solv_eq.
        assert (ThreadPool.get_cs sthdp' stid' = Some (c'' :: scs)).
        { generalize H_tp_scs, H_tp_pop, H_tp_upd. clear. intros.
          solv_thread'. solv_pmap. inversion H. auto. }
        assert (ThreadPool.get_cs tthdp'' stid' =
                Some ({|Core.c:= tcc''; Core.sg:= Core.sg tc'; Core.F := Core.F tc' |} :: tcs)).
        { find_relatives tthdp''. clear; intros.
          solv_thread'. solv_pmap. f_equal. congruence. }
        eexists; split; eauto.
        rewrite H1 in H0. inversion H0; clear H0. subst.
        
        constructor.
        { (** sim cur top *)
          (* why do i have to deal with dependent types? *)
          destruct c' as [i_c' c_c' sg_c' F_c'].
          destruct c'' as [i_c'' c_c'' sg_c'' F_c''].
          assert (i_c' = i_c'' /\ F_c' = F_c'' /\ sg_c' = sg_c'').
          { generalize H_core_upd; clear; intro H; inversion H; simpl in *.
            inversion H0. auto. }
          destruct H0 as [H0 [H3 H4] ]; subst i_c'' F_c''; simpl in *.
          assert (c_c'' = cc'').
          { inversion H_core_upd. subst. inversion H0.
            rewrite eq_sigT_iff_eq_dep in H4.
            apply Eqdep.EqdepTheory.eq_dep_eq in H4.
            trivial. }
          subst c_c'' sg_c''.
          
          constructor; simpl in *; auto.
          exists R_caller. split; auto.
        }
        { (** sim cur other *)
          assumption.
        }
      } 
      (** sim other *)
      {
        intros.
        assert (ThreadPool.get_cs sthdp' t = ThreadPool.get_cs sthdp t).
        { generalize H_tp_upd, H_tp_pop, H0; clear; intros.
          solv_thread'. solv_pmap. auto. }

        assert (ThreadPool.get_cs tthdp'' t = ThreadPool.get_cs tthdp t).
        { generalize H_tp_upd', H_tp_pop', H0; clear; intros.
          solv_thread'. solv_pmap. auto. }
        
        eapply tp_other_sim in H.
        generalize H2 H3 H4 H0 H1 H. clear; intros.
        eapply H; eauto; congruence.
      }
      
      (** ores_rel *)
      generalize Hres_rel. clear; intros.
      unfold ores_rel, res_sg.
      destruct (Core.sg c); simpl in *.
      destruct sig_res; auto.
    }

    (* halt *)
    {
      left.
      assert (ThreadPool.get_cs sthdp stid' = Some (c :: nil)) as H_tp_scs.
      { generalize H_tp_core H_tp_pop H_thread_halt; clear; intros.
        solv_thread'. solv_pmap. inversion H. auto. }
      
      assert (exists tc, ThreadPool.get_cs tthdp stid' = Some (tc :: nil)) as H_tp_tcs.
      { apply tp_match in H. destruct H as [H _].
        inversion H; subst. specialize (H2 stid'); inversion H2.
        congruence. solv_eq; subst.
        inversion H3; subst. inversion H0. eexists; eauto.
        inversion H6. subst. inversion H4. auto. }
      destruct H_tp_tcs as (tc & H_tp_tcs).
      
      destruct i as [index index_order Hwf i].
      
      pose proof (tp_cur_sim _ _ _ _ _ _ _ H _ H_tp_scs) as Hlsim_cur;
        simpl in Hlsim_cur.
      
      destruct Hlsim_cur as (tcs' & H_tp_tcs' & Hlsim_cur).
      rewrite H_tp_tcs in H_tp_tcs'. inversion H_tp_tcs'. subst tcs'. clear H_tp_tcs'.
      
      inversion Hlsim_cur as
          [|sCore sm tCore tm0 scs0 tcs0 H0 H1' Hsim_cur_top Hsim_cur_other H3 H2'].
      subst. clear Hlsim_cur.
      
      inversion Hsim_cur_top. 
      destruct core_config_sim_current0 as (R&Hlsim_top&Hmatch).
      pose proof Hmatch as Hmatch'.

      eapply (AuxLDSim.match_halt _ _ _ _ _ _ _ _ _ Hlsim_top) in Hmatch; eauto.

      destruct tc as [tix_top tcc sg F] eqn:Htc; simpl in *.
      destruct Hmatch as (H_res_src & resT & H_core_halt' & Hres_rel & HLG).

      (* construct return step  in target *)
      assert (exists tthdp', ThreadPool.pop tthdp stid' = Some tthdp').
      { generalize H_tp_tcs. clear. intros. solv_thread'. }
      destruct H0 as [tthdp' H_tp_pop'].
      assert (ThreadPool.halted tthdp' stid') as H_therad_halt.
      { find_relatives tthdp'. clear. intros. solv_thread'.
        econstructor; eauto; solv_thread'. solv_pmap. eauto. }
      assert (forall t', ThreadPool.valid_tid tthdp' t' -> ThreadPool.halted tthdp' t')
        as H_all_thread_halted'.
      {
        assert (ThreadPool.inv sthdp').
        { inversion H. eapply ThreadPool.pop_inv; eauto. }
        assert (ThreadPool.inv tthdp').
        { inversion H. eapply ThreadPool.pop_inv; eauto. }
        intro. rewrite valid_tid_get_cs; auto. destruct 1 as (cs' & Hcs').
        generalize H H_all_thread_halted H_thread_halt H_tp_pop H_tp_pop' Hcs' H0.
        clear; intros.
        
        apply tp_match in H. destruct H as [H _]. inversion H; subst.
        eapply tp_pop_ocs_match with (i:=t') in H3; eauto.
        eapply ThreadPool.Halted; eauto.
        rewrite Hcs' in H3. inversion H3. subst. inversion H4; [auto|].
        subst. exfalso. clear H2 H4.
        assert (ThreadPool.valid_tid sthdp' t').
        { rewrite valid_tid_get_cs; auto. rewrite <- H1. eauto. }
        apply H_all_thread_halted in H2. inversion H2. inversion H5. subst.
        congruence.
      }
      
      assert (np_step {| thread_pool := tthdp; cur_tid := stid'; gm := tm; atom_bit := O|}
                      tau FP.emp
                      {| thread_pool := tthdp'; cur_tid := stid'; gm := tm; atom_bit := O|}
             ) as Htreturn.
      { eapply Halt with (c0:= tc); subst; eauto.
        generalize H_tp_tcs; clear; intros; solv_thread'. }
      
      eexists _, FP.emp, (i_wrap _ _ Hwf i), FP.emp, FP.emp.
      split. econstructor; eauto. 
      split. do 2 rewrite fp_union_emp_r. apply fp_match in H. destruct H. auto.

      (* sim *)
      do 2 rewrite fp_union_emp_r.
      constructor; simpl.
      { inversion H; auto. }
      { inversion H; auto. }
      { inversion H; eapply GE_mod_wd_tp_inv_mem in Hsstep; eauto. }
      { inversion H; eapply GE_mod_wd_tp_inv_mem in Htreturn; eauto. }
      { (** match tp dom *)
        split; [| split; constructor; auto].
        econstructor; eauto; simpl.
        apply tp_match in H; destruct H as [H _].

        generalize H H_tp_pop H_tp_pop' H_tp_scs H_tp_tcs;
          clear; intros.
        inversion H; simpl in *; subst.
        eapply tp_pop_ocs_match in H2; eauto.
      }
      { (** LFPG *)
        (** WTF??? the same routine with the caller sim case *)
        split; [|clear; split; constructor; intros b ofs H; inversion H].
        apply fp_match in H. destruct H; auto.
      }
      (** tp invs *)
      { eapply GE_mod_wd_tp_inv in Hsstep; inversion H; eauto. }
      { inversion H; eapply GE_mod_wd_tp_inv in Htreturn; eauto;
          eapply GE_mod_wd_star_tp_inv in Htstar'; eauto. }
      (** sim cur *)
      { intros. exists nil.
        split. find_relatives tthdp'; clear; intros. solv_thread'.
        assert (scs = nil) by (find_relatives sthdp'; clear; intros; solv_thread').
        subst. econstructor. auto.
      } 
      (** sim other *)
      {
        intros.
        assert (ThreadPool.get_cs sthdp' t = ThreadPool.get_cs sthdp t).
        { generalize H_tp_pop, H0; clear; intros.
          solv_thread'. solv_pmap. auto. }

        assert (ThreadPool.get_cs tthdp' t = ThreadPool.get_cs tthdp t).
        { generalize H_tp_pop', H0; clear; intros.
          solv_thread'. solv_pmap. auto. }
        
        eapply tp_other_sim in H.
        generalize H2 H3 H4 H0 H1 H. clear; intros.
        eapply H; eauto; congruence.
      }
    }
  Qed.

  Lemma sim_ent_atom:
    forall i fpS fpT fpS0 fpT0 spc tpc,
      Config_sim i fpS fpT fpS0 fpT0 spc tpc ->
      forall spc' fpS',
          np_step spc tau fpS' spc' ->
          atom_bit spc <> atom_bit spc' ->
          (exists tpc' fpT' tpc'' fpT'' i',
              tau_star np_step tpc fpT' tpc' /\
              atom_bit tpc = atom_bit tpc' /\
              np_step tpc' tau fpT'' tpc'' /\
              LFPG mu TGE tpc.(cur_tid) (FP.union fpS0 fpS')
                                        (FP.union fpT0 (FP.union fpT' fpT'')) /\
              Config_sim i' FP.emp FP.emp FP.emp FP.emp spc' tpc'').
  Proof.
    intros.
    destruct spc as [sthdp stid sm b].
    destruct tpc as [tthdp ttid tm tb].
    inversion H0; simpl in *; subst; simpl in *; try contradiction. clear H1.
    destruct i eqn:Hi.

    assert (exists scs, ThreadPool.get_cs sthdp stid = Some (c :: scs)) as H_tp_cs.
    { generalize H_tp_core; clear; intro.
      solv_thread.
      match goal with | H: match ?x with _ => _ end = Some _ |- _ => destruct x; inversion H_tp_core end.
      destruct t; inversion H0; eauto. }
    decompose_ex H_tp_cs.
    
    destruct (tp_cur_sim _ _ _ _ _ _ _ H _ H_tp_cs) as (tcs & H_tp_cs' & Hsim_cur_cs).
    destruct tcs as [ | tc ]; [ inversion Hsim_cur_cs | ].

    inversion Hsim_cur_cs; subst.
    rename H9 into Hsim_cur_top.
    rename H10 into Hsim_cur_tail.
    clear Hsim_cur_cs.
    
    assert (ThreadPool.get_top tthdp ttid = Some tc) as H_tp_core'.
    { solv_thread. rewrite H_tp_cs'. auto. }

    destruct Hsim_cur_top as [core_config_sim Hsg].
    destruct core_config_sim as [R_top [Hldsim_top Hmatch_top] ].

    pose proof Hldsim_top as Hldsim_top'.
    eapply match_at_external in Hldsim_top; eauto.
    destruct Hldsim_top as [HGarg [i0' [args' Hldsim_top] ] ].
    destruct Hldsim_top as (H_core_atext' & Hargs & HLG & match_top').

    destruct tc eqn:Htc; simpl in *.

    assert (tb = O /\ ttid = stid).
    { generalize  H. clear. intro.
      inversion H; simpl in *.
      repeat norm_hypos.
      inversion H4; inversion H5; simpl in *; subst; auto. }
    destruct H1 as (?&?); subst.
    (* by simulation on modules in SGE and TGE, 
         we could init a related target core
     *)
    pose proof Hldsim_top' as Hldsim_top.
    eapply match_after_external in  Hldsim_top'; eauto; try (econstructor; eauto; fail).
    destruct Hldsim_top' as (tcc'' & H_core_aftext' & i0'' & Hmatch_top'').
    { instantiate (2:= sm). instantiate (1:= tm).
      generalize HLG Hldsim_top match_top'. clear. intros.
      eapply match_HG in Hldsim_top; eauto. clear match_top'.
      destruct HLG, Hldsim_top. destruct H, H2.
      constructor; auto; constructor; auto;
        try apply GMem.forward_refl; try apply GMem.unchanged_on_refl. }
    
    assert (exists tthdp', ThreadPool.update tthdp stid (<< i, tcc'', Core.sg c, F >>) tthdp')
      as H_tp_upd'.
    { generalize H_tp_core'; clear; intros; solv_thread'.
      eexists. econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto. }
    decompose_ex H_tp_upd'.      
    eexists _, FP.emp, ([[tthdp', stid, tm, I ]]), FP.emp. simpl.
    
    assert (np_step {| thread_pool := tthdp; cur_tid:= stid; gm := tm; atom_bit := O |} tau FP.emp
                    {| thread_pool := tthdp'; cur_tid:= stid; gm := tm; atom_bit := I |}) as Htstep.
    { eapply Ent_Atom; eauto.
      simpl in *. inversion Hargs. subst. auto.
      econstructor; eauto. }

    exists (i_wrap _ _ wf i0'').
    split; constructor. auto.
    split; auto.
    split. 
    { 
      (* * LFPG *)
      destruct (fp_match _ _ _ _ _ _ _ H). destruct H2.
      repeat rewrite fp_union_emp_r. auto.
    }
    {
      constructor; simpl in *.
      (* ** src_fwd *)
      inversion H; auto.
      (* ** tgt_fwd *)
      inversion H; auto.
      (* ** src mem inv *)
      { eapply GE_mod_wd_tp_inv_mem in H0; eauto.
        inversion H; auto.
        inversion H; auto.
      }
      (* ** tgt mem inv *)
      { eapply GE_mod_wd_tp_inv_mem in Htstep; eauto. simpl in *.
        inversion H; auto.
        inversion H; auto.
      }
      (* ** tp_match *)
      { split; [| split; constructor; auto].
        (* /need lemma for upd and dom_eq/ *)
        econstructor; eauto; simpl. intro t.
        eapply sttp_upd_ocs_match; eauto.
        apply tp_match in H. destruct H as [? _]. inversion H; subst; auto.
      }
      (* ** LFPG *)
      { pose proof (fp_match _ _ _ _ _ _ _ H). destruct H1 as (HLFPG&Hfpsubs&Hfpsubt).
        clear. split. constructor.
        constructor; constructor; intros; inversion H0. apply fpG_emp.
        split; constructor; intros b ofs H; solv_belongsto.
      }
      (* ** tp_inv src *)
      { eapply GE_mod_wd_tp_inv in H0; eauto. inversion H; auto. }
      (* ** tp_inv tgt *)
      { eapply GE_mod_wd_tp_inv in Htstep; eauto. inversion H; auto. }
      (* ** sim_invs cur *)
      { intros.
        assert (scs0 = c' :: scs).
        { generalize H_tp_cs H_tp_upd H1; clear; intros. repeat solv_thread. }
        subst scs0. unfold ThreadPool.get_cs in H1.
        exists ({| Core.i := i; Core.c := tcc''; Core.sg := Core.sg c; Core.F := F |} :: tcs).
        split. generalize H_tp_cs' H_tp_upd'. clear. intros.
        solv_thread'. solv_pmap. auto.
          
        constructor.
        (* current top sim *)
        { destruct c, c'; subst; simpl in *.
          inversion H_core_update. inversion H2.
          rewrite eq_sigT_iff_eq_dep in H6. subst.
          apply Eqdep.EqdepTheory.eq_dep_eq in H6. subst.
          constructor; simpl in *; auto.
          exists R_top. split; eauto. }
        (* current tail sim *)
        {
          (* tail *)
          generalize H Hsim_cur_tail H1 GE_wd_tgt. clear; intros.
          induction Hsim_cur_tail. constructor.
          specialize (IHHsim_cur_tail H). 
          econstructor; eauto.
        }
      }
      
      (* ** sim_invs other *)
      { intros.
        
        assert (ThreadPool.get_cs sthdp t = Some scs0).
        { generalize H_tp_upd H1 H2. clear. intros. solv_thread'. solv_pmap. auto. }

        assert (ThreadPool.get_cs tthdp t = Some tcs0).
        { generalize H_tp_upd' H1 H3. clear. intros. solv_thread'. solv_pmap. auto. }

        pose proof (tp_other_sim _ _ _ _ _ _ _ H t _ _ H1 H4 H5). auto.
      }
    }
    { inversion Hargs. constructor. }
  Qed.
  
  Lemma sim_sw_step:
    forall i fpS fpT fpS0 fpT0 spc tpc,
      Config_sim i fpS fpT fpS0 fpT0 spc tpc ->
      forall (o : ETrace.glabel) (spc' : ProgConfig) (fpS' : FP.t),
        o <> ETrace.tau ->
        np_step spc o fpS' spc' ->
        exists (fpT' : FP.t) (tpc' : ProgConfig) (i' : glob_index),
          np_step tpc o fpT' tpc' /\
          LFPG mu TGE (cur_tid tpc) (FP.union fpS0 fpS') (FP.union fpT0 fpT') /\
          Config_sim i' FP.emp FP.emp FP.emp FP.emp spc' tpc'.
  Proof.
    intros i fpS fpT fpS0 fpT0 spc tpc H o spc' fpS' H_o H_step.
    destruct spc as [sthdp stid sm b].
    destruct tpc as [tthdp ttid tm tb].
    destruct i.

    assert (ttid = stid /\ tb = b).
    { inversion H. destruct tp_match0 as (_ & ? & ?).
      inversion H0; inversion H1. subst; simpl in *; auto. }
    destruct H0; subst.
    
    inversion H_step; try (exfalso; apply H_o; auto; fail); subst; clear H_o.
    (** Thrd_Halt case *)
    {
      assert (ThreadPool.get_cs sthdp stid = Some (c :: nil)) as H_tp_cs.
      { solv_thread'. solv_pmap. solv_thread'. } 
      
      destruct (tp_cur_sim _ _ _ _ _ _ _ H _ H_tp_cs) as (tcs & H_tp_cs' & Hsim_cur_cs).
      destruct tcs as [ | tc ]; [ inversion Hsim_cur_cs | ].

      inversion Hsim_cur_cs; subst; clear Hsim_cur_cs.
      rename H8 into Hsim_cur_top. rename H9 into Hsim_cur_tail.

      assert (tcs = nil).
      { apply tp_match in H. destruct H as [H _].
        inversion H. subst. clear H. specialize (H2 stid).
        simpl in H2. rewrite H_tp_cs, H_tp_cs' in H2.
        inversion H2. subst. inversion H1. subst. inversion H. subst. inversion H0. subst.
        inversion H3. auto. }
      subst.
      
      assert (ThreadPool.get_top tthdp stid = Some tc) as H_tp_core' by solv_thread'.
      destruct tc eqn:Htc; simpl in *.
      
      destruct Hsim_cur_top as [core_config_sim Hsg].
      destruct core_config_sim as [R_top [Hldsim_top Hmatch_top] ].

      pose proof Hldsim_top as Hldsim_top'.
      eapply match_halt in Hldsim_top; eauto.
      destruct Hldsim_top as [HGarg [res' [H_core_halt'[Hres HLG] ] ] ].
      simpl in *.
      
      assert (exists tthdp', ThreadPool.pop tthdp stid = Some tthdp' /\ ThreadPool.halted tthdp' stid) as Htmp.
      { find_relatives tthdp. clear; intros.
        solv_thread'. eexists. split; eauto.
        econstructor; eauto. solv_thread'. solv_pmap. eauto.
        constructor. }
      decompose_ex Htmp. destruct Htmp as [H_tp_pop' H_thread_halt'].
      exists FP.emp, {| thread_pool:=tthdp'; cur_tid:= t'; gm:= tm; atom_bit:= O |}.

      assert (ThreadPool.inv thdp') as H_thdp'_inv.
      { eapply ThreadPool.pop_inv; eauto. inversion H; auto. }
      assert (ThreadPool.inv tthdp') as H_tthdp'_inv.
      { eapply ThreadPool.pop_inv; eauto. inversion H; auto. }

      assert (H_tid: ThreadPool.valid_tid tthdp' t' /\ ~ThreadPool.halted tthdp' t').
      {
        pose proof H as H'. apply tp_match in H. destruct H as [H _].
        inversion H; subst; clear H. simpl in *.
        rewrite thrddom_eq_valid_tid.
        4: intro; apply ocs_match_comm; eapply tp_pop_ocs_match in H2; eauto.
        2,3: auto.
        rewrite thrddom_eq_halted; eauto.
        intro; apply ocs_match_comm; eapply tp_pop_ocs_match in H2; eauto.
      }
      destruct H_tid as [H_thread_valid' H_not_halted'].

      (** find the next current thread *)
      assert (H_tid': t' <> stid).
      { find_relatives thdp'; clear; intros.
        intro. subst. congruence. }

      pose proof H_thread_valid as H_tp_cs_t'.
      rewrite (valid_tid_get_cs SGE thdp' t' H_thdp'_inv) in H_tp_cs_t'.
      destruct H_tp_cs_t' as [scs' H_tp_cs_t'].
      pose proof H_thread_valid' as H_tp_cs'_t'.
      rewrite (valid_tid_get_cs TGE tthdp' t' H_tthdp'_inv) in H_tp_cs'_t'.
      destruct H_tp_cs'_t' as [tcs' H_tp_cs'_t'].

      assert (ThreadPool.get_cs sthdp t' = Some scs').
      { generalize H_tid'. find_relatives thdp'; clear; intros.
        solv_thread'; solv_pmap; auto. }
      assert (ThreadPool.get_cs tthdp t' = Some tcs').
      { generalize H_tid'. find_relatives tthdp'; clear; intros.
        solv_thread'; solv_pmap; auto. }
      
      pose proof H as H'. apply tp_other_sim in H'.
      specialize (H' t' scs' tcs' H_tid' H0 H1).
      inversion H'.
      { subst. exfalso. generalize H_not_halted' H_tp_cs'_t'. clear; intros.
        apply H_not_halted'. econstructor; eauto. constructor. }

      subst. clear H'.
      inversion H2. 
      edestruct core_config_sim_block0 as
          (R_t' & Hsim_top_t' & Hmatch_top_t').
      { eapply match_HG in Hldsim_top'; eauto.
        destruct Hldsim_top', HLG. destruct H4, g. 
        destruct mem_rely_src_block0, mem_rely_tgt_block0.
        constructor; eauto; constructor; eauto. }
      destruct Hmatch_top_t' as [i_t' Hmatch_top_t''].

      assert (well_founded index_order) as Hwf by (inversion Hsim_top_t'; auto).

      assert (TGE ||- [[tthdp, stid, tm, O]] =< sw | FP.emp >=>> [[tthdp', t', tm, O]]).
      { eapply Thrd_Halt; eauto. }
      
      exists (i_wrap _ _ Hwf i_t').

      split. auto.
      split. do 2 rewrite fp_union_emp_r. apply fp_match in H. destruct H. auto.
      
      econstructor; eauto.
      { inversion H; auto. }
      { inversion H; auto. }
      { eapply GE_mod_wd_tp_inv_mem; eauto.
        inversion H; auto.
        inversion H; auto. }
      { eapply GE_mod_wd_tp_inv_mem; eauto.
        inversion H; eauto.
        inversion H; auto. }
      { 
      (* ** tp_match *)
      { split; [| split; constructor; auto].
        (* /need lemma for upd and dom_eq/ *)
        econstructor; eauto; simpl. intro t.
        generalize H_tp_pop, H_tp_pop', H. clear; intros.
        apply tp_match in H. destruct H as [? _]. inversion H; subst.
        eapply tp_pop_ocs_match; eauto. }
      }
      (* ** LFPG *)
      { clear. split. 
        constructor.
        constructor; constructor; intros; inversion H0. apply fpG_emp.
        split; constructor; intros b ofs H'; inversion H'.
      }
      (* ** sim_invs cur *)
      { intros.
        assert (scs0 = sCore :: scs).
        { find_relatives thdp'. clear. intros. solv_thread'. }
        subst scs0.
        exists (tCore :: tcs). split. auto.
        constructor; auto. constructor; eauto.
      }
      
      (* ** sim_invs other *)
      { intros.
        destruct (peq t stid).
        { (** the current thread before switch *)
          subst. clear H5.
          assert (scs0 = nil /\ tcs0 = nil).
          { find_relatives thdp'; find_relatives tthdp'; clear; intros.
            solv_thread'. }
          destruct H5; subst. constructor. }
        { inversion H. eapply tp_other_sim0; eauto.
          generalize n. find_relatives thdp'; clear; intros; solv_thread'; solv_pmap; auto.
          generalize n. find_relatives tthdp'; clear; intros; solv_thread'; solv_pmap; auto.
        }
      }
    }

    { (** Ext_Atom *)
      assert (exists scs, ThreadPool.get_cs sthdp stid = Some (c :: scs)) as H_tp_cs.
      { solv_thread'. } 
      decompose_ex H_tp_cs.
      
      destruct (tp_cur_sim _ _ _ _ _ _ _ H _ H_tp_cs) as (tcs & H_tp_cs' & Hsim_cur_cs).
      destruct tcs as [ | tc ]; [ inversion Hsim_cur_cs | ].

      inversion Hsim_cur_cs; subst; clear Hsim_cur_cs.
      rename H8 into Hsim_cur_top. rename H9 into Hsim_cur_tail.

      assert (ThreadPool.get_top tthdp stid = Some tc) as H_tp_core' by
            (generalize H_tp_cs'; clear; intros; solv_thread').
      destruct tc eqn:Htc; simpl in *.
      
      destruct Hsim_cur_top as [core_config_sim Hsg].
      destruct core_config_sim as [R_top [Hldsim_top Hmatch_top] ].

      pose proof Hldsim_top as Hldsim_top'.
      pose proof Hldsim_top as Hldsim_top''.
      eapply match_at_external in Hldsim_top'; eauto.
      destruct Hldsim_top' as [_ (i' & artTgt & H_core_atext' & Hargs & HLG & Hmatch_top')].
      eapply match_after_external in Hldsim_top''; eauto.
      3: instantiate (1:= None); simpl; auto.
      2: constructor.
      destruct Hldsim_top'' as (tc' & H_core_aftext' & Hldsim_top'').
      simpl in *.

      assert (Core.update (<<i0,c0,sg,F>>) tc' (<<i0,tc',sg,F>>)) as H_core_update'.
      { constructor. auto. }
      assert (exists tthdp', ThreadPool.update tthdp stid (<<i0,tc',sg,F>>) tthdp') as H_tp_upd'.
      { generalize H_tp_core'. clear. intros. solv_thread'.
        eexists. econstructor; solv_thread'. econstructor. econstructor; eauto. }
      decompose_ex H_tp_upd'.

      assert (ThreadPool.inv thdp') as H_thdp'_inv.
      { eapply ThreadPool.upd_top_inv; eauto. inversion H; auto. }
      assert (ThreadPool.inv tthdp') as H_tthdp'_inv.
      { eapply ThreadPool.upd_top_inv; eauto. inversion H; auto. }

      assert (ThreadPool.valid_tid tthdp' t' /\ ~ThreadPool.halted tthdp' t').
      { pose proof H as H'. apply tp_match in H. destruct H as [H _].
        inversion H; subst; clear H. simpl in *.
        rewrite thrddom_eq_valid_tid.
        4: intro; apply ocs_match_comm; eapply sttp_upd_ocs_match in H2; eauto.
        2,3: auto.
        rewrite thrddom_eq_halted; eauto.
        intro; apply ocs_match_comm; eapply sttp_upd_ocs_match in H2; eauto.
      }
      destruct H0 as [H_thread_valid' H_not_halted'].

      assert (TGE ||- [[tthdp, stid, tm, I]] =< sw | FP.emp >=>> [[tthdp', t', tm, O]])
        as Htstep.
      { eapply Ext_Atom; eauto. simpl. inversion Hargs. subst. auto. }
      exists FP.emp, ([[tthdp', t', tm, O]]).
      assert (LFPG mu TGE stid (FP.union fpS0 FP.emp) (FP.union fpT0 FP.emp)) as HLFPG.
      { do 2 rewrite fp_union_emp_r. inversion H. destruct fp_match0. auto. }

      cut (exists i'0, Config_sim i'0 FP.emp FP.emp FP.emp FP.emp
                             ([[thdp', t', sm, O]]) ([[tthdp', t', tm, O]])).
      destruct 1. exists x; auto.

      assert (ThreadPool.inv_mem thdp' sm) as H_inv_mem.
      { eapply GE_mod_wd_tp_inv_mem in H_step; eauto.
        inversion H; auto.
        inversion H; auto. }
      assert (ThreadPool.inv_mem tthdp' tm) as H_inv_mem'.
      { eapply GE_mod_wd_tp_inv_mem in Htstep; eauto.
        inversion H; eauto.
        inversion H; auto. }
      assert (thrddom_eq ([[thdp',t',sm,O]]) ([[tthdp',t',tm,O]]) /\
              atombit_eq ([[thdp',t',sm,O]]) ([[tthdp',t',tm,O]]) /\
              tid_eq ([[thdp',t',sm,O]]) ([[tthdp',t',tm,O]])) as H_tp_match'.
      (* ** tp_match *)
      { split; [| split; constructor; auto].
        (* /need lemma for upd and dom_eq/ *)
        econstructor; eauto; simpl. intro t.
        generalize H_tp_upd, H_tp_upd', H. clear; intros.
        apply tp_match in H. destruct H as [? _]. inversion H; subst.
        eapply sttp_upd_ocs_match; eauto. }
      assert (LFPG mu TGE t' FP.emp FP.emp /\
              FP.subset FP.emp FP.emp/\ FP.subset FP.emp FP.emp) as HLFPG'.
      (* ** LFPG *)
      { clear. split. 
        constructor.
        constructor; constructor; intros; inversion H0. apply fpG_emp.
        split; constructor; intros b ofs H'; inversion H'. }

      assert (ThreadPool.get_cs thdp' stid = Some (c' :: scs)) as H_tp_cs_aft.
      { find_relatives thdp'. clear; intros. solv_thread'; solv_pmap. auto. }
      assert (ThreadPool.get_cs tthdp' stid = Some (<<i0,tc',sg,F>> :: tcs)) as H_tp_cs_aft'.
      { find_relatives tthdp'. clear; intros. solv_thread'; solv_pmap. auto. }
      
      (** find the next current thread *)
      destruct (peq t' stid).
      {
        (** t' = stid *)
        subst.
        destruct (Hldsim_top'' sm tm).
        { eapply match_HG in Hldsim_top; eauto.
          destruct Hldsim_top, HLG.
          destruct H1, H0.
          constructor; auto; constructor; auto;
            try apply GMem.forward_refl;
            try apply GMem.unchanged_on_refl. }
        exists (i_wrap _ _ wf x).
        constructor; try (inversion H; auto; fail).
        { (** current sim *)
          intros.
          assert (scs0 = c' :: scs) by congruence; subst.
          eexists; split; eauto.
          constructor; auto.
          destruct c,c'. inversion H_core_update; subst.
          inversion H2. rewrite eq_sigT_iff_eq_dep in H5. subst.
          apply Eqdep.EqdepTheory.eq_dep_eq in H5. subst. simpl in *. clear H2.
          constructor; eauto. }
        { (** other sim *)
          inversion H. intros. eapply tp_other_sim0; eauto.
          rewrite <- H2.
          generalize H1; find_relatives thdp'; clear; intros; solv_thread'; solv_pmap; auto.
          rewrite <- H3.
          generalize H1; find_relatives tthdp'; clear; intros; solv_thread'; solv_pmap; auto.
        }
      }
      {
        (** t' <> stid *)
        assert (exists scs', ThreadPool.get_cs thdp' t' = Some scs').
        { apply valid_tid_get_cs; auto. }
        destruct H0 as (scs' & H_thdp'_scs').
        assert (exists tcs', ThreadPool.get_cs tthdp' t' = Some tcs').
        { apply valid_tid_get_cs; auto. }
        destruct H0 as (tcs' & H_tthdp'_tcs').
        assert (ThreadPool.get_cs sthdp t' = Some scs').
        { generalize n. find_relatives thdp'. clear; intros.
          solv_thread'; solv_pmap; auto. }
        assert (ThreadPool.get_cs tthdp t' = Some tcs').
        { generalize n. find_relatives tthdp'. clear; intros.
          solv_thread'; solv_pmap; auto. }

        pose proof H as H'. apply tp_other_sim in H'.
        specialize (H' t' scs' tcs' n H0 H1).
        inversion H'.
        { subst. exfalso. generalize H_not_halted' H_tthdp'_tcs'. clear; intros.
          apply H_not_halted'. econstructor; eauto. constructor. }

        subst. clear H'.
        inversion H2. 
        edestruct core_config_sim_block0 as
            (R_t' & Hsim_top_t' & Hmatch_top_t').
        { eapply match_HG in Hldsim_top; eauto.
          destruct Hldsim_top, HLG. destruct H4, g.
          destruct mem_rely_src_block0, mem_rely_tgt_block0.
          constructor; eauto; constructor; eauto. }
        destruct (Hmatch_top_t') as [i_t' Hmatch_top_t''].

        assert (well_founded index_order) as Hwf by (inversion Hsim_top_t'; auto).

        exists (i_wrap _ _ Hwf i_t').

        econstructor; eauto.
        { inversion H; auto. }
        { inversion H; auto. }
        (* ** sim_invs cur *)
        { intros.
          assert (scs1 = sCore :: scs0).
          { find_relatives thdp'. clear. intros. solv_thread'. }
          subst scs1.
          exists (tCore :: tcs0). split. auto.
          constructor; auto. constructor; eauto.
        }
        (* ** sim_invs other *)
        { intros.
          destruct (peq t stid).
          { (** the current thread before switch *)
            subst. 
            assert (scs1 = (c'::scs) /\ tcs1 = (<<i0,tc',Core.sg c, F>>)::tcs).
            { find_relatives thdp'; find_relatives tthdp'; clear; intros.
              solv_thread'. }
            destruct H7; subst.
            (* dependent types.... *)
            destruct c,c'. inversion H_core_update; subst.
            inversion H7. rewrite eq_sigT_iff_eq_dep in H10. subst.
            apply Eqdep.EqdepTheory.eq_dep_eq in H10. subst. simpl in *. clear H7.
            econstructor; eauto.
            econstructor; eauto.
            split; [apply GMem.forward_refl|apply GMem.unchanged_on_refl]; eauto.
            split; [apply GMem.forward_refl|apply GMem.unchanged_on_refl]; eauto.
          }
          { inversion H. eapply tp_other_sim0; eauto.
            generalize n0.
            find_relatives thdp'; clear; intros; solv_thread'; solv_pmap; auto.
            generalize n0.
            find_relatives tthdp'; clear; intros; solv_thread'; solv_pmap; auto.
          }
        }
      }
    }

    { (** Ext_Atom *)
      assert (exists scs, ThreadPool.get_cs sthdp stid = Some (c :: scs)) as H_tp_cs.
      { solv_thread'. } 
      decompose_ex H_tp_cs.
      
      destruct (tp_cur_sim _ _ _ _ _ _ _ H _ H_tp_cs) as (tcs & H_tp_cs' & Hsim_cur_cs).
      destruct tcs as [ | tc ]; [ inversion Hsim_cur_cs | ].

      inversion Hsim_cur_cs; subst; clear Hsim_cur_cs.
      rename H8 into Hsim_cur_top. rename H9 into Hsim_cur_tail.

      assert (ThreadPool.get_top tthdp stid = Some tc) as H_tp_core' by
            (generalize H_tp_cs'; clear; intros; solv_thread').
      destruct tc eqn:Htc; simpl in *.
      
      destruct Hsim_cur_top as [core_config_sim Hsg].
      destruct core_config_sim as [R_top [Hldsim_top Hmatch_top] ].

      pose proof Hldsim_top as Hldsim_top'.
      pose proof Hldsim_top as Hldsim_top''.
      eapply match_at_external in Hldsim_top'; eauto.
      destruct Hldsim_top' as
          [HGargS (i' & artTgt & H_core_atext' & Hargs & HLG & Hmatch_top')].
      eapply match_after_external in Hldsim_top''; eauto.
      3: instantiate (1:= None); simpl; auto.
      2: constructor.
      destruct Hldsim_top'' as (tc' & H_core_aftext' & Hldsim_top'').
      simpl in *.

      assert (Core.update (<<i0,c0,sg,F>>) tc' (<<i0,tc',sg,F>>)) as H_core_update'.
      { constructor. auto. }
      assert (exists tthdp', ThreadPool.update tthdp stid (<<i0,tc',sg,F>>) tthdp') as H_tp_upd'.
      { generalize H_tp_core'. clear. intros. solv_thread'.
        eexists. econstructor; solv_thread'. econstructor. econstructor; eauto. }
      decompose_ex H_tp_upd'.

      assert (ThreadPool.inv thdp') as H_thdp'_inv.
      { eapply ThreadPool.upd_top_inv; eauto. inversion H; auto. }
      assert (ThreadPool.inv tthdp') as H_tthdp'_inv.
      { eapply ThreadPool.upd_top_inv; eauto. inversion H; auto. }

      assert (ThreadPool.valid_tid tthdp' t' /\ ~ThreadPool.halted tthdp' t').
      { pose proof H as H'. apply tp_match in H. destruct H as [H _].
        inversion H; subst; clear H. simpl in *.
        rewrite thrddom_eq_valid_tid.
        4: intro; apply ocs_match_comm; eapply sttp_upd_ocs_match in H2; eauto.
        2,3: auto.
        rewrite thrddom_eq_halted; eauto.
        intro; apply ocs_match_comm; eapply sttp_upd_ocs_match in H2; eauto.
      }
      destruct H0 as [H_thread_valid' H_not_halted'].

      assert (TGE ||- [[tthdp, stid, tm, O]] =< evt v | FP.emp >=>> [[tthdp', t', tm, O]])
        as Htstep.
      { eapply EF_Print; eauto. simpl. inversion Hargs. subst. inversion H4. subst.
        generalize H_v H2 H_core_atext'. clear. intros.
        inversion H2; subst v'; auto.
        subst v. inversion H_v.
        subst v. inversion H_v. }
      
      exists FP.emp, ([[tthdp', t', tm, O]]).
      assert (LFPG mu TGE stid (FP.union fpS0 FP.emp) (FP.union fpT0 FP.emp)) as HLFPG.
      { do 2 rewrite fp_union_emp_r. inversion H. destruct fp_match0. auto. }

      cut (exists i'0, Config_sim i'0 FP.emp FP.emp FP.emp FP.emp
                             ([[thdp', t', sm, O]]) ([[tthdp', t', tm, O]])).
      destruct 1. exists x; auto.

      assert (ThreadPool.inv_mem thdp' sm) as H_inv_mem.
      { eapply GE_mod_wd_tp_inv_mem in H_step; eauto.
        inversion H; auto.
        inversion H; auto. }
      assert (ThreadPool.inv_mem tthdp' tm) as H_inv_mem'.
      { eapply GE_mod_wd_tp_inv_mem in Htstep; eauto.
        inversion H; eauto.
        inversion H; auto. }
      assert (thrddom_eq ([[thdp',t',sm,O]]) ([[tthdp',t',tm,O]]) /\
              atombit_eq ([[thdp',t',sm,O]]) ([[tthdp',t',tm,O]]) /\
              tid_eq ([[thdp',t',sm,O]]) ([[tthdp',t',tm,O]])) as H_tp_match'.
      (* ** tp_match *)
      { split; [| split; constructor; auto].
        (* /need lemma for upd and dom_eq/ *)
        econstructor; eauto; simpl. intro t.
        generalize H_tp_upd, H_tp_upd', H. clear; intros.
        apply tp_match in H. destruct H as [? _]. inversion H; subst.
        eapply sttp_upd_ocs_match; eauto. }
      assert (LFPG mu TGE t' FP.emp FP.emp /\
              FP.subset FP.emp FP.emp/\ FP.subset FP.emp FP.emp) as HLFPG'.
      (* ** LFPG *)
      { clear. split. 
        constructor.
        constructor; constructor; intros; inversion H0. apply fpG_emp.
        split; constructor; intros b ofs H'; inversion H'. }

      assert (ThreadPool.get_cs thdp' stid = Some (c' :: scs)) as H_tp_cs_aft.
      { find_relatives thdp'. clear; intros. solv_thread'; solv_pmap. auto. }
      assert (ThreadPool.get_cs tthdp' stid = Some (<<i0,tc',sg,F>> :: tcs)) as H_tp_cs_aft'.
      { find_relatives tthdp'. clear; intros. solv_thread'; solv_pmap. auto. }
      
      (** find the next current thread *)
      destruct (peq t' stid).
      {
        (** t' = stid *)
        subst.
        destruct (Hldsim_top'' sm tm).
        { eapply match_HG in Hldsim_top; eauto.
          destruct Hldsim_top, HLG.
          destruct H1, H0.
          constructor; auto; constructor; auto;
            try apply GMem.forward_refl;
            try apply GMem.unchanged_on_refl. }
        exists (i_wrap _ _ wf x).
        constructor; try (inversion H; auto; fail).
        { (** current sim *)
          intros.
          assert (scs0 = c' :: scs) by congruence; subst.
          eexists; split; eauto.
          constructor; auto.
          destruct c,c'. inversion H_core_update; subst.
          inversion H2. rewrite eq_sigT_iff_eq_dep in H5. subst.
          apply Eqdep.EqdepTheory.eq_dep_eq in H5. subst. simpl in *. clear H2.
          constructor; eauto. }
        { (** other sim *)
          inversion H. intros. eapply tp_other_sim0; eauto.
          rewrite <- H2.
          generalize H1; find_relatives thdp'; clear; intros; solv_thread'; solv_pmap; auto.
          rewrite <- H3.
          generalize H1; find_relatives tthdp'; clear; intros; solv_thread'; solv_pmap; auto.
        }
      }
      {
        (** t' <> stid *)
        assert (exists scs', ThreadPool.get_cs thdp' t' = Some scs').
        { apply valid_tid_get_cs; auto. }
        destruct H0 as (scs' & H_thdp'_scs').
        assert (exists tcs', ThreadPool.get_cs tthdp' t' = Some tcs').
        { apply valid_tid_get_cs; auto. }
        destruct H0 as (tcs' & H_tthdp'_tcs').
        assert (ThreadPool.get_cs sthdp t' = Some scs').
        { generalize n. find_relatives thdp'. clear; intros.
          solv_thread'; solv_pmap; auto. }
        assert (ThreadPool.get_cs tthdp t' = Some tcs').
        { generalize n. find_relatives tthdp'. clear; intros.
          solv_thread'; solv_pmap; auto. }

        pose proof H as H'. apply tp_other_sim in H'.
        specialize (H' t' scs' tcs' n H0 H1).
        inversion H'.
        { subst. exfalso. generalize H_not_halted' H_tthdp'_tcs'. clear; intros.
          apply H_not_halted'. econstructor; eauto. constructor. }

        subst. clear H'.
        inversion H2. 
        edestruct core_config_sim_block0 as
            (R_t' & Hsim_top_t' & Hmatch_top_t').
        { eapply match_HG in Hldsim_top; eauto.
          destruct Hldsim_top, HLG. destruct H4, g.
          destruct mem_rely_src_block0, mem_rely_tgt_block0.
          constructor; eauto; constructor; eauto. }
        destruct (Hmatch_top_t') as [i_t' Hmatch_top_t''].


        assert (well_founded index_order) as Hwf by (inversion Hsim_top_t'; auto).

        exists (i_wrap _ _ Hwf i_t').

        econstructor; eauto.
        { inversion H; auto. }
        { inversion H; auto. }
        (* ** sim_invs cur *)
        { intros.
          assert (scs1 = sCore :: scs0).
          { find_relatives thdp'. clear. intros. solv_thread'. }
          subst scs1.
          exists (tCore :: tcs0). split. auto.
          constructor; auto. constructor; eauto.
        }
        (* ** sim_invs other *)
        { intros.
          destruct (peq t stid).
          { (** the current thread before switch *)
            subst. 
            assert (scs1 = (c'::scs) /\ tcs1 = (<<i0,tc',Core.sg c, F>>)::tcs).
            { find_relatives thdp'; find_relatives tthdp'; clear; intros.
              solv_thread'. }
            destruct H7; subst.
            (* dependent types.... *)
            destruct c,c'. inversion H_core_update; subst.
            inversion H7. rewrite eq_sigT_iff_eq_dep in H10. subst.
            apply Eqdep.EqdepTheory.eq_dep_eq in H10. subst. simpl in *. clear H7.
            econstructor; eauto.
            econstructor; eauto.
            split; [apply GMem.forward_refl|apply GMem.unchanged_on_refl]; eauto.
            split; [apply GMem.forward_refl|apply GMem.unchanged_on_refl]; eauto.
          }
          { inversion H. eapply tp_other_sim0; eauto.
            generalize n0.
            find_relatives thdp'; clear; intros; solv_thread'; solv_pmap; auto.
            generalize n0.
            find_relatives tthdp'; clear; intros; solv_thread'; solv_pmap; auto.
          }
        }
      }
    }
  Qed.

  Definition match_state :=
    fun i mu' fpS0 fpT0 spc tpc =>
      (mu' = mu /\ Bset.inj_inject (inj mu')) /\
      exists fpS fpT,
        Config_sim i fpS fpT fpS0 fpT0 spc tpc.
  
  Theorem Config_sim_GConfigDSim:
    GConfigDSim glob_index glob_order match_state.
  Proof.
    constructor; intros.
    (* index_order well founded *)
    { apply glob_order_wf. }
    (* tp matches *)
    { inversion H. destruct H1 as (fpS0 & fpT0 & H1). inversion H1.
      destruct tp_match0.
      split; auto. apply thrddom_eq_thrddom_eq'. auto. }
    (* tau-step *)
    { inversion H. subst.
      destruct H3 as (fp0 & fpT0 & H3).
      eapply sim_tau_step in H0; eauto.
      destruct H0. destruct H2; subst.
      left.
      destruct H0 as (tpc'&fpT'&i'&fpS''&fpT''&Hstep&HLFPG&Hsim).
      exists tpc', fpT', i'.
      split; auto. split; auto.
      unfold match_state; split; eauto.
      right.
      unfold match_state. do 2 destruct H0. exists x. eauto.
    }
    (* ent-atom *)
    { destruct H. destruct H. subst.
      destruct H2 as (fpS0&fpT0&?).
      pose proof H.
      eapply sim_ent_atom in H; eauto.
      destruct H as (tpc'&fpT'&tpc''&fpT''&i'&Hstar&Hatombit&Hent&HFP&Hsim).
      unfold match_state.
      exists tpc', fpT', tpc'', fpT'', i'.
      do 4 (split; eauto).
    }
    (* evt-step *)
    { inversion H. destruct H2. subst.
      destruct H3 as (fpS0&fpT0&?).
      pose proof H2.
      eapply sim_sw_step in H2; eauto.
      destruct H2 as (?&?&?&?&?&?).
      do 3 eexists. split; eauto. split; eauto.
      unfold match_state.
      split; eauto. }
    (* final-state *)
    { destruct H as (?&?&?&?). destruct H. subst. eapply sim_final; eauto. }
    { inversion H. destruct H0. auto. }
  Qed.
  
End StateInvs.

