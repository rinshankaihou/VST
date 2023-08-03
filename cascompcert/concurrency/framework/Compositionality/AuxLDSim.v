Require Import Coqlib Globalenvs Values AST.
Require Import Blockset Footprint GMemory MemAux MemClosures
        InteractionSemantics Injections LDSimDefs LDSim ReachClose.

(** ** Auxilliary ldsim definition:
    with reach-close, we are able to give a RGSim-like simulation *)

(** Auxilliary Module Local Simulation *)

Record config_ldsim_aux {sl tl: Language}
       (index: Type)
       (index_order: index -> index -> Prop)
       (* bool: the next step is G step (true) or R step (false). *)
       (sfl tfl: freelist)
       (sG: G sl)
       (tG: G tl)
       (sge: Genv.t (F sl) (V sl))
       (tge: Genv.t (F tl) (V tl))
       (match_state: bool -> index -> Mu -> FP.t -> FP.t ->
                     ((core sl) * gmem) -> ((core tl) * gmem) -> Prop): Prop :=
  {
    index_wf: well_founded index_order;
    
    wd_mu: forall b i mu Hfp Lfp Hc Lc,
        match_state b i mu Hfp Lfp Hc Lc ->
        Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) /\
        no_overlap sfl (SharedSrc mu) /\
        no_overlap tfl (SharedTgt mu)
    ;

    match_mu_ge: forall b i mu Hfp Lfp Hc Lc,
      match_state b i mu Hfp Lfp Hc Lc ->
      ge_init_inj mu sge tge
    ;
      

    match_HG: forall b i mu Hfp Lfp Hcore Hm Lcore Lm,
        match_state b i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        HG sfl mu Hfp Hm;

    match_init: forall mu id argSrc argTgt score,
        (** constraints on arguments *)
        ge_init_inj mu sge tge ->
        G_args (SharedSrc mu) argSrc ->
        arg_rel (inj mu) argSrc argTgt ->
        init_core sl sG id argSrc = Some score ->
        exists tcore,
          init_core tl tG id argTgt = Some tcore /\
          (forall sm tm, 
              (** constraint on [sm] and [tm] *)
              init_gmem sl sge sm ->
              init_gmem tl tge tm ->
              local_init_rel mu sfl sm tfl tm ->
              forall sm' tm',
                HLRely sfl tfl mu sm sm' tm tm' ->
                exists i, match_state true i mu FP.emp FP.emp (score, sm') (tcore, tm'))
    ;
    
    match_tau_step: forall i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm',
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (step sl) sG sfl Hcore Hm Hfp' Hcore' Hm' ->
        ( (* 1) no step, index decrease *)
          (exists i',
              index_order i' i /\
              match_state true i' mu (FP.union Hfp Hfp') Lfp (Hcore', Hm') (Lcore, Lm))
          \/
          (* 2) plus step, fp matched *)
          (exists i' Lfp' Lcore' Lm',
              plus (step tl tG tfl) Lcore Lm Lfp' Lcore' Lm' /\
              LfpG' tfl mu (FP.union Hfp Hfp') (FP.union Lfp Lfp') /\
              match_state true i' mu (FP.union Hfp Hfp') (FP.union Lfp Lfp') (Hcore', Hm') (Lcore', Lm'))
        )
    ;

    match_at_external: forall i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc,
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (at_external sl) sG Hcore = Some (f, sg, argSrc) ->
        G_args (SharedSrc mu) argSrc /\
        exists i' argTgt,
          (at_external tl) tG Lcore = Some (f, sg, argTgt) /\
          (* arguments are related *)
          arg_rel (inj mu) argSrc argTgt /\
          LG' tfl mu Hfp Hm Lfp Lm /\
          match_state false i' mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm)
    ;
    
    match_after_external: forall i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt,
        match_state false i mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm) ->
        G_oarg (SharedSrc mu) oresSrc ->
        (after_external sl) Hcore oresSrc = Some Hcore' ->
        ores_rel (inj mu) oresSrc oresTgt ->
        exists Lcore',
          (after_external tl) Lcore oresTgt = Some Lcore' /\
          (forall Hm' Lm', HLRely sfl tfl mu Hm Hm' Lm Lm' ->
                      exists i', match_state true i' mu FP.emp FP.emp (Hcore', Hm') (Lcore', Lm'))
    ;

    match_halt: forall i mu Hfp Lfp Hcore Hm Lcore Lm resSrc,
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (halt sl) Hcore = Some resSrc ->
        G_arg (SharedSrc mu) resSrc /\
        exists resTgt,
          (halt tl) Lcore = Some resTgt /\
          (* return val related *)
          res_rel (inj mu) resSrc resTgt /\
          (* return state related, fp matched *)
          LG' tfl mu Hfp Hm Lfp Lm
  }.

Lemma config_rc_ldsim_ldsimaux:
  forall sl tl index index_order sfl tfl sG tG sge tge R I,
    @config_ldsim sl tl index index_order sfl tfl sG tG sge tge R ->
    rc_inv sG sge I ->
    wd sl ->
    exists R', config_ldsim_aux index index_order sfl tfl sG tG sge tge R'.
Proof.
  intros sl tl index index_order sfl tfl sG tG sge tge R I CONFIGSIM RCINV WDSL.
  remember (fun b i mu fp fp' sc tc =>
              R b i mu fp fp' sc tc /\
              I (SharedSrc mu) sfl (fst sc) (snd sc) /\
              HG sfl mu fp (snd sc)) as R'.
  exists R'.
  constructor; intros; subst R'. 
  { inversion CONFIGSIM. auto. }
  { inversion CONFIGSIM. destruct H. eapply wd_mu0; eauto. }
  { inversion CONFIGSIM. destruct H. eauto. }
  { tauto. }
  { pose proof (LDSim.match_init _ _ _ _ _ _ _ _ _ CONFIGSIM _ _ _ _ _ H H0 H1 H2).
    destruct H3 as (tcore, (INIT, MATCH)).
    exists tcore. split. auto. intros sm tm SINIT TINIT INITREL sm' tm' RELY.
    specialize (MATCH sm tm SINIT TINIT INITREL sm' tm' RELY). destruct MATCH as (i, MATCH).
    exists i. split; auto. simpl. split.
    inv RELY. inv H3. eapply rc_rely_step; eauto.
    inv INITREL. eapply rc_init. eauto. auto.
    erewrite mu_shared_src; eauto. intros b. auto.
    unfold valid_block_bset. intros b ? . apply valid_Src. auto.
    tauto. auto. eauto. eauto.
    constructor. constructor. apply fpG_emp. inv RELY. inv H3. auto. }
  { inversion CONFIGSIM. inversion RCINV. 
    clear match_halt0 match_after_external0 match_at_external0 index_wf0 wd_mu0 rc_atext rc_aftext rc_halt.
    destruct H as (MATCH&RCI&HGINV).
    specialize (rc_step _ _ _ _ _ _ _ RCI H0). destruct rc_step. destruct H.
    assert (HfpG sfl mu Hfp') by (constructor; auto).
    specialize (match_tau_step0 _ _ _ _ _ _ _ _ _ _ _ MATCH H0 H3). clear H3.
    destruct match_tau_step0.
    left. destruct H3 as (i'&Hord&HR').
    exists i'. split; auto. split; auto. split; auto.
    constructor. constructor; auto.
    destruct HGINV. destruct H3.
    apply fpG_union; auto. 
    right. destruct H3 as (i'&Lfp'&Lcore'&Lm'&Hplus&HLfpG&HR').
    exists i', Lfp', Lcore', Lm'. simpl. split; auto. split; auto. split; auto. split; auto.
    constructor. constructor; auto.
    destruct HGINV. destruct H3.
    apply fpG_union; auto.
  }
  { inversion RCINV. destruct H as (MATCH&RCI&HGINV).
    specialize (rc_atext _ _ _ _ _ _ _ RCI H0). destruct rc_atext.
    clear rc_step rc_aftext rc_halt.
    split; auto. 
    inversion CONFIGSIM.
    clear match_halt0 match_after_external0 match_tau_step0 index_wf0 wd_mu0.
    specialize (match_at_external0 _ _ _ _ _ _ _ _ _ _ _ MATCH H0 HGINV H).
    destruct match_at_external0 as (i'&argTgt&Hatext&Hargrel&HLG&HR').
    exists i', argTgt.
    do 5 (split; auto). constructor. constructor. apply fpG_emp. eapply rc_closed; eauto.
  }
  { simpl in *. inversion RCINV. inversion CONFIGSIM.
    clear match_halt0 match_at_external0 match_tau_step0 index_wf0 wd_mu0.
    destruct H as (MATCH&RCI&HGINV).
    destruct (match_after_external0 _ _ _ _ _ _ _ _ _ MATCH H0 H1 H2) as (Lcore' & Haft & Hrely).
    exists Lcore'. split; [auto|intros].
    destruct (Hrely _ _ H) as [i' Hmatch].
    exists i'. split; [auto|].
    inversion H. inversion H3.
    specialize (rc_aftext _ _ _ _ _ _ _ RCI H1 H0 H8).
    split; auto.
    constructor. constructor; simpl in *; auto. apply fpG_emp.
  }
  { inversion RCINV. clear rc_step rc_atext rc_aftext.
    destruct H as (MATCH&RCI&HGINV).
    specialize (rc_halt _ _ _ _ _ RCI H0).
    split; auto.
    inversion CONFIGSIM. clear match_tau_step0 match_at_external0 match_after_external0 wd_mu0 index_wf0.
    eapply match_halt0; eauto.
  }
Qed.

Definition ldsim_aux {sl tl: Language}
           (su: comp_unit sl) (tu: comp_unit tl) : Prop :=
  forall sG sge tG tge sfl tfl,
    init_genv sl su sge sG ->
    init_genv tl tu tge tG ->
    Genv.genv_next sge = Genv.genv_next tge ->
    exists index index_order match_state,
      config_ldsim_aux index index_order sfl tfl sG tG sge tge match_state.

Theorem ldsim_rc_ldsim_aux:
  forall (sl tl: Language) (su: comp_unit sl) (tu: comp_unit tl),
    ldsim su tu ->
    wd sl ->
    reach_close su ->
    ldsim_aux su tu.
Proof.
  intros sl tl su tu Hldsim Hwd Hrc
         sG sge tG tge sfl tfl Hinit_ge_su Hinit_ge_tu HGENVDOM.
  (* ldsim R *)
  specialize (Hldsim sG sge tG tge sfl tfl Hinit_ge_su Hinit_ge_tu HGENVDOM).
  destruct Hldsim as (index&index_order&match_state&Hsim).
  exists index, index_order.
  (* rc_inv I *)
  apply Hrc in Hinit_ge_su. destruct Hinit_ge_su as (I&RCINV).
  eapply config_rc_ldsim_ldsimaux; eauto.
Qed.
