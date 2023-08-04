Require Import Coqlib Maps Streams Errors Values Globalenvs.

Require Import Blockset Footprint Memory
        Injections MemClosures_local LDSimDefs LDSimDefs_local
        InteractionSemantics IS_local.

Require Import Events.

(** Local simulation over compcert memory *)

(** The ident-block bindings are captured by mu *)

(** Mem domain = Shared, Memories are injected *)
Record mem_init_inj (mu: Mu) (m tm: mem) : Prop :=
  {
    (** forall b, SharedSrc b <-> b < m.next_block *)
    dom_eq_src:
      forall b, Bset.belongsto (SharedSrc mu) b <-> Plt b (Mem.nextblock m);
    (** forall tb, SharedTgt b <-> b < tm.next_block *)
    dom_eq_tgt:
      forall tb, Bset.belongsto (SharedTgt mu) tb <-> Plt tb (Mem.nextblock tm);
    (** general memory injection m --inj--> tm *)
    mem_mu_inj:
      Mem.inject (Bset.inj_to_meminj (inj mu)) m tm;
    (** BUG: reach-close required but not implemented *)
    (** wd mu ? 
        TODO:
        wierd. We require all source shared blocks mapped by mu, 
        which implies we have same number of blocks in SharedSrc and SharedTgt,
        and mu.inj is in fact bijection.
        This requires that ge of source and target should be equal on domain *)
    wd_mu_init:
      Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu);
    
    inj_inject_id:
      inject_incr (Bset.inj_to_meminj (inj mu)) inject_id;
  }.

Record ge_match_strict {F1 V1 F2 V2: Type} (sge: Genv.t F1 V1) (tge: Genv.t F2 V2) : Prop :=
  {
    genv_public_eq: forall id, In id (Genv.genv_public sge) <-> In id (Genv.genv_public tge);
    genv_symb_eq: forall id, (Genv.genv_symb sge) ! id = (Genv.genv_symb tge) ! id;
    genv_defs_match: forall id b b',
        (Genv.genv_symb sge) ! id = Some b ->
        (Genv.genv_symb tge) ! id = Some b' ->
        option_rel globdef_match (Genv.genv_defs sge) ! b (Genv.genv_defs tge) ! b';
    genv_next_eq: Genv.genv_next sge = Genv.genv_next tge;
  }.

Section LocalSimulation.

Context {ssem tsem: sem_local}.


(** ** Module Local Simulation *)
Record local_ldsim_properties
       (index: Type)
       (index_order: index -> index -> Prop)
       (sG: G ssem)
       (tG: G tsem)
       (sge: Genv.t (F ssem) (V ssem))
       (tge: Genv.t (F tsem) (V tsem))
       (match_state: bool -> index -> Mu -> FP.t -> FP.t ->
                     ((core ssem) * mem) -> ((core tsem) * mem) -> Prop): Prop :=
  {
    index_wf: well_founded index_order;
    
    wd_mu: forall b i mu Hfp Lfp Hc Lc,
        match_state b i mu Hfp Lfp Hc Lc ->
        Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) 
    ;

    match_mu_ge: forall b i mu Hfp Lfp Hc Lc,
      match_state b i mu Hfp Lfp Hc Lc ->
      ge_init_inj mu sge tge;
    
    match_genv: ge_match_strict sge tge
    ;

    match_init: forall mu id argSrc argTgt score,
        (** constraints on arguments *)
        ge_init_inj mu sge tge ->
        (inject_incr (Bset.inj_to_meminj (inj mu)) inject_id) ->
        G_args (SharedSrc mu) argSrc ->
        arg_rel (inj mu) argSrc argTgt ->
        (** initial core matched *)
        init_core_local ssem sG id argSrc = Some score ->
        exists tcore,
          init_core_local tsem tG id argTgt = Some tcore /\
          (forall sm tm,
              (** constraint on [sm] and [tm] *)
              init_mem ssem sge sm ->
              init_mem tsem tge tm ->
              mem_init_inj mu sm tm ->
              forall sm' tm',
                LDefs.HLRely mu sm sm' tm tm' ->
                exists i, match_state true i mu FP.emp FP.emp (score, sm') (tcore, tm'))
    ;

    match_tau_step: forall i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm',
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (step_local ssem) sG Hcore Hm Hfp' Hcore' Hm' -> 
        (exists i', index_order i' i /\
               match_state true i' mu (FP.union Hfp Hfp') Lfp (Hcore', Hm') (Lcore, Lm))
        \/
        (exists i' Lfp' Lcore' Lm',
            plus (step_local tsem tG) Lcore Lm Lfp' Lcore' Lm' /\
            FPMatch' mu (FP.union Hfp Hfp') (FP.union Lfp Lfp') /\
            match_state true i' mu (FP.union Hfp Hfp') (FP.union Lfp Lfp') (Hcore', Hm') (Lcore', Lm'))
    ;

    match_at_external: forall i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc,
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (at_external_local ssem) sG Hcore = Some (f, sg, argSrc) ->
        reach_closed Hm (SharedSrc mu) ->
        G_args (SharedSrc mu) argSrc ->
        exists i' argTgt,
          (at_external_local tsem) tG Lcore = Some (f, sg, argTgt) /\
          arg_rel (inj mu) argSrc argTgt /\
          reach_closed Lm (SharedTgt mu) /\
          FPMatch' mu Hfp Lfp /\
          LDefs.Inv mu Hm Lm /\
          match_state false i' mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm)
    ;
    
    match_after_external: forall i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt,
        (** TODO: is this clause too strong for CompCert? *)
        match_state false i mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm) ->
        G_oarg (SharedSrc mu) oresSrc ->
        (after_external_local ssem) Hcore oresSrc = Some Hcore' ->
        ores_rel (inj mu) oresSrc oresTgt ->
        exists Lcore',
          (after_external_local tsem) Lcore oresTgt = Some Lcore' /\
          (forall Hm' Lm', LDefs.HLRely mu Hm Hm' Lm Lm' ->
                      exists i', match_state true i' mu FP.emp FP.emp (Hcore', Hm') (Lcore', Lm'))
    ;

    match_halt: forall i mu Hfp Lfp Hcore Hm Lcore Lm resSrc,
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (halt_local ssem) Hcore = Some resSrc ->
        reach_closed Hm (SharedSrc mu) ->
        G_arg (SharedSrc mu) resSrc ->
        exists resTgt,
          (halt_local tsem) Lcore = Some resTgt /\
          res_rel (inj mu) resSrc resTgt /\
          reach_closed Lm (SharedTgt mu) /\
          FPMatch' mu Hfp Lfp /\
          LDefs.Inv mu Hm Lm 
  }.
      

Inductive local_ldsim
          (sG: G ssem) (tG: G tsem)
          (sge: Genv.t (F ssem) (V ssem))
          (tge: Genv.t (F tsem) (V tsem)) : Prop :=
  Local_ldsim :
    forall I I_order match_state,
      local_ldsim_properties I I_order sG tG sge tge match_state ->
      local_ldsim sG tG sge tge.

Definition ldsim_local (su: comp_unit ssem) (tu: comp_unit tsem) : Prop :=
  forall sG sge tG tge,
    init_genv_local ssem su sge sG ->
    init_genv_local tsem tu tge tG ->
    Genv.genv_next sge = Genv.genv_next tge ->
    local_ldsim sG tG sge tge.

End LocalSimulation.