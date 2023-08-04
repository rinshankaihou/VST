Require Import Values.

Require Import Blockset Footprint GMemory InteractionSemantics GAST
        GlobDefs ETrace NPSemantics
        Injections GSimDefs.

(** * Global Downward Simulation *)

(** This file defines the global downward simulation [S < T].
    The definition is standard, 
    with additional constraints [LFPG] on footprint, 
    and additional clauses [match_ent_atom] and [match_npsw_step] 
    handling atomic blocks and switching points. *)

(* GDSIM e S T := S < T *)
Record GConfigDSim {sge tge: GlobEnv.t}
          (index: Type)
          (index_order: index -> index -> Prop)
          (match_state: index -> Mu -> FP.t -> FP.t -> 
                        @ProgConfig sge -> @ProgConfig tge -> Prop)
  : Prop :=
  {
    index_wf: well_founded index_order;

    match_tp:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        thrddom_eq' spc tpc /\
        atombit_eq spc tpc /\
        tid_eq spc tpc;

    (** silent-step (of thread) clause *)
    match_tau_step:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        forall spc' fpS',
          np_step spc tau fpS' spc' ->
          atom_bit spc = atom_bit spc' ->
          (** plus step and match *)
          (exists tpc' fpT' i',
              tau_plus np_step tpc fpT' tpc' /\
              LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS') (FP.union fpT fpT') /\
              match_state i' mu (FP.union fpS fpS') (FP.union fpT fpT') spc' tpc'
          )
          \/
          (** no-step, index decrease *)
          (exists i',
              index_order i' i /\
              match_state i' mu (FP.union fpS fpS') fpT spc' tpc
          );

    (** enter atomic block clause *)
    match_ent_atom:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        forall spc' fpS',
          np_step spc tau fpS' spc' ->
          atom_bit spc <> atom_bit spc' ->
          (exists tpc' fpT' tpc'' fpT'' i',
              tau_star np_step tpc fpT' tpc' /\
              atom_bit tpc = atom_bit tpc' /\
              np_step tpc' tau fpT'' tpc'' /\
              LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS')
                                        (FP.union fpT (FP.union fpT' fpT'')) /\
              match_state i' mu FP.emp FP.emp spc' tpc'');
                    
    match_npsw_step:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        forall o spc' fpS',
          o <> tau ->
          np_step spc o fpS' spc' ->
          (* star step to event *)
          (exists fpT' tpc' i',
              np_step tpc o fpT' tpc' /\
              LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS')
                                        (FP.union fpT fpT') /\
              match_state i' mu FP.emp FP.emp spc' tpc');

    match_final:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        final_state spc ->
        exists tpc' fpT',
          tau_star np_step tpc fpT' tpc' /\ atom_bit tpc = atom_bit tpc' /\
          LFPG mu tge tpc.(cur_tid) fpS (FP.union fpT fpT') /\
          final_state tpc';
    
    match_mu_wd:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        Bset.inj_inject (inj mu)
    
            
  }.


Definition GlobDSim {NL: nat} {L: @langs NL} (sprog tprog: prog L): Prop :=
    forall mu sgm sge spc tgm tge tpc t,
      InitRel mu sge tge sgm tgm ->
      init_config sprog sgm sge spc t ->
      init_config tprog tgm tge tpc t ->
      exists I ord match_state i,
        GConfigDSim I ord match_state /\
        match_state i mu FP.emp FP.emp spc tpc.

