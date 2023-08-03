Require Import Values.

Require Import Blockset Footprint GMemory InteractionSemantics GAST
        GlobDefs ETrace NPSemantics
        Injections GSimDefs.

Local Notation "{-| PC , T }" := 
  ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |})  (at level 70,right associativity).

(** * Global Upward Simulation *)

(** This file defines the global upward simulation [S > T] *)

Record GConfigUSim {sge tge: GlobEnv.t}
          (index: Type)
          (index_order: index -> index -> Prop)
          (match_state: index -> Mu -> FP.t -> FP.t -> 
                        @ProgConfig sge -> @ProgConfig tge -> Prop)
  : Prop :=
  {
    index_wf: well_founded index_order;
    (** The program configurations are matched:
        - threadpool domains are equal
        - atomic bit are equal
        - current thread id are equal
     *)

    match_tp:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        ThreadPool.inv spc.(thread_pool) /\
        ThreadPool.inv tpc.(thread_pool) /\
        thrddom_eq' spc tpc /\
        atombit_eq spc tpc /\
        tid_eq spc tpc;
    (** The tau-step rule:
        [sge, tge, O |- S >^i_(fpS,fpT) T] implies
        [S --tau--> S' =>]
        (1) [exists T' i',
            T --tau-->+ T'] and [...|- S' >^i'_(...) T'] and FP matches ...
        (2) [exists i'<i,
            ...|- S' >^i'_(...) T] *)
    match_tau_step:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        forall tpc' fpT',
          np_step tpc tau fpT' tpc' ->
          atom_bit tpc = atom_bit tpc' ->
          (* 1. plus step and match *)
          (exists spc' fpS' i',
              tau_plus np_step spc fpS' spc' /\
              LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS') (FP.union fpT fpT') /\
              match_state i' mu (FP.union fpS fpS') (FP.union fpT fpT') spc' tpc'
          )
          \/
          (* 2. no-step, index decrease *)
          (exists i',
              index_order i' i /\
              match_state i' mu fpS (FP.union fpT fpT') spc tpc'
          );
    (** ent_atom rule: *)
    match_ent_atom:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        forall fpT' tpc',
          np_step tpc tau fpT' tpc' ->
          atom_bit tpc <> atom_bit tpc' ->
          (* star step and enter atomic block *)
          (exists fpS' spc' fpS'' spc'' i',
              tau_star np_step spc fpS' spc' /\
              atom_bit spc = atom_bit spc' /\
              np_step spc' tau fpS'' spc'' /\
              (* fp matches *)
              LFPG mu tge tpc.(cur_tid) (FP.union fpS (FP.union fpS' fpS''))
                                        (FP.union fpT fpT') /\
              match_state i' mu FP.emp FP.emp spc'' tpc'
          )
    ;
    (** The event step rule:
        [sge, tge, O |- S >^i_(fpS,fpT) T] implies
        [S --o--> S' => exists T' i',
            T --o-->+ T'] and [...|- S' >^i'_(...) T'] and FP matches ...
     *)
    match_npsw_step:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        forall o tpc' fpT',
          o <> tau ->
          np_step tpc o fpT' tpc' ->
          (* star step to event *)
          (exists fpS' spc' fpS'' spc'' id,
              tau_star np_step spc fpS' spc' /\ atom_bit spc = atom_bit spc' /\
              pc_valid_tid spc'' id /\ np_step spc' o fpS'' spc'' /\
              forall t,
                pc_valid_tid spc'' t ->
                np_step spc' o fpS'' ({-|spc'',t}) /\
                LFPG mu tge tpc.(cur_tid) (FP.union fpS (FP.union fpS' fpS''))(FP.union fpT fpT') /\
                exists j,match_state j mu FP.emp FP.emp ({-|spc'',t})({-|tpc',t}));

    
    (** The final state rule:
        [sge, tge, O |- S >^i_(fpS,fpT) T] implies
        [final_state S => exists T',
        T --tau-->* T'] and [final_state T'] and FP matches ...
     *)
    match_final:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        final_state tpc ->
        exists spc' fpS',
          tau_star np_step spc fpS' spc' /\ atom_bit spc = atom_bit spc' /\
          LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS') fpT /\
          final_state spc';
    (** None of source or target state would abort *)
    match_abort:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        ~ np_abort spc /\
        ~ np_abort tpc;
    
    match_mu_wd:
      forall i mu fpS fpT spc tpc,
        match_state i mu fpS fpT spc tpc ->
        Bset.inj_inject (inj mu)    

          
  }.


Definition GlobUSim {NL: nat} {L: @langs NL} (sprog tprog: prog L) : Prop :=
    forall mu sgm sge spc tgm tge tpc t,
      InitRel mu sge tge sgm tgm ->
      init_config sprog sgm sge spc t ->
      init_config tprog tgm tge tpc t ->
      exists I ord match_state i,
        GConfigUSim I ord match_state /\
        match_state i mu FP.emp FP.emp spc tpc.