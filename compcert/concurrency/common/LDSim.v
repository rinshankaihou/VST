Require Import Coqlib Streams Errors Values Globalenvs.

Require Import Blockset Footprint GMemory 
        Injections MemAux MemClosures LDSimDefs
        InteractionSemantics.

Require Import Events.

(** This file defines the downward local simulation of modules and [SeqCorrect] condition for compilers *)


(* exposing mu.f *)
(* memory and freelists are related by mu:
   - inj(dom(sm)) = dom(tm); dom(sm) = sharedS; dom(tm) = sharedT.
   - val_inj on domain.
   - freelists are out of domains.
   - sharedS reach-closed
   - TODO: freelist norep????
 *)

(** initial relation on source and target memories *)
Record local_init_rel (mu: Mu) (sfl: freelist) (sm: gmem)
       (tfl: freelist) (tm: gmem) : Prop :=
  {
    (** Mu is well-formed w.r.t. freelists *)
    init_mu:
      Bset.inject_weak (inj mu) (SharedSrc mu) (SharedTgt mu) /\
      no_overlap sfl (SharedSrc mu) /\
      no_overlap tfl (SharedTgt mu);

    (** Mu is injective *)
    Binj:
      GMem.Binject_weak (inj mu) sm tm;

    (** freelists do not overlap with valid blocks *)
    sfl_free:
      no_overlap sfl (valid_block_bset sm);

    tfl_free:
      no_overlap tfl (valid_block_bset tm);

    (** freelists have no duplicated blocks *)
    sfl_norep:
      norep sfl;

    tfl_norep:
      norep tfl;

    (** SharedSrc/SharedTgt in Mu is set to validblocks of memory *)
    valid_Src:
      forall b, GMem.valid_block sm b <-> SharedSrc mu b;

    valid_Tgt:
      forall b, GMem.valid_block tm b <-> SharedTgt mu b;

    (** SharedSrc/SharedTgt are closed *)
    rc_shared_Src:
      reach_closed sm (SharedSrc mu);

    rc_shared_Tgt:
      reach_closed tm (SharedTgt mu);
  }.

Section LocalSimulation.

Context {sl tl: Language}.

(** * Module Local Simulation *)

(** ** Simulation between configurations (Def. 3) *)
(** local simulation is defined as inductively parameterized by
    [match_state] relation between source and target configurations *)

Record config_ldsim {sl tl: Language}
       (index: Type)
       (index_order: index -> index -> Prop)
       (sfl tfl: freelist)
       (sG: G sl)
       (tG: G tl)
       (sge: Genv.t (F sl) (V sl))
       (tge: Genv.t (F tl) (V tl))
       (match_state: bool -> index -> Mu -> FP.t -> FP.t ->
                     ((core sl) * gmem) -> ((core tl) * gmem) -> Prop): Prop :=
  {
    index_wf: well_founded index_order;

    (** Mu is well-formed *)
    wd_mu: forall b i mu Hfp Lfp Hc Lc,
      match_state b i mu Hfp Lfp Hc Lc ->
      Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) /\
      no_overlap sfl (SharedSrc mu) /\
      no_overlap tfl (SharedTgt mu)
    ;

    (** freelists have no duplicated blocks *)
    fl_norep: forall b i mu Hfp Lfp Hc Lc,
        match_state b i mu Hfp Lfp Hc Lc ->
        norep sfl /\ norep tfl
    ;

    (** global environments are matched *)
    match_ge: ge_match sge tge;

    (** global environments consistent with mu *)
    match_mu_ge: forall b i mu Hfp Lfp Hc Lc,
      match_state b i mu Hfp Lfp Hc Lc ->
      ge_init_inj mu sge tge
    ;

    (** init core clause:
     if source could [init_core] given function [id] and [argSrc],
     and [argTgt] is related with [argSrc] by [arg_rel] (similar to value injection),
     then target could [init_core] given [id] and [argTgt], 
     and the initialized cores together with related initial memories [sm] and [tm] 
     are related by [match_state] *)
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

    (** internal step clause:
        if source performs an internal step, the target either
        1) perform no step, and the target configuration matches with source's resulting configuration with decreased index, or
        2) perform multiple steps, and the target resulting configuration matches with source's resulting configuration
        [HfpG] appears in preconditions since we assume source to be reach-closed,
        and [LfpG'] states that target footprint is confined in S union F, 
        and [FPMatch]ed with source footprint.
     *)
    match_tau_step: forall i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm',
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (step sl) sG sfl Hcore Hm Hfp' Hcore' Hm' -> 
        HfpG sfl mu Hfp' ->
        (* 1) no step, index decrease *)
        (exists i',
            index_order i' i /\
            match_state true i' mu (FP.union Hfp Hfp') Lfp (Hcore', Hm') (Lcore, Lm))
        \/
        (* 2) plus step, fp matched *)
        (exists i' Lfp' Lcore' Lm',
            plus (step tl tG tfl) Lcore Lm Lfp' Lcore' Lm' /\
            LfpG' tfl mu (FP.union Hfp Hfp') (FP.union Lfp Lfp') /\
            match_state true i' mu (FP.union Hfp Hfp') (FP.union Lfp Lfp') (Hcore', Hm') (Lcore', Lm'))
    ;

    (** at_external clause:
        if source reaches the external call point with function [f] and arguments [argSrc],
        and the resulting configuration satisfies [HG], 
        and the arguments satisfies [G_args] such that escape of stack pointers is disallowed,
        then target reaches the external call point after star steps,
        with the same [f] and [arg_rel] related [argTgt],
        and the resulting configuartion and footprints satisfies [LG], 
        and [match_state] holds on resulting configurations.
        Footprint recorded in [match_state] is cleared at this point.
     *)
    match_at_external: forall i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc,
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (at_external sl) sG Hcore = Some (f, sg, argSrc) ->
        HG sfl mu Hfp Hm ->
        G_args (SharedSrc mu) argSrc ->
        exists i' argTgt,
          (at_external tl) tG Lcore = Some (f, sg, argTgt) /\
          arg_rel (inj mu) argSrc argTgt /\
          LG' tfl mu Hfp Hm Lfp Lm /\
          match_state false i' mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm)
    ;

    (** after external clause:
        when environments performes action satisfies [HLRely],
        with [ores_rel] related return values [oresSrc] and [oresTgt],
        then if source is updated to [Hcore'] by [after_external],
        then target could be updated to [match_state] related [Lcore'] by [after_external]. 
        [G_oarg] is required to disallow recieving of stack pointers from return value.
*)
    match_after_external: forall i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt,
        (** TODO: is this clause too strong for CompCert? *)
        match_state false i mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm) ->
        G_oarg (SharedSrc mu) oresSrc ->
        (after_external sl) Hcore oresSrc = Some Hcore' ->
        ores_rel (inj mu) oresSrc oresTgt ->
        exists Lcore',
          (after_external tl) Lcore oresTgt = Some Lcore' /\
          (forall Hm' Lm', HLRely sfl tfl mu Hm Hm' Lm Lm' ->
                      exists i', match_state true i' mu FP.emp FP.emp (Hcore', Hm') (Lcore', Lm'))
    ;

    (** halted clause:
        if source core halts with resulting footprint and memory satisfies [HG],
        then target core halts with footprint and memory satisfies [LG'],
        and the returning value of source and target cores are related by [res_rel].
        [G_arg] is required to disallow escap of stack pointers via return value. *)
    match_halt: forall i mu Hfp Lfp Hcore Hm Lcore Lm resSrc,
        match_state true i mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
        (halt sl) Hcore = Some resSrc ->
        HG sfl mu Hfp Hm ->
        G_arg (SharedSrc mu) resSrc ->
        exists resTgt,
          (halt tl) Lcore = Some resTgt /\
          (* return val related *)
          res_rel (inj mu) resSrc resTgt /\
          (* return state related, fp matched *)
          LG' tfl mu Hfp Hm Lfp Lm
  }.
      
End LocalSimulation.

(** ** The simultion definition (Def. 2) *)
(** The simulation is defined as an inductive type
    with an existential relation [match_state] between source and target configurations, 
    instead of a co-inductive formulation presented in the paper.
    It is for the convenience of proof development, and could be proved 
    equivalent to a CoInductive formulation *)
Definition ldsim {sl tl: Language}
           (su: comp_unit sl) (tu: comp_unit tl) : Prop :=
  forall sG sge tG tge sfl tfl,
    init_genv sl su sge sG ->
    init_genv tl tu tge tG ->
    Genv.genv_next sge = Genv.genv_next tge ->
    exists I I_order match_state,
      (* match_state is a simulation relation on local configurations *)
      config_ldsim I I_order sfl tfl sG tG sge tge match_state.


Lemma no_overlap_unchg_freelist:
  forall fl m m',
    no_overlap fl (valid_block_bset m) ->
    unchg_freelist fl m m' ->
    no_overlap fl (valid_block_bset m').
Proof.
  intros.
  destruct H0.
  intros b ofs H_in H_contra.
  unfold valid_block_bset, Bset.belongsto in H_contra.
  rewrite <- unchanged_on_validity in H_contra.
  eapply H; eauto. constructor.
  unfold in_fl. eexists; eauto.
Qed.

Local Hint Resolve no_overlap_unchg_freelist.