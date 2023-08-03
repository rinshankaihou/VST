(* This file is adapted from contents in [rc_semantics.v] of Compositional CompCert,
   with simplifications that forbid stack pointer escape.
   Modifications were made for supporting footprints instead of effects. *)

Require Import Coqlib Globalenvs.
Require Import Streams
        Blockset GMemory Footprint MemAux MemClosures
        LDSimDefs InteractionSemantics.


Record rc_inv {L: Language}
       (Ge: G L)
       (ge: Genv.t (F L) (V L))
       (I : Bset.t -> freelist -> core L -> gmem -> Prop) : Prop :=
  {
    (** [I S c m] implies [m] is reach-closed on [S] *)
    rc_closed:
      forall S fl c m,
        I S fl c m ->
        reach_closed m S;
    (** initial states with reach-closed shared memory satisfies [I] *)
    rc_init:
      forall m S fl fnid args c,
        init_gmem L ge m ->
        Bset.subset (fun b => Plt b (Genv.genv_next ge)) S ->
        Bset.subset S (valid_block_bset m) ->
        no_overlap fl (valid_block_bset m) ->
        reach_closed m S ->
        G_args S args ->
        init_core L Ge fnid args = Some c ->
        I S fl c m;

    (** temporarily add this case, for general rely step *)
    rc_rely_step:
      forall S fl c m m',
        I S fl c m ->
        GMem.forward m m' ->
        unchg_freelist fl m m' ->
        reach_closed m' S ->
        I S fl c m';
    
    (** [(c,m) --fp--> (c',m')] implies
        blocks in fp subset of [S U F] *)
    rc_step:
      forall S fl c m fp c' m',
        I S fl c m ->
        step L Ge fl c m fp c' m' ->
        Guarantee fl S fp m' /\
        I S fl c' m';
    
    (** [(c,m) at external (f,args)] implies
        closure of blocks in [args] subset of [S] *)
    rc_atext:
      forall S fl c m fnid sg args,
        I S fl c m ->
        at_external L Ge c = Some (fnid, sg, args) ->
        G_args S args /\
        I S fl c m;

    (** [(c,m) -- ores --> (c',m')] and 
        [m'] reach-closed on [S] and
        block in [ores] belongs to S then
        I |- resulting state  *)
    rc_aftext:
      forall S fl c m ores c' m',
        I S fl c m ->
        after_external L c ores = Some c' ->
        G_oarg S ores ->
        reach_closed m' S ->
        unchg_freelist fl m m' ->
        I S fl c' m';

    (** [(c,m) --halt--> ores] then block in [ores] belongs to [S] *)
    rc_halt:
      forall S fl c m res,
        I S fl c m ->
        halt L c = Some res ->
        G_arg S res;
    
  }.

(** A compilation unit is reach-closed if we could find such [I] *)
Definition reach_close {L} (cu: comp_unit L) : Prop :=
  forall ge Ge, init_genv L cu ge Ge -> exists I, rc_inv Ge ge I.
      


