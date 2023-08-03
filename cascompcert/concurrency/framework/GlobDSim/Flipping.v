Require Import InteractionSemantics GAST GlobDefs NPSemantics GlobUSim GlobDSim GlobSim.


(** * Flipping *)

(** This file defines the flipping lemma on global simulations.
    It says when languages of target modules are [deterministic], 
    then the global downward simulation could be flipped to
    global upward simulation. Thus we could prove DRF preservation and
    upward refinement using the global upward simulation. *)

(** Main result: the global downward simluation is flippable. 
    sub-proofs of this lemma are in file [GlobSim] *)

Lemma flipping:
  forall NL (L: @langs NL) (sprog tprog: prog L),
    GlobDSim sprog tprog ->
    det_langs (fst tprog) ->
    wd_langs (fst tprog) ->
    np_safe_prog sprog ->
    GlobUSim sprog tprog.
Proof.
  intros.
  apply GlobSim.flipping';auto.
Qed.