Require Import Streams Errors Globalenvs.

Require Import Blockset Footprint GMemory 
        Injections MemAux MemClosures LDSimDefs
        InteractionSemantics LDSim.

(** * SeqCorrect *)
(** a sequential compiler [comp] is correct w.r.t. the source language [sl] and target language [tl] if:
    for any source compilation unit [su] and the compiled compilation unit [tu] that
    [comp su = OK tu],
    [su] and [tu] satisfies the module local downward simulation, 
    and the [internal_fn] (the set of functions which could be called by other modules) 
    of [su] and [tu] are equal *)
Definition seq_correct {sl tl: Language} (comp: @seq_comp sl tl): Prop :=
  forall su tu,
    comp su = OK tu ->
    ldsim su tu /\
    (internal_fn sl su) = (internal_fn tl tu).


Open Scope error_monad_scope.
 
Definition comp_compose {l1 l2 l3: Language}
           (comp12: @seq_comp l1 l2)
           (comp23: @seq_comp l2 l3) : @seq_comp l1 l3 :=
  fun (cu1: comp_unit l1) =>
    match comp12 cu1 with
    | Error msg => Error msg
    | OK cu2 => comp23 cu2
    end.
