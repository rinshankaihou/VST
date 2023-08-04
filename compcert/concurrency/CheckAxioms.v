Require Import
        GAST CUAST ETrace
        GlobSemantics GlobDSim GlobUSim GlobUSimRefine SimDRF
        Compositionality Soundness
        SeqCorrect CompCorrect.

(** * Explanation on axioms we use *)
(** In the next section, the assumptions printed by 
    [Print Assumption] would be with in the following list *)

(** ** Axioms in Coq standard library *)
(** The following axioms are taken from the Coq 8.6 standard library.
    These axioms should not cause inconsistencies according to Coq documentation.
    - [ProofIrrelevance.proof_irrelevance] 
    - [FunctionalExtensionality.functional_extensionality_dep]
    - [Eqdep.Eq_rect_eq.eq_rect_eq]
    - [Classical_Prop.classic]
    - [JMeq.JMeq_eq]
 *)

(** ** Original CompCert [Parameters] or [Axioms] *)
(** - [Axioms.proof_irr]
    - [SelectOp.symbol_es_external]
    - [Compopts.optim_for_size]
    - [SplitLongproof.i64_helpers_correct]
    - [Events.inline_assembly_sem]
    - [Events.inline_assembly_properties]
    - [Events.external_functions_sem]
    - [Events.external_functions_properties]
    - [Selection.compile_switch]
    - [RTLgen.more_likely] 
    - [Linearize.enumerate_aux]
 *)

(** ** Axioms for helper functions *)
(** These axioms are the axioms we introduced:
    
    - [helpers.i64ext_effects]:
    assumes the int64 helper functions does not modify memory, 
    and generates no observable events.

    - [helpers.i64ext_inject]:
    the semantics of int64 helper functions commute with memory injection.
    this axiom is slightly stronger than the original CompCert axiom,
    requiring that the semantics do not modify memory, 
    and do not depend on global environment.
    It seems possible to prove this axiom assuming the above axiom holds, 
    using original CompCert's axioms about external calls.
    We left this work as future works.
 *)

(** ** Axioms about real numbers *)
(** Possibly because we imported `Flocq` library code (`Fcore_Raux.v`) in proving compiler passes,
    it automatically imported axioms about real numbers (from module `Reals`), which has the name of:
    - [Rdefinitions.*], or
    - [Raxioms.*]
    We did not explicitly use these axioms in our development (folder `concurrency`).
*)


(** * Selected important mechanized results *)

(** ** Lemma 4 Compositionality *)
Check compositionality.
Print Assumptions compositionality.

(** ** Lemma 5 Soundness *)
Check USim_Refine.
Print Assumptions USim_Refine.

(** ** Lemma 6 DRF Preservation *)
Check USim_NPDRF_Config.
Print Assumptions USim_NPDRF_Config.

(** ** Lemma 7 Semantics Equivalence *)
Check RefineEquiv.NP_P_Equiv.
Print Assumptions RefineEquiv.NP_P_Equiv.

(** ** Theorem 10 Final Theorem *)
Check framework_final_theorem.
Print Assumptions framework_final_theorem.

(** ** Lemma 11 CompCert Correctness *)
Check compcert_correct.

(** [Print Assumptions compcert_correct.] 
    would result in an [Uncaught exception] which seems to be a bug of Coq. 
    We provide an alternative way for checking 
    the Axioms used in the proof by printing assumptions of 
    correctness proof of each individual compilation pass. *)

Print Assumptions cshmgen_proof.TRANSF_local_ldsim. 

Print Assumptions cminorgenproof.TRANSF_local_ldsim.

Print Assumptions selection_proof.transf_local_ldsim.

Print Assumptions rtlgen_proof.transf_local_ldsim.

Print Assumptions tailcall_proof.transf_local_ldsim.

(** Coq bug ? *)
(* Print Assumptions alloc_proof.transf_local_ldsim. *)

Print Assumptions linearize_proof.transf_local_ldsim.

Print Assumptions stacking_proof.transf_local_ldsim. 

Print Assumptions asmgen_proof.transf_local_ldsim.

(** ** Theorem 12 Correctness with x86-SC backend and obj *)
Require Import FinalTheoremExt.
Check refinement_sc.


(** * Ongoing work *)

(** ** Theorem 13 Correctness with x86-TSO backend and obj *)
Check refinement_tso_clight.

(** ** Lemma 14 Restore SC semantics for DRF x86 programs *)
Check refinement_tso_asm_sc.
