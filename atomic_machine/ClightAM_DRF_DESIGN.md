# Clight atomic-machine execution correspondence

`ClightAM_DRF.v` relates terminating executions of the VST Clight atomic
machine to executions of CASCompCert's global interaction semantics.  It uses
a concrete relation on `CAM_config` and `ProgConfig`; the old abstract
`match_config` parameter and `CAM_case_simulation` obligation record are gone.

## Programs P and P'

The target program is

```coq
CAM_translated_program P ids entries :=
  ClightAtomicTarget.linked_program [P] ids entries.
```

`CAM_translated_program_shape` exposes its two compilation units:

```text
[ client_unit P ; wrapper_unit ids ]
```

This is a link-time implementation, not a source-to-source rewrite of every
call site.  `P` is unchanged, and its external atomic calls resolve to the
appended implementations.  Those implementations have the following bodies:

```text
atomic_load:  ent_atom(); old = *p;                         ext_atom(); return old
atomic_store: ent_atom(); *p = new;                         ext_atom(); return
atomic_CAS:   ent_atom(); old = *p; if equal then *p = new; ext_atom(); return success
```

The initialized call lemmas execute these actual functions through global
`Call`, `Ent_Atom`, the sequential body, `Ext_Atom`, and `Return` transitions.

## Source executions

`CAM_execution ge s0 sf` is a finite sequence of the unchanged `CAM_step`
relation.  Every recorded source state excludes explicit `StuckState`, obeys
the supported assignment syntax, and every atomic memory transfer is required
by the step rule itself to be defined.  Canonical atomic declarations and
pointer/integer argument shapes are enforced directly by
`clight_decode_atomic`; malformed reserved calls do not decode and therefore
cannot take a CAM atomic step.  There is no configuration-level atomic-call
or atomic-read-shape premise.
The decoder derives each access chunk from the checked Clight declaration:
from the declared result/pointee type for load, and from the declared
object/value type for store and CAS.  The canonical integer API therefore
computes to `Mint32`; that chunk is not selected independently by name.
The load wrapper is proved for every defined value that a `Mint32` read can
produce.  CAS uses Clight's comparison at the declaration-derived object
type; for the canonical `int` declaration, either successful comparison
result proves that the current value is a `Vint`.  The reflexive endpoint
requires `CAM_all_threads_terminated`.

`CAM_all_threads_terminated` uses `Clight_core.cl_halted` and requires every
pending event list to be empty.  It therefore does not refer to a nonexistent
`CC_core_Returnstate` constructor.

## Direct configuration relation

`CAM_memory_match` compares a CompCert `Memory.mem` with a CASCompCert
`GMemory.gmem` on identical blocks.  Contents are equal, access maps agree
after the explicit permission conversions, and the valid-block predicates
are equivalent.

`CAM_core_to_target` structurally maps VST Clight core states to CASCompCert
Clight core states.  `CAM_tid i := Pos.of_succ_nat i` maps source thread IDs
to target IDs.

At an O-bit boundary, `CAM_quiescent_match` requires:

- related memories;
- every source thread to match its target client stack;
- source-map membership to agree with target `valid_tid`; and
- the target current thread to name some source thread.

Pending CAM events and `CAM_rw` are erased.  This makes `Core_Commit` a target
stutter.  `ThreadPool.next_fmap` is also target-only and is not compared.

Inside an I-bit critical section, `CAM_critical_match` keeps the memory,
thread domain, current selected thread, and every nonselected stack related.
It requires a marker-enabled wrapper frame above a canonical suspended atomic
client frame.  `CAM_atomic_phase_matches` restricts the selected source core
to either that call or its operation-specific load/store/CAS continuation,
but does not equate the active wrapper core with either endpoint.  This permits
the source to sit on either side of the linearization point while the target
is inside the wrapper.  The relation contains no source transition, target
path, or promised future endpoint.

Thus `match_config` has only two constructors:

```text
CAM_match_quiescent : CAM_quiescent_match s pc -> match_config s pc
CAM_match_critical  : CAM_critical_match  s pc -> match_config s pc
```

The source-driven execution proof uses quiescent boundaries.  Starting an
arbitrary source step from an I-bit match would be invalid because the target
cannot switch threads while its atomic bit is set.
The theorem below does not assert that every intermediate configuration in
its returned target star satisfies `CAM_match_critical`.

## How translated functions enter the proof

`CAM_initialized_quiescent_step_refinement` proves a complete O-to-O target
execution for one source step.  It does not assume atomic simulations.

- `Core_Try` uses the explicit VST-Clight/CAS-Clight interoperability premise
  `CAM_core_try_refinement_at`.
- `Core_Commit` takes zero target steps.
- source load, store, successful CAS, and failed CAS steps invoke,
  respectively, the four
  `initialized_atomic_*_global_call_and_return` lemmas;
- `SC_Cas_Stuck` contradicts the successor no-stuck invariant.

To invoke those four lemmas, the proof uses initialization of P' together
with `wrapper_ids_wf`, `clients_reserve_wrapper_ids`, and
`client_atomic_declarations`.  From these it derives the exact initialized
wrapper module, ownership of all three atomic identifiers, and resolution of
the client's external calls.  Consequently, replacing P' by an unrelated
program no longer leaves the theorem provable by the same argument.

The four cases also use `CAM_atomic_memory_views`, an explicit representation
bridge from the source memory to the fresh freelist-indexed `FMemory` passed
to an actual selected atomic thread.  It transports atomic loads/stores and
preserves the post-memory relation.  Definedness and declaration-typed CAS
comparison are part of the atomic transition itself, rather than a separate
state invariant.
The top theorem asks for `CAM_atomic_memory_views_from pc_initial`, so views
are required only at configurations reachable from the initialized target,
not at arbitrary records with unconstrained fresh-frame counters.

## Top-level theorem

`CAM_program_execution_corresponds_quiescent` extracts

```coq
GlobEnv.init (ClightAtomicTarget.linked_units [P] ids) GE
```

from `init_config P'`, applies the concrete one-step theorem throughout the
source execution, and concatenates the target traces and footprints.  Its
result remains at an O-bit boundary.  The source `ge` is separately required
to arise from `ClightLang.init_genv P`; that evidence specializes the
program-indexed ordinary-step bridge, so both sides are tied to the same `P`.

`CAM_program_execution_corresponds` packages the final quiescent state in the
public `match_config` relation.  Its behavioral assumptions are limited to:

1. `CAM_core_try_refinements_for_from P ge GE pc_initial`, the ordinary
   VST/CAS Clight interoperability lemma specialized by source initialization
   and target reachability; and
2. `CAM_atomic_memory_views_from pc_initial`, the reachable-state
   CompCert-memory/FMemory representation bridge.

There is no top-level `Hstep : CAM_step_refinement`; all four translated
atomic cases are proved in this file.

## Remaining bridge work

The two reachable-state providers above remain to be derived from lower-level
semantic and memory results.  In particular, a full closed instantiation
still needs:

- preservation of the identity-block memory relation for ordinary Clight
  steps;
- construction of the fresh wrapper `FMemory` embedding at every reachable
  atomic call; and
- a source initial-configuration theorem connecting entries, the source
  thread gmap, empty pending events, and the initial reservation map; and
- a reachable-client restriction for unsupported direct builtins/markers.

The theorem does not yet claim CASCompCert `final_state`.  A source-halted
core may still be represented by a target singleton client frame; draining
such frames with global `Halt` steps is separate.  This also matters because
VST considers a `Vundef` return halted while `ClightLang.halted` rejects it.
