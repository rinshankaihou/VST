# VST-on-Iris

An Iris instantiation of the CompCert C semantics.
This artifact is a fork of the Verified Software Toolchain (VST).
This document describes how to build the Coq code, and where to find the corresponding Coq mechanization of some theorems mentioned in the paper. 

Some other information is documented in [file_organization_misc.md](./file_organization_misc.md). Other .md files, such as the original VST readme [README_VST.md](./README_VST.md) are included for reference, but they may be outdated. 

## Building

### Prerequisites

We assume opam is already installed. The building instructions are tested on Linux version 5.10.16.3-microsoft-standard-WSL2, and should be compatible with most Unix machines.

The proof for the example [verif_reverse2.v](./progs64/verif_reverse2.v) assumes 64-bit pointers, so compiling that requires your machine to be 64-bit and that opam installs 64-bit compcert for you.

### Installing Dependencies

We recommend using opam for managing dependencies. To install opam, see https://opam.ocaml.org/doc/Install.html.

Create a new opam switch:

```(bash)
opam switch create vst_on_iris ocaml-variants.4.14.1+options ocaml-option-flambda
eval $(opam env --switch=vst_on_iris)
```

Install dependencies (and say yes to every prompt):

```(bash)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add https://github.com/mansky1/ora.git
opam pin add builddep/
```

### Compilation

At this point, we use [`Makefile`](./Makefile) to compile proof scripts.

To compile a file, simply do

```(bash)
make filename
```

To compile the share algebra:

```(bash)
make shared/* -j
```


We have 10 examples in [progs64/](./progs64/). (The proof scripts are `progs64/verif_*.v`, for example, [verif_append2.v](./progs64/verif_append2.v) is the functional correctness proof of [append.c](./progs64/verif_append2.v)). To compile them:

```(bash)
make progs64 -j
```

The [`Makefile`](./Makefile) uses bundled 64-bit compcert.


If your Coq IDE requires a `_CoqProject` file, do:

```(bash)
make _CoqProject
```

### Mechanisation Map

#### Section 3
- Section 3.1:
 In [`shared`](./shared). In particular:
  | Coq Definition / Theorem | Content in paper                                                            |
  | ------------------------ | --------------------------------------------------------------------------- |
  | [`shared/shared.v`](./shared/shared.v)             | camera of shared values                           |
  | [`shared/shared.v: writable_update`](./shared/shared.v)        | Lemma 3.1                             |
  | `shared/resource_map.v, shared/gen_heap.v`               | resource maps  |
- Section 3.2:
 In [`veric/juicy_mem.v`](./veric/juicy_mem.v). In particular:
  | Coq Definition / Theorem | Content in paper                                                            |
  | ------------------------ | --------------------------------------------------------------------------- |
  | `perm_of_sh`             | relationship between rmap shares and memory permissions                     |
  | `coherent`               | Definition 3.2 *coherent*                                                   |
  | `mem_auth`               | (partial) State interpretation *S(m)* (see full definition in Section 4.1)  |
  | `mapsto_storebyte`       | Theorem 3.3 (Relationship between points-to and compcert memory operations) |
- Section 3.3:
  In [`veric/res_predicates.v`](./veric/res_predicates.v).

  | Coq Definition / Theorem | Content in paper |
  | ------------------------ | ---------------- |
  | `resource`               | LK and FUN       |

#### Section 4
  In [`veric/juicy_extspec.v`](./veric/juicy_extspec.v), unless otherwise mentioned.

  | Coq Definition / Theorem                    | Content in paper                |
  | ------------------------------------------- | ------------------------------- |
  | `state_interp`                              | State interpretation *S((m,z))* |
  | `jsafe` (the meat is really `jsafe_Pre`)    | Weakest Precondition *WP*       |
  | [`sepcomp/step_lemmas: safeN_`](./sepcomp/step_lemmas.v)     | Definition 4.1  *safety*        |
  | [`veric/SequentialClight.v: adequacy`](./veric/SequentialClight.v)                | Theorem 4.2 *adequacy*          |
  
#### Section 5
Note that `semax` is short for "sémantique axiomatique" (axiomatic semantics), and `semax _ _ P c Q` roughly corresponds to the Hoare triple `{P} c {Q}`.
  | Coq Definition / Theorem                                                 | Content in paper                                  |
  | ------------------------------------------------------------------------ | ------------------------------------------------- |
  | Section 5.1                                                              |                                                   |
  | [`veric/expr_lemmas4.v: eval_both_relate`](./veric/expr_lemmas4.v)       | Theorem 5.3 *new*                                 |
  | [`veric/semax_straight.v: semax_store`](./veric/semax_straight.v)        | the store rule and the proof, Theorem 5.4 *store* |
  | Section 5.1.1                                                            |                                                   |
  | [`veric/semax.v: believe`](./veric/semax.v)                              | *believe*                                         |
  | [`veric/seplog.v: funspecs_assert`](./veric/seplog.v)                    | *funs_valid*                                      |
  | [`veric/semax.v: semax`](./veric/semax.v)                                | {P} c {Q} with *fs*                               |
  | [`veric/semax_call.v: semax_call`](./veric/semax_call.v)                 | the call rule                                     |
  | Section 5.2                                                              |                                                   |
  | [`veric/initial_world.v: res_of_loc`](./veric/initial_world.v)           | res_of_loc                                        |
  | [`veric/initial_world.v: rmap_of_mem_coherent`](./veric/initial_world.v) | Theorem 5.5                                       |
  | [`veric/initial_world.v: rmap_inflate_equiv`](./veric/initial_world.v)?  | Theorem 5.6                                       |
  | [`veric/SequentialClight.v: adequacy`](./veric/SequentialClight.v)       | Theorem 5.7 *whole-program adequacy*              |

#### Section 6
 | Coq Definition / Theorem                               | Content in paper                               |
 | ------------------------------------------------------ | ---------------------------------------------- |
 | [`progs64/verif_reverse2.v`](progs64/verif_reverse2.v) | Verification of a linked-list reverse function |
 | [`progs64/verif_*.v`](progs64/)                        | Other verification examples                    |
