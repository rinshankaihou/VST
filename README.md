# VST-on-Iris

An Iris instantiation of the CompCert C semantics.
This artifact is a fork of the Verified Software Toolchain (VST).
This document describes how to build the examples in the paper; some other information are documented in [file_organization_misc.md](./file_organization_misc.md). 

Other .md files, such as the original VST readme [README_VST.md](./README_VST.md) are included for reference, but they may be outdated. 

## Building

### Prerequisites

We assume opam is already installed. The building instructions are tested on Linux version 5.10.16.3-microsoft-standard-WSL2, and should be compatible with most Unix machines.

The proof for the example [verif_reverse2.v](./progs64/verif_reverse2.v) assumes 64-bit pointers, so compiling that requires your machine to be 64-bit and that opam installs 64-bit compcert for you.

### Installing Dependencies

We recommend using opam for managing dependencies with a new opam switch:

```(bash)
opam switch create vst_on_iris ocaml-variants.4.14.1+options ocaml-option-flambda
```

Install dependencies:

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