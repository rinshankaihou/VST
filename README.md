# VST-on-Iris

An Iris instantiation of the CompCert C semantics.
This artifact is a fork of the Verified Software Toolchain (VST).
The original VST readme can be found in [README_VST.md](./README_VST.md),
and some other information are documented in [file_organization_misc.md](./file_organization_misc.md).

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

At this point, we use [`Makefile`](./Makefile) to compile proof scripts. For example,
to compile the [proof for the list reverse function](./progs64/verif_reverse2.v):

```(bash)
make progs64/verif_reverse2.vo -j
```

We recommend using opam installed compcert and do  [`Makefile`](./Makefile) as is.

now you can run the compiled scripts.

If your Coq IDE requires a `_CoqProject` file, do:

```(bash)
make _CoqProject
```
