# VST-on-Iris

An Iris instantiation of the CompCert C semantics.
This artifact is a fork of the Verified Software Toolchain (VST).
The original VST readme can be found in [README_VST.md](./README_VST.md),
and some other information are documented in [file_organization_misc.md](./file_organization_misc.md).

## Building

### Prerequisites

We assume opam, the ocaml package manager, is already installed. The building instructions are tested on Linux version 5.10.16.3-microsoft-standard-WSL2, and should be compatible with most Unix machines.

The proof for the example [verif_reverse2.v](./progs64/verif_reverse2.v) assumes 64-bit pointers, but if you use the bundled 64-bit compcert (which is the default option), you should be able to compile it even if your machine is a 32-bit one, since they are just proof scripts. Alternative methods for installing CompCert are described at the bottom of this file.

### Installing Dependencies

We recommend opam for managing dependencies with a new opam switch:

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

Now you can run the compiled scripts -- just remember to generate the `_CoqProject` file your Coq IDE requires one:

```(bash)
make _CoqProject
```

### Alternative Installation Methods for CompCert

If you wish to use a compcert that's not the bundled one (though not required), we recommend opam (opam pin add compcert), and currently we requrie that it is a 64-bit one. After installation, it should be under `<opam-switch-name>/lib/coq/user-contrib/compcert`, then in the [Makefile](./Makefile), modify the COMPCERT variable under `# User settable variables #` to platform.

For other installation methods (although not tested and not recommended), make sure the installed files are in Coq's load path, and in the [Makefile](./Makefile), modify the COMPCERT variable under `# User settable variables #` accordingly.
