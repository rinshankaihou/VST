# Towards Certified Separate Compilation for Concurrent Programs

The `concurrency/` directory contains all our Coq implementation.

The `concurrency/framework` directory contains the framework described in Sec. 6.

The `concurrency/comp_correct` directory contains the adapted CompCert compiler and correctness proof.

The `concurrency/x86TSO` directory contains the extended framework for x86TSO, and a spinlock implementation.

See [`Files.md`](Files.html) for more detailed file structure.



## Main results

The main result of our framework (Theorem 12 in Sec. 6)
is in file `concurrency/framework/Soundness.v`.

The adapted CompCert compiler and the compiler correctness proof (Lemma 13 in Sec. 7)
is in file `concurrency/comp_correct/CompCorrect.v`.

Theorem 14 in Sec.7 is in file `concurrency/FinalTheorem.v`.

The main results of the extended framework (Theorem 15 and Lemma 16 in Sec. 7) 
are in file `concurrency/x86TSO/FinalTheoremExt.v`.

The spinlock spec. and impl. are defined in file `concurrency/x86TSO/lock_proof/code.v`.
The spinlock correctness proof is in file `concurrency/x86TSO/lock_proof/LockProof.v`.



## Compiling Coq files
To compile coq files in `concurrency/`, we need to install
`ssreflect` library for finite types, and compile CompCert-3.0.1.
The `opam`(currently we use opam version 2.0.3) ocaml package manager is recommended.

### installing ssreflect and coq using opam
The compilation environment could be installed and configured
using following shell commands:

<pre><code>opam init
opam switch 4.04.1
eval `opam config env`
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.6
opam install coq-mathcomp-ssreflect.1.6.1</code></pre>

Opam will install all dependencies for you.

### compile 
`./configure x86_32-linux` for linux or 
`./configure x86_32-cygwin` for cygwin or
`./configure x86_32-macosx` for osx

(You may find some dependencies missing. 
If so, install the missing part and re-run this command.)

`make`


### developing using Emacs
You may need to install `ProofGeneral` first.
Then you could change the workign directory to `CompCert-3.0.1`
and run `./pg` (or `./pg_mac` if you use mac osx and Emacs application),
it will open `emacs` with the coq directories automatically set.


