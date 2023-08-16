Require Import Coqlib.
Ltac xomega := unfold Plt, Ple in *; zify; lia.
Ltac xomegaContradiction := exfalso; xomega.