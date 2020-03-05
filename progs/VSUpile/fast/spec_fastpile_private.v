Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile.

Instance FastpileCompSpecs : compspecs. make_compspecs prog. Defined.

(*Previsouly called pilerep, and will be used to instantiate spec_pile.pilerep,
  but given a different name for didactic purposes and to avoid qualified names*)
Definition fastprep (sigma: list Z) (p: val) : mpred :=
 EX s:Z, !! (0 <= s <= Int.max_signed /\
   Forall (Z.le 0) sigma /\
  (0 <= sumlist sigma <= Int.max_signed -> s=sumlist sigma))
   &&  data_at Ews tpile (Vint (Int.repr s)) p.

Record FastpilePrivatePredicates := {
  pilepreds :> PilePredicates;
  pile_rep_exposed:  spec_fastpile.pilerep pilepreds = fastprep
}.

Section FastpilePrivateASI.
Variable FASTPILEPRIV:FastpilePrivatePredicates.

Definition FastpilePrivateASI:funspecs := PileASI FASTPILEPRIV.

End FastpilePrivateASI.
