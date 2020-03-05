Require Import VST.floyd.proofauto.
Require Import pile.
Require Import spec_stdlib.
Require Import spec_pile.

Instance PileCompSpecs : compspecs. make_compspecs prog. Defined.
Definition tlist := Tstruct _list noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val,
       !! (0 <= h <=  Int.max_signed) && 
      data_at Ews tlist (Vint (Int.repr h), y) x 
     * malloc_token Ews tlist x
     *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

(*Previsouly called pilerep, and will be used to instantiate spec_pile.pilerep,
  but given a different name for didactic purposes and to avoid qualified names*)
Definition prep (sigma: list Z) (p: val) : mpred :=
  EX x:val, data_at Ews tpile x p * listrep sigma x.

Record PilePrivatePredicates := {
  pilepreds :> PilePredicates;
  pile_rep_exposed:  spec_pile.pilerep pilepreds = prep
}.

Section PilePrivateASI.
Variable PILEPRIV:PilePrivatePredicates.

Definition PilePrivateASI:funspecs := PileASI PILEPRIV.

End PilePrivateASI.
