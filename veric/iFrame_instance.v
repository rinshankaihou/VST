From iris.proofmode Require Import classes_make.
Instance absorbing_quick_absorbing {PROP:bi} (P:PROP):
  Absorbing P -> QuickAbsorbing P.
Proof. rewrite /QuickAbsorbing //. Qed.