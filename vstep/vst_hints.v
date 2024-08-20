Require Import VST.vstep.vstep.
From diaframe Require Import defs proofmode_base.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.

Section CONC_HINTS.
Context `{!VSTGS unit Σ}.
Global Instance lock_prop_hint {prop:bi} (P:prop):
ExclusiveProp P ->
  HINT ε₀ ✱ [-; emp] ⊫ [id] ; (<affine> (P ∗ P -∗ False))%assert5 ✱ [emp].
  Proof. rewrite empty_hyp_first_eq. unfold ExclusiveProp, SEPx, fold_right_sepcon. intros->. iSteps as "H". Qed.

Global Instance lock_prop_hint2 (P:mpred)  E:
ExclusiveProp P ->
  HINT ε₀ ✱ [-; emp] ⊫ [id] ; (|={E}=> <affine> (P ∗ P -∗ False))%assert5 ✱ [emp].
  Proof. rewrite empty_hyp_first_eq. unfold ExclusiveProp, SEPx, fold_right_sepcon, BiAbd. simpl. intros.
    rewrite !bi.sep_emp.
    rewrite -(fupd_intro E _). rewrite H. iSteps. Qed.
End CONC_HINTS.