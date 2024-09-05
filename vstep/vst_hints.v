Require Import VST.vstep.vstep.
From diaframe Require Import defs proofmode_base.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.

Section SPECS.
Context `{!VSTGS OK_ty Σ}.
Context {LI : lock_impl}.

Notation InvType := Mpred.

  Program Definition release_spec_simple2 :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP (ExclusiveProp R)
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R; R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R).
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Lemma release_simple2 : funspec_sub lock_specs.release_spec release_spec_simple2.
  Proof.
    Admitted.
End SPECS.



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