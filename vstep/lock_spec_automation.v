(* Require Import VST.vstep.vstep. *)
From diaframe Require Import defs proofmode_base util_classes.
From VST.atomics Require Import general_atomics verif_lock_atomic.
Require Import VST.floyd.library.
From  VST.concurrency Require Import threads lock_specs.

Section DVST_LOCK_SPECS.

  (* #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined. *)

  Context `{!VSTGS OK_ty Σ}.
   (*
  Lemma make_lock_inv_1' : forall v N, 
    atomic_int_at Ews (vint 1) v ⊢
      ∀ R, |={⊤}=> (∃ h, <affine> ⌜ptr_of h = v /\ name_of h = N⌝ ∗ lock_inv 1 h (R h)).
    Proof.
      intros.
      iIntros "a".
      iDestruct (atomic_int_isptr with "a") as %Ha.
      iMod cinv_alloc_strong as (g) "(_ & Hg & Hi)"; first apply pred_infinite_True.
      iIntros (h).
      iExists (v, N, g); unfold lock_inv; simpl; iFrame.
      iMod ("Hi" $! (inv_for_lock v (h (v, N, g))) with "[-]").
    { iExists true; iFrame; done. }
      iModIntro; iSplit. done. iSplit; done.
    Qed.
    (* lock specs that defers committing to a certain invariant *)
  Program Definition makelock_spec_inv_defered :=
  WITH gv: _, N : _
  PRE [ ]
     PROP ()
     PARAMS () GLOBALS (gv)
     SEP (mem_mgr gv)
  POST [ tptr t_lock ] (* asymmetric consequence makes this messy *) ∃ v,
     PROP ()
     RETURN (v)
     SEP (mem_mgr gv;  ∀ R, |={⊤}=> ∃ h , <affine> ⌜ptr_of h = v /\ name_of h = N⌝ ∗ lock_inv 1 h (R h)).

  Lemma makelock_inv_defered: funspec_sub (snd makelock_spec) makelock_spec_inv_defered.
  Proof.
    split; first done. intros (gv, N) ?; simpl in *. Intros.
    iIntros "H !>". iExists gv, emp. rewrite bi.emp_sep. iSplit; first done; iSplit; auto.
    iPureIntro. intros. Intros. rewrite bi.emp_sep. monPred.unseal. Intros x; Exists x.
    iIntros "(? & $ & $ & H & _)".
    iSplit; first done.
    rewrite bi.sep_emp. iApply make_lock_inv_1'.
    iFrame. 
  Qed.

  Lemma and_affine_sep {prop:bi} P (Q:prop) :
    Persistent P -> Absorbing P ->
      P ∧ Q ⊣⊢ <affine> P ∗ Q.
  Proof. intros; iSplit; iIntros "[? ?]"; iFrame. Qed.

  Program Definition release_inv_spec_defered :=
    WITH h : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (∀ R, lock_inv 1 h R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (∀ R, R -∗ lock_inv 1 h R).

  Lemma release_inv_defered : funspec_sub (snd release_spec) release_inv_spec_defered.
  Proof.
    split; first done. intros h ?. simpl in *. Intros.
    unfold rev_curry, tcurry. iIntros "H !>".
    destruct h as ((v, N), g).
    iExists (v, emp), emp. simpl in *.
    rewrite bi.emp_sep. iSplit; first done; iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; monPred.unseal.
      iDestruct "H" as "(_ & % & _ & H)".
      do 4 (iSplit; auto).
      iDestruct "H" as "(H & _)".
      unfold lock_inv; simpl; unfold atomic_lock_inv.
      (* iDestruct "H2" as "(% & #H & H2)". *)
      (* rewrite -> prop_true_andp by auto. *)
      unfold atomic_shift. iAuIntro. unfold atomic_acc; simpl.
      admit.
    - iPureIntro. iIntros (rho') "[% _]".
      unfold PROPx, LOCALx, SEPx; simpl. rewrite bi.sep_emp //.

      iSplit; [done|].
      iSplit; [done|].
      iIntros.
      unfold lock_inv. unfold atomic_impl.
      unfold atomic_lock_inv.
  Admitted.

 *)

  Context {LI : lock_impl}.

  Notation InvType := Mpred.
  
  Program Definition release_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R; <affine> ⌜ExclusiveProp R⌝; R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R).
  Next Obligation.
  Admitted.
  
  Lemma release_simple : funspec_sub release_spec release_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; first done; intros ((sh, h), R) ?; Intros.
    iIntros "(? & ? & H) !>"; iExists (sh, h, R, R, lock_inv sh h R), emp.
    iSplit; first done.
    iSplit; last by iPureIntro; entailer!.
    repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(? & HR & % & ? & _)".
    iSplitR.
    { rewrite H0; done. }
    iFrame; auto.
  Qed.

 Program Definition freelock_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH h : _, R : _
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (lock_inv 1 h R; <affine> ⌜ExclusiveProp R⌝; R)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (R).
  Next Obligation.
  Admitted.
  
  Lemma freelock_simple : funspec_sub freelock_spec freelock_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; first done; intros (h, R) ?; Intros.
    iIntros "(? & ? & H) !>"; iExists (h, R, R), emp.
    iSplit; first done.
    iSplit; last by iPureIntro; entailer!.
    repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(? & $ & %HR & ? & _)".
    iFrame; rewrite bi.sep_emp.
    iModIntro.
    iIntros " (r1 & ? & r2)".
    iPoseProof (HR with "[r1 r2]") as "?"; iFrame.
  Qed.

End DVST_LOCK_SPECS.

(* name of function (an AST.ident), a list of spec subsume relations to try  *)
Ltac2 Type vstep_specs_type := (constr * constr) list.
Ltac2 mutable vstep_specs : unit -> vstep_specs_type  := fun _ => [].

Ltac2 Set vstep_specs as old_vstep_specs :=
  fun _ => 
            (constr:(_makelock), constr:(funspec_sub_refl_dep))::
            (constr:(_freelock), constr:(freelock_simple))::
            (constr:(_release), constr:(release_simple))::
            (* (constr:(_release), constr:(release_simple2)):: *)
            (constr:(_acquire), constr:(funspec_sub_refl_dep))::
            (constr:(_spawn), constr:(funspec_sub_refl_dep))::
            (old_vstep_specs ()).
