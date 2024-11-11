(* Require Import VST.vstep.vstep. *)
From diaframe Require Import defs proofmode_base util_classes.
From VST.atomics Require Import general_atomics verif_lock_atomic.
Require Import VST.floyd.library.
From  VST.concurrency Require Import threads lock_specs.

Section DVST_LOCK_SPECS.

  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr)}.

  Program Definition release_inv_spec_defered :=
  WITH p : val  
  PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP (atomic_int_at Ews (vint 1) p)
    POST [ tvoid ]
       ∀ R : mpred,
       ∀ N,
       PROP ()
       LOCAL ()
       SEP (R ={⊤}=∗ ∃ h : lock_handle, ⌜ptr_of h = p /\ name_of h = N⌝ ∧ lock_inv 1 h R).

  Lemma release_inv_defered : funspec_sub ( release_spec_nonatomic) release_inv_spec_defered.
  Proof.
    split; first done. intros p ?. simpl in *. Intros.
    unfold rev_curry, tcurry. iIntros "H !>".
    simpl. 
    unfold atomic_spec_type0.
    iExists (p), emp. simpl in *.
    rewrite bi.emp_sep. iSplit; first done; iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; monPred.unseal.
      rewrite !bi.sep_emp.
      iDestruct "H" as "(_ & % & _ & H)".
      do 3 (iSplit; auto).
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl. rewrite bi.sep_emp //.
      iDestruct "H" as "(_ & _ & H )".
      iIntros (R N).
      iDestruct (atomic_int_isptr with "H") as %Ha.
      repeat iSplit; auto.
      iIntros "R".
      iPoseProof (make_lock_inv_0 with "[-]") as "H". { iAccu. }
      done.
  Qed.
End DVST_LOCK_SPECS.

(* name of function (an AST.ident), a list of spec subsume relations to try  *)
  Ltac2 Type vstep_specs_type := (constr * constr) list.
  Ltac2 mutable vstep_specs : unit -> vstep_specs_type  := fun _ => [].

  Ltac2 Set vstep_specs as old_vstep_specs :=
    fun _ => 
             (constr:(_makelock), constr:(makelock_spec))::
             (* (constr:(_freelock), constr:(funspec_sub_refl_dep)):: *)
             (constr:(_release), constr:(release_inv_defered))::
             (* (constr:(_release), constr:(release_simple2)):: *)
             (* (constr:(_acquire), constr:(funspec_sub_refl_dep)):: *)
             (* (constr:(_spawn), constr:(funspec_sub_refl_dep)):: *)
             (old_vstep_specs ()).
