From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset frac agree.
From VST.lithium Require Import programs.
From VST.lithium Require Import type_options.
Require Import iris_ora.algebra.frac_auth.

Definition lockN : namespace := nroot.@"lockN".
Definition lock_id := gname.

(** Registering the necessary ghost state. *)

Lemma gs_disjUR (n : nat) (x y : gset_disjUR string): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof. intros Hv Hxy; destruct y; destruct Hxy; subst; hnf; eexists x0; auto. Qed.
Canonical Structure gset_disjUR_authR := @authR (gset_disjUR string) gs_disjUR.

Class lockG Σ := LockG {
   lock_inG :: inG Σ (gset_disjUR_authR);
   lock_excl_inG :: inG Σ (iris.algebra.excl.exclR unitO);
}.

(*
Definition lockΣ : gFunctors :=
  #[GFunctor (constRF (authR (gset_disjUR string)));
    GFunctor (constRF (exclR unitO))].
Global Instance subG_lockG {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.
*)


Section type.
  Context `{!lockG Σ} `{!typeG Σ} {cs : compspecs} .

  Definition lock_token (γ : lock_id) (l : list string) : mpred :=
    ∃ s : gset string, ⌜l ≡ₚ elements s⌝ ∧ own  γ (● (GSet s)).

  Global Instance lock_token_timeless γ l : Timeless (lock_token γ l).
  Proof. apply _. Qed.

  Theorem lock_token_exclusive (γ : gname) (l1 l2 : list string):
    lock_token γ l1 -∗ lock_token γ l2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (?) "[_ H1]".
    iDestruct "H2" as (?) "[_ H2]".
    iCombine "H1 H2" as "H".
    rewrite -own_op own_valid.
    (* iDestruct "H" as %H. *)
  Admitted.

  Theorem alloc_lock_token :
    ⊢ |==> ∃ γ, lock_token γ [].
  Proof.
    iMod (own_alloc (● GSet ∅)) as (γ) "Hγ"; first by apply auth_auth_valid.
    iModIntro. iExists γ, ∅. by iFrame.
  Qed.

  Program Definition tylocked_ex {A} (γ : lock_id) (n : string) (x : A) (ty : A → type) : type := {|
    ty_has_op_type ot mt := (ty x).(ty_has_op_type) ot mt;
    ty_own β l := (match β return _ with
                  | Own => l ◁ₗ ty x
                  | Shr => ∃ γ', inv lockN ((∃ x', l ◁ₗ ty x' ∗ own γ' (Excl ())) ∨ own γ (◯ GSet {[ n ]}))
                  end)%I;
    ty_own_val v := (v ◁ᵥ (ty x))%I;
  |}.
  Next Obligation.
    iIntros (A γ n x ty l E HE) "Hl".
    iMod (own_alloc (Excl ())) as (γ') "Hown" => //.
    iExists _. iApply inv_alloc. iIntros "!#". iLeft. iExists _. by iFrame.
  Qed.
  Next Obligation. iIntros (A γ n x ty ot mt v ?) "Hl". by iApply ty_aligned. Qed.
  Next Obligation. iIntros (A γ n x ty ot mt v ?) "Hl". by iApply ty_deref. Qed.
  Next Obligation. iIntros (A γ n x ty ot mt l ? ?) "Hl". by iApply ty_ref. Qed.

  Lemma tylocked_simplify_hyp_place A γ n x (ty : A → type) l T:
    (l ◁ₗ ty x -∗ T)
    ⊢ simplify_hyp (l ◁ₗ tylocked_ex γ n x ty) T.
  Proof. done. Qed.

  Definition tylocked_simplify_hyp_place_inst := [instance tylocked_simplify_hyp_place with 0%N].
  Global Existing Instance tylocked_simplify_hyp_place_inst.

  Lemma tylocked_simplify_goal_place A γ n x (ty : A → type) l T:
    l ◁ₗ ty x ∗ T
    ⊢ simplify_goal (l ◁ₗ tylocked_ex γ n x ty) T.
  Proof. iIntros "[$ $]". Qed.
  Definition tylocked_simplify_goal_place_inst := [instance tylocked_simplify_goal_place with 0%N].
  Global Existing Instance tylocked_simplify_goal_place_inst.

  Lemma tylocked_subsume A B γ n x1 x2 (ty : A → type) l β T:
    (∃ y, ⌜β = Own → x1 = x2 y⌝ ∧ T y)
    ⊢ subsume (l ◁ₗ{β} tylocked_ex γ n x1 ty) (λ y : B, l ◁ₗ{β} tylocked_ex γ n (x2 y) ty) T.
  Proof.
    iIntros "H". iDestruct "H" as (?) "(%H & ?)".
    iIntros "Hl".
    iExists _. iFrame. by destruct β; naive_solver. Qed.
  Definition tylocked_subsume_inst := [instance tylocked_subsume].
  Global Existing Instance tylocked_subsume_inst | 10.

  Definition tylocked_ex_token {A} (γ : lock_id) (n : string) (l : address) (β : own_state) (ty : A → type)  : mpred :=
    (∀ E x, <affine> ⌜↑lockN ⊆ E⌝ -∗ l ◁ₗ ty x ={E}=∗ l ◁ₗ{β} tylocked_ex γ n x ty ∗ own γ (◯ GSet {[ n ]}))%I.

  Lemma locked_open A n s l γ (x : A) ty β E:
    n ∉ s → ↑lockN ⊆ E →
    l ◁ₗ{β} tylocked_ex γ n x ty -∗
      lock_token γ s ={E}=∗
      ▷ ∃ x', l ◁ₗ ty x' ∗ lock_token γ (n :: s) ∗ tylocked_ex_token γ n l β ty ∗ ⌜β = Own → x = x'⌝.
  Proof.
    iIntros (Hnotin ?) "Hl Hown".
    iDestruct "Hown" as (st Hperm) "Hown". rewrite ->Hperm in Hnotin.
    iMod (own_update with "Hown") as "[Hown Hs]". { eapply auth_update_alloc.
      apply (gset_disj_alloc_empty_local_update st {[n]}). set_solver. }
    rewrite {1}/ty_own /=.
    iAssert (lock_token γ (n :: s)) with "[Hown]" as "$". {
      iExists _. iFrame. iPureIntro. rewrite Hperm elements_union_singleton //. set_solver.
    }
    destruct β.
    { iIntros "!# !#". iExists _. iFrame. iSplit => //.
      iIntros (? ?) "H1 Hl". iModIntro.
      iFrame "Hl". 
    }

    iDestruct "Hl" as (γ') "#Hinv".
    iInv "Hinv" as "[Hl|>Hn]" "Hc".
    2: {
      Check own_valid_2 γ.
      
    Admitted.
  (*
    2: {
      iDestruct (own_valid_2 with "Hs Hn") as %Hown. exfalso. move: Hown.
      rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op. set_solver.
    }
    iMod ("Hc" with "[Hs]") as "_"; [by iRight|].
    iIntros "!# !#". iDestruct "Hl" as (x') "[Hl Hexcl]".
    iExists _. iFrame. iSplitL => //.
    (** locked_token *)
    iIntros (E' x'' ?) "Hl".
    iInv "Hinv" as "[H|>$]" "Hc". 1: {
      have ? : Inhabited A by apply (populate x).
      iDestruct "H" as (?) "[_ >He]".
        by iDestruct (own_valid_2 with "Hexcl He") as %Hown%exclusive_l.
    }
    iMod ("Hc" with "[Hl Hexcl]") as "_". 2: by iExists _.
    iModIntro. iLeft. iExists _. iFrame.
  Qed.
*)
  
  Lemma locked_close A n s l γ (x : A) ty β E:
    ↑lockN ⊆ E →
    tylocked_ex_token γ n l β ty -∗ l ◁ₗ ty x -∗ lock_token γ (n :: s) ={E}=∗
    lock_token γ s ∗ l ◁ₗ{β} tylocked_ex γ n x ty.
  Proof.
    iIntros (HE) "Hlocked Hl Hlock".
    iMod ("Hlocked" with "[//] Hl") as "[$ Hn]".
    iDestruct "Hlock" as (st Hst) "Htok".
    iExists (st ∖ {[n]}).
    iModIntro.
    iSplit.
    - iPureIntro.
      move: (Hst). rewrite {1}(union_difference_L {[n]} st).
      + rewrite ->elements_union_singleton => ?; last set_solver.
        by apply: Permutation.Permutation_cons_inv.
      + set_unfold => ??. subst. apply elem_of_elements. rewrite -Hst. set_solver.
    - iCombine "Htok" "Hn" as "Htok".
    Admitted.
      (*
      iMod (own_update with "[Htok]") as "H".
      iMod (own_update with "Htok") as "$" => //.
    eapply auth_update_dealloc.
      by apply gset_disj_dealloc_local_update.
  Qed.
*)

  Lemma annot_unlock A l β γ n ty (x : A) T:
    (find_in_context (FindDirect (lock_token γ)) (λ s : list string, ⌜n∉s⌝ ∗ (∀ x',
        lock_token γ (n :: s) -∗ tylocked_ex_token γ n l β ty -∗ ⌜β = Own → x = x'⌝ -∗
                       l ◁ₗ ty x' -∗ T)))
    ⊢ typed_annot_stmt UnlockA l (l ◁ₗ{β} tylocked_ex γ n x ty) T.
  Proof.
    iDestruct 1 as (s) "(Hs&%&HT)". iIntros "Hlocked".
    iMod (locked_open with "Hlocked Hs") as "Htok" => //.
    iApply step_fupd_intro => //. iModIntro.
   (* iDestruct "Htok" as (x') "(Hl&Hs&Htok&%)".
    by iApply ("HT" with "Hs Htok [//] Hl").
  Qed. *) Admitted.
  
  Definition annot_unlock_inst := [instance annot_unlock].
  Global Existing Instance annot_unlock_inst.

  Class WithLockId (ty : type) (γ : lock_id) := with_lock_id : True.

  Lemma type_annot_lock (l : address) β ty γ `{!WithLockId ty γ} T:
    (find_in_context (FindDirect (lock_token γ)) (λ s : list string, foldr (λ t T,
        find_in_context (FindDirect (λ '(existT A (l2, ty)), tylocked_ex_token (A:=A) γ t l2 β ty)) (λ '(existT A (l2, ty)), ∃ x,
          l2 ◁ₗ ty x ∗ (l2 ◁ₗ{β} tylocked_ex γ t x ty -∗ T))) (l ◁ₗ{β} ty -∗ lock_token γ [] -∗ T) s))
    ⊢ typed_annot_expr 1%nat LockA l (l ◁ₗ{β} ty) T.
  Proof.
    iIntros "H Hty".
    iDestruct "H" as (s) "[Htok Hs]".
    iApply step_fupd_intro => //. iModIntro.
    iInduction s as [|t s] "IH" => /=. 1: by iApply ("Hs" with "Hty Htok").
    iDestruct "Hs" as ([A [l2 ty2]]) "[Hlt H]".
    iDestruct "H" as (x) "[Hl HT]".
    iMod (locked_close with "Hlt Hl Htok") as "[Htok Hl]" => //.
    iApply ("IH" with "Htok [HT Hl] Hty"). by iApply "HT".
  Qed.
  Definition type_annot_lock_inst := [instance type_annot_lock].
  Global Existing Instance type_annot_lock_inst.
End type.

(* TODO: Do something stronger, e.g. sealing? *)
Global Typeclasses Opaque tylocked_ex lock_token tylocked_ex_token.
Notation tylocked γ n ty := (tylocked_ex γ n tt (λ _, ty)).
Notation tylocked_token γ n l β ty := (tylocked_ex_token γ n l β (λ _ : unit, ty)).
