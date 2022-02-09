Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics.
Require Import VST.atomics.general_atomics.
Require Import VST.atomics.lock.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_lock := Tstruct _atom_int noattr.

Section PROOFS.

  Definition atomic_int := Tstruct _atom_int noattr.
  Variable atomic_int_at : share -> val -> val -> mpred.
  Hypothesis atomic_int_at__ :
    forall sh v p, atomic_int_at sh v p |-- atomic_int_at sh Vundef p.
  Hypothesis atomic_int_isptr : forall sh v p, atomic_int_at sh v p |-- !! isptr p.
  Hint Resolve atomic_int_isptr : saturate_local.

  Definition make_atomic_spec :=
    DECLARE _make_atomic (make_atomic_spec atomic_int atomic_int_at).
  Definition free_atomic_spec :=
    DECLARE _free_atomic (free_atomic_int_spec atomic_int atomic_int_at).
  Definition atom_store_spec :=
    DECLARE _atom_store (atomic_store_spec atomic_int atomic_int_at).
  Definition atom_CAS_spec :=
    DECLARE _atom_CAS (atomic_CAS_spec atomic_int atomic_int_at).

  Definition makelock_spec :=
    DECLARE _makelock
    WITH gv: globals
    PRE []
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] EX p: val,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; atomic_int_at Ews (vint 0) p).

  Definition freelock_spec :=
    DECLARE _freelock
    WITH p : val
    PRE [ tptr t_lock ]
     PROP (is_pointer_or_null p)
     PARAMS (p)
     SEP (EX v : val, atomic_int_at Ews v p)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

  Program Definition release_spec :=
    DECLARE _release
    ATOMIC TYPE (rmaps.ConstType _) INVS empty top
    WITH p, gv
    PRE [ tptr t_lock ]
       PROP (is_pointer_or_null p)
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv) | (atomic_int_at Ews (vint 1) p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv) | (atomic_int_at Ews (vint 0) p).

  Program Definition acquire_spec :=
    DECLARE _acquire
    ATOMIC TYPE (rmaps.ConstType _) OBJ l INVS empty top
    WITH p, gv
    PRE [ tptr t_lock ]
       PROP (is_pointer_or_null p)
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv) | ((!! (l = true) && atomic_int_at Ews (vint 0) p) ||
                           (!! (l = false) && atomic_int_at Ews (vint 1) p))
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv) | (!! (l = true) && atomic_int_at Ews (vint 1) p).

  Definition Gprog : funspecs :=
    ltac:(with_library prog [make_atomic_spec; atom_store_spec; atom_CAS_spec;
                             free_atomic_spec; makelock_spec; freelock_spec;
                             release_spec; acquire_spec]).

  Lemma body_makelock: semax_body Vprog Gprog f_makelock makelock_spec.
  Proof.
    start_function.
    forward_call (vint 0).
    Intros p.
    forward.
    Exists p.
    entailer !.
  Qed.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    forward_call (p).
    entailer !.
  Qed.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (p, (vint 0), top: coPset, empty: coPset, Q, inv_names).
    - assert (Frame = [mem_mgr gv]); subst Frame; [ reflexivity | clear H0].
      simpl fold_right_sepcon. cancel.
      iIntros "AS".
      unfold atomic_shift, ashift.
      iDestruct "AS" as (P) "[P AS]".
      iMod ("AS" with "P") as (x) "[a [_ H]]".
      iExists Ews. iModIntro. iSplitL "a".
      + iSplit.
        * iPureIntro. apply writable_Ews.
        * iApply atomic_int_at__. iAssumption.
      + iIntros "AA".
        iPoseProof (sepcon_emp (atomic_int_at Ews (vint 0) p)) as "HA".
        iSpecialize ("HA" with "AA"). iMod ("H" $! tt with "HA"). auto.
    - entailer !.
  Qed.

  Lemma body_acquire: semax_body Vprog Gprog f_acquire acquire_spec.
    Proof.
      start_function.
      forward.
      forward.
      forward_loop (PROP ( )
       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
       gvars gv; temp _lock p)
       SEP (data_at Tsh tint (vint 0) v_expected;
            atomic_shift
              (λ l : bool,
                  !! (l = true) && atomic_int_at Ews (vint 0) p
                  || !! (l = false) && atomic_int_at Ews (vint 1) p) ∅ ⊤
              (λ (l : bool) (_ : ()),
                fold_right_sepcon [!! (l = true) && atomic_int_at Ews (vint 1) p])
              (λ _ : (), Q); mem_mgr gv)).
      - entailer !.
      - forward_call (p , Tsh, v_expected, (vint 0), (vint 1), top : coPset,
                         empty : coPset, fun _:val => Q, inv_names).
        + assert (Frame = [mem_mgr gv]); subst Frame; [ reflexivity | clear H0].
          simpl fold_right_sepcon. cancel.
          iIntros "AS".
          unfold atomic_shift, ashift.
          iDestruct "AS" as (P) "[P AS]".
          iMod ("AS" with "P") as (x) "[[a | a] [_ H]]".
          * iDestruct "a" as (a) "b". iExists Ews, (vint 0). iModIntro. iSplitL "b".
            -- iSplit; auto.
            -- iSpecialize ("H" $! tt). iIntros "AA". iApply "H".
               destruct (eq_dec (vint 0) (vint 0)). 2: exfalso; now apply n.
               iSplit; [iSplit|]; auto.
          * iExists Ews, (vint 1). iModIntro. destruct (eq_dec (vint 1) (vint 0)).
            1: inversion e. do 2 rewrite sepcon_andp_prop'. iSplit.
            -- iPureIntro. apply writable_Ews.
            -- admit.
        + Intros r. destruct (eq_dec r (vint 0)).
          * forward_if. 1: exfalso; apply H0'; auto. forward. entailer !.
          * forward_if. 2: inversion H0. forward. entailer !. admit.
    Abort.

End PROOFS.
