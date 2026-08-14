(** The heterogeneous CASCompCert target used by [ClightAM_DRF].

    Client compilation units retain the checked-in [Clight_IS_2] language.
    Only the implementation of the three atomic primitives uses the contained
    marker-enabled variant. *)

From mathcomp.boot Require Import fintype ssrnat.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.AST.
Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.common.GlobDefs.
Require Import compcert.concurrency.common.InteractionSemantics.
Require Import compcert.concurrency.comp_correct.ClightLang.

Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.

From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Module ClightAtomicTarget.

  Definition language_count : nat := 2.

  Program Definition client_language_id : 'I_language_count :=
    @Ordinal language_count 0 _.

  Program Definition wrapper_language_id : 'I_language_count :=
    @Ordinal language_count 1 _.

  (** A program may contain ordinary Clight clients and marker-enabled Clight
      wrappers, but no other languages. *)
  Program Definition languages (i : 'I_language_count) : Language :=
    if eqn i 0 then ClightLang.Clight_IS_2
    else Clight_IS_2_with_markers.

  Program Definition client_unit
      (cu : ClightLang.clight_comp_unit) :
      @cunit language_count languages :=
    {| lid := client_language_id;
       cu := cu |}.

  Program Definition wrapper_unit
      (ids : ClightAtomicWrappers.wrapper_ids) :
      @cunit language_count languages :=
    {| lid := wrapper_language_id;
       cu := ClightAtomicWrappers.wrapper_comp_unit ids |}.

  (** The target retains every client unit verbatim and links one concrete
      implementation unit for [atomic_load], [atomic_store], and
      [atomic_CAS]. *)
  Definition linked_units
      (clients : list ClightLang.clight_comp_unit)
      (ids : ClightAtomicWrappers.wrapper_ids) :
      @cunits language_count languages :=
    map client_unit clients ++ [wrapper_unit ids].

  Definition linked_program
      (clients : list ClightLang.clight_comp_unit)
      (ids : ClightAtomicWrappers.wrapper_ids)
      (thread_entries : entries) :
      @prog language_count languages :=
    (linked_units clients ids, thread_entries).

  (** The wrapper occupies the first index after the client prefix. *)
  Lemma linked_units_wrapper_nth_error clients ids :
    nth_error (linked_units clients ids) (length clients) =
      Some (wrapper_unit ids).
  Proof.
    unfold linked_units.
    induction clients as [|client clients IH]; simpl; auto.
  Qed.

  Lemma linked_units_client_nth_error clients ids n client :
    nth_error clients n = Some client ->
    nth_error (linked_units clients ids) n = Some (client_unit client).
  Proof.
    intros Hclient.
    unfold linked_units.
    rewrite nth_error_app1.
    - rewrite nth_error_map, Hclient. reflexivity.
    - rewrite length_map. apply nth_error_Some.
      rewrite Hclient. discriminate.
  Qed.

  (** Client modules reserve the wrapper API: none of the identifiers
      exported by the wrapper is the name of a client-side internal
      function.  External declarations of these identifiers are allowed and
      are precisely what an ordinary client uses to call the wrapper. *)
  Definition clients_reserve_wrapper_ids
      (clients : list ClightLang.clight_comp_unit)
      (ids : ClightAtomicWrappers.wrapper_ids) : Prop :=
    forall client id,
      In client clients ->
      In id (ClightAtomicWrappers.wrapper_public ids) ->
      ~ In id (ClightLang.internal_fn client).

  Definition internal_owner_step
      (id : ident)
      (ir : nat * option nat)
      (cui : @cunit language_count languages) : nat * option nat :=
    let (i, res) := ir in
    if res then (S i, res)
    else if In_dec ident_eq id
           (InteractionSemantics.internal_fn
             (languages (lid languages cui)) (cu languages cui))
         then (S i, Some i)
         else (S i, res).

  Lemma scan_reserved_clients clients id n :
    (forall client,
      In client clients -> ~ In id (ClightLang.internal_fn client)) ->
    fold_left (internal_owner_step id) (map client_unit clients) (n, None) =
      (Nat.add n (length clients), None).
  Proof.
    revert n.
    induction clients as [|client clients IH]; intros n Hreserve; simpl.
    - f_equal; lia.
    - unfold internal_owner_step at 1; simpl.
      destruct (In_dec ident_eq id (ClightLang.internal_fn client))
        as [Hin | Hnotin].
      + exfalso. eapply Hreserve; [left; reflexivity | exact Hin].
      + rewrite IH.
        * f_equal; lia.
        * intros client' Hin'. eapply Hreserve. right; exact Hin'.
  Qed.

  Lemma scan_linked_units_finds_wrapper clients ids id :
    clients_reserve_wrapper_ids clients ids ->
    ClightAtomicWrappers.wrapper_ids_wf ids ->
    In id (ClightAtomicWrappers.wrapper_public ids) ->
    snd (fold_left (internal_owner_step id) (linked_units clients ids)
      (0%nat, None)) = Some (length clients).
  Proof.
    intros Hreserve Hwf Hpublic.
    unfold linked_units.
    rewrite fold_left_app.
    rewrite scan_reserved_clients.
    - simpl. unfold internal_owner_step; simpl.
      destruct (In_dec ident_eq id
        (ClightLang.internal_fn
          (ClightAtomicWrappers.wrapper_comp_unit ids))) as [Hin | Hnotin].
      + reflexivity.
      + exfalso. apply Hnotin.
        rewrite ClightAtomicWrappers.wrapper_internal_functions by exact Hwf.
        exact Hpublic.
    - intros client Hin. eapply Hreserve; eauto.
  Qed.

  (** The owner scan used by [GlobEnv.init] therefore resolves any wrapper
      public identifier to the appended module, provided the supplied ordinal
      is that module's list index. *)
  Lemma initialized_linked_units_get_mod_at_wrapper
      clients ids GE id (wrapper_ix : 'I_(GlobEnv.M GE)) :
    GlobEnv.init (linked_units clients ids) GE ->
    clients_reserve_wrapper_ids clients ids ->
    ClightAtomicWrappers.wrapper_ids_wf ids ->
    In id (ClightAtomicWrappers.wrapper_public ids) ->
    nat_of_ord wrapper_ix = length clients ->
    GlobEnv.get_mod GE id = Some wrapper_ix.
  Proof.
    intros Hinit Hreserve Hwf Hpublic Hix.
    apply (proj2 (GlobEnv.get_mod_init
      (linked_units clients ids) GE Hinit id wrapper_ix)).
    change (snd (fold_left (internal_owner_step id)
      (linked_units clients ids) (0%nat, None)) =
      Some (nat_of_ord wrapper_ix)).
    rewrite Hix.
    eapply scan_linked_units_finds_wrapper; eauto.
  Qed.

  Corollary initialized_linked_units_get_mod_atomic_load
      clients ids GE (wrapper_ix : 'I_(GlobEnv.M GE)) :
    GlobEnv.init (linked_units clients ids) GE ->
    clients_reserve_wrapper_ids clients ids ->
    ClightAtomicWrappers.wrapper_ids_wf ids ->
    nat_of_ord wrapper_ix = length clients ->
    GlobEnv.get_mod GE (ClightAtomicWrappers.atomic_load_id ids) =
      Some wrapper_ix.
  Proof.
    intros. eapply initialized_linked_units_get_mod_at_wrapper; eauto.
    unfold ClightAtomicWrappers.wrapper_public. destruct ids; simpl; auto.
  Qed.

  Corollary initialized_linked_units_get_mod_atomic_store
      clients ids GE (wrapper_ix : 'I_(GlobEnv.M GE)) :
    GlobEnv.init (linked_units clients ids) GE ->
    clients_reserve_wrapper_ids clients ids ->
    ClightAtomicWrappers.wrapper_ids_wf ids ->
    nat_of_ord wrapper_ix = length clients ->
    GlobEnv.get_mod GE (ClightAtomicWrappers.atomic_store_id ids) =
      Some wrapper_ix.
  Proof.
    intros. eapply initialized_linked_units_get_mod_at_wrapper; eauto.
    unfold ClightAtomicWrappers.wrapper_public. destruct ids; simpl; auto.
  Qed.

  Corollary initialized_linked_units_get_mod_atomic_CAS
      clients ids GE (wrapper_ix : 'I_(GlobEnv.M GE)) :
    GlobEnv.init (linked_units clients ids) GE ->
    clients_reserve_wrapper_ids clients ids ->
    ClightAtomicWrappers.wrapper_ids_wf ids ->
    nat_of_ord wrapper_ix = length clients ->
    GlobEnv.get_mod GE (ClightAtomicWrappers.atomic_CAS_id ids) =
      Some wrapper_ix.
  Proof.
    intros. eapply initialized_linked_units_get_mod_at_wrapper; eauto.
    unfold ClightAtomicWrappers.wrapper_public. destruct ids; simpl; auto.
  Qed.

  Lemma initialized_linked_units_have_wrapper_at
      clients ids GE (wrapper_ix : 'I_(GlobEnv.M GE)) :
    GlobEnv.init (linked_units clients ids) GE ->
    nat_of_ord wrapper_ix = length clients ->
    exists (raw_ge : Genv.t Clight_IS_2_with_markers.(F)
                            Clight_IS_2_with_markers.(V))
           (wrapper_ge : Clight_IS_2_with_markers.(G)),
      GlobEnv.modules GE wrapper_ix =
        ModSem.Build_t Clight_IS_2_with_markers raw_ge wrapper_ge /\
      InteractionSemantics.init_genv Clight_IS_2_with_markers
        (ClightAtomicWrappers.wrapper_comp_unit ids) raw_ge wrapper_ge.
  Proof.
    intros Hinit Hix.
    destruct (GlobEnv.ge_init (linked_units clients ids) GE Hinit wrapper_ix)
      as [cui [Hnth Hmod]].
    change (nth_error (linked_units clients ids) (nat_of_ord wrapper_ix) =
      Some cui) in Hnth.
    rewrite Hix, linked_units_wrapper_nth_error in Hnth.
    inversion Hnth; subst cui; clear Hnth.
    change (ModSem.init_modsem
      Clight_IS_2_with_markers
      (ClightAtomicWrappers.wrapper_comp_unit ids)
      (GlobEnv.modules GE wrapper_ix)) in Hmod.
    inversion Hmod; subst. eauto.
  Qed.

  (** Runtime identity and initialization of any client unit at its original
      list position.  Unlike the wrapper, a client retains the exact
      checked-in [Clight_IS_2] language. *)
  Lemma initialized_linked_units_have_client_at
      clients ids GE n client (client_ix : 'I_(GlobEnv.M GE)) :
    GlobEnv.init (linked_units clients ids) GE ->
    nth_error clients n = Some client ->
    nat_of_ord client_ix = n ->
    exists (raw_ge : Genv.t ClightLang.Clight_IS_2.(F)
                            ClightLang.Clight_IS_2.(V))
           (client_ge : ClightLang.Clight_IS_2.(G)),
      GlobEnv.modules GE client_ix =
        ModSem.Build_t ClightLang.Clight_IS_2 raw_ge client_ge /\
      InteractionSemantics.init_genv ClightLang.Clight_IS_2
        client raw_ge client_ge.
  Proof.
    intros Hinit Hclient Hix.
    destruct (GlobEnv.ge_init (linked_units clients ids) GE Hinit client_ix)
      as [cui [Hnth Hmod]].
    change (nth_error (linked_units clients ids) (nat_of_ord client_ix) =
      Some cui) in Hnth.
    rewrite Hix, (linked_units_client_nth_error clients ids n client Hclient)
      in Hnth.
    inversion Hnth; subst cui; clear Hnth.
    change (ModSem.init_modsem ClightLang.Clight_IS_2 client
      (GlobEnv.modules GE client_ix)) in Hmod.
    inversion Hmod; subst. eauto.
  Qed.

  Corollary initialized_linked_units_have_single_client client ids GE :
    GlobEnv.init (linked_units [client] ids) GE ->
    exists (client_ix : 'I_(GlobEnv.M GE))
           (raw_ge : Genv.t ClightLang.Clight_IS_2.(F)
                            ClightLang.Clight_IS_2.(V))
           (client_ge : ClightLang.Clight_IS_2.(G)),
      nat_of_ord client_ix = 0 /\
      GlobEnv.modules GE client_ix =
        ModSem.Build_t ClightLang.Clight_IS_2 raw_ge client_ge /\
      InteractionSemantics.init_genv ClightLang.Clight_IS_2
        client raw_ge client_ge.
  Proof.
    intros Hinit.
    assert (Hlt : is_true (0 < GlobEnv.M GE)).
    { rewrite (GlobEnv.mod_num (linked_units [client] ids));
        [reflexivity | exact Hinit]. }
    pose (client_ix := @Ordinal (GlobEnv.M GE) 0 Hlt).
    destruct (initialized_linked_units_have_client_at
      [client] ids GE 0 client client_ix Hinit eq_refl eq_refl)
      as [raw_ge [client_ge [Hmodule Hclient_init]]].
    exists client_ix, raw_ge, client_ge.
    split; [reflexivity |].
    split; assumption.
  Qed.

  (** A single canonical ordinal witnesses both facts needed by the global
      call rule: it is the initialized marker-enabled wrapper module and it
      owns all three atomic entry identifiers. *)
  Theorem initialized_linked_units_have_owned_wrapper clients ids GE :
    GlobEnv.init (linked_units clients ids) GE ->
    clients_reserve_wrapper_ids clients ids ->
    ClightAtomicWrappers.wrapper_ids_wf ids ->
    exists (wrapper_ix : 'I_(GlobEnv.M GE))
           (raw_ge : Genv.t Clight_IS_2_with_markers.(F)
                            Clight_IS_2_with_markers.(V))
           (wrapper_ge : Clight_IS_2_with_markers.(G)),
      nat_of_ord wrapper_ix = length clients /\
      GlobEnv.modules GE wrapper_ix =
        ModSem.Build_t Clight_IS_2_with_markers raw_ge wrapper_ge /\
      InteractionSemantics.init_genv Clight_IS_2_with_markers
        (ClightAtomicWrappers.wrapper_comp_unit ids) raw_ge wrapper_ge /\
      GlobEnv.get_mod GE (ClightAtomicWrappers.atomic_load_id ids) =
        Some wrapper_ix /\
      GlobEnv.get_mod GE (ClightAtomicWrappers.atomic_store_id ids) =
        Some wrapper_ix /\
      GlobEnv.get_mod GE (ClightAtomicWrappers.atomic_CAS_id ids) =
        Some wrapper_ix.
  Proof.
    intros Hinit Hreserve Hwf.
    assert (Hlt : is_true (length clients < GlobEnv.M GE)).
    { rewrite (GlobEnv.mod_num (linked_units clients ids)); [| exact Hinit].
      unfold linked_units. rewrite length_app, length_map.
      simpl. rewrite addn1. apply ltnSn. }
    pose (wrapper_ix := @Ordinal (GlobEnv.M GE) (length clients) Hlt).
    destruct (initialized_linked_units_have_wrapper_at
      clients ids GE wrapper_ix Hinit eq_refl)
      as [raw_ge [wrapper_ge [Hmodule Hgenv]]].
    exists wrapper_ix, raw_ge, wrapper_ge.
    split; [reflexivity |].
    split; [exact Hmodule |].
    split; [exact Hgenv |].
    split.
    - eapply initialized_linked_units_get_mod_atomic_load; eauto.
    - split.
      + eapply initialized_linked_units_get_mod_atomic_store; eauto.
      + eapply initialized_linked_units_get_mod_atomic_CAS; eauto.
  Qed.

  (** Initialization of the linked collection necessarily creates a runtime
      module for the appended wrapper compilation unit.  In particular, this
      exposes both its marker-enabled language and the language-specific
      global environments used to initialize it. *)
  Lemma initialized_linked_units_have_wrapper clients ids GE :
    GlobEnv.init (linked_units clients ids) GE ->
    exists (i : 'I_(GlobEnv.M GE))
           (raw_ge : Genv.t Clight_IS_2_with_markers.(F)
                            Clight_IS_2_with_markers.(V))
           (wrapper_ge : Clight_IS_2_with_markers.(G)),
      GlobEnv.modules GE i =
        ModSem.Build_t Clight_IS_2_with_markers raw_ge wrapper_ge /\
      InteractionSemantics.init_genv Clight_IS_2_with_markers
        (ClightAtomicWrappers.wrapper_comp_unit ids) raw_ge wrapper_ge.
  Proof.
    intros Hinit.
    assert (Hlt : is_true (length clients < GlobEnv.M GE)).
    { rewrite (GlobEnv.mod_num (linked_units clients ids)); [| exact Hinit].
      unfold linked_units.
      rewrite length_app, length_map.
      simpl. rewrite addn1. apply ltnSn. }
    pose (i := @Ordinal (GlobEnv.M GE) (length clients) Hlt).
    destruct (initialized_linked_units_have_wrapper_at
      clients ids GE i Hinit eq_refl)
      as [raw_ge [wrapper_ge [Hmodule Hgenv]]].
    exists i, raw_ge, wrapper_ge. split; assumption.
  Qed.

  Corollary initialized_linked_units_wrapper_language clients ids GE :
    GlobEnv.init (linked_units clients ids) GE ->
    exists i : 'I_(GlobEnv.M GE),
      ModSem.lang (GlobEnv.modules GE i) = Clight_IS_2_with_markers.
  Proof.
    intros Hinit.
    destruct (initialized_linked_units_have_wrapper clients ids GE Hinit)
      as [i [raw_ge [wrapper_ge [Hmodule _]]]].
    exists i. rewrite Hmodule. reflexivity.
  Qed.

End ClightAtomicTarget.
