(** Facts about the global environment obtained by initializing the concrete
    atomic-wrapper compilation unit.

    [ClightLang.init_genv] permits the runtime environment to use different
    block numbers from the canonical environment built from the compilation
    unit.  Its [ge_related] witness nevertheless preserves symbols and the
    definitions at related blocks.  The lemmas below turn that relational
    guarantee into the concrete lookups needed by the wrapper executions. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.

Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.comp_correct.CUAST.
Require Import compcert.concurrency.comp_correct.ClightLang.

Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
Import ListNotations.
Local Open Scope string_scope.

Module ClightAtomicWrapperInit.

  Import ClightAtomicWrappers.

  Definition wrapper_canonical_ge (ids : wrapper_ids) :
      Genv.t Clight.fundef type :=
    Genv.globalenv
      (mkprogram (wrapper_definitions ids) (wrapper_public ids) 1%positive).

  (** A reusable consequence of [ge_related]: a symbol together with its
      function definition in the canonical environment has the same function
      definition, at a possibly different block, in the runtime environment. *)
  Lemma ge_related_find_symbol_funct_ptr
      (ge ge_local : Genv.t Clight.fundef type) id b_local fd
      (Hrelated : ge_related ge ge_local)
      (Hsymbol : Genv.find_symbol ge_local id = Some b_local)
      (Hfun : Genv.find_funct_ptr ge_local b_local = Some fd) :
    exists b,
      Genv.find_symbol ge id = Some b /\
      Genv.find_funct_ptr ge b = Some fd.
  Proof.
    inversion Hrelated as
      [j Hdom Hinj Hpublic Hsymbols Hdefs_local Hdefs_runtime
       Hdefs Hnext].
    specialize (Hsymbols id).
    rewrite Hsymbol in Hsymbols.
    inversion Hsymbols as [j' b0 b Hmap |]; subst.
    exists b. split; [reflexivity |].
    unfold Genv.find_funct_ptr, Genv.find_def in *.
    destruct ((Genv.genv_defs ge_local) ! b_local) as [gd |]
      eqn:Hlocal_def; try discriminate.
    destruct gd; try discriminate.
    inversion Hfun; subst f.
    specialize (Hdefs b_local b Hmap).
    rewrite Hlocal_def in Hdefs.
    rewrite <- Hdefs. reflexivity.
  Qed.

  Lemma wrapper_canonical_symbols ids :
    wrapper_ids_wf ids ->
    Genv.find_symbol (wrapper_canonical_ge ids) GAST.ent_atom =
      Some 1%positive /\
    Genv.find_symbol (wrapper_canonical_ge ids) GAST.ext_atom =
      Some 2%positive /\
    Genv.find_symbol (wrapper_canonical_ge ids) (atomic_load_id ids) =
      Some 3%positive /\
    Genv.find_symbol (wrapper_canonical_ge ids) (atomic_store_id ids) =
      Some 4%positive /\
    Genv.find_symbol (wrapper_canonical_ge ids) (atomic_CAS_id ids) =
      Some 5%positive.
  Proof.
    destruct ids as [load_id store_id cas_id].
    intros Hwf.
    unfold wrapper_ids_wf in Hwf; cbn in Hwf.
    destruct Hwf as
      (Hload_store & Hload_cas & Hstore_cas & Hload_print & Hload_ent &
       Hload_ext & Hstore_print & Hstore_ent & Hstore_ext & Hcas_print &
       Hcas_ent & Hcas_ext).
    assert (Hent_ext : GAST.ent_atom <> GAST.ext_atom) by discriminate.
    unfold wrapper_canonical_ge, wrapper_definitions, wrapper_public.
    cbn [atomic_load_id atomic_store_id atomic_CAS_id].
    repeat split; unfold Genv.find_symbol; cbn;
      repeat rewrite PTree.gsspec;
      repeat match goal with
        | |- context [peq ?x ?y] =>
            destruct (peq x y); [subst |];
              try contradiction; try congruence
        end;
      reflexivity.
  Qed.

  Lemma wrapper_canonical_functions ids :
    Genv.find_funct_ptr (wrapper_canonical_ge ids) 1%positive =
      Some ent_atom_external /\
    Genv.find_funct_ptr (wrapper_canonical_ge ids) 2%positive =
      Some ext_atom_external /\
    Genv.find_funct_ptr (wrapper_canonical_ge ids) 3%positive =
      Some (Internal atomic_load_function) /\
    Genv.find_funct_ptr (wrapper_canonical_ge ids) 4%positive =
      Some (Internal atomic_store_function) /\
    Genv.find_funct_ptr (wrapper_canonical_ge ids) 5%positive =
      Some (Internal atomic_CAS_function).
  Proof.
    destruct ids.
    unfold wrapper_canonical_ge, wrapper_definitions, wrapper_public.
    cbn [Genv.find_funct_ptr Genv.find_def].
    repeat split; reflexivity.
  Qed.

  Theorem initialized_wrapper_environment
      ids (Hids : wrapper_ids_wf ids)
      (raw_ge : Genv.t Clight.fundef type) (ge : Clight.genv)
      (Hinit : InteractionSemantics.init_genv
        Clight_IS_2_with_markers (wrapper_comp_unit ids) raw_ge ge) :
    exists ent_block ext_block load_block store_block cas_block,
      Genv.find_symbol ge GAST.ent_atom = Some ent_block /\
      Genv.find_funct_ptr ge ent_block = Some ent_atom_external /\
      Genv.find_symbol ge GAST.ext_atom = Some ext_block /\
      Genv.find_funct_ptr ge ext_block = Some ext_atom_external /\
      Genv.find_symbol ge (atomic_load_id ids) = Some load_block /\
      Genv.find_funct_ptr ge load_block =
        Some (Internal atomic_load_function) /\
      Genv.find_symbol ge (atomic_store_id ids) = Some store_block /\
      Genv.find_funct_ptr ge store_block =
        Some (Internal atomic_store_function) /\
      Genv.find_symbol ge (atomic_CAS_id ids) = Some cas_block /\
      Genv.find_funct_ptr ge cas_block =
        Some (Internal atomic_CAS_function).
  Proof.
    change (ClightLang.init_genv (wrapper_comp_unit ids) raw_ge ge) in Hinit.
    unfold ClightLang.init_genv in Hinit.
    destruct Hinit as [Hge Hrelated]. subst ge.
    change (ge_related raw_ge (wrapper_canonical_ge ids)) in Hrelated.
    pose proof (wrapper_canonical_symbols ids Hids) as Hsymbols.
    pose proof (wrapper_canonical_functions ids) as Hfunctions.
    destruct Hsymbols as
      (Hent_symbol & Hext_symbol & Hload_symbol & Hstore_symbol & Hcas_symbol).
    destruct Hfunctions as
      (Hent_fun & Hext_fun & Hload_fun & Hstore_fun & Hcas_fun).
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (wrapper_canonical_ge ids) GAST.ent_atom 1%positive
      ent_atom_external Hrelated Hent_symbol Hent_fun)
      as (ent_block & Hent_symbol' & Hent_fun').
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (wrapper_canonical_ge ids) GAST.ext_atom 2%positive
      ext_atom_external Hrelated Hext_symbol Hext_fun)
      as (ext_block & Hext_symbol' & Hext_fun').
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (wrapper_canonical_ge ids) (atomic_load_id ids) 3%positive
      (Internal atomic_load_function) Hrelated Hload_symbol Hload_fun)
      as (load_block & Hload_symbol' & Hload_fun').
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (wrapper_canonical_ge ids) (atomic_store_id ids) 4%positive
      (Internal atomic_store_function) Hrelated Hstore_symbol Hstore_fun)
      as (store_block & Hstore_symbol' & Hstore_fun').
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (wrapper_canonical_ge ids) (atomic_CAS_id ids) 5%positive
      (Internal atomic_CAS_function) Hrelated Hcas_symbol Hcas_fun)
      as (cas_block & Hcas_symbol' & Hcas_fun').
    exists ent_block, ext_block, load_block, store_block, cas_block.
    repeat split; assumption.
  Qed.

  (** Transport a successful external-name lookup through [ge_related].
      This is shared by client initialization: unlike the builtin wrapper
      markers, client declarations for [atomic_load], [atomic_store], and
      [atomic_CAS] remain [EF_external] definitions. *)
  Lemma ge_related_invert_external_symbol
      (ge ge_local : Genv.t Clight.fundef type) name id b_local
      (Hnorep : ClightLang.norep_ef_name ge_local)
      (Hall_symbols : forall b gd,
        (Genv.genv_defs ge_local) ! b = Some gd ->
        exists id0, (Genv.genv_symb ge_local) ! id0 = Some b)
      (Hrelated : ge_related ge ge_local)
      (Hblock :
        ClightLang.invert_block_from_string ge_local name = Some b_local)
      (Hsymbol : Genv.find_symbol ge_local id = Some b_local) :
    ClightLang.invert_symbol_from_string ge name = Some id.
  Proof.
    pose proof (ClightLang.invert_block_from_string_eq ge ge_local
      Hnorep Hall_symbols Hrelated name) as Hblocks.
    rewrite Hblock in Hblocks.
    inversion Hblocks as [| b b' Hpair]; subst.
    destruct Hpair as (id' & Hruntime_symbol & Hlocal_symbol).
    unfold ClightLang.invert_symbol_from_string.
    rewrite <- H. cbn.
    assert (Hruntime_inv : Genv.invert_symbol ge b = Some id').
    { apply Genv.find_invert_symbol. exact Hruntime_symbol. }
    rewrite Hruntime_inv.
    assert (Hid : id' = id).
    { assert (Hinv' : Genv.invert_symbol ge_local b_local = Some id').
      { apply Genv.find_invert_symbol. exact Hlocal_symbol. }
      assert (Hinv : Genv.invert_symbol ge_local b_local = Some id).
      { apply Genv.find_invert_symbol. exact Hsymbol. }
      congruence. }
    now subst id'.
  Qed.

  Lemma ge_related_invert_external_absent
      (ge ge_local : Genv.t Clight.fundef type) name
      (Hnorep : ClightLang.norep_ef_name ge_local)
      (Hall_symbols : forall b gd,
        (Genv.genv_defs ge_local) ! b = Some gd ->
        exists id0, (Genv.genv_symb ge_local) ! id0 = Some b)
      (Hrelated : ge_related ge ge_local)
      (Hblock : ClightLang.invert_block_from_string ge_local name = None) :
    ClightLang.invert_symbol_from_string ge name = None.
  Proof.
    pose proof (ClightLang.invert_block_from_string_eq ge ge_local
      Hnorep Hall_symbols Hrelated name) as Hblocks.
    rewrite Hblock in Hblocks.
    inversion Hblocks; subst.
    unfold ClightLang.invert_symbol_from_string.
    rewrite <- H0. reflexivity.
  Qed.

  Lemma wrapper_canonical_norep_external_names ids :
    ClightLang.norep_ef_name (wrapper_canonical_ge ids).
  Proof.
    intros b b' gd gd' name name' Hneq Hdef Hdef' Hname Hname'.
    unfold wrapper_canonical_ge, wrapper_definitions, wrapper_public in *.
    unfold Genv.find_def in Hdef, Hdef'.
    cbn in Hdef, Hdef'.
    repeat rewrite PTree.gsspec in Hdef, Hdef'.
    repeat match goal with
      | H : context [peq ?x ?y] |- _ =>
          destruct (peq x y); [subst |]; cbn in H; try discriminate
      end.
    all: inversion Hdef; inversion Hdef'; subst.
    all: cbn [ClightLang.gd_ef_fun_name ent_atom_external
      ext_atom_external] in Hname, Hname'.
    all: inversion Hname; inversion Hname'; subst;
      try contradiction; try congruence; try discriminate.
  Qed.

  Lemma wrapper_canonical_definitions_have_symbols ids :
    wrapper_ids_wf ids ->
    forall b gd,
      (Genv.genv_defs (wrapper_canonical_ge ids)) ! b = Some gd ->
      exists id, (Genv.genv_symb (wrapper_canonical_ge ids)) ! id = Some b.
  Proof.
    intros Hids.
    pose proof (wrapper_canonical_symbols ids Hids) as Hsymbols.
    destruct Hsymbols as
      (Hent & Hext & Hload & Hstore & Hcas).
    unfold Genv.find_symbol in Hent, Hext, Hload, Hstore, Hcas.
    intros b gd Hdef.
    unfold wrapper_canonical_ge, wrapper_definitions, wrapper_public in Hdef.
    cbn in Hdef.
    repeat rewrite PTree.gsspec in Hdef.
    repeat match goal with
      | H : context [peq ?x ?y] |- _ =>
          destruct (peq x y); [subst |]; cbn in H; try discriminate
      end.
    all: inversion Hdef; subst.
    - exists (atomic_CAS_id ids). exact Hcas.
    - exists (atomic_store_id ids). exact Hstore.
    - exists (atomic_load_id ids). exact Hload.
    - exists GAST.ext_atom. exact Hext.
    - exists GAST.ent_atom. exact Hent.
  Qed.

  Lemma wrapper_canonical_atomic_invert_blocks ids :
    ClightLang.invert_block_from_string (wrapper_canonical_ge ids)
      "atomic_load" = None /\
    ClightLang.invert_block_from_string (wrapper_canonical_ge ids)
      "atomic_store" = None /\
    ClightLang.invert_block_from_string (wrapper_canonical_ge ids)
      "atomic_CAS" = None.
  Proof.
    destruct ids. vm_compute. repeat split; reflexivity.
  Qed.

  (** The three atomic implementations are internal definitions.  Therefore
      inter-module call proofs obtain, e.g.,
      [invert_symbol_from_string caller_ge "atomic_load"] from the caller's
      external declaration, not from initialization of this compilation unit. *)
  Theorem initialized_wrapper_atomic_names_are_internal
      ids (Hids : wrapper_ids_wf ids)
      (raw_ge : Genv.t Clight.fundef type) (ge : Clight.genv)
      (Hinit : InteractionSemantics.init_genv
        Clight_IS_2_with_markers (wrapper_comp_unit ids) raw_ge ge) :
    ClightLang.invert_symbol_from_string ge "atomic_load" = None /\
    ClightLang.invert_symbol_from_string ge "atomic_store" = None /\
    ClightLang.invert_symbol_from_string ge "atomic_CAS" = None.
  Proof.
    change (ClightLang.init_genv (wrapper_comp_unit ids) raw_ge ge) in Hinit.
    unfold ClightLang.init_genv in Hinit.
    destruct Hinit as [Hge Hrelated]. subst ge.
    change (ge_related raw_ge (wrapper_canonical_ge ids)) in Hrelated.
    change
      (ClightLang.invert_symbol_from_string raw_ge "atomic_load" = None /\
       ClightLang.invert_symbol_from_string raw_ge "atomic_store" = None /\
       ClightLang.invert_symbol_from_string raw_ge "atomic_CAS" = None).
    pose proof (wrapper_canonical_atomic_invert_blocks ids) as Hblocks.
    destruct Hblocks as (Hload & Hstore & Hcas).
    repeat split; eapply ge_related_invert_external_absent.
    all: try apply wrapper_canonical_norep_external_names.
    all: try (apply wrapper_canonical_definitions_have_symbols; exact Hids).
    all: try exact Hrelated.
    all: assumption.
  Qed.

End ClightAtomicWrapperInit.
