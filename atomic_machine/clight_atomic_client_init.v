(** Client-side initialization facts for calls to the atomic wrappers.

    A client compilation unit contains external declarations named
    [atomic_load], [atomic_store], and [atomic_CAS].  The global interaction
    semantics dispatches such a call by first recovering its identifier with
    [ClightLang.invert_symbol_from_string].  This file states a precise,
    program-level condition on the client's canonical environment and proves
    that ordinary [Clight_IS_2] initialization preserves all three name
    resolutions, even when the runtime environment renumbers blocks. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.

Require Import compcert.concurrency.comp_correct.CUAST.
Require Import compcert.concurrency.comp_correct.ClightLang.

Require Import atomic_machine.clight_atomic_wrappers.
Require Import atomic_machine.clight_atomic_wrapper_init.

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
Import ListNotations.
Local Open Scope string_scope.

Module ClightAtomicClientInit.

  Import ClightAtomicWrappers.
  Import ClightAtomicWrapperInit.

  Definition client_canonical_ge (cu : ClightLang.clight_comp_unit) :
      Genv.t Clight.fundef type :=
    Genv.globalenv
      (mkprogram (ClightLang.cu_defs cu) (ClightLang.cu_public cu)
        1%positive).

  (** A directly usable well-formedness condition for atomic clients.

      The first two fields make the external-name scan transportable through
      [ge_related].  Each remaining group says that the canonical environment
      has the expected external declaration at the configured identifier and
      that scanning by its external name selects that same block.  Thus the
      condition rules out ambiguous duplicate external names and mismatched
      signatures at the program level, rather than postulating facts about a
      particular runtime environment. *)
  Definition canonical_external_declaration_at
      (ge : Genv.t Clight.fundef type) (id : ident)
      (name : string) (fd : fundef) : Prop :=
    exists b,
      Genv.find_symbol ge id = Some b /\
      Genv.find_funct_ptr ge b = Some fd /\
      ClightLang.invert_block_from_string ge name = Some b.

  Definition client_atomic_declarations
      (ids : wrapper_ids) (cu : ClightLang.clight_comp_unit) : Prop :=
    ClightLang.norep_ef_name (client_canonical_ge cu) /\
    (forall b gd,
      (Genv.genv_defs (client_canonical_ge cu)) ! b = Some gd ->
      exists id, (Genv.genv_symb (client_canonical_ge cu)) ! id = Some b) /\
    canonical_external_declaration_at (client_canonical_ge cu)
      (atomic_load_id ids) "atomic_load" client_atomic_load_external /\
    canonical_external_declaration_at (client_canonical_ge cu)
      (atomic_store_id ids) "atomic_store" client_atomic_store_external /\
    canonical_external_declaration_at (client_canonical_ge cu)
      (atomic_CAS_id ids) "atomic_CAS" client_atomic_CAS_external.

  Definition client_atomic_runtime_lookups
      (ids : wrapper_ids) (ge : Clight.genv) : Prop :=
    exists load_block store_block cas_block,
      Genv.find_symbol ge (atomic_load_id ids) = Some load_block /\
      Genv.find_funct_ptr ge load_block =
        Some client_atomic_load_external /\
      Genv.find_symbol ge (atomic_store_id ids) = Some store_block /\
      Genv.find_funct_ptr ge store_block =
        Some client_atomic_store_external /\
      Genv.find_symbol ge (atomic_CAS_id ids) = Some cas_block /\
      Genv.find_funct_ptr ge cas_block =
        Some client_atomic_CAS_external.

  (** Initialization transports the exact declarations, including their
      signatures and Clight argument/result types, into the runtime client
      environment.  This complements name resolution: it is the fact needed
      to identify a decoded source call with the canonical target call
      state. *)
  Theorem initialized_client_atomic_function_lookups
      ids cu (raw_ge : Genv.t Clight.fundef type) (client_ge : Clight.genv)
      (Hdecls : client_atomic_declarations ids cu)
      (Hinit : InteractionSemantics.init_genv ClightLang.Clight_IS_2
        cu raw_ge client_ge) :
    client_atomic_runtime_lookups ids client_ge.
  Proof.
    change (ClightLang.init_genv cu raw_ge client_ge) in Hinit.
    unfold ClightLang.init_genv in Hinit.
    destruct Hinit as [Hge Hrelated]. subst client_ge.
    change (ge_related raw_ge (client_canonical_ge cu)) in Hrelated.
    unfold client_atomic_declarations,
      canonical_external_declaration_at in Hdecls.
    destruct Hdecls as
      (Hnorep & Hall_symbols &
       (load_block & Hload_symbol & Hload_fundef & Hload_name) &
       (store_block & Hstore_symbol & Hstore_fundef & Hstore_name) &
       (cas_block & Hcas_symbol & Hcas_fundef & Hcas_name)).
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (client_canonical_ge cu) (atomic_load_id ids) load_block
      client_atomic_load_external Hrelated Hload_symbol Hload_fundef)
      as (load_block' & Hload_symbol' & Hload_fundef').
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (client_canonical_ge cu) (atomic_store_id ids) store_block
      client_atomic_store_external Hrelated Hstore_symbol Hstore_fundef)
      as (store_block' & Hstore_symbol' & Hstore_fundef').
    destruct (ge_related_find_symbol_funct_ptr raw_ge
      (client_canonical_ge cu) (atomic_CAS_id ids) cas_block
      client_atomic_CAS_external Hrelated Hcas_symbol Hcas_fundef)
      as (cas_block' & Hcas_symbol' & Hcas_fundef').
    exists load_block', store_block', cas_block'.
    repeat split; assumption.
  Qed.

  Theorem initialized_client_atomic_resolution
      ids cu (raw_ge : Genv.t Clight.fundef type) (client_ge : Clight.genv)
      (Hdecls : client_atomic_declarations ids cu)
      (Hinit : InteractionSemantics.init_genv ClightLang.Clight_IS_2
        cu raw_ge client_ge) :
    ClightLang.invert_symbol_from_string client_ge "atomic_load" =
      Some (atomic_load_id ids) /\
    ClightLang.invert_symbol_from_string client_ge "atomic_store" =
      Some (atomic_store_id ids) /\
    ClightLang.invert_symbol_from_string client_ge "atomic_CAS" =
      Some (atomic_CAS_id ids).
  Proof.
    change (ClightLang.init_genv cu raw_ge client_ge) in Hinit.
    unfold ClightLang.init_genv in Hinit.
    destruct Hinit as [Hge Hrelated]. subst client_ge.
    change (ge_related raw_ge (client_canonical_ge cu)) in Hrelated.
    change
      (ClightLang.invert_symbol_from_string raw_ge "atomic_load" =
         Some (atomic_load_id ids) /\
       ClightLang.invert_symbol_from_string raw_ge "atomic_store" =
         Some (atomic_store_id ids) /\
       ClightLang.invert_symbol_from_string raw_ge "atomic_CAS" =
         Some (atomic_CAS_id ids)).
    unfold client_atomic_declarations,
      canonical_external_declaration_at in Hdecls.
    destruct Hdecls as
      (Hnorep & Hall_symbols &
       (load_block & Hload_symbol & Hload_fundef & Hload_name) &
       (store_block & Hstore_symbol & Hstore_fundef & Hstore_name) &
       (cas_block & Hcas_symbol & Hcas_fundef & Hcas_name)).
    split.
    - eapply ge_related_invert_external_symbol;
        [exact Hnorep | exact Hall_symbols | exact Hrelated |
         exact Hload_name | exact Hload_symbol].
    - split.
      + eapply ge_related_invert_external_symbol;
          [exact Hnorep | exact Hall_symbols | exact Hrelated |
           exact Hstore_name | exact Hstore_symbol].
      + eapply ge_related_invert_external_symbol;
          [exact Hnorep | exact Hall_symbols | exact Hrelated |
           exact Hcas_name | exact Hcas_symbol].
  Qed.

End ClightAtomicClientInit.
