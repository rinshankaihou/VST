(** Concrete Clight implementations of the three atomic-machine primitives.

    The source atomic machine treats calls named [atomic_load],
    [atomic_store], and [atomic_CAS] specially.  On the target side these
    functions can instead be supplied by a small Clight compilation unit.
    Their only ordinary memory accesses are [Mint32] accesses, and those
    accesses occur between calls to the reserved [ent_atom] and [ext_atom]
    primitives.

    The wrapper identifiers are parameters because they must agree with the
    identifiers used by the client compilation units.  The marker identifiers
    themselves are fixed by [GAST]. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import compcert.common.Errors.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Clight.

Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.common.FMemory.
Require Import compcert.concurrency.comp_correct.cfrontend.FCop.
Require Import compcert.concurrency.comp_correct.ClightLang.
Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_specs.

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
Import ListNotations.

Local Open Scope string_scope.

Module ClightAtomicWrappers.

  (** Global identifiers exported by the wrapper module. *)
  Record wrapper_ids : Type := {
    atomic_load_id : ident;
    atomic_store_id : ident;
    atomic_CAS_id : ident
  }.

  Definition wrapper_ids_wf (ids : wrapper_ids) : Prop :=
    let load_id := atomic_load_id ids in
    let store_id := atomic_store_id ids in
    let cas_id := atomic_CAS_id ids in
    load_id <> store_id /\
    load_id <> cas_id /\
    store_id <> cas_id /\
    load_id <> GAST.print /\
    load_id <> GAST.ent_atom /\
    load_id <> GAST.ext_atom /\
    store_id <> GAST.print /\
    store_id <> GAST.ent_atom /\
    store_id <> GAST.ext_atom /\
    cas_id <> GAST.print /\
    cas_id <> GAST.ent_atom /\
    cas_id <> GAST.ext_atom.

  (** Function-local identifiers.  Parameters are represented by temporary
      variables by [ClightLang.function_entry2], the entry convention used by
      [Clight_IS_2]. *)
  Definition target_temp : ident := 10%positive.
  Definition expected_temp : ident := 11%positive.
  Definition new_temp : ident := 12%positive.
  Definition old_temp : ident := 13%positive.
  Definition result_temp : ident := 14%positive.

  Definition tint : type := ClightAtomicSpecs.tint.
  Definition tvoid : type := ClightAtomicSpecs.tvoid.
  Definition atomic_pointer_type : type :=
    ClightAtomicSpecs.atomic_pointer_type.

  Definition atomic_load_signature : signature :=
    ClightAtomicSpecs.atomic_load_signature.

  Definition atomic_store_signature : signature :=
    ClightAtomicSpecs.atomic_store_signature.

  Definition atomic_CAS_signature : signature :=
    ClightAtomicSpecs.atomic_CAS_signature.

  (** Canonical client declarations for the three wrapper entry points.  Keep
      these declarations next to their signatures so every client/global
      proof refers to the same [fundef] constants. *)
  Definition client_atomic_load_external : fundef :=
    ClightAtomicSpecs.client_atomic_load_external.

  Definition client_atomic_store_external : fundef :=
    ClightAtomicSpecs.client_atomic_store_external.

  Definition client_atomic_CAS_external : fundef :=
    ClightAtomicSpecs.client_atomic_CAS_external.

  Definition marker_type : type :=
    Tfunction [] tvoid cc_default.

  Definition marker_call (id : ident) : statement :=
    Scall None (Evar id marker_type) [].

  Definition enter_atomic : statement := marker_call GAST.ent_atom.
  Definition exit_atomic : statement := marker_call GAST.ext_atom.

  Definition target_expr : expr :=
    Etempvar target_temp atomic_pointer_type.

  Definition target_lvalue : expr :=
    Ederef target_expr tint.

  Definition old_expr : expr := Etempvar old_temp tint.
  Definition expected_expr : expr := Etempvar expected_temp tint.
  Definition new_expr : expr := Etempvar new_temp tint.
  Definition result_expr : expr := Etempvar result_temp tint.

  Definition load_entry_temps (p : val) : temp_env :=
    PTree.set target_temp p
      (create_undef_temps [(old_temp, tint)]).

  Definition store_entry_temps (p v : val) : temp_env :=
    PTree.set new_temp v
      (PTree.set target_temp p (create_undef_temps [])).

  Definition CAS_entry_temps (p expected new : val) : temp_env :=
    PTree.set new_temp new
      (PTree.set expected_temp expected
        (PTree.set target_temp p
          (create_undef_temps [(old_temp, tint); (result_temp, tint)]))).

  (** [int atomic_load(int *target)]

      [old = *target] is a [Mint32] read by definition of [access_mode tint]. *)
  Definition atomic_load_function : function := {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := [(target_temp, atomic_pointer_type)];
    fn_vars := [];
    fn_temps := [(old_temp, tint)];
    fn_body :=
      Ssequence enter_atomic
        (Ssequence (Sset old_temp target_lvalue)
          (Ssequence exit_atomic
            (Sreturn (Some old_expr))))
  |}.

  (** Target implementation of

        [void atomic_store(int *target, int new_value)].

      The implementation itself returns a defined dummy integer.  This is
      necessary because [ClightLang.halted] rejects [Vundef], which is what a
      Clight [void] return produces.  The client-facing signature remains
      [atomic_store_signature] (result [Xvoid]); consequently
      [GlobSemantics.Return] discards this dummy value through [res_sg] before
      resuming the client. *)
  Definition atomic_store_function : function := {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params :=
      [(target_temp, atomic_pointer_type); (new_temp, tint)];
    fn_vars := [];
    fn_temps := [];
    fn_body :=
      Ssequence enter_atomic
        (Ssequence (Sassign target_lvalue new_expr)
          (Ssequence exit_atomic
            (Sreturn (Some (Econst_int Int.zero tint)))))
  |}.

  (** [int atomic_CAS(int *target, int expected, int new_value)]

      This operation returns [1] on success and [0] on failure, matching the
      [Vtrue]/[Vfalse] supplied to the continuation by [SC_Cas_Suc] and
      [SC_Cas_Fail] in [atomic_machine.v].  The read, comparison, conditional
      write, and construction of the result all occur while the target atomic
      bit is [I]. *)
  Definition atomic_CAS_function : function := {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params :=
      [(target_temp, atomic_pointer_type);
       (expected_temp, tint);
       (new_temp, tint)];
    fn_vars := [];
    fn_temps := [(old_temp, tint); (result_temp, tint)];
    fn_body :=
      Ssequence enter_atomic
        (Ssequence (Sset old_temp target_lvalue)
          (Ssequence
            (Sifthenelse
              (Ebinop Oeq old_expr expected_expr tint)
              (Ssequence
                (Sassign target_lvalue new_expr)
                (Sset result_temp (Econst_int Int.one tint)))
              (Sset result_temp (Econst_int Int.zero tint)))
            (Ssequence exit_atomic
              (Sreturn (Some result_expr)))))
  |}.

  (** Inline-builtin declarations for the two primitive markers.  The
      marker-enabled target language recognizes these exact name/signature
      pairs without relying on [invert_symbol_from_string], which only scans
      [EF_external] definitions. *)
  Definition ent_atom_external : fundef :=
    External (EF_builtin "ent_atom" GAST.ent_atom_sg)
      [] tvoid cc_default.

  Definition ext_atom_external : fundef :=
    External (EF_builtin "ext_atom" GAST.ext_atom_sg)
      [] tvoid cc_default.

  Definition wrapper_definitions (ids : wrapper_ids) :
      list (ident * globdef fundef type) :=
    [(GAST.ent_atom, Gfun ent_atom_external);
     (GAST.ext_atom, Gfun ext_atom_external);
     (atomic_load_id ids, Gfun (Internal atomic_load_function));
     (atomic_store_id ids, Gfun (Internal atomic_store_function));
     (atomic_CAS_id ids, Gfun (Internal atomic_CAS_function))].

  Definition wrapper_public (ids : wrapper_ids) : list ident :=
    [atomic_load_id ids; atomic_store_id ids; atomic_CAS_id ids].

  (** An empty composite environment suffices: the wrappers operate on raw
      [int *] values and contain no structs or unions. *)
  Program Definition wrapper_comp_unit (ids : wrapper_ids) :
      ClightLang.clight_comp_unit := {|
    ClightLang.cu_defs := wrapper_definitions ids;
    ClightLang.cu_public := wrapper_public ids;
    ClightLang.cu_types := [];
    ClightLang.cu_comp_env := PTree.empty _
  |}.

  (** All three exported wrapper operations are internal functions.  The
      distinctness part of [wrapper_ids_wf] is needed because
      [ClightLang.is_internal] returns the kind of the first definition with
      a matching identifier. *)
  Lemma wrapper_internal_functions ids :
    wrapper_ids_wf ids ->
    ClightLang.internal_fn (wrapper_comp_unit ids) = wrapper_public ids.
  Proof.
    destruct ids as [load_id store_id cas_id].
    unfold wrapper_ids_wf; cbn zeta.
    intros (Hload_store & Hload_cas & Hstore_cas & Hload_print &
      Hload_ent & Hload_ext & Hstore_print & Hstore_ent & Hstore_ext &
      Hcas_print & Hcas_ent & Hcas_ext).
    unfold ClightLang.internal_fn, wrapper_comp_unit, wrapper_public.
    cbn [ClightLang.cu_defs ClightLang.cu_public atomic_load_id
      atomic_store_id atomic_CAS_id wrapper_definitions
      ent_atom_external ext_atom_external ClightLang.is_internal] in *.
    simpl.
    repeat match goal with
      | |- context [ident_eq ?x ?y] =>
          destruct (ident_eq x y); [subst |]; try contradiction; try congruence
      end.
  Qed.

  Corollary wrapper_atomic_load_internal ids :
    wrapper_ids_wf ids ->
    In (atomic_load_id ids)
      (ClightLang.internal_fn (wrapper_comp_unit ids)).
  Proof.
    intros Hwf. rewrite wrapper_internal_functions by exact Hwf.
    destruct ids; simpl; auto.
  Qed.

  Corollary wrapper_atomic_store_internal ids :
    wrapper_ids_wf ids ->
    In (atomic_store_id ids)
      (ClightLang.internal_fn (wrapper_comp_unit ids)).
  Proof.
    intros Hwf. rewrite wrapper_internal_functions by exact Hwf.
    destruct ids; simpl; auto.
  Qed.

  Corollary wrapper_atomic_CAS_internal ids :
    wrapper_ids_wf ids ->
    In (atomic_CAS_id ids)
      (ClightLang.internal_fn (wrapper_comp_unit ids)).
  Proof.
    intros Hwf. rewrite wrapper_internal_functions by exact Hwf.
    destruct ids; simpl; auto.
  Qed.

  Lemma access_mode_wrapper_value :
    access_mode (typeof target_lvalue) = By_value Mint32.
  Proof. reflexivity. Qed.

  Lemma atomic_load_result_type :
    type_of_function atomic_load_function =
      Tfunction [atomic_pointer_type] tint cc_default.
  Proof. reflexivity. Qed.

  Lemma atomic_store_result_type :
    type_of_function atomic_store_function =
      Tfunction [atomic_pointer_type; tint]
        tint cc_default.
  Proof. reflexivity. Qed.

  Lemma atomic_CAS_result_type :
    type_of_function atomic_CAS_function =
      Tfunction
        [atomic_pointer_type; tint; tint]
        tint cc_default.
  Proof. reflexivity. Qed.

  Lemma marker_external_signatures :
    type_of_fundef ent_atom_external = marker_type /\
    type_of_fundef ext_atom_external = marker_type.
  Proof. split; reflexivity. Qed.

  Lemma atomic_CAS_success_result :
    Vint Int.one = Vtrue.
  Proof. reflexivity. Qed.

  Lemma atomic_CAS_failure_result :
    Vint Int.zero = Vfalse.
  Proof. reflexivity. Qed.

  Lemma wrapper_ent_atom_builtin_is_exposed (ge : Clight.genv) k :
    InteractionSemantics.at_external Clight_IS_2_with_markers ge
      (ClightLang.Core_Callstate ent_atom_external [] k) =
      Some (GAST.ent_atom, GAST.ent_atom_sg, []).
  Proof.
    apply clight_is2_markers_exposes_builtin. reflexivity.
  Qed.

  Lemma wrapper_ext_atom_builtin_is_exposed (ge : Clight.genv) k :
    InteractionSemantics.at_external Clight_IS_2_with_markers ge
      (ClightLang.Core_Callstate ext_atom_external [] k) =
      Some (GAST.ext_atom, GAST.ext_atom_sg, []).
  Proof.
    apply clight_is2_markers_exposes_builtin. reflexivity.
  Qed.

  Lemma wrapper_after_ent_atom k :
    InteractionSemantics.after_external Clight_IS_2_with_markers
      (ClightLang.Core_Callstate ent_atom_external [] k) None =
      Some (ClightLang.Core_Returnstate Vundef k).
  Proof.
    apply clight_is2_markers_after_builtin with (fnid := GAST.ent_atom).
    reflexivity.
  Qed.

  Lemma wrapper_after_ext_atom k :
    InteractionSemantics.after_external Clight_IS_2_with_markers
      (ClightLang.Core_Callstate ext_atom_external [] k) None =
      Some (ClightLang.Core_Returnstate Vundef k).
  Proof.
    apply clight_is2_markers_after_builtin with (fnid := GAST.ext_atom).
    reflexivity.
  Qed.

  Lemma wrapper_bodies_have_atomic_shape :
    fn_body atomic_load_function =
      Ssequence enter_atomic
        (Ssequence (Sset old_temp target_lvalue)
          (Ssequence exit_atomic (Sreturn (Some old_expr)))) /\
    fn_body atomic_store_function =
      Ssequence enter_atomic
        (Ssequence (Sassign target_lvalue new_expr)
          (Ssequence exit_atomic
            (Sreturn (Some (Econst_int Int.zero tint))))) /\
    fn_body atomic_CAS_function =
      Ssequence enter_atomic
        (Ssequence (Sset old_temp target_lvalue)
          (Ssequence
            (Sifthenelse (Ebinop Oeq old_expr expected_expr tint)
              (Ssequence
                (Sassign target_lvalue new_expr)
                (Sset result_temp (Econst_int Int.one tint)))
              (Sset result_temp (Econst_int Int.zero tint)))
            (Ssequence exit_atomic (Sreturn (Some result_expr))))).
  Proof. repeat split; reflexivity. Qed.

  Lemma load_params_norepet :
    list_norepet [target_temp].
  Proof.
    constructor; [simpl; tauto | constructor].
  Qed.

  Lemma store_params_norepet :
    list_norepet [target_temp; new_temp].
  Proof.
    constructor.
    - intro Hin. simpl in Hin. destruct Hin as [Heq | Hnil].
      + discriminate.
      + contradiction.
    - constructor; [simpl; tauto | constructor].
  Qed.

  Lemma CAS_params_norepet :
    list_norepet [target_temp; expected_temp; new_temp].
  Proof.
    constructor.
    - intro Hin. simpl in Hin.
      destruct Hin as [Heq | [Heq | Hnil]];
        [discriminate | discriminate | contradiction].
    - constructor.
      + intro Hin. simpl in Hin. destruct Hin as [Heq | Hnil].
        * discriminate.
        * contradiction.
      + constructor; [simpl; tauto | constructor].
  Qed.

  Lemma load_params_temps_disjoint :
    list_disjoint [target_temp] [old_temp].
  Proof.
    intros x y Hx Hy.
    simpl in Hx, Hy.
    destruct Hx as [Hx | Hx]; [subst x | contradiction].
    destruct Hy as [Hy | Hy]; [subst y | contradiction].
    discriminate.
  Qed.

  Lemma store_params_temps_disjoint :
    list_disjoint [target_temp; new_temp] [].
  Proof.
    intros x y _ Hy. simpl in Hy. contradiction.
  Qed.

  Lemma CAS_params_temps_disjoint :
    list_disjoint [target_temp; expected_temp; new_temp]
      [old_temp; result_temp].
  Proof.
    intros x y Hx Hy.
    simpl in Hx, Hy.
    destruct Hx as [Hx | [Hx | [Hx | Hx]]];
      try subst x; try contradiction;
      destruct Hy as [Hy | [Hy | Hy]];
      try subst y; try contradiction;
      discriminate.
  Qed.

  (** Since the wrappers have no addressable locals, entering them under the
      [function_entry2] convention allocates no memory. *)
  Lemma atomic_load_function_entry ge p m :
    ClightLang.function_entry2 ge atomic_load_function [p] m
      empty_env (load_entry_temps p) m.
  Proof.
    econstructor; simpl.
    - constructor.
    - apply load_params_norepet.
    - apply load_params_temps_disjoint.
    - constructor.
    - reflexivity.
  Qed.

  Lemma atomic_store_function_entry ge p v m :
    ClightLang.function_entry2 ge atomic_store_function [p; v] m
      empty_env (store_entry_temps p v) m.
  Proof.
    econstructor; simpl.
    - constructor.
    - apply store_params_norepet.
    - apply store_params_temps_disjoint.
    - constructor.
    - reflexivity.
  Qed.

  Lemma atomic_CAS_function_entry ge p expected new m :
    ClightLang.function_entry2 ge atomic_CAS_function [p; expected; new] m
      empty_env (CAS_entry_temps p expected new) m.
  Proof.
    econstructor; simpl.
    - constructor.
    - apply CAS_params_norepet.
    - apply CAS_params_temps_disjoint.
    - constructor.
    - reflexivity.
  Qed.

  Lemma init_atomic_load_core
      (ge : Genv.t Clight.fundef type) ids b p ofs :
    @Genv.find_symbol Clight.fundef type ge (atomic_load_id ids) = Some b ->
    @Genv.find_funct_ptr Clight.fundef type ge b =
      Some (Internal atomic_load_function) ->
    ClightLang.init_core ge (atomic_load_id ids) [Vptr p ofs] =
      Some (ClightLang.Core_Callstate
        (Internal atomic_load_function) [Vptr p ofs] Kstop).
  Proof.
    destruct ids as [load_id store_id CAS_id].
    cbn [atomic_load_id].
    intros Hsymbol Hfun.
    unfold ClightLang.init_core.
    rewrite Hsymbol, Hfun. reflexivity.
  Qed.

  Lemma init_atomic_store_core
      (ge : Genv.t Clight.fundef type) ids b p ofs n :
    @Genv.find_symbol Clight.fundef type ge (atomic_store_id ids) = Some b ->
    @Genv.find_funct_ptr Clight.fundef type ge b =
      Some (Internal atomic_store_function) ->
    ClightLang.init_core ge (atomic_store_id ids) [Vptr p ofs; Vint n] =
      Some (ClightLang.Core_Callstate
        (Internal atomic_store_function) [Vptr p ofs; Vint n] Kstop).
  Proof.
    destruct ids as [load_id store_id CAS_id]; simpl.
    intros Hsymbol Hfun.
    unfold ClightLang.init_core. rewrite Hsymbol, Hfun.
    unfold type_of_fundef. rewrite atomic_store_result_type.
    cbn [atomic_pointer_type tint
      ClightAtomicSpecs.atomic_pointer_type ClightAtomicSpecs.tint
      clight_val_casted.val_casted_list_func
      clight_val_casted.val_casted_func
      clight_val_casted.tys_nonvoid
      clight_val_casted.vals_defined Cop.cast_int_int].
    destruct (Int.eq_dec n n) as [_ | Hneq].
    - vm_compute. reflexivity.
    - contradiction Hneq. reflexivity.
  Qed.

  Lemma init_atomic_CAS_core
      (ge : Genv.t Clight.fundef type) ids b p ofs expected new :
    @Genv.find_symbol Clight.fundef type ge (atomic_CAS_id ids) = Some b ->
    @Genv.find_funct_ptr Clight.fundef type ge b =
      Some (Internal atomic_CAS_function) ->
    ClightLang.init_core ge (atomic_CAS_id ids)
      [Vptr p ofs; Vint expected; Vint new] =
      Some (ClightLang.Core_Callstate (Internal atomic_CAS_function)
        [Vptr p ofs; Vint expected; Vint new] Kstop).
  Proof.
    destruct ids as [load_id store_id CAS_id]; simpl.
    intros Hsymbol Hfun.
    unfold ClightLang.init_core. rewrite Hsymbol, Hfun.
    unfold type_of_fundef. rewrite atomic_CAS_result_type.
    cbn [atomic_pointer_type tint
      ClightAtomicSpecs.atomic_pointer_type ClightAtomicSpecs.tint
      clight_val_casted.val_casted_list_func
      clight_val_casted.val_casted_func
      clight_val_casted.tys_nonvoid
      clight_val_casted.vals_defined Cop.cast_int_int].
    destruct (Int.eq_dec expected expected) as [_ | Hexpected];
      [|contradiction Hexpected; reflexivity].
    destruct (Int.eq_dec new new) as [_ | Hnew].
    - vm_compute. reflexivity.
    - contradiction Hnew. reflexivity.
  Qed.

  Lemma eval_target_lvalue ge e le m b ofs :
    le ! target_temp = Some (Vptr b ofs) ->
    ClightLang.eval_lvalue ge e le m target_lvalue b ofs.
  Proof.
    intros Htarget.
    unfold target_lvalue, target_expr.
    econstructor. econstructor. exact Htarget.
  Qed.

  Lemma eval_target_load ge e le m b ofs v :
    le ! target_temp = Some (Vptr b ofs) ->
    FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v ->
    ClightLang.eval_expr ge e le m target_lvalue v.
  Proof.
    intros Htarget Hload.
    econstructor.
    - eapply eval_target_lvalue; eauto.
    - econstructor; [reflexivity | exact Hload].
  Qed.

  Lemma assign_target_store ge m b ofs v m' :
    FMemory.Mem.storev Mint32 m (Vptr b ofs) v = Some m' ->
    ClightLang.assign_loc ge (typeof target_lvalue) m b ofs v m'.
  Proof.
    intros Hstore.
    econstructor; [reflexivity | exact Hstore].
  Qed.

  Lemma eval_CAS_comparison (ge : Clight.genv) e le m old expected result :
    le ! old_temp = Some old ->
    le ! expected_temp = Some expected ->
    FCop.sem_binary_operation ge.(Clight.genv_cenv)
      Oeq old tint expected tint m = Some result ->
    ClightLang.eval_expr ge e le m
      (Ebinop Oeq old_expr expected_expr tint) result.
  Proof.
    intros Hold Hexpected Hcmp.
    econstructor.
    - econstructor. exact Hold.
    - econstructor. exact Hexpected.
    - exact Hcmp.
  Qed.

End ClightAtomicWrappers.
