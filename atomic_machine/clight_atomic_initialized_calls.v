(** Atomic wrapper calls after initialization of the wrapper compilation unit.

    The corollaries below hide all target-wrapper lookup details.  Their one
    environment premise is the [init_genv] fact produced when the appended
    wrapper unit is initialized; [initialized_wrapper_environment] derives
    the marker and wrapper-entry symbol/function facts consumed by the
    concrete call/body/return theorems. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.

From mathcomp.boot Require Import fintype.

Require Import compcert.concurrency.common.ETrace.
Require Import compcert.concurrency.common.FMemory.
Require Import compcert.concurrency.common.GlobDefs.
Require Import compcert.concurrency.common.GlobSemantics.
Require Import compcert.concurrency.common.InteractionSemantics.
Require Import compcert.concurrency.comp_correct.ClightLang.

Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.
Require Import atomic_machine.clight_atomic_global_calls.
Require Import atomic_machine.clight_atomic_wrapper_init.

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
Import ListNotations.
Local Open Scope string_scope.

Module ClightAtomicInitializedCalls.

  Import ClightAtomicWrappers.
  Module Calls := ClightAtomicGlobalCalls.
  Module WrapperInit := ClightAtomicWrapperInit.

  Section InitializedRuntimeModules.

    Context {GE : GlobEnv.t}.
    Variables caller_ix wrapper_ix : 'I_(GlobEnv.M GE).
    Variables caller_raw_ge wrapper_raw_ge :
      Genv.t Clight.fundef Ctypes.type.
    Variables caller_ge wrapper_ge : Clight.genv.
    Hypothesis Hcaller_module :
      GlobEnv.modules GE caller_ix =
        ModSem.Build_t ClightLang.Clight_IS_2 caller_raw_ge caller_ge.
    Hypothesis Hwrapper_module :
      GlobEnv.modules GE wrapper_ix =
        ModSem.Build_t Clight_IS_2_with_markers wrapper_raw_ge wrapper_ge.

    Variable ids : wrapper_ids.
    Hypothesis Hids : wrapper_ids_wf ids.
    Hypothesis Hwrapper_init :
      InteractionSemantics.init_genv Clight_IS_2_with_markers
        (wrapper_comp_unit ids) wrapper_raw_ge wrapper_ge.

    Local Definition caller_core : ClightLang.core ->
        InteractionSemantics.core
          (ModSem.lang (GlobEnv.modules GE caller_ix)) :=
      Calls.runtime_core caller_ix ClightLang.Clight_IS_2
        caller_raw_ge caller_ge Hcaller_module.

    Corollary initialized_atomic_load_global_call_and_return
        (Hget_mod : GlobEnv.get_mod GE (atomic_load_id ids) = Some wrapper_ix)
        (Hcaller_resolve :
          ClightLang.invert_symbol_from_string caller_ge "atomic_load" =
            Some (atomic_load_id ids))
        (gm : GMemory.gmem) (m : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (v : val)
        (Hload :
          FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
        (Hdefined : clight_val_casted.vals_defined [v] = true)
        (tp : @ThreadPool.t GE) t caller_F caller_sg cs k
        (Hembed : FMemory.embed gm
          (FLists.get_fl (GlobEnv.freelists GE)
            (FLists.get_tfid (GlobEnv.freelists GE) t
              (ThreadPool.next_fmap tp t))) m)
        (Hcs : ThreadPool.get_cs tp t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Callstate client_atomic_load_external
                  [Vptr b ofs] k)) caller_sg caller_F :: cs)) :
      exists tp' fp,
        ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm O) fp
          (Build_ProgConfig GE tp' t gm O) /\
        ThreadPool.get_cs tp' t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Returnstate v k))
              caller_sg caller_F :: cs).
    Proof.
      destruct (WrapperInit.initialized_wrapper_environment
        ids Hids wrapper_raw_ge wrapper_ge Hwrapper_init) as
        (ent_block & ext_block & load_block & _ & _ &
         Hent_symbol & Hent_fun & Hext_symbol & Hext_fun &
         Hload_symbol & Hload_fun & _ & _ & _ & _).
      eapply Calls.atomic_load_global_call_and_return; eauto.
    Qed.

    Corollary initialized_atomic_store_global_call_and_return
        (Hget_mod : GlobEnv.get_mod GE (atomic_store_id ids) = Some wrapper_ix)
        (Hcaller_resolve :
          ClightLang.invert_symbol_from_string caller_ge "atomic_store" =
            Some (atomic_store_id ids))
        (gm gm' : GMemory.gmem) (m m' : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (n : int)
        (Hstore :
          FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint n) = Some m')
        (tp : @ThreadPool.t GE) t caller_F caller_sg cs k
        (Hembed : FMemory.embed gm
          (FLists.get_fl (GlobEnv.freelists GE)
            (FLists.get_tfid (GlobEnv.freelists GE) t
              (ThreadPool.next_fmap tp t))) m)
        (Hembed' : FMemory.embed gm'
          (FLists.get_fl (GlobEnv.freelists GE)
            (FLists.get_tfid (GlobEnv.freelists GE) t
              (ThreadPool.next_fmap tp t))) m')
        (Hcs : ThreadPool.get_cs tp t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Callstate client_atomic_store_external
                  [Vptr b ofs; Vint n] k)) caller_sg caller_F :: cs)) :
      exists tp' fp,
        ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm O) fp
          (Build_ProgConfig GE tp' t gm' O) /\
        ThreadPool.get_cs tp' t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Returnstate Vundef k))
              caller_sg caller_F :: cs).
    Proof.
      destruct (WrapperInit.initialized_wrapper_environment
        ids Hids wrapper_raw_ge wrapper_ge Hwrapper_init) as
        (ent_block & ext_block & _ & store_block & _ &
         Hent_symbol & Hent_fun & Hext_symbol & Hext_fun &
         _ & _ & Hstore_symbol & Hstore_fun & _ & _).
      eapply Calls.atomic_store_global_call_and_return; eauto.
    Qed.

    Corollary initialized_atomic_CAS_success_global_call_and_return
        (Hget_mod : GlobEnv.get_mod GE (atomic_CAS_id ids) = Some wrapper_ix)
        (Hcaller_resolve :
          ClightLang.invert_symbol_from_string caller_ge "atomic_CAS" =
            Some (atomic_CAS_id ids))
        (gm : GMemory.gmem) (m m' : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (expected new : int)
        (Hload :
          FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint expected))
        (Hstore :
          FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint new) = Some m')
        (tp : @ThreadPool.t GE) t caller_F caller_sg cs k
        (Hembed : FMemory.embed gm
          (FLists.get_fl (GlobEnv.freelists GE)
            (FLists.get_tfid (GlobEnv.freelists GE) t
              (ThreadPool.next_fmap tp t))) m)
        (Hcs : ThreadPool.get_cs tp t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Callstate client_atomic_CAS_external
                  [Vptr b ofs; Vint expected; Vint new] k))
              caller_sg caller_F :: cs)) :
      exists tp' fp,
        ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm O) fp
          (Build_ProgConfig GE tp' t (FMemory.strip m') O) /\
        ThreadPool.get_cs tp' t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Returnstate Vtrue k))
              caller_sg caller_F :: cs).
    Proof.
      destruct (WrapperInit.initialized_wrapper_environment
        ids Hids wrapper_raw_ge wrapper_ge Hwrapper_init) as
        (ent_block & ext_block & _ & _ & cas_block &
         Hent_symbol & Hent_fun & Hext_symbol & Hext_fun &
         _ & _ & _ & _ & HCAS_symbol & HCAS_fun).
      eapply Calls.atomic_CAS_success_global_call_and_return; eauto.
    Qed.

    Corollary initialized_atomic_CAS_failure_global_call_and_return
        (Hget_mod : GlobEnv.get_mod GE (atomic_CAS_id ids) = Some wrapper_ix)
        (Hcaller_resolve :
          ClightLang.invert_symbol_from_string caller_ge "atomic_CAS" =
            Some (atomic_CAS_id ids))
        (gm : GMemory.gmem) (m : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (old expected new : int)
        (Hneq : old <> expected)
        (Hload :
          FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint old))
        (tp : @ThreadPool.t GE) t caller_F caller_sg cs k
        (Hembed : FMemory.embed gm
          (FLists.get_fl (GlobEnv.freelists GE)
            (FLists.get_tfid (GlobEnv.freelists GE) t
              (ThreadPool.next_fmap tp t))) m)
        (Hcs : ThreadPool.get_cs tp t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Callstate client_atomic_CAS_external
                  [Vptr b ofs; Vint expected; Vint new] k))
              caller_sg caller_F :: cs)) :
      exists tp' fp,
        ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm O) fp
          (Build_ProgConfig GE tp' t gm O) /\
        ThreadPool.get_cs tp' t =
          Some
            (Core.Build_t caller_ix
              (caller_core
                (ClightLang.Core_Returnstate Vfalse k))
              caller_sg caller_F :: cs).
    Proof.
      destruct (WrapperInit.initialized_wrapper_environment
        ids Hids wrapper_raw_ge wrapper_ge Hwrapper_init) as
        (ent_block & ext_block & _ & _ & cas_block &
         Hent_symbol & Hent_fun & Hext_symbol & Hext_fun &
         _ & _ & _ & _ & HCAS_symbol & HCAS_fun).
      eapply Calls.atomic_CAS_failure_global_call_and_return; eauto.
    Qed.

  End InitializedRuntimeModules.

End ClightAtomicInitializedCalls.
