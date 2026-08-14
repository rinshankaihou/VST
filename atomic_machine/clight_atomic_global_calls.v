(** Concrete inter-module call/atomic-wrapper/return executions.

    [clight_atomic_global_clight] proves the body of each wrapper as a global
    atomic macro.  This file encloses those macros in the genuine
    [GlobSemantics.Call] and [GlobSemantics.Return] rules.  The caller keeps
    the unmodified [Clight_IS_2] language; only the callee module uses
    [Clight_IS_2_with_markers]. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.

From mathcomp.boot Require Import fintype.

Require Import compcert.concurrency.common.ETrace.
Require Import compcert.concurrency.common.FMemory.
Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.common.GlobDefs.
Require Import compcert.concurrency.common.GlobSemantics.
Require Import compcert.concurrency.common.InteractionSemantics.
Require Import compcert.concurrency.comp_correct.ClightLang.

Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.
Require Import atomic_machine.clight_atomic_wrapper_steps.
Require Import atomic_machine.clight_atomic_store_steps.
Require Import atomic_machine.clight_atomic_cas_steps.
Require Import atomic_machine.clight_atomic_global_steps.
Require Import atomic_machine.clight_atomic_global_clight.

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
Import ListNotations.
Local Open Scope string_scope.

Module ClightAtomicGlobalCalls.

  Import ClightAtomicWrappers.
  Import ClightAtomicStoreSteps.
  Import ClightAtomicCASSteps.
  Module Global := ClightAtomicGlobalSteps.
  Module ConcreteGlobal := ClightAtomicGlobalClight.

  Definition runtime_core
      {GE : GlobEnv.t} (ix : 'I_(GlobEnv.M GE))
      (L : Language) (raw_ge : Genv.t L.(F) L.(V)) (ge : L.(G))
      (Hmodule : GlobEnv.modules GE ix = ModSem.Build_t L raw_ge ge)
      (c : InteractionSemantics.core L) :
      InteractionSemantics.core
        (ModSem.lang (GlobEnv.modules GE ix)) :=
    ConcreteGlobal.transport_module_core Hmodule c.

  Lemma transport_module_init_core
      {md1 md2 : ModSem.t} (Hmd : md1 = md2) funid args
      (c : InteractionSemantics.core (ModSem.lang md2))
      (Hinit : InteractionSemantics.init_core
        (ModSem.lang md2) (ModSem.Ge md2) funid args = Some c) :
    InteractionSemantics.init_core
      (ModSem.lang md1) (ModSem.Ge md1) funid args =
      Some (ConcreteGlobal.transport_module_core Hmd c).
  Proof. destruct Hmd. exact Hinit. Qed.

  Lemma transport_module_halt
      {md1 md2 : ModSem.t} (Hmd : md1 = md2)
      (c : InteractionSemantics.core (ModSem.lang md2)) res
      (Hhalt : InteractionSemantics.halt (ModSem.lang md2) c = Some res) :
    InteractionSemantics.halt (ModSem.lang md1)
      (ConcreteGlobal.transport_module_core Hmd c) = Some res.
  Proof. destruct Hmd. exact Hhalt. Qed.

  Lemma original_clight_exposes_nonprimitive_external
      (ge : Clight.genv) name sig targs tres cc args k funid
      (Hdefined : clight_val_casted.vals_defined args = true)
      (Hresolve : ClightLang.invert_symbol_from_string ge name = Some funid)
      (Hnotprim : GAST.not_primitive funid) :
    InteractionSemantics.at_external ClightLang.Clight_IS_2 ge
      (ClightLang.Core_Callstate
        (External (EF_external name sig) targs tres cc) args k) =
      Some (funid, sig, args).
  Proof.
    unfold ClightLang.Clight_IS_2; cbn.
    rewrite Hdefined, Hresolve.
    apply GAST.not_primitive_cases in Hnotprim.
    destruct Hnotprim as (_ & Hent & Hext).
    destruct (peq funid GAST.ent_atom); [contradiction |].
    destruct (peq funid GAST.ext_atom); [contradiction |].
    reflexivity.
  Qed.

  Local Lemma not_primitive_intro funid :
    funid <> GAST.print ->
    funid <> GAST.ent_atom ->
    funid <> GAST.ext_atom ->
    GAST.not_primitive funid.
  Proof.
    intros Hprint Hent Hext.
    unfold GAST.not_primitive.
    destruct (peq funid GAST.print); [contradiction |].
    destruct (peq funid GAST.ent_atom); [contradiction |].
    destruct (peq funid GAST.ext_atom); [contradiction |].
    reflexivity.
  Qed.

  Lemma atomic_load_not_primitive ids :
    wrapper_ids_wf ids -> GAST.not_primitive (atomic_load_id ids).
  Proof.
    destruct ids as [load_id store_id cas_id].
    cbn [wrapper_ids_wf atomic_load_id].
    intros (_ & _ & _ & Hprint & Hent & Hext & _).
    apply not_primitive_intro; assumption.
  Qed.

  Lemma atomic_store_not_primitive ids :
    wrapper_ids_wf ids -> GAST.not_primitive (atomic_store_id ids).
  Proof.
    destruct ids as [load_id store_id cas_id].
    cbn [wrapper_ids_wf atomic_store_id].
    intros (_ & _ & _ & _ & _ & _ & Hprint & Hent & Hext & _).
    apply not_primitive_intro; assumption.
  Qed.

  Lemma atomic_CAS_not_primitive ids :
    wrapper_ids_wf ids -> GAST.not_primitive (atomic_CAS_id ids).
  Proof.
    destruct ids as [load_id store_id cas_id].
    cbn [wrapper_ids_wf atomic_CAS_id].
    intros (_ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hprint & Hent & Hext).
    apply not_primitive_intro; assumption.
  Qed.

  Section RuntimeModules.

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

    Local Definition caller_core : ClightLang.core ->
        InteractionSemantics.core
          (ModSem.lang (GlobEnv.modules GE caller_ix)) :=
      runtime_core caller_ix ClightLang.Clight_IS_2
        caller_raw_ge caller_ge Hcaller_module.

    Local Definition wrapper_core : ClightLang.core ->
        InteractionSemantics.core
          (ModSem.lang (GlobEnv.modules GE wrapper_ix)) :=
      runtime_core wrapper_ix Clight_IS_2_with_markers
        wrapper_raw_ge wrapper_ge Hwrapper_module.

    Variables ent_block ext_block : block.
    Hypothesis Hent_symbol :
      Genv.find_symbol wrapper_ge GAST.ent_atom = Some ent_block.
    Hypothesis Hent_fun :
      Genv.find_funct_ptr wrapper_ge ent_block = Some ent_atom_external.
    Hypothesis Hext_symbol :
      Genv.find_symbol wrapper_ge GAST.ext_atom = Some ext_block.
    Hypothesis Hext_fun :
      Genv.find_funct_ptr wrapper_ge ext_block = Some ext_atom_external.

    Theorem atomic_load_global_call_and_return
        ids (Hids : wrapper_ids_wf ids)
        (Hget_mod : GlobEnv.get_mod GE (atomic_load_id ids) = Some wrapper_ix)
        (load_block : block)
        (Hload_symbol :
          Genv.find_symbol wrapper_ge (atomic_load_id ids) = Some load_block)
        (Hload_fun :
          Genv.find_funct_ptr wrapper_ge load_block =
            Some (Internal atomic_load_function))
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
      pose proof (atomic_load_not_primitive ids Hids) as Hnot_primitive.
      set (wrapper_F := FLists.get_tfid (GlobEnv.freelists GE) t
        (ThreadPool.next_fmap tp t)).
      set (caller0 := caller_core
        (ClightLang.Core_Callstate client_atomic_load_external [Vptr b ofs] k)).
      set (caller1 := caller_core
        (ClightLang.Core_Returnstate v k)).
      set (wrapper0 := wrapper_core
        (ClightLang.Core_Callstate (Internal atomic_load_function)
          [Vptr b ofs] Kstop)).
      set (wrapper1 := wrapper_core
        (ClightLang.Core_Returnstate v Kstop)).
      set (tp_push := ThreadPool.Build_t
        (PMap.set t
          (Some
            (Core.Build_t wrapper_ix wrapper0 atomic_load_signature wrapper_F ::
             Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          (ThreadPool.content tp))
        (ThreadPool.next_tid tp)
        (fun i' =>
          if peq t i' then S (ThreadPool.next_fmap tp t)
          else ThreadPool.next_fmap tp i')).
      assert (Hpush : ThreadPool.push tp t wrapper_ix wrapper0
        atomic_load_signature = Some tp_push).
      { change (PMap.get t (ThreadPool.content tp) =
          Some
            (Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          in Hcs.
        unfold ThreadPool.push. rewrite Hcs. reflexivity. }
      eapply (@Global.call_wrapper_macro_and_return GE caller_ix wrapper_ix
        caller0 caller1 wrapper0 wrapper1 tp tp_push t caller_F caller_sg cs
        (atomic_load_id ids) atomic_load_signature [Vptr b ofs]
        gm gm v).
      - exact Hcs.
      - apply (ConcreteGlobal.transport_module_at_external Hcaller_module).
        apply original_clight_exposes_nonprimitive_external.
        + reflexivity.
        + exact Hcaller_resolve.
        + exact Hnot_primitive.
      - exact Hnot_primitive.
      - exact Hget_mod.
      - apply (transport_module_init_core Hwrapper_module).
        eapply init_atomic_load_core; eauto.
      - exact Hpush.
      - cbn zeta.
        intros tp0 Hcs0.
        eapply (@ConcreteGlobal.atomic_load_global_macro GE wrapper_ix
          wrapper_raw_ge wrapper_ge Hwrapper_module wrapper_F gm m b ofs v
          ent_block ext_block); eauto.
      - apply (transport_module_halt Hwrapper_module).
        unfold ClightLang.halted.
        destruct v; cbn in Hdefined |- *; try discriminate; reflexivity.
      - apply (ConcreteGlobal.transport_module_after_external Hcaller_module).
        change
          ((if clight_val_casted.val_has_rettype_func v
                 (sig_res atomic_load_signature)
            then Some (ClightLang.Core_Returnstate v k)
            else None) = Some (ClightLang.Core_Returnstate v k)).
        rewrite
          (ClightAtomicWrapperSteps.defined_Mint32_load_has_rettype
            m b ofs v Hload Hdefined).
        reflexivity.
    Qed.

    Theorem atomic_store_global_call_and_return
        ids (Hids : wrapper_ids_wf ids)
        (Hget_mod : GlobEnv.get_mod GE (atomic_store_id ids) = Some wrapper_ix)
        (store_block : block)
        (Hstore_symbol :
          Genv.find_symbol wrapper_ge (atomic_store_id ids) = Some store_block)
        (Hstore_fun :
          Genv.find_funct_ptr wrapper_ge store_block =
            Some (Internal atomic_store_function))
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
      pose proof (atomic_store_not_primitive ids Hids) as Hnot_primitive.
      set (wrapper_F := FLists.get_tfid (GlobEnv.freelists GE) t
        (ThreadPool.next_fmap tp t)).
      set (caller0 := caller_core
        (ClightLang.Core_Callstate client_atomic_store_external
          [Vptr b ofs; Vint n] k)).
      set (caller1 := caller_core
        (ClightLang.Core_Returnstate Vundef k)).
      set (wrapper0 := wrapper_core
        (ClightLang.Core_Callstate (Internal atomic_store_function)
          [Vptr b ofs; Vint n] Kstop)).
      set (wrapper1 := wrapper_core
        (ClightLang.Core_Returnstate Vzero Kstop)).
      set (tp_push := ThreadPool.Build_t
        (PMap.set t
          (Some
            (Core.Build_t wrapper_ix wrapper0 atomic_store_signature wrapper_F ::
             Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          (ThreadPool.content tp))
        (ThreadPool.next_tid tp)
        (fun i' =>
          if peq t i' then S (ThreadPool.next_fmap tp t)
          else ThreadPool.next_fmap tp i')).
      assert (Hpush : ThreadPool.push tp t wrapper_ix wrapper0
        atomic_store_signature = Some tp_push).
      { change (PMap.get t (ThreadPool.content tp) =
          Some
            (Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          in Hcs.
        unfold ThreadPool.push. rewrite Hcs. reflexivity. }
      eapply (@Global.call_wrapper_macro_and_return GE caller_ix wrapper_ix
        caller0 caller1 wrapper0 wrapper1 tp tp_push t caller_F caller_sg cs
        (atomic_store_id ids) atomic_store_signature [Vptr b ofs; Vint n]
        gm gm' Vzero).
      - exact Hcs.
      - apply (ConcreteGlobal.transport_module_at_external Hcaller_module).
        apply original_clight_exposes_nonprimitive_external.
        + reflexivity.
        + exact Hcaller_resolve.
        + exact Hnot_primitive.
      - exact Hnot_primitive.
      - exact Hget_mod.
      - apply (transport_module_init_core Hwrapper_module).
        eapply init_atomic_store_core; eauto.
      - exact Hpush.
      - cbn zeta.
        intros tp0 Hcs0.
        eapply (@ConcreteGlobal.atomic_store_global_macro GE wrapper_ix
          wrapper_raw_ge wrapper_ge Hwrapper_module wrapper_F gm gm' m m' b ofs n
          ent_block ext_block); eauto.
      - apply (transport_module_halt Hwrapper_module).
        exact atomic_store_return_halted.
      - apply (ConcreteGlobal.transport_module_after_external Hcaller_module).
        reflexivity.
    Qed.

    Theorem atomic_CAS_success_global_call_and_return
        ids (Hids : wrapper_ids_wf ids)
        (Hget_mod : GlobEnv.get_mod GE (atomic_CAS_id ids) = Some wrapper_ix)
        (CAS_block : block)
        (HCAS_symbol :
          Genv.find_symbol wrapper_ge (atomic_CAS_id ids) = Some CAS_block)
        (HCAS_fun :
          Genv.find_funct_ptr wrapper_ge CAS_block =
            Some (Internal atomic_CAS_function))
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
      pose proof (atomic_CAS_not_primitive ids Hids) as Hnot_primitive.
      set (wrapper_F := FLists.get_tfid (GlobEnv.freelists GE) t
        (ThreadPool.next_fmap tp t)).
      set (caller0 := caller_core
        (ClightLang.Core_Callstate client_atomic_CAS_external
          [Vptr b ofs; Vint expected; Vint new] k)).
      set (caller1 := caller_core
        (ClightLang.Core_Returnstate Vtrue k)).
      set (wrapper0 := wrapper_core
        (ClightLang.Core_Callstate (Internal atomic_CAS_function)
          [Vptr b ofs; Vint expected; Vint new] Kstop)).
      set (wrapper1 := wrapper_core
        (ClightLang.Core_Returnstate Vtrue Kstop)).
      set (tp_push := ThreadPool.Build_t
        (PMap.set t
          (Some
            (Core.Build_t wrapper_ix wrapper0 atomic_CAS_signature wrapper_F ::
             Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          (ThreadPool.content tp))
        (ThreadPool.next_tid tp)
        (fun i' =>
          if peq t i' then S (ThreadPool.next_fmap tp t)
          else ThreadPool.next_fmap tp i')).
      assert (Hpush : ThreadPool.push tp t wrapper_ix wrapper0
        atomic_CAS_signature = Some tp_push).
      { change (PMap.get t (ThreadPool.content tp) =
          Some
            (Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          in Hcs.
        unfold ThreadPool.push. rewrite Hcs. reflexivity. }
      eapply (@Global.call_wrapper_macro_and_return GE caller_ix wrapper_ix
        caller0 caller1 wrapper0 wrapper1 tp tp_push t caller_F caller_sg cs
        (atomic_CAS_id ids) atomic_CAS_signature
        [Vptr b ofs; Vint expected; Vint new]
        gm (FMemory.strip m') Vtrue).
      - exact Hcs.
      - apply (ConcreteGlobal.transport_module_at_external Hcaller_module).
        apply original_clight_exposes_nonprimitive_external.
        + reflexivity.
        + exact Hcaller_resolve.
        + exact Hnot_primitive.
      - exact Hnot_primitive.
      - exact Hget_mod.
      - apply (transport_module_init_core Hwrapper_module).
        eapply init_atomic_CAS_core; eauto.
      - exact Hpush.
      - cbn zeta.
        intros tp0 Hcs0.
        eapply (@ConcreteGlobal.atomic_CAS_success_global_macro GE wrapper_ix
          wrapper_raw_ge wrapper_ge Hwrapper_module wrapper_F gm m m' b ofs expected new
          ent_block ext_block); eauto.
      - apply (transport_module_halt Hwrapper_module).
        exact atomic_CAS_success_halted.
      - apply (ConcreteGlobal.transport_module_after_external Hcaller_module).
        reflexivity.
    Qed.

    Theorem atomic_CAS_failure_global_call_and_return
        ids (Hids : wrapper_ids_wf ids)
        (Hget_mod : GlobEnv.get_mod GE (atomic_CAS_id ids) = Some wrapper_ix)
        (CAS_block : block)
        (HCAS_symbol :
          Genv.find_symbol wrapper_ge (atomic_CAS_id ids) = Some CAS_block)
        (HCAS_fun :
          Genv.find_funct_ptr wrapper_ge CAS_block =
            Some (Internal atomic_CAS_function))
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
      pose proof (atomic_CAS_not_primitive ids Hids) as Hnot_primitive.
      set (wrapper_F := FLists.get_tfid (GlobEnv.freelists GE) t
        (ThreadPool.next_fmap tp t)).
      set (caller0 := caller_core
        (ClightLang.Core_Callstate client_atomic_CAS_external
          [Vptr b ofs; Vint expected; Vint new] k)).
      set (caller1 := caller_core
        (ClightLang.Core_Returnstate Vfalse k)).
      set (wrapper0 := wrapper_core
        (ClightLang.Core_Callstate (Internal atomic_CAS_function)
          [Vptr b ofs; Vint expected; Vint new] Kstop)).
      set (wrapper1 := wrapper_core
        (ClightLang.Core_Returnstate Vfalse Kstop)).
      set (tp_push := ThreadPool.Build_t
        (PMap.set t
          (Some
            (Core.Build_t wrapper_ix wrapper0 atomic_CAS_signature wrapper_F ::
             Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          (ThreadPool.content tp))
        (ThreadPool.next_tid tp)
        (fun i' =>
          if peq t i' then S (ThreadPool.next_fmap tp t)
          else ThreadPool.next_fmap tp i')).
      assert (Hpush : ThreadPool.push tp t wrapper_ix wrapper0
        atomic_CAS_signature = Some tp_push).
      { change (PMap.get t (ThreadPool.content tp) =
          Some
            (Core.Build_t caller_ix caller0 caller_sg caller_F :: cs))
          in Hcs.
        unfold ThreadPool.push. rewrite Hcs. reflexivity. }
      eapply (@Global.call_wrapper_macro_and_return GE caller_ix wrapper_ix
        caller0 caller1 wrapper0 wrapper1 tp tp_push t caller_F caller_sg cs
        (atomic_CAS_id ids) atomic_CAS_signature
        [Vptr b ofs; Vint expected; Vint new] gm gm Vfalse).
      - exact Hcs.
      - apply (ConcreteGlobal.transport_module_at_external Hcaller_module).
        apply original_clight_exposes_nonprimitive_external.
        + reflexivity.
        + exact Hcaller_resolve.
        + exact Hnot_primitive.
      - exact Hnot_primitive.
      - exact Hget_mod.
      - apply (transport_module_init_core Hwrapper_module).
        eapply init_atomic_CAS_core; eauto.
      - exact Hpush.
      - cbn zeta.
        intros tp0 Hcs0.
        eapply (@ConcreteGlobal.atomic_CAS_failure_global_macro GE wrapper_ix
          wrapper_raw_ge wrapper_ge Hwrapper_module wrapper_F gm m b ofs old expected new
          ent_block ext_block); eauto.
      - apply (transport_module_halt Hwrapper_module).
        exact atomic_CAS_failure_halted.
      - apply (ConcreteGlobal.transport_module_after_external Hcaller_module).
        reflexivity.
    Qed.

  End RuntimeModules.

End ClightAtomicGlobalCalls.
