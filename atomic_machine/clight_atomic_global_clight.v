(** Concrete global executions of the marker-enabled Clight wrappers.

    The generic global lifting theorem is indexed by the language stored in
    the active runtime module.  The corollaries in this file discharge that
    index using an equality saying that the selected module is precisely the
    marker-enabled Clight wrapper module.  No simulation or desired global
    execution is assumed. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
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

Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.
Require Import atomic_machine.clight_atomic_wrapper_steps.
Require Import atomic_machine.clight_atomic_store_steps.
Require Import atomic_machine.clight_atomic_cas_steps.
Require Import atomic_machine.clight_atomic_global_steps.

From Stdlib Require Import List.
Import ListNotations.

Module ClightAtomicGlobalClight.

  Import ClightAtomicWrappers.
  Import ClightAtomicWrapperSteps.
  Import ClightAtomicStoreSteps.
  Import ClightAtomicCASSteps.
  Module Global := ClightAtomicGlobalSteps.

  Definition transport_module_core
      {md1 md2 : ModSem.t} (Hmd : md1 = md2)
      (c : InteractionSemantics.core (ModSem.lang md2)) :
      InteractionSemantics.core (ModSem.lang md1) :=
    match Hmd in (_ = md)
      return InteractionSemantics.core (ModSem.lang md) ->
        InteractionSemantics.core (ModSem.lang md1) with
    | eq_refl => fun c0 => c0
    end c.

  Lemma transport_module_star
      {md1 md2 : ModSem.t} (Hmd : md1 = md2)
      (fl : MemAux.freelist)
      (c0 c1 : InteractionSemantics.core (ModSem.lang md2))
      gm0 fp gm1
      (Hstar : InteractionSemantics.star
        (InteractionSemantics.step (ModSem.lang md2) (ModSem.Ge md2) fl)
        c0 gm0 fp c1 gm1) :
    InteractionSemantics.star
      (InteractionSemantics.step (ModSem.lang md1) (ModSem.Ge md1) fl)
      (transport_module_core Hmd c0) gm0 fp
      (transport_module_core Hmd c1) gm1.
  Proof. destruct Hmd. exact Hstar. Qed.

  Lemma transport_module_at_external
      {md1 md2 : ModSem.t} (Hmd : md1 = md2)
      (c : InteractionSemantics.core (ModSem.lang md2)) call
      (Hat : InteractionSemantics.at_external
        (ModSem.lang md2) (ModSem.Ge md2) c = call) :
    InteractionSemantics.at_external
      (ModSem.lang md1) (ModSem.Ge md1)
      (transport_module_core Hmd c) = call.
  Proof. destruct Hmd. exact Hat. Qed.

  Lemma transport_module_after_external
      {md1 md2 : ModSem.t} (Hmd : md1 = md2)
      (c c' : InteractionSemantics.core (ModSem.lang md2)) res
      (Hafter : InteractionSemantics.after_external
        (ModSem.lang md2) c res = Some c') :
    InteractionSemantics.after_external
      (ModSem.lang md1) (transport_module_core Hmd c) res =
      Some (transport_module_core Hmd c').
  Proof. destruct Hmd. exact Hafter. Qed.

  (** [Core.t] stores a core whose type depends on the language projection of
      its module index.  Consequently an equality identifying a runtime
      module with the wrapper module must also transport concrete Clight
      cores across the induced language equality.  This is only dependent
      equality bookkeeping: it carries no step or execution premise. *)
  Definition wrapper_runtime_core
      {GE : GlobEnv.t} (ix : 'I_(GlobEnv.M GE))
      (raw_ge : Genv.t Clight.fundef Ctypes.type) (ge : Clight.genv)
      (Hmodule :
        GlobEnv.modules GE ix =
          ModSem.Build_t Clight_IS_2_with_markers raw_ge ge)
      (c : ClightLang.core) :
      InteractionSemantics.core
        (ModSem.lang (GlobEnv.modules GE ix)) :=
    transport_module_core Hmodule c.

  Section RuntimeWrapper.

    Context {GE : GlobEnv.t}.
    Variable ix : 'I_(GlobEnv.M GE).
    Variable raw_ge : Genv.t Clight.fundef Ctypes.type.
    Variable ge : Clight.genv.
    Hypothesis Hmodule :
      GlobEnv.modules GE ix =
        ModSem.Build_t Clight_IS_2_with_markers raw_ge ge.

    Variable F : fid.
    Local Definition wrapper_fl : MemAux.freelist :=
      FLists.get_fl (GlobEnv.freelists GE) F.
    Local Definition runtime_core : ClightLang.core ->
        InteractionSemantics.core
          (ModSem.lang (GlobEnv.modules GE ix)) :=
      wrapper_runtime_core ix raw_ge ge Hmodule.

    (** This is the cast-free-at-the-execution-level composition point.  Its
        only transport is [runtime_core], forced by [Core.t]'s dependent
        module index; all seven semantic premises are concrete Clight paths
        or marker boundaries. *)
    Lemma bracketed_clight_paths_to_global_atomic
        (c0 cent cent_resume cext cext_resume cfinal : ClightLang.core)
        (gm0 gm1 gm2 gm3 : GMemory.gmem) fp0 fp1 fp2
        (Hto_ent : InteractionSemantics.star (ClightLang.step2 ge wrapper_fl)
          c0 gm0 fp0 cent gm1)
        (Hat_ent : InteractionSemantics.at_external
          Clight_IS_2_with_markers ge cent =
          Some (GAST.ent_atom, GAST.ent_atom_sg, []))
        (Hafter_ent : InteractionSemantics.after_external
          Clight_IS_2_with_markers cent None = Some cent_resume)
        (Hinside : InteractionSemantics.star (ClightLang.step2 ge wrapper_fl)
          cent_resume gm1 fp1 cext gm2)
        (Hat_ext : InteractionSemantics.at_external
          Clight_IS_2_with_markers ge cext =
          Some (GAST.ext_atom, GAST.ext_atom_sg, []))
        (Hafter_ext : InteractionSemantics.after_external
          Clight_IS_2_with_markers cext None = Some cext_resume)
        (Hfrom_ext : InteractionSemantics.star
          (ClightLang.step2 ge wrapper_fl)
          cext_resume gm2 fp2 cfinal gm3) :
      forall (tp : @ThreadPool.t GE) t sg cs,
        ThreadPool.get_cs tp t =
          Some (Core.Build_t ix (runtime_core c0) sg F :: cs) ->
        exists tp' fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp t gm0 O) fp
            (Build_ProgConfig GE tp' t gm3 O) /\
          ThreadPool.get_cs tp' t =
            Some (Core.Build_t ix (runtime_core cfinal) sg F :: cs).
    Proof.
      intros tp t sg cs Hcs.
      eapply (@Global.bracketed_local_paths_to_global_atomic GE ix F
        (runtime_core c0) (runtime_core cent) (runtime_core cent_resume)
        (runtime_core cext) (runtime_core cext_resume)
        (runtime_core cfinal) gm0 gm1 gm2 gm3 fp0 fp1 fp2).
      - exact (transport_module_star Hmodule wrapper_fl _ _ _ _ _ Hto_ent).
      - exact (transport_module_at_external Hmodule _ _ Hat_ent).
      - exact (transport_module_after_external Hmodule _ _ _ Hafter_ent).
      - exact (transport_module_star Hmodule wrapper_fl _ _ _ _ _ Hinside).
      - exact (transport_module_at_external Hmodule _ _ Hat_ext).
      - exact (transport_module_after_external Hmodule _ _ _ Hafter_ext).
      - exact (transport_module_star Hmodule wrapper_fl _ _ _ _ _ Hfrom_ext).
      - exact Hcs.
    Qed.

    (** A concrete [atomic_load] call is a silent global execution containing
        [Ent_Atom], the read, and [Ext_Atom], and it restores the atomic bit. *)
    Corollary atomic_load_global_macro
        (gm : GMemory.gmem) (m : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (v : val)
        (ent_block ext_block : block)
        (Hembed : FMemory.embed gm wrapper_fl m)
        (Hload :
          FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
        (Hdefined : clight_val_casted.vals_defined [v] = true)
        (Hent_symbol :
          Genv.find_symbol ge GAST.ent_atom = Some ent_block)
        (Hent_fun :
          Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
        (Hext_symbol :
          Genv.find_symbol ge GAST.ext_atom = Some ext_block)
        (Hext_fun :
          Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
      forall (tp : @ThreadPool.t GE) t sg cs,
        ThreadPool.get_cs tp t =
          Some
            (Core.Build_t ix
              (runtime_core
                (ClightLang.Core_Callstate (Internal atomic_load_function)
                  [Vptr b ofs] Kstop)) sg F :: cs) ->
        exists tp' fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp t gm O) fp
            (Build_ProgConfig GE tp' t gm O) /\
          ThreadPool.get_cs tp' t =
            Some
              (Core.Build_t ix
                (runtime_core
                  (ClightLang.Core_Returnstate v Kstop)) sg F :: cs).
    Proof.
      intros tp t sg cs Hcs.
      pose proof
        (atomic_load_step2_macro ge wrapper_fl gm m b ofs v
          ent_block ext_block Hembed Hload Hdefined Hent_symbol Hent_fun
          Hext_symbol Hext_fun) as Hmacro.
      cbn beta in Hmacro.
      destruct Hmacro as
        (fp0 & fp1 & fp2 & Hto_ent & Hat_ent & Hafter_ent & Hinside &
         Hat_ext & Hafter_ext & Hfrom_ext).
      eapply bracketed_clight_paths_to_global_atomic.
      - exact Hto_ent.
      - exact Hat_ent.
      - exact Hafter_ent.
      - exact Hinside.
      - exact Hat_ext.
      - exact Hafter_ext.
      - exact Hfrom_ext.
      - exact Hcs.
    Qed.

    (** A concrete [atomic_store] call changes the global memory only in the
        middle, while the atomic bit is set. *)
    Corollary atomic_store_global_macro
        (gm gm' : GMemory.gmem) (m m' : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (n : int)
        (ent_block ext_block : block)
        (Hembed : FMemory.embed gm wrapper_fl m)
        (Hembed' : FMemory.embed gm' wrapper_fl m')
        (Hstore :
          FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint n) = Some m')
        (Hent_symbol :
          Genv.find_symbol ge GAST.ent_atom = Some ent_block)
        (Hent_fun :
          Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
        (Hext_symbol :
          Genv.find_symbol ge GAST.ext_atom = Some ext_block)
        (Hext_fun :
          Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
      forall (tp : @ThreadPool.t GE) t sg cs,
        ThreadPool.get_cs tp t =
          Some
            (Core.Build_t ix
              (runtime_core
                (ClightLang.Core_Callstate (Internal atomic_store_function)
                  [Vptr b ofs; Vint n] Kstop)) sg F :: cs) ->
        exists tp' fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp t gm O) fp
            (Build_ProgConfig GE tp' t gm' O) /\
          ThreadPool.get_cs tp' t =
            Some
              (Core.Build_t ix
                (runtime_core
                  (ClightLang.Core_Returnstate Vzero Kstop)) sg F :: cs).
    Proof.
      intros tp t sg cs Hcs.
      pose proof
        (atomic_store_step2_macro ge wrapper_fl gm gm' m m' b ofs n
          ent_block ext_block Hembed Hembed' Hstore Hent_symbol Hent_fun
          Hext_symbol Hext_fun) as Hmacro.
      cbn beta in Hmacro.
      destruct Hmacro as
        (fp0 & fp1 & fp2 & Hto_ent & Hat_ent & Hafter_ent & Hinside &
         Hat_ext & Hafter_ext & Hfrom_ext & _).
      eapply bracketed_clight_paths_to_global_atomic.
      - exact Hto_ent.
      - exact Hat_ent.
      - exact Hafter_ent.
      - exact Hinside.
      - exact Hat_ext.
      - exact Hafter_ext.
      - exact Hfrom_ext.
      - exact Hcs.
    Qed.

    (** Successful [atomic_CAS]: read, equality test, and conditional store
        all occur between the two global marker steps. *)
    Corollary atomic_CAS_success_global_macro
        (gm : GMemory.gmem) (m m' : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (expected new : int)
        (ent_block ext_block : block)
        (Hembed : FMemory.embed gm wrapper_fl m)
        (Hload :
          FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint expected))
        (Hstore :
          FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint new) = Some m')
        (Hent_symbol :
          Genv.find_symbol ge GAST.ent_atom = Some ent_block)
        (Hent_fun :
          Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
        (Hext_symbol :
          Genv.find_symbol ge GAST.ext_atom = Some ext_block)
        (Hext_fun :
          Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
      forall (tp : @ThreadPool.t GE) t sg cs,
        ThreadPool.get_cs tp t =
          Some
            (Core.Build_t ix
              (runtime_core
                (ClightLang.Core_Callstate (Internal atomic_CAS_function)
                  [Vptr b ofs; Vint expected; Vint new] Kstop)) sg F :: cs) ->
        exists tp' fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp t gm O) fp
            (Build_ProgConfig GE tp' t (FMemory.strip m') O) /\
          ThreadPool.get_cs tp' t =
            Some
              (Core.Build_t ix
                (runtime_core
                  (ClightLang.Core_Returnstate Vtrue Kstop)) sg F :: cs).
    Proof.
      intros tp t sg cs Hcs.
      pose proof
        (atomic_CAS_success_step2_macro ge wrapper_fl gm m m'
          b ofs expected new ent_block ext_block Hembed Hload Hstore
          Hent_symbol Hent_fun Hext_symbol Hext_fun) as Hmacro.
      cbn beta in Hmacro.
      destruct Hmacro as
        (fp0 & fp1 & fp2 & Hto_ent & Hat_ent & Hafter_ent & Hinside &
         Hat_ext & Hafter_ext & Hfrom_ext & _).
      eapply bracketed_clight_paths_to_global_atomic.
      - exact Hto_ent.
      - exact Hat_ent.
      - exact Hafter_ent.
      - exact Hinside.
      - exact Hat_ext.
      - exact Hafter_ext.
      - exact Hfrom_ext.
      - exact Hcs.
    Qed.

    (** Failed [atomic_CAS]: the read and failed comparison occur inside the
        marker pair and the global memory is unchanged. *)
    Corollary atomic_CAS_failure_global_macro
        (gm : GMemory.gmem) (m : FMemory.Mem.mem)
        (b : block) (ofs : ptrofs) (old expected new : int)
        (ent_block ext_block : block)
        (Hembed : FMemory.embed gm wrapper_fl m)
        (Hneq : old <> expected)
        (Hload :
          FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint old))
        (Hent_symbol :
          Genv.find_symbol ge GAST.ent_atom = Some ent_block)
        (Hent_fun :
          Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
        (Hext_symbol :
          Genv.find_symbol ge GAST.ext_atom = Some ext_block)
        (Hext_fun :
          Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
      forall (tp : @ThreadPool.t GE) t sg cs,
        ThreadPool.get_cs tp t =
          Some
            (Core.Build_t ix
              (runtime_core
                (ClightLang.Core_Callstate (Internal atomic_CAS_function)
                  [Vptr b ofs; Vint expected; Vint new] Kstop)) sg F :: cs) ->
        exists tp' fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp t gm O) fp
            (Build_ProgConfig GE tp' t gm O) /\
          ThreadPool.get_cs tp' t =
            Some
              (Core.Build_t ix
                (runtime_core
                  (ClightLang.Core_Returnstate Vfalse Kstop)) sg F :: cs).
    Proof.
      intros tp t sg cs Hcs.
      pose proof
        (atomic_CAS_failure_step2_macro ge wrapper_fl gm m
          b ofs old expected new ent_block ext_block Hembed Hneq Hload
          Hent_symbol Hent_fun Hext_symbol Hext_fun) as Hmacro.
      cbn beta in Hmacro.
      destruct Hmacro as
        (fp0 & fp1 & fp2 & Hto_ent & Hat_ent & Hafter_ent & Hinside &
         Hat_ext & Hafter_ext & Hfrom_ext & _).
      eapply bracketed_clight_paths_to_global_atomic.
      - exact Hto_ent.
      - exact Hat_ent.
      - exact Hafter_ent.
      - exact Hinside.
      - exact Hat_ext.
      - exact Hafter_ext.
      - exact Hfrom_ext.
      - exact Hcs.
    Qed.

  End RuntimeWrapper.

End ClightAtomicGlobalClight.
