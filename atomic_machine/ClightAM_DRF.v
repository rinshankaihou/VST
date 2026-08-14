(** Finite-execution correspondence from the Clight atomic machine to
    CASCompCert's global semantics.

    [match_config] below is a direct relation on [CAM_config] and
    [ProgConfig].  It compares memories and every thread stack when the
    target atomic bit is clear.  While the bit is set, it keeps the wrapper
    and suspended atomic client-frame shape but forgets their selected-core
    correspondence. *)

Require Import compcert.common.AST.
Require Import compcert.common.Builtins.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.concurrency.common.Footprint.
Require Import compcert.concurrency.common.FMemPerm.
Require Import compcert.concurrency.common.GlobDefs.
Require Import compcert.concurrency.common.GlobSemantics.
Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.common.InteractionSemantics.

From Stdlib Require Import List.
From Stdlib Require Import Eqdep.
From Stdlib Require Import Strings.String.
From mathcomp.boot Require Import fintype.
Require Import stdpp.gmap.
Require Import VST.veric.val_lemmas.

Require Import atomic_machine.atomic_machine.
Require Import atomic_machine.clight_atomic_specs.
Require Import atomic_machine.clight_at_mach.
Require Import atomic_machine.clight_atomic_source_decode.
Require Import atomic_machine.clight_atomic_source_restriction.
Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.
Require Import atomic_machine.clight_atomic_client_init.
Require Import atomic_machine.clight_atomic_target.
Require Import atomic_machine.clight_atomic_global_steps.
Require Import atomic_machine.clight_atomic_global_calls.
Require Import atomic_machine.clight_atomic_initialized_calls.

Import Address Values.
Import ListNotations.

Module Wrappers := ClightAtomicWrappers.
Module ClientInit := ClightAtomicClientInit.
Module InitializedCalls := ClightAtomicInitializedCalls.
Module GlobalSteps := ClightAtomicGlobalSteps.

Lemma clight_val_defined_as_target_boolean v :
  clight_val_defined v ->
  clight_val_casted.vals_defined [v] = true.
Proof.
  destruct v; cbn [clight_val_defined]; intros Hdefined;
    try reflexivity; contradiction.
Qed.

(** ** Finite executions of the source atomic machine

    These executions use the bare [at_step] instantiated with the unchanged
    [Clight_language].  Any ordinary source marker/builtin behavior must be
    covered (or excluded as unreachable) by the program-indexed [Core_Try]
    bridge used below. *)

Definition CAM_tpool (ge : Clight.genv) : Type :=
  @tpool address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge).

Definition CAM_rw_map : Type := @rw_map address _ _.

Record CAM_config (ge : Clight.genv) : Type := {
  CAM_threads : CAM_tpool ge;
  CAM_memory : mem;
  CAM_rw : CAM_rw_map
}.

Arguments CAM_threads {ge} _.
Arguments CAM_memory {ge} _.
Arguments CAM_rw {ge} _.

Section CAMSteps.

Context (ge : Clight.genv).
Implicit Types (sc : CAM_config ge).

Definition CAM_step sc1 sc2 : Prop :=
  @at_step address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge)
    (CAM_threads sc1) (CAM_memory sc1) (CAM_rw sc1)
    (CAM_threads sc2) (CAM_memory sc2) (CAM_rw sc2).

End CAMSteps.

Section CAMSourceConfigurationPredicates.

Context {ge : Clight.genv}.
Implicit Types (sc : CAM_config ge).

(** If the statement is assign, . *)
Definition CAM_assign_loc_value_syntax sc : Prop :=
  forall i c T,
    CAM_threads sc !! i =
      Some (@Running address val _ _ mem memory_chunk clight_mem_mixin
        (Clight_language ge) c T) ->
    clight_core_assign_loc_value_syntax ge c.

Local Definition CAM_stuck_state :=
  @StuckState address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge).

(** Absence of the atomic machine's explicit [StuckState].  This is exactly
    the invariant needed to exclude [SC_Cas_Stuck]; it is weaker than semantic
    progress because a [Running] Clight core may still have no transition. *)
Definition CAM_no_explicit_stuck sc : Prop :=
  forall i,
    CAM_threads sc !! i <> Some CAM_stuck_state.

End CAMSourceConfigurationPredicates.

(** A convenient internal classifier for the three call shapes accepted by
    the decoder.  Unlike the old configuration invariant, this proposition is
    derived from every successful [clight_at_external] result below. *)
Inductive CAM_supported_atomic_call : Clight_core.CC_core -> Prop :=
| CAM_supported_load_call b ofs k :
    CAM_supported_atomic_call
      (Clight_core.Callstate Wrappers.client_atomic_load_external
        [Vptr b ofs] k)
| CAM_supported_store_call b ofs n k :
    CAM_supported_atomic_call
      (Clight_core.Callstate Wrappers.client_atomic_store_external
        [Vptr b ofs; Vint n] k)
| CAM_supported_CAS_call b ofs expected new k :
    CAM_supported_atomic_call
      (Clight_core.Callstate Wrappers.client_atomic_CAS_external
        [Vptr b ofs; Vint expected; Vint new] k).

(** Direct pre/post compatibility for the source core while the corresponding
    target client call is suspended under its wrapper.  The wrapper's active
    core is intentionally not equated with either endpoint. *)
Inductive CAM_atomic_phase_matches :
    Clight_core.CC_core -> Clight_core.CC_core -> Prop :=
| CAM_atomic_phase_before c :
    CAM_supported_atomic_call c ->
    CAM_atomic_phase_matches c c
| CAM_atomic_phase_load_after b ofs v k :
    CAM_atomic_phase_matches
      (Clight_core.Returnstate v k)
      (Clight_core.Callstate Wrappers.client_atomic_load_external
        [Vptr b ofs] k)
| CAM_atomic_phase_store_after b ofs n k :
    CAM_atomic_phase_matches
      (Clight_core.Returnstate Vundef k)
      (Clight_core.Callstate Wrappers.client_atomic_store_external
        [Vptr b ofs; Vint n] k)
| CAM_atomic_phase_CAS_success_after b ofs expected new k :
    CAM_atomic_phase_matches
      (Clight_core.Returnstate Vtrue k)
      (Clight_core.Callstate Wrappers.client_atomic_CAS_external
        [Vptr b ofs; Vint expected; Vint new] k)
| CAM_atomic_phase_CAS_failure_after b ofs expected new k :
    CAM_atomic_phase_matches
      (Clight_core.Returnstate Vfalse k)
      (Clight_core.Callstate Wrappers.client_atomic_CAS_external
        [Vptr b ofs; Vint expected; Vint new] k).

(** The machine performs the same statically typed comparison as the
    concrete CAS wrapper.  With two [tint] operands, any successful dynamic
    comparison forces the loaded operand to be a [Vint], even on 32-bit
    targets where a defined [Mint32] load can otherwise produce [Vptr]. *)
Lemma clight_tint_Ceq_true_inv m v expected :
  Cop.sem_cmp Ceq v ClightAtomicSpecs.tint
    (Vint expected) ClightAtomicSpecs.tint m = Some Vtrue ->
  v = Vint expected.
Proof.
  intros Hcmp.
  unfold Cop.sem_cmp, Cop.classify_cmp, ClightAtomicSpecs.tint,
    Cop.sem_binarith, Cop.classify_binarith, Cop.binarith_type,
    Cop.sem_cast, Cop.classify_cast in Hcmp.
  destruct Archi.ptr64; destruct v; cbn in Hcmp; try discriminate.
  all: destruct (Int.eq i expected) eqn:Heq; cbn in Hcmp;
    try discriminate.
  all: f_equal; apply Int.same_if_eq; exact Heq.
Qed.

Lemma clight_tint_Ceq_false_inv m v expected :
  Cop.sem_cmp Ceq v ClightAtomicSpecs.tint
    (Vint expected) ClightAtomicSpecs.tint m = Some Vfalse ->
  exists old, v = Vint old /\ old <> expected.
Proof.
  intros Hcmp.
  unfold Cop.sem_cmp, Cop.classify_cmp, ClightAtomicSpecs.tint,
    Cop.sem_binarith, Cop.classify_binarith, Cop.binarith_type,
    Cop.sem_cast, Cop.classify_cast in Hcmp.
  destruct Archi.ptr64; destruct v; cbn in Hcmp; try discriminate.
  all: destruct (Int.eq i expected) eqn:Heq; cbn in Hcmp;
    try discriminate.
  all: exists i; split; [reflexivity |].
  all: intros Hequal; subst expected; rewrite Int.eq_true in Heq;
    discriminate.
Qed.

Lemma clight_ValEq_CAS_Vint_same m b ofs current expected new k :
  clight_ValEq
    (Clight_core.Callstate Wrappers.client_atomic_CAS_external
      [Vptr b ofs; Vint expected; Vint new] k)
    m current (Vint expected) ->
  current = Vint expected.
Proof.
  unfold clight_ValEq, clight_pending_CAS_type.
  cbn [clight_atomic_CAS_type clight_value_chunk
    Wrappers.client_atomic_CAS_external
    ClightAtomicSpecs.client_atomic_CAS_external
    ClightAtomicSpecs.atomic_pointer_type ClightAtomicSpecs.tint].
  apply clight_tint_Ceq_true_inv.
Qed.

Lemma clight_ValNEq_CAS_Vint_different m b ofs current expected new k :
  clight_ValNEq
    (Clight_core.Callstate Wrappers.client_atomic_CAS_external
      [Vptr b ofs; Vint expected; Vint new] k)
    m current (Vint expected) ->
  exists old, current = Vint old /\ old <> expected.
Proof.
  unfold clight_ValNEq, clight_pending_CAS_type.
  cbn [clight_atomic_CAS_type clight_value_chunk
    Wrappers.client_atomic_CAS_external
    ClightAtomicSpecs.client_atomic_CAS_external
    ClightAtomicSpecs.atomic_pointer_type ClightAtomicSpecs.tint].
  apply clight_tint_Ceq_false_inv.
Qed.

Lemma CAM_decoded_atomic_call_supported c op K :
  clight_at_external c = Some (op, K) ->
  CAM_supported_atomic_call c.
Proof.
  intros Hext. destruct op as [ly l | ly l v | ly l expected new].
  - destruct (clight_at_external_load_inv _ _ _ _ Hext)
      as (b & ofs & k & Hc & Hly & Hl & HK).
    subst c. constructor.
  - destruct (clight_at_external_store_inv _ _ _ _ _ Hext)
      as (b & ofs & n & k & Hc & Hly & Hl & Hv & HK).
    subst c. constructor.
  - destruct (clight_at_external_CAS_inv _ _ _ _ _ _ Hext)
      as (b & ofs & expected_int & new_int & k & Hc & Hly & Hl &
          Hexpected & Hnew & HK).
    subst c. constructor.
Qed.

Lemma CAM_supported_load_inv c ly l K :
  CAM_supported_atomic_call c ->
  clight_at_external c = Some (ALoad ly l, K) ->
  exists b ofs k,
    c = Clight_core.Callstate Wrappers.client_atomic_load_external
      [Vptr b ofs] k /\
    ly = Mint32 /\
    l = (b, Ptrofs.unsigned ofs) /\
    K = (fun ov => Clight_core.Returnstate (force_val ov) k).
Proof.
  intros _ Hext.
  destruct (clight_at_external_load_inv _ _ _ _ Hext)
    as (b & ofs & k & Hc & Hly & Hl & HK).
  repeat eexists; eauto.
Qed.

Lemma CAM_supported_store_inv c ly l v K :
  CAM_supported_atomic_call c ->
  clight_at_external c = Some (AStore ly l v, K) ->
  exists b ofs n k,
    c = Clight_core.Callstate Wrappers.client_atomic_store_external
      [Vptr b ofs; Vint n] k /\
    ly = Mint32 /\
    l = (b, Ptrofs.unsigned ofs) /\
    v = Vint n /\
    K = (fun _ => Clight_core.Returnstate Vundef k).
Proof.
  intros _ Hext.
  destruct (clight_at_external_store_inv _ _ _ _ _ Hext)
    as (b & ofs & n & k & Hc & Hly & Hl & Hv & HK).
  repeat eexists; eauto.
Qed.

Lemma CAM_supported_CAS_inv c ly l expected new K :
  CAM_supported_atomic_call c ->
  clight_at_external c = Some (ACAS ly l expected new, K) ->
  exists b ofs expected_int new_int k,
    c = Clight_core.Callstate Wrappers.client_atomic_CAS_external
      [Vptr b ofs; Vint expected_int; Vint new_int] k /\
    ly = Mint32 /\
    l = (b, Ptrofs.unsigned ofs) /\
    expected = Vint expected_int /\
    new = Vint new_int /\
    K = (fun ov => Clight_core.Returnstate (force_val ov) k).
Proof.
  intros _ Hext.
  destruct (clight_at_external_CAS_inv _ _ _ _ _ _ Hext)
    as (b & ofs & expected_int & new_int & k & Hc & Hly & Hl &
        Hexpected & Hnew & HK).
  repeat eexists; eauto.
Qed.

(** Every thread has finished its Clight computation and has no pending
    memory events left to commit. *)
Section CAMSourceTermination.

Context {ge : Clight.genv}.
Implicit Types (sc : CAM_config ge).

Definition CAM_all_threads_terminated sc : Prop :=
  forall (i : nat) (c : Clight_core.CC_core)
    (T : list (@mem_ev address)),
    CAM_threads sc !! i =
      Some (@Running address val _ _ mem memory_chunk clight_mem_mixin
        (Clight_language ge) c T) ->
    T = [] /\ Clight_core.cl_halted c <> None.

End CAMSourceTermination.

(** Finite, terminating executions in the source fragment considered by this
    development.  Every state carries the static assignment restriction;
    canonical atomic call shapes now follow directly from the decoder, while
    definedness of transferred values is enforced by [CAM_step] itself.
    Every transition is the unchanged [CAM_step], and the reflexive endpoint
    requires every thread to have terminated.  Direct client marker calls
    require a separate program restriction; assignment syntax alone neither
    admits nor excludes them. *)
Section CAMExecutions.

Context (ge : Clight.genv).
Implicit Types (sc : CAM_config ge).

Inductive CAM_execution :
    CAM_config ge -> CAM_config ge -> Prop :=
| CAM_exec_refl sc
    (Hnot_stuck : CAM_no_explicit_stuck sc)
    (Hsyntax : CAM_assign_loc_value_syntax sc)
    (Hterminated : CAM_all_threads_terminated sc) :
    CAM_execution sc sc
| CAM_exec_step sc1 sc2 sc3
    (Hnot_stuck : CAM_no_explicit_stuck sc1)
    (Hsyntax : CAM_assign_loc_value_syntax sc1)
    (Hstep : CAM_step ge sc1 sc2)
    (Hexec : CAM_execution sc2 sc3) :
    CAM_execution sc1 sc3.

Lemma CAM_execution_source_no_explicit_stuck_1 sc1 sc2 :
  CAM_execution sc1 sc2 ->
  CAM_no_explicit_stuck sc1.
Proof.
  intros Hexec; inversion Hexec; auto.
Qed.

Lemma CAM_execution_no_explicit_stuck_2 sc1 sc2 :
  CAM_execution sc1 sc2 ->
  CAM_no_explicit_stuck sc2.
Proof.
  intros Hexec; induction Hexec; auto.
Qed.


Lemma CAM_execution_target_syntax sc1 sc2 :
  CAM_execution sc1 sc2 ->
  CAM_assign_loc_value_syntax sc2.
Proof.
  intros Hexec; induction Hexec; auto.
Qed.

Lemma CAM_execution_source_syntax sc1 sc2 :
  CAM_execution sc1 sc2 ->
  CAM_assign_loc_value_syntax sc1.
Proof.
  intros Hexec; inversion Hexec; auto.
Qed.

Lemma CAM_execution_target_terminated sc1 sc2 :
  CAM_execution sc1 sc2 ->
  CAM_all_threads_terminated sc2.
Proof.
  intros Hexec; induction Hexec; auto.
Qed.

End CAMExecutions.

(** ** The concrete CAM/GlobSemantics configuration relation *)

(** Target thread identifiers start at [1], whereas CAM identifiers start at
    [0].  The linked target has one client unit, so ordinal [0] is the client
    and ordinal [1] is the appended wrapper. *)
Definition CAM_tid (i : nat) : tid := Pos.of_succ_nat i.

(** Source and target use the same shape of core states but different datatypes. *)
Definition s2t_core
    (score : Clight_core.CC_core) : ClightLang.core :=
  match score with
  | Clight_core.State f s k e le =>
      ClightLang.Core_State f s k e le
  | Clight_core.Callstate fd args k =>
      ClightLang.Core_Callstate fd args k
  | Clight_core.Returnstate v k =>
      ClightLang.Core_Returnstate v k
  end.

(** Identity-block correspondence between a CompCert source memory and a
    CASCompCert global memory.  The permission types are distinct, hence the
    explicit conversions in the access-map clause.  In mixed-language
    relations below, [s]-prefixed binders name source components and
    [t]-prefixed binders name target components. *)
Record CAM_memory_match (sm : mem) (tm : GMemory.gmem) : Prop := {
  CAM_memory_contents_match :
    Mem.mem_contents sm = GMemory.GMem.mem_contents tm;
  CAM_memory_access_match :
    forall b ofs k,
      Maps.PMap.get b (GMemory.GMem.mem_access tm) ofs
        (perm_kind_convert k) =
      option_map permission_convert
        (Maps.PMap.get b (Mem.mem_access sm) ofs k);
  CAM_memory_valid_match :
    forall b, Mem.valid_block sm b <-> GMemory.GMem.valid_block tm b
}.

Section CAMConfigurationRelation.

  Context {ge : Clight.genv} {GE : GlobEnv.t}.
  Implicit Types (sc : CAM_config ge) (tc : @ProgConfig GE).

  Local Definition source_running
      (score : Clight_core.CC_core) (T : list (@mem_ev address)) :=
    @Running address val _ _ mem memory_chunk clight_mem_mixin
      (Clight_language ge) score T.

  (** A client frame is concrete: it is module zero, that module is the
      checked-in [Clight_IS_2], and its dependent core is the structural
      export of the CAM core. *)
  Inductive CAM_client_frame_matches
      (score : Clight_core.CC_core) : @Core.t GE -> Prop :=
  | CAM_client_frame_intro
      (client_ix : 'I_(GlobEnv.M GE))
      (raw_ge : Genv.t ClightLang.Clight_IS_2.(F)
                       ClightLang.Clight_IS_2.(V))
      (client_ge : Clight.genv)
      (Hix : nat_of_ord client_ix = 0)
      (Hmodule : GlobEnv.modules GE client_ix =
        ModSem.Build_t ClightLang.Clight_IS_2 raw_ge client_ge)
      sg F :
      CAM_client_frame_matches score
        (Core.Build_t client_ix
          (ClightAtomicGlobalCalls.runtime_core client_ix
            ClightLang.Clight_IS_2 raw_ge client_ge Hmodule
            (s2t_core score)) sg F).

  Definition CAM_wrapper_frame (tframe : @Core.t GE) : Prop :=
    nat_of_ord (Core.i tframe) = 1 /\
    ModSem.lang (GlobEnv.modules GE (Core.i tframe)) =
      Clight_IS_2_with_markers.

  (** Pending CAM events and the reservation map are source ghost state.
      Erasing the event list here is what makes [Core_Commit] target
      stuttering.  A halted source core may match either its final singleton
      frame or the empty stack after a target [Halt] step. *)
  Definition CAM_stack_matches
      (sst : @tstate address val _ _ mem memory_chunk clight_mem_mixin
              (Clight_language ge))
      (tcs : @CallStack.t GE) : Prop :=
    match sst with
    | Running score _ =>
        (exists tframe,
          CAM_client_frame_matches score tframe /\ tcs = [tframe]) \/
        (ClightLang.halted (s2t_core score) <> None /\ tcs = [])
    | StuckState => False
    end.

  Definition CAM_option_stack_matches
      (sost : option
        (@tstate address val _ _ mem memory_chunk clight_mem_mixin
          (Clight_language ge)))
      (tocs : option (@CallStack.t GE)) : Prop :=
    match sost, tocs with
    | Some sst, Some tcs => CAM_stack_matches sst tcs
    | None, None => True
    | _, _ => False
    end.

  Definition CAM_pool_matches
      (stp : CAM_tpool ge) (ttp : @ThreadPool.t GE) : Prop :=
    (forall i,
      CAM_option_stack_matches (stp !! i)
        (ThreadPool.get_cs ttp (CAM_tid i))) /\
    (forall i,
      (exists sst, stp !! i = Some sst) <->
      ThreadPool.valid_tid ttp (CAM_tid i)).

  Definition CAM_current_thread_in_pool
      (stp : CAM_tpool ge) tc : Prop :=
    exists i sst, stp !! i = Some sst /\ cur_tid tc = CAM_tid i.

  Record CAM_uncrit_match sc tc : Prop := {
    CAM_uncrit_bit : atom_bit tc = O;
    CAM_uncrit_memory : CAM_memory_match (CAM_memory sc) (gm tc);
    CAM_uncrit_pool :
      CAM_pool_matches (CAM_threads sc) (thread_pool tc);
    CAM_uncrit_current :
      CAM_current_thread_in_pool (CAM_threads sc) tc
  }.

  (** An atomic source step at [i], with the selected thread and exact post
      configuration in the proposition itself.  Merely observing that some
      thread is parked at an atomic call would be insufficient: a different
      thread could be taking the actual [CAM_step]. *)
  Inductive CAM_atomic_step_at (i : nat) :
      CAM_config ge -> CAM_config ge -> Prop :=
  | CAM_atomic_read tp m mu c ly l v K :
      tp !! i = Some (source_running c []) ->
      clight_at_external c = Some (ALoad ly l, K) ->
      readable mu (layout_to_locs l ly) ->
      load m l ly = Some v ->
      clight_val_defined v ->
      CAM_atomic_step_at i
        {| CAM_threads := tp; CAM_memory := m; CAM_rw := mu |}
        {| CAM_threads := <[i := source_running (K (Some v)) []]> tp;
           CAM_memory := m; CAM_rw := mu |}
  | CAM_atomic_write tp m mu c ly l v m' K :
      tp !! i = Some (source_running c []) ->
      clight_at_external c = Some (AStore ly l v, K) ->
      writable mu (layout_to_locs l ly) ->
      store m l ly v = Some m' ->
      clight_val_defined v ->
      CAM_atomic_step_at i
        {| CAM_threads := tp; CAM_memory := m; CAM_rw := mu |}
        {| CAM_threads := <[i := source_running (K None) []]> tp;
           CAM_memory := m'; CAM_rw := mu |}
  | CAM_atomic_CAS_success tp m mu c ly l expected new current m' K :
      tp !! i = Some (source_running c []) ->
      clight_at_external c = Some (ACAS ly l expected new, K) ->
      writable mu (layout_to_locs l ly) ->
      load m l ly = Some current ->
      clight_val_defined current ->
      clight_ValEq c m current expected ->
      store m l ly new = Some m' ->
      clight_val_defined new ->
      CAM_atomic_step_at i
        {| CAM_threads := tp; CAM_memory := m; CAM_rw := mu |}
        {| CAM_threads := <[i := source_running (K (Some Vtrue)) []]> tp;
           CAM_memory := m'; CAM_rw := mu |}
  | CAM_atomic_CAS_failure tp m mu c ly l expected new current K :
      tp !! i = Some (source_running c []) ->
      clight_at_external c = Some (ACAS ly l expected new, K) ->
      readable mu (layout_to_locs l ly) ->
      load m l ly = Some current ->
      clight_val_defined current ->
      clight_ValNEq c m current expected ->
      CAM_atomic_step_at i
        {| CAM_threads := tp; CAM_memory := m; CAM_rw := mu |}
        {| CAM_threads := <[i := source_running (K (Some Vfalse)) []]> tp;
           CAM_memory := m; CAM_rw := mu |}.

  Definition CAM_pool_matches_except
      (stp : CAM_tpool ge) (ttp : @ThreadPool.t GE)
      (selected : nat) : Prop :=
    (forall i, i <> selected ->
      CAM_option_stack_matches (stp !! i)
        (ThreadPool.get_cs ttp (CAM_tid i))) /\
    (forall i,
      (exists sst, stp !! i = Some sst) <->
      ThreadPool.valid_tid ttp (CAM_tid i)).

  (** During a target critical section, the selected source core need not
      equal the client core suspended below the wrapper: the source can be
      placed on either side of the atomic linearization point.  The relation
      still requires an actual marker-enabled wrapper over a canonical atomic
      client call, and relates every nonselected thread exactly. *)
  Record CAM_crit_match sc tc : Prop := {
    CAM_crit_bit : atom_bit tc = I;
    CAM_crit_memory : CAM_memory_match (CAM_memory sc) (gm tc);
    CAM_crit_selected : exists selected score
        twrapper_frame tclient_frame tcore,
      CAM_threads sc !! selected =
        Some (source_running score []) /\
      cur_tid tc = CAM_tid selected /\
      CAM_pool_matches_except (CAM_threads sc)
        (thread_pool tc) selected /\
      CAM_wrapper_frame twrapper_frame /\
      CAM_supported_atomic_call tcore /\
      CAM_atomic_phase_matches score tcore /\
      CAM_client_frame_matches tcore tclient_frame /\
      ThreadPool.get_cs (thread_pool tc) (CAM_tid selected) =
        Some [twrapper_frame; tclient_frame]
  }.

  (** This is only a relation between configurations: it contains no target
      path, source transition, or future endpoint.  No theorem below claims
      that every intermediate state in its returned target star satisfies the
      crit constructor. *)
  Inductive match_config : CAM_config ge -> @ProgConfig GE -> Prop :=
  | CAM_match_uncrit sc tc :
      CAM_uncrit_match sc tc ->
      match_config sc tc
  | CAM_match_crit sc tc :
      CAM_crit_match sc tc ->
      match_config sc tc.

End CAMConfigurationRelation.

Lemma CAM_tid_injective i j : CAM_tid i = CAM_tid j -> i = j.
Proof. apply SuccNat2Pos.inj. Qed.

Lemma CAM_supported_atomic_call_not_halted c :
  CAM_supported_atomic_call c ->
  ClightLang.halted (s2t_core c) = None.
Proof. intros Hcall; inversion Hcall; reflexivity. Qed.

Section CAMUncritLemmas.

  Context {ge : Clight.genv} {GE : GlobEnv.t}.
  Implicit Types (sc : CAM_config ge) (tc : @ProgConfig GE).

  Local Definition CAM_q_running
      (score : Clight_core.CC_core) (T : list (@mem_ev address)) :=
    @Running address val _ _ mem memory_chunk clight_mem_mixin
      (Clight_language ge) score T.

  Lemma CAM_uncrit_atomic_frame sc tc i score :
    CAM_uncrit_match sc tc ->
    CAM_threads sc !! i = Some (CAM_q_running score []) ->
    CAM_supported_atomic_call score ->
    exists (client_ix : 'I_(GlobEnv.M GE))
           (raw_ge : Genv.t Clight.fundef Ctypes.type)
           (client_ge : Clight.genv)
           (Hmodule : GlobEnv.modules GE client_ix =
             ModSem.Build_t ClightLang.Clight_IS_2 raw_ge client_ge) sg F,
      nat_of_ord client_ix = 0 /\
      ThreadPool.get_cs (thread_pool tc) (CAM_tid i) =
        Some
          [Core.Build_t client_ix
            (ClightAtomicGlobalCalls.runtime_core client_ix
              ClightLang.Clight_IS_2 raw_ge client_ge
              Hmodule
              (s2t_core score)) sg F].
  Proof.
    intros Hq Hget Hsupported.
    destruct Hq as [Hbit Hmemory [Hstacks Hdomain] Hcurrent].
    specialize (Hstacks i).
    rewrite Hget in Hstacks.
    destruct (ThreadPool.get_cs (thread_pool tc) (CAM_tid i)) as [tcs|]
      eqn:Htcs; simpl in Hstacks; try contradiction.
    destruct Hstacks as [(tframe & Hframe & ->) | [Hhalt ->]].
    - inversion Hframe; subst tframe.
      exists client_ix, raw_ge, client_ge, Hmodule, sg, F.
      split; [assumption | reflexivity].
    - rewrite (CAM_supported_atomic_call_not_halted _ Hsupported) in Hhalt.
      contradiction.
  Qed.

  Lemma CAM_thread_with_frame_not_halted
      (ttp : @ThreadPool.t GE) t tframe
      (Htcs : ThreadPool.get_cs ttp t = Some [tframe]) :
    ~ ThreadPool.halted ttp t.
  Proof.
    intros Hhalt. inversion Hhalt; subst.
    rewrite Htcs in H. inversion H. subst cs.
    discriminate.
  Qed.

  Lemma CAM_atomic_pool_after
      (stp : CAM_tpool ge) (ttp ttp' : @ThreadPool.t GE)
      i score score' tframe'
      (Hpool : CAM_pool_matches stp ttp)
      (Hget : stp !! i = Some (CAM_q_running score []))
      (Hframe' : CAM_client_frame_matches score' tframe')
      (Hselected : ThreadPool.get_cs ttp' (CAM_tid i) =
        Some [tframe'])
      (Hother : forall other, other <> CAM_tid i ->
        ThreadPool.get_cs ttp' other =
          ThreadPool.get_cs ttp other)
      (Hnext : ThreadPool.next_tid ttp' =
        ThreadPool.next_tid ttp) :
    CAM_pool_matches (<[i := CAM_q_running score' []]> stp) ttp'.
  Proof.
    destruct Hpool as [Hstacks Hdomain]. split.
    - intros j. destruct (Nat.eq_dec j i) as [-> | Hji].
      + assert (Hlookup :
          (<[i := CAM_q_running score' []]> stp) !! i =
            Some (CAM_q_running score' [])).
        { apply (lookup_insert_eq (K := nat) (M := gmap nat)). }
        rewrite Hlookup.
        rewrite Hselected. simpl.
        left. exists tframe'. auto.
      + assert (Hlookup :
          (<[i := CAM_q_running score' []]> stp) !! j = stp !! j).
        { apply (lookup_insert_ne (K := nat) (M := gmap nat)). congruence. }
        rewrite Hlookup.
        rewrite Hother.
        * apply Hstacks.
        * intros Htid. apply CAM_tid_injective in Htid. contradiction.
    - intros j. unfold ThreadPool.valid_tid. rewrite Hnext.
      destruct (Nat.eq_dec j i) as [-> | Hji].
      + split; intros _.
        * apply (proj1 (Hdomain i)).
          exists (CAM_q_running score []). exact Hget.
        * exists (CAM_q_running score' []).
          apply (lookup_insert_eq (K := nat) (M := gmap nat)).
      + assert (Hlookup :
          (<[i := CAM_q_running score' []]> stp) !! j = stp !! j).
        { apply (lookup_insert_ne (K := nat) (M := gmap nat)). congruence. }
        rewrite Hlookup.
        apply Hdomain.
  Qed.

  Lemma CAM_pool_after_commit
      (stp : CAM_tpool ge) (ttp : @ThreadPool.t GE)
      i score T
      (Hpool : CAM_pool_matches stp ttp)
      (Hget : stp !! i = Some (CAM_q_running score T)) :
    CAM_pool_matches (<[i := CAM_q_running score []]> stp) ttp.
  Proof.
    destruct Hpool as [Hstacks Hdomain]. split.
    - intros j. destruct (Nat.eq_dec j i) as [-> | Hji].
      + assert (Hlookup :
          (<[i := CAM_q_running score []]> stp) !! i =
            Some (CAM_q_running score [])).
        { apply (lookup_insert_eq (K := nat) (M := gmap nat)). }
        rewrite Hlookup.
        specialize (Hstacks i). rewrite Hget in Hstacks.
        exact Hstacks.
      + assert (Hlookup :
          (<[i := CAM_q_running score []]> stp) !! j = stp !! j).
        { apply (lookup_insert_ne (K := nat) (M := gmap nat)). congruence. }
        rewrite Hlookup. apply Hstacks.
    - intros j. destruct (Nat.eq_dec j i) as [-> | Hji].
      + split; intros _.
        * apply (proj1 (Hdomain i)).
          exists (CAM_q_running score T). exact Hget.
        * exists (CAM_q_running score []).
          apply (lookup_insert_eq (K := nat) (M := gmap nat)).
      + assert (Hlookup :
          (<[i := CAM_q_running score []]> stp) !! j = stp !! j).
        { apply (lookup_insert_ne (K := nat) (M := gmap nat)). congruence. }
        rewrite Hlookup. apply Hdomain.
  Qed.

  Lemma CAM_current_after_commit
      (stp : CAM_tpool ge) tc i score T
      (Hcurrent : CAM_current_thread_in_pool stp tc)
      (Hget : stp !! i = Some (CAM_q_running score T)) :
    CAM_current_thread_in_pool (<[i := CAM_q_running score []]> stp) tc.
  Proof.
    destruct Hcurrent as (j & sst & Hj & Hcur).
    destruct (Nat.eq_dec j i) as [-> | Hji].
    - exists i, (CAM_q_running score []). split.
      + apply (lookup_insert_eq (K := nat) (M := gmap nat)).
      + exact Hcur.
    - exists j, sst. split; [| exact Hcur].
      assert (Hlookup :
        (<[i := CAM_q_running score []]> stp) !! j = stp !! j).
      { apply (lookup_insert_ne (K := nat) (M := gmap nat)). congruence. }
      rewrite Hlookup. exact Hj.
  Qed.

End CAMUncritLemmas.

(** ** The two remaining representation bridges

    The wrapper proofs execute over a freelist-indexed [FMemory.Mem.mem],
    whereas CAM executes over CompCert [Mem.mem].  This record says only how
    loads and stores at an identity-related atomic address are transported.
    It does not postulate any target execution or impose a value-shape
    restriction.  Definedness is now a premise of the atomic-machine rules,
    and a taken CAS branch obtains its integer shape from the declaration-
    typed comparison. *)

Record CAM_atomic_memory_view {GE : GlobEnv.t}
    (sm : mem) (tc : @ProgConfig GE) (i : nat) : Type := {
  CAM_view_fmemory : FMemory.Mem.mem;
  CAM_view_embed :
    FMemory.embed (gm tc)
      (FLists.get_fl (GlobEnv.freelists GE)
        (FLists.get_tfid (GlobEnv.freelists GE) (CAM_tid i)
          (ThreadPool.next_fmap (thread_pool tc) (CAM_tid i))))
      CAM_view_fmemory;
  CAM_view_load : forall b ofs v,
    Mem.loadv Mint32 sm (Vptr b ofs) = Some v ->
    FMemory.Mem.loadv Mint32 CAM_view_fmemory (Vptr b ofs) = Some v;
  CAM_view_store : forall b ofs v sm',
    Mem.storev Mint32 sm (Vptr b ofs) v = Some sm' ->
    exists tfm',
      FMemory.Mem.storev Mint32 CAM_view_fmemory (Vptr b ofs) v =
        Some tfm' /\
      FMemory.embed (FMemory.strip tfm')
        (FLists.get_fl (GlobEnv.freelists GE)
          (FLists.get_tfid (GlobEnv.freelists GE) (CAM_tid i)
            (ThreadPool.next_fmap (thread_pool tc) (CAM_tid i)))) tfm' /\
      CAM_memory_match sm' (FMemory.strip tfm')
}.

Definition CAM_atomic_memory_views
    {ge : Clight.genv} {GE : GlobEnv.t}
    (sc : CAM_config ge) (tc : @ProgConfig GE) : Type :=
  forall i score,
    CAM_threads sc !! i =
      Some (@Running address val _ _ mem memory_chunk clight_mem_mixin
        (Clight_language ge) score []) ->
    CAM_supported_atomic_call score ->
    CAM_atomic_memory_view (CAM_memory sc) tc i.

(** The view provider is restricted to target configurations reachable from
    the initialized configuration.  This avoids demanding fresh-freelist
    embeddings for arbitrary records that happen to satisfy the extensional
    configuration relation but violate target runtime invariants. *)
Definition CAM_atomic_memory_views_from
    {ge : Clight.genv} {GE : GlobEnv.t}
    (tc_initial : @ProgConfig GE) : Type :=
  forall (sc : CAM_config ge) (tc : @ProgConfig GE) labels fp,
    ETrace.star (@glob_step GE) tc_initial labels fp tc ->
    CAM_uncrit_match sc tc ->
    CAM_atomic_memory_views sc tc.

(** [Core_Try] is precisely the missing VST-Clight/CAS-Clight semantic
    interoperability lemma.  Atomic calls and [Core_Commit] are deliberately
    absent: the former are proved using the translated wrappers below, and
    the latter is target stuttering because pending events and [CAM_rw] are
    erased by the relation. *)
Inductive CAM_core_try_step (ge : Clight.genv) :
    CAM_config ge -> CAM_config ge -> Prop :=
| CAM_core_try_intro : forall tp m mu i c T c' m' mu',
    tp !! i =
      Some (@Running address val _ _ mem memory_chunk clight_mem_mixin
        (Clight_language ge) c []) ->
    ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge) c m T c' m' ->
    rsv T mu = Some mu' ->
    CAM_core_try_step ge
      {| CAM_threads := tp; CAM_memory := m; CAM_rw := mu |}
      {| CAM_threads := <[i :=
           @Running address val _ _ mem memory_chunk clight_mem_mixin
             (Clight_language ge) c' T]> tp;
         CAM_memory := m'; CAM_rw := mu' |}.

Definition CAM_core_try_refinement_at
    {ge : Clight.genv} {GE : GlobEnv.t}
    (sc1 : CAM_config ge) (tc : @ProgConfig GE) : Prop :=
  forall (sc2 : CAM_config ge),
    CAM_core_try_step ge sc1 sc2 ->
    CAM_assign_loc_value_syntax sc1 ->
    CAM_uncrit_match sc1 tc ->
    exists tc' labels fp,
      ETrace.star (@glob_step GE) tc labels fp tc' /\
      CAM_uncrit_match sc2 tc'.

(** Reachability- and program-indexed form of the ordinary-step bridge.  It
    is required only at target configurations reachable from the initialized
    [tc_initial], and its source [ge] is initialized from the same client [P]
    that is linked into the target. *)
Definition CAM_core_try_refinements_for_from
    (P : ClightLang.clight_comp_unit)
    (ge : Clight.genv) (GE : GlobEnv.t)
    (tc_initial : @ProgConfig GE) : Prop :=
  forall raw_ge,
    ClightLang.init_genv P raw_ge ge ->
    forall (sc : CAM_config ge) (tc : @ProgConfig GE) labels fp,
      ETrace.star (@glob_step GE) tc_initial labels fp tc ->
      CAM_core_try_refinement_at sc tc.

Lemma CAM_core_commit_stutters
    {ge : Clight.genv} {GE : GlobEnv.t}
    stp sm mu i score T mu' (tc : @ProgConfig GE)
    (Hget : stp !! i =
      Some (@Running address val _ _ mem memory_chunk clight_mem_mixin
        (Clight_language ge) score T))
    (Hq : CAM_uncrit_match
      {| CAM_threads := stp; CAM_memory := sm; CAM_rw := mu |} tc) :
  exists labels fp,
    ETrace.star (@glob_step GE) tc labels fp tc /\
    CAM_uncrit_match
      {| CAM_threads := <[i :=
           @Running address val _ _ mem memory_chunk clight_mem_mixin
             (Clight_language ge) score []]> stp;
         CAM_memory := sm; CAM_rw := mu' |} tc.
Proof.
  exists [], FP.emp. split; [constructor |].
  destruct Hq as [Hbit Hmemory Hpool Hcurrent].
  change (CAM_memory_match sm (gm tc)) in Hmemory.
  change (CAM_pool_matches stp (thread_pool tc)) in Hpool.
  change (CAM_current_thread_in_pool stp tc) in Hcurrent.
  refine (@Build_CAM_uncrit_match ge GE
    {| CAM_threads := <[i :=
         @Running address val _ _ mem memory_chunk clight_mem_mixin
           (Clight_language ge) score []]> stp;
       CAM_memory := sm; CAM_rw := mu' |} tc Hbit Hmemory _ _).
  - eapply CAM_pool_after_commit; eauto.
  - eapply CAM_current_after_commit; eauto.
Qed.

(** ** Trace composition *)

Section CAMTraceComposition.

  Context {ge : Clight.genv} {GE : GlobEnv.t}.
  Implicit Types (tc : @ProgConfig GE).

  Lemma CAM_etrace_star_trans
      tc1 tc2 tc3
      labels1 fp1 labels2 fp2 :
    ETrace.star (@glob_step GE) tc1 labels1 fp1 tc2 ->
    ETrace.star (@glob_step GE) tc2 labels2 fp2 tc3 ->
    ETrace.star (@glob_step GE) tc1 (labels1 ++ labels2)
      (FP.union fp1 fp2) tc3.
  Proof.
    intros Hstar1 Hstar2.
    induction Hstar1.
    - rewrite FP.emp_union_fp. exact Hstar2.
    - simpl. rewrite <- FP.fp_union_assoc.
      econstructor; eauto.
  Qed.

End CAMTraceComposition.

(** ** The program translation and top-level theorem *)

Definition CAM_translated_program
    (P : ClightLang.clight_comp_unit)
    (ids : ClightAtomicWrappers.wrapper_ids)
    (thread_entries : GAST.entries) :=
  ClightAtomicTarget.linked_program [P] ids thread_entries.

Definition CAM_source_program_initialized
    (P : ClightLang.clight_comp_unit) (ge : Clight.genv) : Prop :=
  exists raw_ge, ClightLang.init_genv P raw_ge ge.

Lemma CAM_translated_program_shape P ids thread_entries :
  CAM_translated_program P ids thread_entries =
    ([ClightAtomicTarget.client_unit P;
      ClightAtomicTarget.wrapper_unit ids], thread_entries).
Proof. reflexivity. Qed.

Lemma CAM_translated_program_init_GE P ids thread_entries m GE tc t :
  init_config (CAM_translated_program P ids thread_entries) m GE tc t ->
  GlobEnv.init (ClightAtomicTarget.linked_units [P] ids) GE.
Proof. inversion 1; assumption. Qed.

(** Static runtime facts extracted from initialization of [P'] rather than
    assumed as part of a simulation relation. *)
Definition CAM_initialized_wrapper
    (ids : Wrappers.wrapper_ids) (GE : GlobEnv.t) : Prop :=
  exists (wrapper_ix : 'I_(GlobEnv.M GE))
         (raw_ge : Genv.t Clight.fundef Ctypes.type)
         (wrapper_ge : Clight.genv),
    nat_of_ord wrapper_ix = 1 /\
    GlobEnv.modules GE wrapper_ix =
      ModSem.Build_t Clight_IS_2_with_markers raw_ge wrapper_ge /\
    InteractionSemantics.init_genv Clight_IS_2_with_markers
      (Wrappers.wrapper_comp_unit ids) raw_ge wrapper_ge /\
    GlobEnv.get_mod GE (Wrappers.atomic_load_id ids) = Some wrapper_ix /\
    GlobEnv.get_mod GE (Wrappers.atomic_store_id ids) = Some wrapper_ix /\
    GlobEnv.get_mod GE (Wrappers.atomic_CAS_id ids) = Some wrapper_ix.

Lemma CAM_initialized_wrapper_of_link
    P ids GE
    (Hinit : GlobEnv.init
      (ClightAtomicTarget.linked_units [P] ids) GE)
    (Hreserve :
      ClightAtomicTarget.clients_reserve_wrapper_ids [P] ids)
    (Hids : Wrappers.wrapper_ids_wf ids) :
  CAM_initialized_wrapper ids GE.
Proof.
  exact (ClightAtomicTarget.initialized_linked_units_have_owned_wrapper
    [P] ids GE Hinit Hreserve Hids).
Qed.

Lemma CAM_initialized_client_resolution_at
    P ids GE
    (Hinit : GlobEnv.init
      (ClightAtomicTarget.linked_units [P] ids) GE)
    (Hdecls : ClientInit.client_atomic_declarations ids P)
    (client_ix : 'I_(GlobEnv.M GE))
    (raw_ge : Genv.t Clight.fundef Ctypes.type)
    (client_ge : Clight.genv)
    (Hix : nat_of_ord client_ix = 0)
    (Hmodule : GlobEnv.modules GE client_ix =
      ModSem.Build_t ClightLang.Clight_IS_2 raw_ge client_ge) :
  ClightLang.invert_symbol_from_string (Clight.genv_genv client_ge)
      "atomic_load" =
      Some (Wrappers.atomic_load_id ids) /\
  ClightLang.invert_symbol_from_string (Clight.genv_genv client_ge)
      "atomic_store" =
      Some (Wrappers.atomic_store_id ids) /\
  ClightLang.invert_symbol_from_string (Clight.genv_genv client_ge)
      "atomic_CAS" =
      Some (Wrappers.atomic_CAS_id ids).
Proof.
  destruct (GlobEnv.ge_init
    (ClightAtomicTarget.linked_units [P] ids) GE Hinit client_ix)
    as [cui [Hnth Hmod]].
  change (nth_error (ClightAtomicTarget.linked_units [P] ids)
    (nat_of_ord client_ix) = Some cui) in Hnth.
  rewrite Hix,
    (ClightAtomicTarget.linked_units_client_nth_error
      [P] ids 0 P eq_refl) in Hnth.
  inversion Hnth; subst cui; clear Hnth.
  change (ModSem.init_modsem ClightLang.Clight_IS_2 P
    (GlobEnv.modules GE client_ix)) in Hmod.
  rewrite Hmodule in Hmod.
  inversion Hmod; subst.
  apply inj_pairT2 in H. apply inj_pairT2 in H1. subst.
  eapply ClientInit.initialized_client_atomic_resolution; eauto.
Qed.

Section CAMInitializedAtomicEndpoints.

  Context {ge : Clight.genv} {GE : GlobEnv.t}.
  Implicit Types (sc : CAM_config ge) (tc : @ProgConfig GE).
  Variables P : ClightLang.clight_comp_unit.
  Variable ids : Wrappers.wrapper_ids.
  Hypothesis HGEinit : GlobEnv.init
    (ClightAtomicTarget.linked_units [P] ids) GE.
  Hypothesis Hids : Wrappers.wrapper_ids_wf ids.
  Hypothesis Hdecls : ClientInit.client_atomic_declarations ids P.
  Hypothesis Hwrapper : CAM_initialized_wrapper ids GE.

  Local Definition CAM_endpoint_running
      (score : Clight_core.CC_core) (T : list (@mem_ev address)) :=
    @Running address val _ _ mem memory_chunk clight_mem_mixin
      (Clight_language ge) score T.

  Lemma CAM_initialized_atomic_load_endpoint
      stp sm mu tc i b ofs v k
      (Hq : CAM_uncrit_match
        {| CAM_threads := stp; CAM_memory := sm; CAM_rw := mu |} tc)
      (Hget : stp !! i = Some
        (CAM_endpoint_running
          (Clight_core.Callstate Wrappers.client_atomic_load_external
            [Vptr b ofs] k) []))
      (Hload : Mem.load Mint32 sm b (Ptrofs.unsigned ofs) = Some v)
      (Hdefined : clight_val_defined v)
      (Hview : CAM_atomic_memory_view sm tc i) :
    exists tc' labels fp,
      ETrace.star (@glob_step GE) tc labels fp tc' /\
      CAM_uncrit_match
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate v k) []]> stp;
           CAM_memory := sm; CAM_rw := mu |} tc'.
  Proof.
    destruct Hwrapper as
      (wrapper_ix & wrapper_raw_ge & wrapper_ge & Hwrapper_ix &
       Hwrapper_module & Hwrapper_init & Hload_owner & Hstore_owner &
       HCAS_owner).
    pose proof (CAM_supported_load_call b ofs k) as Hsupported.
    destruct (CAM_uncrit_atomic_frame _ _ _ _ Hq Hget Hsupported) as
      (client_ix & caller_raw_ge & caller_ge & Hcaller_module & caller_sg &
       caller_F & Hclient_ix & Hcs).
    destruct (CAM_initialized_client_resolution_at P ids GE HGEinit Hdecls
      client_ix caller_raw_ge caller_ge Hclient_ix Hcaller_module) as
      (Hload_resolve & Hstore_resolve & HCAS_resolve).
    destruct Hview as [tfm Hembed Hload_view Hstore_view].
    assert (Hsource_loadv :
      Mem.loadv Mint32 sm (Vptr b ofs) = Some v).
    { exact Hload. }
    pose proof (Hload_view b ofs v Hsource_loadv) as Hfload.
    pose proof (clight_val_defined_as_target_boolean v Hdefined)
      as Htarget_defined.
    cbn [s2t_core] in Hcs.
    destruct (InitializedCalls.initialized_atomic_load_global_call_and_return
      client_ix wrapper_ix caller_raw_ge wrapper_raw_ge caller_ge wrapper_ge
      Hcaller_module Hwrapper_module ids Hids Hwrapper_init Hload_owner
      Hload_resolve (gm tc) tfm b ofs v Hfload Htarget_defined
      (thread_pool tc) (CAM_tid i)
      caller_F caller_sg [] k Hembed Hcs) as (ttp' & fp & Htau & Hcs').
    destruct Hq as [Hbit Hmemory Hpool Hcurrent].
    change (CAM_memory_match sm (gm tc)) in Hmemory.
    change (CAM_pool_matches stp (thread_pool tc)) in Hpool.
    assert (Hvalid : ThreadPool.valid_tid (thread_pool tc) (CAM_tid i)).
    { apply (proj1 (proj2 Hpool i)).
      exists (CAM_endpoint_running
        (Clight_core.Callstate Wrappers.client_atomic_load_external
          [Vptr b ofs] k) []). exact Hget. }
    assert (Hnot_halted :
      ~ ThreadPool.halted (thread_pool tc) (CAM_tid i)).
    { eapply CAM_thread_with_frame_not_halted; exact Hcs. }
    destruct (GlobalSteps.scheduled_tau_star_with_pool_preservation
      (thread_pool tc) ttp' (cur_tid tc) (CAM_tid i) (gm tc) (gm tc) fp
      Hvalid Hnot_halted Htau) as
      (labels & Hstar & Hother & Hnext & Hfmap).
    set (return_frame := Core.Build_t client_ix
      (ClightAtomicGlobalCalls.runtime_core client_ix
        ClightLang.Clight_IS_2 caller_raw_ge caller_ge Hcaller_module
        (ClightLang.Core_Returnstate v k)) caller_sg caller_F).
    assert (Hreturn_frame :
      CAM_client_frame_matches (Clight_core.Returnstate v k)
        return_frame).
    { unfold return_frame. constructor; assumption. }
    exists (Build_ProgConfig GE ttp' (CAM_tid i) (gm tc) O),
      (ETrace.sw :: labels), fp.
    split.
    - replace tc with
        (Build_ProgConfig GE (thread_pool tc) (cur_tid tc) (gm tc) O).
      + exact Hstar.
      + destruct tc. cbn in *. subst. reflexivity.
    - refine (@Build_CAM_uncrit_match ge GE
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate v k) []]> stp;
           CAM_memory := sm; CAM_rw := mu |}
        (Build_ProgConfig GE ttp' (CAM_tid i) (gm tc) O)
        eq_refl Hmemory _ _).
      + eapply CAM_atomic_pool_after; eauto.
      + exists i, (CAM_endpoint_running
          (Clight_core.Returnstate v k) []).
        split.
        * apply (lookup_insert_eq (K := nat) (M := gmap nat)).
        * reflexivity.
  Qed.

  Lemma CAM_initialized_atomic_store_endpoint
      stp sm sm' mu tc i b ofs n k
      (Hq : CAM_uncrit_match
        {| CAM_threads := stp; CAM_memory := sm; CAM_rw := mu |} tc)
      (Hget : stp !! i = Some
        (CAM_endpoint_running
          (Clight_core.Callstate Wrappers.client_atomic_store_external
            [Vptr b ofs; Vint n] k) []))
      (Hstore :
        Mem.store Mint32 sm b (Ptrofs.unsigned ofs) (Vint n) = Some sm')
      (Hview : CAM_atomic_memory_view sm tc i) :
    exists tc' labels fp,
      ETrace.star (@glob_step GE) tc labels fp tc' /\
      CAM_uncrit_match
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate Vundef k) []]> stp;
           CAM_memory := sm'; CAM_rw := mu |} tc'.
  Proof.
    destruct Hwrapper as
      (wrapper_ix & wrapper_raw_ge & wrapper_ge & Hwrapper_ix &
       Hwrapper_module & Hwrapper_init & Hload_owner & Hstore_owner &
       HCAS_owner).
    pose proof (CAM_supported_store_call b ofs n k) as Hsupported.
    destruct (CAM_uncrit_atomic_frame _ _ _ _ Hq Hget Hsupported) as
      (client_ix & caller_raw_ge & caller_ge & Hcaller_module & caller_sg &
       caller_F & Hclient_ix & Hcs).
    destruct (CAM_initialized_client_resolution_at P ids GE HGEinit Hdecls
      client_ix caller_raw_ge caller_ge Hclient_ix Hcaller_module) as
      (Hload_resolve & Hstore_resolve & HCAS_resolve).
    destruct Hview as [tfm Hembed Hload_view Hstore_view].
    assert (Hsource_storev :
      Mem.storev Mint32 sm (Vptr b ofs) (Vint n) = Some sm').
    { exact Hstore. }
    destruct (Hstore_view b ofs (Vint n) sm' Hsource_storev) as
      (tfm' & Hfstore & Hembed' & Hmemory').
    cbn [s2t_core] in Hcs.
    destruct (InitializedCalls.initialized_atomic_store_global_call_and_return
      client_ix wrapper_ix caller_raw_ge wrapper_raw_ge caller_ge wrapper_ge
      Hcaller_module Hwrapper_module ids Hids Hwrapper_init Hstore_owner
      Hstore_resolve (gm tc) (FMemory.strip tfm') tfm tfm' b ofs n Hfstore
      (thread_pool tc) (CAM_tid i) caller_F caller_sg [] k Hembed Hembed' Hcs)
      as (ttp' & fp & Htau & Hcs').
    destruct Hq as [Hbit Hmemory Hpool Hcurrent].
    change (CAM_pool_matches stp (thread_pool tc)) in Hpool.
    assert (Hvalid : ThreadPool.valid_tid (thread_pool tc) (CAM_tid i)).
    { apply (proj1 (proj2 Hpool i)).
      exists (CAM_endpoint_running
        (Clight_core.Callstate Wrappers.client_atomic_store_external
          [Vptr b ofs; Vint n] k) []). exact Hget. }
    assert (Hnot_halted :
      ~ ThreadPool.halted (thread_pool tc) (CAM_tid i)).
    { eapply CAM_thread_with_frame_not_halted; exact Hcs. }
    destruct (GlobalSteps.scheduled_tau_star_with_pool_preservation
      (thread_pool tc) ttp' (cur_tid tc) (CAM_tid i) (gm tc)
      (FMemory.strip tfm') fp Hvalid Hnot_halted Htau) as
      (labels & Hstar & Hother & Hnext & Hfmap).
    set (return_frame := Core.Build_t client_ix
      (ClightAtomicGlobalCalls.runtime_core client_ix
        ClightLang.Clight_IS_2 caller_raw_ge caller_ge Hcaller_module
        (ClightLang.Core_Returnstate Vundef k)) caller_sg caller_F).
    assert (Hreturn_frame :
      CAM_client_frame_matches (Clight_core.Returnstate Vundef k)
        return_frame).
    { unfold return_frame. constructor; assumption. }
    exists (Build_ProgConfig GE ttp' (CAM_tid i) (FMemory.strip tfm') O),
      (ETrace.sw :: labels), fp.
    split.
    - replace tc with
        (Build_ProgConfig GE (thread_pool tc) (cur_tid tc) (gm tc) O).
      + exact Hstar.
      + destruct tc. cbn in *. subst. reflexivity.
    - refine (@Build_CAM_uncrit_match ge GE
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate Vundef k) []]> stp;
           CAM_memory := sm'; CAM_rw := mu |}
        (Build_ProgConfig GE ttp' (CAM_tid i) (FMemory.strip tfm') O)
        eq_refl Hmemory' _ _).
      + eapply CAM_atomic_pool_after; eauto.
      + exists i, (CAM_endpoint_running
          (Clight_core.Returnstate Vundef k) []).
        split.
        * apply (lookup_insert_eq (K := nat) (M := gmap nat)).
        * reflexivity.
  Qed.

  Lemma CAM_initialized_atomic_CAS_success_endpoint
      stp sm sm' mu tc i b ofs expected new k
      (Hq : CAM_uncrit_match
        {| CAM_threads := stp; CAM_memory := sm; CAM_rw := mu |} tc)
      (Hget : stp !! i = Some
        (CAM_endpoint_running
          (Clight_core.Callstate Wrappers.client_atomic_CAS_external
            [Vptr b ofs; Vint expected; Vint new] k) []))
      (Hload :
        Mem.load Mint32 sm b (Ptrofs.unsigned ofs) = Some (Vint expected))
      (Hstore :
        Mem.store Mint32 sm b (Ptrofs.unsigned ofs) (Vint new) = Some sm')
      (Hview : CAM_atomic_memory_view sm tc i) :
    exists tc' labels fp,
      ETrace.star (@glob_step GE) tc labels fp tc' /\
      CAM_uncrit_match
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate Vtrue k) []]> stp;
           CAM_memory := sm'; CAM_rw := mu |} tc'.
  Proof.
    destruct Hwrapper as
      (wrapper_ix & wrapper_raw_ge & wrapper_ge & Hwrapper_ix &
       Hwrapper_module & Hwrapper_init & Hload_owner & Hstore_owner &
       HCAS_owner).
    pose proof (CAM_supported_CAS_call b ofs expected new k) as Hsupported.
    destruct (CAM_uncrit_atomic_frame _ _ _ _ Hq Hget Hsupported) as
      (client_ix & caller_raw_ge & caller_ge & Hcaller_module & caller_sg &
       caller_F & Hclient_ix & Hcs).
    destruct (CAM_initialized_client_resolution_at P ids GE HGEinit Hdecls
      client_ix caller_raw_ge caller_ge Hclient_ix Hcaller_module) as
      (Hload_resolve & Hstore_resolve & HCAS_resolve).
    destruct Hview as [tfm Hembed Hload_view Hstore_view].
    assert (Hsource_loadv :
      Mem.loadv Mint32 sm (Vptr b ofs) = Some (Vint expected)).
    { exact Hload. }
    pose proof (Hload_view b ofs (Vint expected) Hsource_loadv) as Hfload.
    assert (Hsource_storev :
      Mem.storev Mint32 sm (Vptr b ofs) (Vint new) = Some sm').
    { exact Hstore. }
    destruct (Hstore_view b ofs (Vint new) sm' Hsource_storev) as
      (tfm' & Hfstore & Hembed' & Hmemory').
    cbn [s2t_core] in Hcs.
    destruct
      (InitializedCalls.initialized_atomic_CAS_success_global_call_and_return
        client_ix wrapper_ix caller_raw_ge wrapper_raw_ge caller_ge wrapper_ge
        Hcaller_module Hwrapper_module ids Hids Hwrapper_init HCAS_owner
        HCAS_resolve (gm tc) tfm tfm' b ofs expected new Hfload Hfstore
        (thread_pool tc) (CAM_tid i) caller_F caller_sg [] k Hembed Hcs)
      as (ttp' & fp & Htau & Hcs').
    destruct Hq as [Hbit Hmemory Hpool Hcurrent].
    change (CAM_pool_matches stp (thread_pool tc)) in Hpool.
    assert (Hvalid : ThreadPool.valid_tid (thread_pool tc) (CAM_tid i)).
    { apply (proj1 (proj2 Hpool i)).
      exists (CAM_endpoint_running
        (Clight_core.Callstate Wrappers.client_atomic_CAS_external
          [Vptr b ofs; Vint expected; Vint new] k) []). exact Hget. }
    assert (Hnot_halted :
      ~ ThreadPool.halted (thread_pool tc) (CAM_tid i)).
    { eapply CAM_thread_with_frame_not_halted; exact Hcs. }
    destruct (GlobalSteps.scheduled_tau_star_with_pool_preservation
      (thread_pool tc) ttp' (cur_tid tc) (CAM_tid i) (gm tc)
      (FMemory.strip tfm') fp Hvalid Hnot_halted Htau) as
      (labels & Hstar & Hother & Hnext & Hfmap).
    set (return_frame := Core.Build_t client_ix
      (ClightAtomicGlobalCalls.runtime_core client_ix
        ClightLang.Clight_IS_2 caller_raw_ge caller_ge Hcaller_module
        (ClightLang.Core_Returnstate Vtrue k)) caller_sg caller_F).
    assert (Hreturn_frame :
      CAM_client_frame_matches (Clight_core.Returnstate Vtrue k)
        return_frame).
    { unfold return_frame. constructor; assumption. }
    exists (Build_ProgConfig GE ttp' (CAM_tid i) (FMemory.strip tfm') O),
      (ETrace.sw :: labels), fp.
    split.
    - replace tc with
        (Build_ProgConfig GE (thread_pool tc) (cur_tid tc) (gm tc) O).
      + exact Hstar.
      + destruct tc. cbn in *. subst. reflexivity.
    - refine (@Build_CAM_uncrit_match ge GE
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate Vtrue k) []]> stp;
           CAM_memory := sm'; CAM_rw := mu |}
        (Build_ProgConfig GE ttp' (CAM_tid i) (FMemory.strip tfm') O)
        eq_refl Hmemory' _ _).
      + eapply CAM_atomic_pool_after; eauto.
      + exists i, (CAM_endpoint_running
          (Clight_core.Returnstate Vtrue k) []).
        split.
        * apply (lookup_insert_eq (K := nat) (M := gmap nat)).
        * reflexivity.
  Qed.

  Lemma CAM_initialized_atomic_CAS_failure_endpoint
      stp sm mu tc i b ofs old expected new k
      (Hq : CAM_uncrit_match
        {| CAM_threads := stp; CAM_memory := sm; CAM_rw := mu |} tc)
      (Hget : stp !! i = Some
        (CAM_endpoint_running
          (Clight_core.Callstate Wrappers.client_atomic_CAS_external
            [Vptr b ofs; Vint expected; Vint new] k) []))
      (Hload : Mem.load Mint32 sm b (Ptrofs.unsigned ofs) = Some (Vint old))
      (Hneq : old <> expected)
      (Hview : CAM_atomic_memory_view sm tc i) :
    exists tc' labels fp,
      ETrace.star (@glob_step GE) tc labels fp tc' /\
      CAM_uncrit_match
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate Vfalse k) []]> stp;
           CAM_memory := sm; CAM_rw := mu |} tc'.
  Proof.
    destruct Hwrapper as
      (wrapper_ix & wrapper_raw_ge & wrapper_ge & Hwrapper_ix &
       Hwrapper_module & Hwrapper_init & Hload_owner & Hstore_owner &
       HCAS_owner).
    pose proof (CAM_supported_CAS_call b ofs expected new k) as Hsupported.
    destruct (CAM_uncrit_atomic_frame _ _ _ _ Hq Hget Hsupported) as
      (client_ix & caller_raw_ge & caller_ge & Hcaller_module & caller_sg &
       caller_F & Hclient_ix & Hcs).
    destruct (CAM_initialized_client_resolution_at P ids GE HGEinit Hdecls
      client_ix caller_raw_ge caller_ge Hclient_ix Hcaller_module) as
      (Hload_resolve & Hstore_resolve & HCAS_resolve).
    destruct Hview as [tfm Hembed Hload_view Hstore_view].
    assert (Hsource_loadv :
      Mem.loadv Mint32 sm (Vptr b ofs) = Some (Vint old)).
    { exact Hload. }
    pose proof (Hload_view b ofs (Vint old) Hsource_loadv) as Hfload.
    cbn [s2t_core] in Hcs.
    destruct
      (InitializedCalls.initialized_atomic_CAS_failure_global_call_and_return
        client_ix wrapper_ix caller_raw_ge wrapper_raw_ge caller_ge wrapper_ge
        Hcaller_module Hwrapper_module ids Hids Hwrapper_init HCAS_owner
        HCAS_resolve (gm tc) tfm b ofs old expected new Hneq Hfload
        (thread_pool tc) (CAM_tid i) caller_F caller_sg [] k Hembed Hcs)
      as (ttp' & fp & Htau & Hcs').
    destruct Hq as [Hbit Hmemory Hpool Hcurrent].
    change (CAM_memory_match sm (gm tc)) in Hmemory.
    change (CAM_pool_matches stp (thread_pool tc)) in Hpool.
    assert (Hvalid : ThreadPool.valid_tid (thread_pool tc) (CAM_tid i)).
    { apply (proj1 (proj2 Hpool i)).
      exists (CAM_endpoint_running
        (Clight_core.Callstate Wrappers.client_atomic_CAS_external
          [Vptr b ofs; Vint expected; Vint new] k) []). exact Hget. }
    assert (Hnot_halted :
      ~ ThreadPool.halted (thread_pool tc) (CAM_tid i)).
    { eapply CAM_thread_with_frame_not_halted; exact Hcs. }
    destruct (GlobalSteps.scheduled_tau_star_with_pool_preservation
      (thread_pool tc) ttp' (cur_tid tc) (CAM_tid i) (gm tc) (gm tc) fp
      Hvalid Hnot_halted Htau) as
      (labels & Hstar & Hother & Hnext & Hfmap).
    set (return_frame := Core.Build_t client_ix
      (ClightAtomicGlobalCalls.runtime_core client_ix
        ClightLang.Clight_IS_2 caller_raw_ge caller_ge Hcaller_module
        (ClightLang.Core_Returnstate Vfalse k)) caller_sg caller_F).
    assert (Hreturn_frame :
      CAM_client_frame_matches (Clight_core.Returnstate Vfalse k)
        return_frame).
    { unfold return_frame. constructor; assumption. }
    exists (Build_ProgConfig GE ttp' (CAM_tid i) (gm tc) O),
      (ETrace.sw :: labels), fp.
    split.
    - replace tc with
        (Build_ProgConfig GE (thread_pool tc) (cur_tid tc) (gm tc) O).
      + exact Hstar.
      + destruct tc. cbn in *. subst. reflexivity.
    - refine (@Build_CAM_uncrit_match ge GE
        {| CAM_threads := <[i := CAM_endpoint_running
             (Clight_core.Returnstate Vfalse k) []]> stp;
           CAM_memory := sm; CAM_rw := mu |}
        (Build_ProgConfig GE ttp' (CAM_tid i) (gm tc) O)
        eq_refl Hmemory _ _).
      + eapply CAM_atomic_pool_after; eauto.
      + exists i, (CAM_endpoint_running
          (Clight_core.Returnstate Vfalse k) []).
        split.
        * apply (lookup_insert_eq (K := nat) (M := gmap nat)).
        * reflexivity.
  Qed.

End CAMInitializedAtomicEndpoints.

Section CAMInitializedAtomicStep.

  Context {ge : Clight.genv} {GE : GlobEnv.t}.
  Implicit Types (sc : CAM_config ge) (tc : @ProgConfig GE).
  Variables P : ClightLang.clight_comp_unit.
  Variable ids : Wrappers.wrapper_ids.
  Hypothesis HGEinit : GlobEnv.init
    (ClightAtomicTarget.linked_units [P] ids) GE.
  Hypothesis Hids : Wrappers.wrapper_ids_wf ids.
  Hypothesis Hdecls : ClientInit.client_atomic_declarations ids P.
  Hypothesis Hwrapper : CAM_initialized_wrapper ids GE.

  Lemma CAM_initialized_atomic_step_refines
      (i : nat) sc1 sc2 tc :
    CAM_atomic_step_at i sc1 sc2 ->
    CAM_uncrit_match sc1 tc ->
    CAM_atomic_memory_views sc1 tc ->
    exists tc' labels fp,
      ETrace.star (@glob_step GE) tc labels fp tc' /\
      CAM_uncrit_match sc2 tc'.
  Proof.
    intros Hatomic Hq Hviews.
    destruct Hatomic as
      [stp sm mu c ly l v K Hget Hext Hreadable Hload Hdefined |
       stp sm mu c ly l v sm' K Hget Hext Hwritable Hstore Hdefined |
       stp sm mu c ly l expected new current sm' K Hget Hext Hwritable
         Hload Hdefined_current Heq Hstore Hdefined_new |
       stp sm mu c ly l expected new current K Hget Hext Hreadable
         Hload Hdefined_current Hneq].
    - pose proof (CAM_decoded_atomic_call_supported _ _ _ Hext)
        as Hsupported.
      destruct (CAM_supported_load_inv _ _ _ _ Hsupported Hext) as
        (b & ofs & k & Hc & Hly & Hl & HK).
      subst c ly l K.
      pose proof (Hviews i _ Hget Hsupported) as Hview.
      eapply (@CAM_initialized_atomic_load_endpoint ge GE P ids HGEinit
        Hids Hdecls Hwrapper); eauto.
    - pose proof (CAM_decoded_atomic_call_supported _ _ _ Hext)
        as Hsupported.
      destruct (CAM_supported_store_inv _ _ _ _ _ Hsupported Hext) as
        (b & ofs & n & k & Hc & Hly & Hl & Hv & HK).
      subst c ly l v K.
      pose proof (Hviews i _ Hget Hsupported) as Hview.
      eapply (@CAM_initialized_atomic_store_endpoint ge GE P ids HGEinit
        Hids Hdecls Hwrapper); eauto.
    - pose proof (CAM_decoded_atomic_call_supported _ _ _ Hext)
        as Hsupported.
      destruct (CAM_supported_CAS_inv _ _ _ _ _ _ Hsupported Hext) as
        (b & ofs & expected_int & new_int & k & Hc & Hly & Hl &
         Hexpected & Hnew & HK).
      subst c ly l expected new K.
      pose proof (clight_ValEq_CAS_Vint_same
        sm b ofs current expected_int new_int k Heq) as Hcurrent.
      subst current.
      pose proof (Hviews i _ Hget Hsupported) as Hview.
      eapply (@CAM_initialized_atomic_CAS_success_endpoint ge GE P ids
        HGEinit Hids Hdecls Hwrapper); eauto.
    - pose proof (CAM_decoded_atomic_call_supported _ _ _ Hext)
        as Hsupported.
      destruct (CAM_supported_CAS_inv _ _ _ _ _ _ Hsupported Hext) as
        (b & ofs & expected_int & new_int & k & Hc & Hly & Hl &
         Hexpected & Hnew & HK).
      subst c ly l expected new K.
      destruct (clight_ValNEq_CAS_Vint_different
        sm b ofs current expected_int new_int k Hneq)
        as (old & Hcurrent & Hold).
      subst current.
      pose proof (Hviews i _ Hget Hsupported) as Hview.
      eapply (@CAM_initialized_atomic_CAS_failure_endpoint ge GE P ids
        HGEinit Hids Hdecls Hwrapper); eauto.
  Qed.

End CAMInitializedAtomicStep.

Section CAMInitializeduncritStep.

  Context {ge : Clight.genv} {GE : GlobEnv.t}.
  Implicit Types (sc : CAM_config ge) (tc : @ProgConfig GE).
  Variables P : ClightLang.clight_comp_unit.
  Variable ids : Wrappers.wrapper_ids.
  Hypothesis HGEinit : GlobEnv.init
    (ClightAtomicTarget.linked_units [P] ids) GE.
  Hypothesis Hids : Wrappers.wrapper_ids_wf ids.
  Hypothesis Hreserve :
    ClightAtomicTarget.clients_reserve_wrapper_ids [P] ids.
  Hypothesis Hdecls : ClientInit.client_atomic_declarations ids P.

  Theorem CAM_initialized_uncrit_step_refinement :
    forall sc1 sc2 tc,
      CAM_step ge sc1 sc2 ->
      CAM_assign_loc_value_syntax sc1 ->
      CAM_no_explicit_stuck sc2 ->
      CAM_uncrit_match sc1 tc ->
      CAM_core_try_refinement_at sc1 tc ->
      CAM_atomic_memory_views sc1 tc ->
      exists tc' labels fp,
        ETrace.star (@glob_step GE) tc labels fp tc' /\
        CAM_uncrit_match sc2 tc'.
  Proof.
    intros [stp sm mu] [stp2 sm2 mu2] tc Hstep Hsyntax
      Hnot_stuck Hq Htry Hviews.
    pose proof (CAM_initialized_wrapper_of_link
      P ids GE HGEinit Hreserve Hids) as Hwrapper.
    unfold CAM_step in Hstep. cbn in Hstep.
    inversion Hstep; subst stp2 sm2 mu2.
    - eapply Htry.
      + econstructor; eauto.
      + exact Hsyntax.
      + exact Hq.
    - destruct (CAM_core_commit_stutters
        stp sm mu i c T μ' tc Hget Hq) as (labels & fp & Hstar & Hq').
      exists tc, labels, fp. auto.
    - eapply (CAM_initialized_atomic_step_refines
        P ids HGEinit Hids Hdecls Hwrapper i).
      + eapply CAM_atomic_read; eauto.
      + exact Hq.
      + exact Hviews.
    - eapply (CAM_initialized_atomic_step_refines
        P ids HGEinit Hids Hdecls Hwrapper i).
      + eapply CAM_atomic_write; eauto.
      + exact Hq.
      + exact Hviews.
    - eapply (CAM_initialized_atomic_step_refines
        P ids HGEinit Hids Hdecls Hwrapper i).
      + eapply CAM_atomic_CAS_success; eauto.
      + exact Hq.
      + exact Hviews.
    - eapply (CAM_initialized_atomic_step_refines
        P ids HGEinit Hids Hdecls Hwrapper i).
      + eapply CAM_atomic_CAS_failure; eauto.
      + exact Hq.
      + exact Hviews.
    - exfalso. apply (Hnot_stuck i).
      apply (lookup_insert_eq (K := nat) (M := gmap nat)).
  Qed.

End CAMInitializeduncritStep.

Section ClightAtomicProgramCorrespondence.

  Context {ge : Clight.genv} {GE : GlobEnv.t}.
  Implicit Types
    (sc sc_initial sc_final : CAM_config ge)
    (tc tc_initial tc_final : @ProgConfig GE).

  Variable P : ClightLang.clight_comp_unit.
  Variable ids : ClightAtomicWrappers.wrapper_ids.
  Variable thread_entries : GAST.entries.

  Hypothesis Hids : Wrappers.wrapper_ids_wf ids.
  Hypothesis Hreserve :
    ClightAtomicTarget.clients_reserve_wrapper_ids [P] ids.
  Hypothesis Hdecls : ClientInit.client_atomic_declarations ids P.
  Hypothesis Hsource : CAM_source_program_initialized P ge.

  (** [P'] is [P] verbatim plus the appended wrapper compilation unit.  The
      wrapper bodies are, by [wrapper_bodies_have_atomic_shape], exactly
      [ent_atom(); sequential operation; ext_atom()].  Thus this is a
      link-time implementation of the requested call translation rather than
      a syntactic rewrite of each call site. *)
  (** The induction stays at O-bit wrapper boundaries.  In particular, its
      atomic cases are discharged by
      [CAM_initialized_uncrit_step_refinement], which extracts the
      initialized wrapper and client-resolution facts from [P'] and invokes
      the four concrete translated-function executions. *)
  Theorem CAM_program_execution_corresponds_uncrit :
    forall sc_initial sc_final tc_initial,
      init_config (CAM_translated_program P ids thread_entries)
        (gm tc_initial) GE tc_initial
        (cur_tid tc_initial) ->
      CAM_execution ge sc_initial sc_final ->
      CAM_uncrit_match sc_initial tc_initial ->
      CAM_core_try_refinements_for_from P ge GE tc_initial ->
      @CAM_atomic_memory_views_from ge GE tc_initial ->
      exists tc_final labels fp,
        ETrace.star (@glob_step GE) tc_initial labels fp tc_final /\
        CAM_uncrit_match sc_final tc_final.
  Proof.
    intros sc_initial sc_final tc_initial Htarget Hexec Hmatch Htries_for_from
      Hviews_from.
    pose proof (CAM_translated_program_init_GE
      P ids thread_entries (gm tc_initial) GE tc_initial
      (cur_tid tc_initial) Htarget) as HGEinit.
    destruct Hsource as (source_raw_ge & Hsource_init).
    pose proof (Htries_for_from source_raw_ge Hsource_init) as Htries_from.
    clear Htarget Htries_for_from.
    revert tc_initial Hmatch Htries_from Hviews_from.
    induction Hexec as
      [sc Hnot_stuck Hsyntax Hterminated |
       sc1 sc2 sc3 Hnot_stuck Hsyntax Hsource_step Hexec IHexec];
      intros tc1 Hmatch Htries_from Hviews_from.
    - exists tc1, [], FP.emp. split; [constructor | exact Hmatch].
    - pose proof (CAM_execution_source_no_explicit_stuck_1 _ _ _ Hexec)
        as Hnext_not_stuck.
      pose proof (Hviews_from sc1 tc1 [] FP.emp ltac:(constructor) Hmatch)
        as Hviews.
      pose proof (Htries_from sc1 tc1 [] FP.emp ltac:(constructor))
        as Hcore_try.
      destruct (CAM_initialized_uncrit_step_refinement
        P ids HGEinit Hids Hreserve Hdecls
        sc1 sc2 tc1 Hsource_step Hsyntax
        Hnext_not_stuck Hmatch Hcore_try Hviews)
        as (tc2 & labels1 & fp1 & Hstar1 & Hmatch2).
      assert (Hviews_from2 : @CAM_atomic_memory_views_from ge GE tc2).
      { intros sc tc labels fp Hstar Hq.
        eapply (Hviews_from sc tc (labels1 ++ labels) (FP.union fp1 fp)).
        - eapply CAM_etrace_star_trans; eauto.
        - exact Hq. }
      assert (Htries_from2 : forall sc tc labels fp,
          ETrace.star (@glob_step GE) tc2 labels fp tc ->
          CAM_core_try_refinement_at sc tc).
      { intros sc tc labels fp Hstar.
        eapply (Htries_from sc tc (labels1 ++ labels) (FP.union fp1 fp)).
        eapply CAM_etrace_star_trans; eauto. }
      destruct (IHexec tc2 Hmatch2 Htries_from2 Hviews_from2)
        as (tc3 & labels2 & fp2 & Hstar2 & Hmatch3).
      exists tc3, (labels1 ++ labels2), (FP.union fp1 fp2).
      split; [eapply CAM_etrace_star_trans; eauto | exact Hmatch3].
  Qed.

  (** Public result, stated with the direct two-case configuration relation.
      The stronger theorem above also establishes that both endpoints are
      outside a target crit section. *)
  Corollary CAM_program_execution_corresponds :
    forall sc_initial sc_final tc_initial,
      init_config (CAM_translated_program P ids thread_entries)
        (gm tc_initial) GE tc_initial
        (cur_tid tc_initial) ->
      CAM_execution ge sc_initial sc_final ->
      CAM_uncrit_match sc_initial tc_initial ->
      CAM_core_try_refinements_for_from P ge GE tc_initial ->
      @CAM_atomic_memory_views_from ge GE tc_initial ->
      exists tc_final labels fp,
        ETrace.star (@glob_step GE) tc_initial labels fp tc_final /\
        match_config sc_final tc_final.
  Proof.
    intros sc_initial sc_final tc_initial Htarget Hexec Hmatch Htries Hviews.
    destruct (CAM_program_execution_corresponds_uncrit
      sc_initial sc_final tc_initial Htarget Hexec Hmatch Htries Hviews)
      as (tc_final & labels & fp & Hstar & Hfinal).
    exists tc_final, labels, fp. split; [exact Hstar |].
    constructor. exact Hfinal.
  Qed.

End ClightAtomicProgramCorrespondence.
