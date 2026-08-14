(** Forward-simulation interface from the Clight atomic machine to a local
    semantics for the translated program.

    The source transition is indexed by the thread which takes the step and
    exposes its memory-event trace.  The target interface below is indexed by
    the same thread.  Its configuration relation compares only memories and
    threads: atomic-marker phases and linearization points belong to the
    simulation diagram, not to the state relation. *)

Require Import compcert.common.AST.
Require Import compcert.common.Builtins.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require compcert.lib.Maps.
Require Import compcert.concurrency.common.Footprint.
Require Import compcert.concurrency.common.GAST.
From compcert.concurrency.comp_correct.cfrontend Require Import Clight_local.

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
Require Import stdpp.gmap.
Require Import VST.veric.val_lemmas.

Require Import atomic_machine.atomic_machine.
Require Import atomic_machine.clight_atomic_specs.
Require Import atomic_machine.clight_at_mach.
Require Import atomic_machine.clight_atomic_source_decode.
Require Import atomic_machine.clight_atomic_source_restriction.
Require Import atomic_machine.clight_atomic_wrappers.
Require Import atomic_machine.clight_atomic_client_init.

Import Address Values.
Import ListNotations.

Module Wrappers := ClightAtomicWrappers.
Module ClientInit := ClightAtomicClientInit.
Module LocalClight := Clight_local.

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

Local Notation CAM_Running :=
  (@Running address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge)).
Local Notation CAM_StuckState :=
  (@StuckState address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge)).

Definition CAM_trace : Type := list (@mem_ev address).

Definition CAM_read_trace (l : address) (ly : memory_chunk) : CAM_trace :=
  map (fun l => @Read address l) (layout_to_locs l ly).

Definition CAM_write_trace (l : address) (ly : memory_chunk) : CAM_trace :=
  map (fun l => @Write address l) (layout_to_locs l ly).

(** A labeled presentation of the unchanged atomic-machine rules.  Atomic
    reads and writes expose their byte-granular access at the source level;
    a successful CAS exposes its read followed by its write.  A commit is
    silent because the events were exposed by [CAM_core_try]. *)
Inductive CAM_step : nat -> CAM_config ge -> CAM_trace -> CAM_config ge -> Prop :=
| CAM_core_try : forall
    (stp : CAM_tpool ge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (T : CAM_trace)
    (score' : Clight_core.CC_core) (sm' : mem) (mu' : CAM_rw_map)
    (Hget : stp !! i = Some (CAM_Running score []))
    (Hstep : ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge)
      score sm T score' sm')
    (Hreserve : rsv T mu = Some mu'),
    CAM_step i
      (Build_CAM_config ge stp sm mu) T
      (Build_CAM_config ge (<[i := CAM_Running score' T]> stp) sm' mu')
| CAM_core_commit : forall
    (stp : CAM_tpool ge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (T : CAM_trace) (mu' : CAM_rw_map)
    (Hget : stp !! i = Some (CAM_Running score T))
    (Hne : T <> [])
    (Hcommit : fin T mu = Some mu'),
    CAM_step i
      (Build_CAM_config ge stp sm mu) []
      (Build_CAM_config ge (<[i := CAM_Running score []]> stp) sm mu')
| CAM_sc_read : forall
    (stp : CAM_tpool ge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (ly : memory_chunk) (l : address)
    (v : val) (K : option val -> Clight_core.CC_core)
    (Hget : stp !! i = Some (CAM_Running score []))
    (Hext : clight_at_external score = Some (ALoad ly l, K))
    (Hmu : readable mu (layout_to_locs l ly))
    (Hload : load sm l ly = Some v)
    (Hdefined : clight_val_defined v),
    CAM_step i
      (Build_CAM_config ge stp sm mu) (CAM_read_trace l ly)
      (Build_CAM_config ge
        (<[i := CAM_Running (K (Some v)) []]> stp) sm mu)
| CAM_sc_write : forall
    (stp : CAM_tpool ge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (ly : memory_chunk) (l : address)
    (v : val) (sm' : mem) (K : option val -> Clight_core.CC_core)
    (Hget : stp !! i = Some (CAM_Running score []))
    (Hext : clight_at_external score = Some (AStore ly l v, K))
    (Hmu : writable mu (layout_to_locs l ly))
    (Hstore : store sm l ly v = Some sm')
    (Hdefined : clight_val_defined v),
    CAM_step i
      (Build_CAM_config ge stp sm mu) (CAM_write_trace l ly)
      (Build_CAM_config ge (<[i := CAM_Running (K None) []]> stp) sm' mu)
| CAM_sc_cas_success :
    forall (stp : CAM_tpool ge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (ly : memory_chunk) (l : address)
    (expected new current : val) (sm' : mem)
    (K : option val -> Clight_core.CC_core)
    (Hget : stp !! i = Some (CAM_Running score []))
    (Hext : clight_at_external score =
      Some (ACAS ly l expected new, K))
    (Hmu : writable mu (layout_to_locs l ly))
    (Hload : load sm l ly = Some current)
    (Hdefined_current : clight_val_defined current)
    (Heq : clight_ValEq score sm current expected)
    (Hstore : store sm l ly new = Some sm')
    (Hdefined_new : clight_val_defined new),
    CAM_step i
      (Build_CAM_config ge stp sm mu)
      (CAM_read_trace l ly ++ CAM_write_trace l ly)
      (Build_CAM_config ge
        (<[i := CAM_Running (K (Some Vtrue)) []]> stp) sm' mu)
| CAM_sc_cas_failure :
    forall (stp : CAM_tpool ge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (ly : memory_chunk) (l : address)
    (expected new current : val) (K : option val -> Clight_core.CC_core)
    (Hget : stp !! i = Some (CAM_Running score []))
    (Hext : clight_at_external score =
      Some (ACAS ly l expected new, K))
    (Hmu : readable mu (layout_to_locs l ly))
    (Hload : load sm l ly = Some current)
    (Hdefined_current : clight_val_defined current)
    (Hneq : clight_ValNEq score sm current expected),
    CAM_step i
      (Build_CAM_config ge stp sm mu) (CAM_read_trace l ly)
      (Build_CAM_config ge
        (<[i := CAM_Running (K (Some Vfalse)) []]> stp) sm mu)
| CAM_sc_cas_stuck :
    forall (stp : CAM_tpool ge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (ly : memory_chunk) (l : address)
    (expected new current : val) (K : option val -> Clight_core.CC_core)
    (Hget : stp !! i = Some (CAM_Running score []))
    (Hext : clight_at_external score =
      Some (ACAS ly l expected new, K))
    (Hload : load sm l ly = Some current)
    (Hdefined_current : clight_val_defined current)
    (Heq : clight_ValEq score sm current expected)
    (Hnot_writable : ~ writable mu (layout_to_locs l ly)),
    CAM_step i
      (Build_CAM_config ge stp sm mu) (CAM_read_trace l ly)
      (Build_CAM_config ge (<[i := CAM_StuckState]> stp) sm mu).

Lemma CAM_step_is_atomic_machine_step i sc1 T sc2 :
  CAM_step i sc1 T sc2 ->
  @at_step address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge)
    (CAM_threads sc1) (CAM_memory sc1) (CAM_rw sc1)
    (CAM_threads sc2) (CAM_memory sc2) (CAM_rw sc2).
Proof.
  intros Hstep; destruct Hstep.
  - eapply Core_Try; eauto.
  - eapply Core_Commit; eauto.
  - eapply SC_Read; eauto.
  - eapply SC_Write; eauto.
  - eapply (@SC_Cas_Suc address val _ _ mem memory_chunk
      clight_mem_mixin (Clight_language ge)); eauto.
  - eapply (@SC_Cas_Fail address val _ _ mem memory_chunk
      clight_mem_mixin (Clight_language ge)); eauto.
  - eapply SC_Cas_Stuck; eauto.
Qed.

(** Conversely, every rule of the underlying atomic machine has a thread
    index and the constructor-canonical memory-event label exposed by
    [CAM_step]. *)
Lemma atomic_machine_step_has_CAM_label
    stp sm mu stp' sm' mu' :
  @at_step address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge) stp sm mu stp' sm' mu' ->
  exists i T,
    CAM_step i
      (Build_CAM_config ge stp sm mu) T
      (Build_CAM_config ge stp' sm' mu').
Proof.
  intros Hstep. inversion Hstep; subst.
  - exists i, T. eapply CAM_core_try; eauto.
  - exists i, []. eapply CAM_core_commit; eauto.
  - match goal with
    | Hext : ?lhs = Some (ALoad ?ly ?addr, ?K) |- _ =>
        exists i, (CAM_read_trace addr ly); eapply CAM_sc_read; eauto
    end.
  - match goal with
    | Hext : ?lhs = Some (AStore ?ly ?addr ?v, ?K) |- _ =>
        exists i, (CAM_write_trace addr ly); eapply CAM_sc_write; eauto
    end.
  - match goal with
    | Hext : ?lhs = Some (ACAS ?ly ?addr ?expected ?new, ?K) |- _ =>
        exists i, (CAM_read_trace addr ly ++ CAM_write_trace addr ly);
        eapply CAM_sc_cas_success; eauto
    end.
  - match goal with
    | Hext : ?lhs = Some (ACAS ?ly ?addr ?expected ?new, ?K) |- _ =>
        exists i, (CAM_read_trace addr ly);
        eapply CAM_sc_cas_failure; eauto
    end.
  - match goal with
    | Hext : ?lhs = Some (ACAS ?ly ?addr ?expected ?new, ?K) |- _ =>
        exists i, (CAM_read_trace addr ly);
        eapply CAM_sc_cas_stuck; eauto
    end.
Qed.

Corollary CAM_step_iff_atomic_machine_step stp sm mu stp' sm' mu' :
  (exists i T,
    CAM_step i
      (Build_CAM_config ge stp sm mu) T
      (Build_CAM_config ge stp' sm' mu')) <->
  @at_step address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language ge) stp sm mu stp' sm' mu'.
Proof.
  split.
  - intros (i & T & Hstep). now apply CAM_step_is_atomic_machine_step in Hstep.
  - apply atomic_machine_step_has_CAM_label.
Qed.

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
    requires every thread to have terminated.  The program restriction below
    separately excludes marker references, inline builtins, and non-atomic
    external definitions. *)
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
    (i : nat) (T : CAM_trace)
    (Hstep : CAM_step ge i sc1 T sc2)
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

(** ** The marker-free local target program [P'] *)

(** Markers are needed only by the global heterogeneous semantics.  In the
    local target, the simulation cases below require one source atomic
    transition to follow a same-thread path through a wrapper and single out
    its linearization step.  Removing markers keeps [P'] in ordinary Clight
    and, importantly, adds no target-only global blocks. *)
Definition CAM_local_atomic_load_function : Clight.function := {|
  Clight.fn_return := Wrappers.tint;
  Clight.fn_callconv := cc_default;
  Clight.fn_params := [(Wrappers.target_temp, Wrappers.atomic_pointer_type)];
  Clight.fn_vars := [];
  Clight.fn_temps := [(Wrappers.old_temp, Wrappers.tint)];
  Clight.fn_body :=
    Clight.Ssequence
      (Clight.Sset Wrappers.old_temp Wrappers.target_lvalue)
      (Clight.Sreturn (Some Wrappers.old_expr))
|}.

(** The global wrapper returns a dummy [int] to cross a module boundary.
    A local internal call must instead have the client's actual [void]
    function type, so this version returns [Vundef] through [Sreturn None]. *)
Definition CAM_local_atomic_store_function : Clight.function := {|
  Clight.fn_return := Wrappers.tvoid;
  Clight.fn_callconv := cc_default;
  Clight.fn_params :=
    [(Wrappers.target_temp, Wrappers.atomic_pointer_type);
     (Wrappers.new_temp, Wrappers.tint)];
  Clight.fn_vars := [];
  Clight.fn_temps := [];
  Clight.fn_body :=
    Clight.Ssequence
      (Clight.Sassign Wrappers.target_lvalue Wrappers.new_expr)
      (Clight.Sreturn None)
|}.

Definition CAM_local_atomic_CAS_function : Clight.function := {|
  Clight.fn_return := Wrappers.tint;
  Clight.fn_callconv := cc_default;
  Clight.fn_params :=
    [(Wrappers.target_temp, Wrappers.atomic_pointer_type);
     (Wrappers.expected_temp, Wrappers.tint);
     (Wrappers.new_temp, Wrappers.tint)];
  Clight.fn_vars := [];
  Clight.fn_temps :=
    [(Wrappers.old_temp, Wrappers.tint);
     (Wrappers.result_temp, Wrappers.tint)];
  Clight.fn_body :=
    Clight.Ssequence
      (Clight.Sset Wrappers.old_temp Wrappers.target_lvalue)
      (Clight.Ssequence
        (Clight.Sifthenelse
          (Clight.Ebinop Cop.Oeq Wrappers.old_expr
            Wrappers.expected_expr Wrappers.tint)
          (Clight.Ssequence
            (Clight.Sassign Wrappers.target_lvalue Wrappers.new_expr)
            (Clight.Sset Wrappers.result_temp
              (Clight.Econst_int Int.one Wrappers.tint)))
          (Clight.Sset Wrappers.result_temp
            (Clight.Econst_int Int.zero Wrappers.tint)))
        (Clight.Sreturn (Some Wrappers.result_expr)))
|}.

Definition CAM_replace_atomic_globdef
    (ids : Wrappers.wrapper_ids) (id : ident)
    (gd : globdef Clight.fundef Ctypes.type) :
    globdef Clight.fundef Ctypes.type :=
  if peq id (Wrappers.atomic_load_id ids) then
    Gfun (Ctypes.Internal CAM_local_atomic_load_function)
  else if peq id (Wrappers.atomic_store_id ids) then
    Gfun (Ctypes.Internal CAM_local_atomic_store_function)
  else if peq id (Wrappers.atomic_CAS_id ids) then
    Gfun (Ctypes.Internal CAM_local_atomic_CAS_function)
  else gd.

Definition CAM_replace_atomic_definition
    (ids : Wrappers.wrapper_ids)
    (d : ident * globdef Clight.fundef Ctypes.type) :=
  let '(id, gd) := d in (id, CAM_replace_atomic_globdef ids id gd).

(** [P'] changes only the fundefs at the three existing atomic identifiers.
    Definition order and cardinality are unchanged, so this translation does
    not itself shift the global blocks or the initial [nextblock]. *)
Definition CAM_local_translated_program
    (P : ClightLang.clight_comp_unit)
    (ids : Wrappers.wrapper_ids) : ClightLang.clight_comp_unit :=
  {| ClightLang.cu_defs :=
       map (CAM_replace_atomic_definition ids) (ClightLang.cu_defs P);
     ClightLang.cu_public := ClightLang.cu_public P;
     ClightLang.cu_types := ClightLang.cu_types P;
     ClightLang.cu_comp_env := ClightLang.cu_comp_env P;
     ClightLang.cu_comp_env_eq := ClightLang.cu_comp_env_eq P |}.

Lemma CAM_local_atomic_load_type :
  Clight.type_of_fundef (Ctypes.Internal CAM_local_atomic_load_function) =
  Clight.type_of_fundef Wrappers.client_atomic_load_external.
Proof. reflexivity. Qed.

Lemma CAM_local_atomic_store_type :
  Clight.type_of_fundef (Ctypes.Internal CAM_local_atomic_store_function) =
  Clight.type_of_fundef Wrappers.client_atomic_store_external.
Proof. reflexivity. Qed.

Lemma CAM_local_atomic_CAS_type :
  Clight.type_of_fundef (Ctypes.Internal CAM_local_atomic_CAS_function) =
  Clight.type_of_fundef Wrappers.client_atomic_CAS_external.
Proof. reflexivity. Qed.

Lemma CAM_replace_atomic_definition_fst ids d :
  fst (CAM_replace_atomic_definition ids d) = fst d.
Proof. destruct d; reflexivity. Qed.

Lemma CAM_local_translation_def_ids P ids :
  map fst (ClightLang.cu_defs (CAM_local_translated_program P ids)) =
  map fst (ClightLang.cu_defs P).
Proof.
  change
    (map fst
      (map (CAM_replace_atomic_definition ids) (ClightLang.cu_defs P)) =
     map fst (ClightLang.cu_defs P)).
  rewrite map_map.
  apply map_ext. intros d. apply CAM_replace_atomic_definition_fst.
Qed.

Lemma CAM_local_translation_defs_length P ids :
  length (ClightLang.cu_defs (CAM_local_translated_program P ids)) =
  length (ClightLang.cu_defs P).
Proof. cbn [CAM_local_translated_program]. apply length_map. Qed.

Lemma CAM_local_translation_public P ids :
  ClightLang.cu_public (CAM_local_translated_program P ids) =
  ClightLang.cu_public P.
Proof. reflexivity. Qed.

Lemma CAM_local_translation_norepet P ids :
  list_norepet (map fst (ClightLang.cu_defs P)) ->
  list_norepet
    (map fst (ClightLang.cu_defs (CAM_local_translated_program P ids))).
Proof. rewrite CAM_local_translation_def_ids. auto. Qed.

(** ** Source-program restrictions *)

Definition CAM_external_avoids_markers (ef : external_function) : Prop :=
  match ef with
  | EF_builtin name _ =>
      name <> "ent_atom"%string /\ name <> "ext_atom"%string
  | _ => True
  end.

Fixpoint CAM_expr_avoids_markers (a : Clight.expr) : Prop :=
  match a with
  | Clight.Evar id _ => id <> GAST.ent_atom /\ id <> GAST.ext_atom
  | Clight.Ederef a _ | Clight.Eaddrof a _ | Clight.Eunop _ a _ |
    Clight.Ecast a _ | Clight.Efield a _ _ => CAM_expr_avoids_markers a
  | Clight.Ebinop _ a1 a2 _ =>
      CAM_expr_avoids_markers a1 /\ CAM_expr_avoids_markers a2
  | _ => True
  end.

Fixpoint CAM_exprlist_avoids_markers (al : list Clight.expr) : Prop :=
  match al with
  | [] => True
  | a :: rest =>
      CAM_expr_avoids_markers a /\ CAM_exprlist_avoids_markers rest
  end.

Fixpoint CAM_statement_avoids_markers (s : Clight.statement) : Prop :=
  match s with
  | Clight.Sskip | Clight.Sbreak | Clight.Scontinue | Clight.Sgoto _ => True
  | Clight.Sassign a1 a2 =>
      CAM_expr_avoids_markers a1 /\ CAM_expr_avoids_markers a2
  | Clight.Sset _ a => CAM_expr_avoids_markers a
  | Clight.Scall _ fn args =>
      CAM_expr_avoids_markers fn /\ CAM_exprlist_avoids_markers args
  (** CASCompCert's local Clight relation deliberately has no inline-builtin
      rule.  Such statements are therefore excluded from the source
      fragment, including (but not limited to) the two atomic markers. *)
  | Clight.Sbuiltin _ _ _ _ => False
  | Clight.Ssequence s1 s2 | Clight.Sloop s1 s2 =>
      CAM_statement_avoids_markers s1 /\
      CAM_statement_avoids_markers s2
  | Clight.Sifthenelse a s1 s2 =>
      CAM_expr_avoids_markers a /\
      CAM_statement_avoids_markers s1 /\
      CAM_statement_avoids_markers s2
  | Clight.Sreturn oa =>
      match oa with None => True | Some a => CAM_expr_avoids_markers a end
  | Clight.Sswitch a ls =>
      CAM_expr_avoids_markers a /\
      CAM_labeled_statements_avoid_markers ls
  | Clight.Slabel _ s => CAM_statement_avoids_markers s
  end
with CAM_labeled_statements_avoid_markers
    (ls : Clight.labeled_statements) : Prop :=
  match ls with
  | Clight.LSnil => True
  | Clight.LScons _ s rest =>
      CAM_statement_avoids_markers s /\
      CAM_labeled_statements_avoid_markers rest
  end.

Definition CAM_definition_avoids_markers
    (d : ident * globdef Clight.fundef Ctypes.type) : Prop :=
  let '(id, gd) := d in
  id <> GAST.ent_atom /\ id <> GAST.ext_atom /\
  gd <> Gfun Wrappers.ent_atom_external /\
  gd <> Gfun Wrappers.ext_atom_external /\
  match gd with
  | Gfun (Ctypes.Internal f) =>
      CAM_statement_avoids_markers (Clight.fn_body f)
  | Gfun (Ctypes.External ef _ _ _) =>
      CAM_external_avoids_markers ef
  | _ => True
  end.

Definition CAM_program_avoids_markers
    (P : ClightLang.clight_comp_unit) : Prop :=
  Forall CAM_definition_avoids_markers (ClightLang.cu_defs P).

Definition CAM_source_fragment (P : ClightLang.clight_comp_unit) : Prop :=
  clight_comp_unit_assign_loc_value_only P /\
  CAM_program_avoids_markers P.

(** A bare local Clight step stops at external functions.  The three atomic
    declarations are handled by the atomic-machine rules and are replaced by
    internal wrappers in [P']; every other source function must be internal. *)
Definition CAM_definition_external_is_atomic
    (ids : Wrappers.wrapper_ids)
    (d : ident * globdef Clight.fundef Ctypes.type) : Prop :=
  let '(id, gd) := d in
  match gd with
  | Gfun (Ctypes.External _ _ _ _) =>
      id = Wrappers.atomic_load_id ids \/
      id = Wrappers.atomic_store_id ids \/
      id = Wrappers.atomic_CAS_id ids
  | _ => True
  end.

Definition CAM_program_only_atomic_externals
    (ids : Wrappers.wrapper_ids)
    (P : ClightLang.clight_comp_unit) : Prop :=
  Forall (CAM_definition_external_is_atomic ids)
    (ClightLang.cu_defs P).

Definition CAM_source_program_initialized
    (P : ClightLang.clight_comp_unit) (sge : Clight.genv) : Prop :=
  exists raw_sge, LocalClight.init_genv P raw_sge sge.

Definition CAM_local_program_initialized
    (P' : ClightLang.clight_comp_unit) (tge : Clight.genv) : Prop :=
  exists raw_tge, LocalClight.init_genv P' raw_tge tge.

(** Ordered traces below use the same concrete block identifiers on both
    sides.  Since [P'] preserves the order and number of definitions, the
    canonical local initializers can be chosen with the same symbol blocks
    and allocation base.  We record that choice explicitly rather than
    pretending that the diagram is parametric in an arbitrary block
    renaming. *)
Definition CAM_program_blocks_aligned
    (sge tge : Clight.genv) : Prop :=
  (forall id,
    Genv.find_symbol (Clight.genv_genv sge) id =
    Genv.find_symbol (Clight.genv_genv tge) id) /\
  Genv.genv_next (Clight.genv_genv sge) =
  Genv.genv_next (Clight.genv_genv tge).

(** The two Clight developments share statements, continuations,
    environments, and memories, but expose distinct core datatypes. *)
Definition CAM_core_to_local
    (score : Clight_core.CC_core) : ClightLang.core :=
  match score with
  | Clight_core.State f s k e le =>
      ClightLang.Core_State f s k e le
  | Clight_core.Callstate fd args k =>
      ClightLang.Core_Callstate fd args k
  | Clight_core.Returnstate v k =>
      ClightLang.Core_Returnstate v k
  end.

Definition CAM_local_core_to_event
    (tcore : ClightLang.core) : Clight_core.CC_core :=
  match tcore with
  | ClightLang.Core_State f s k e le =>
      Clight_core.State f s k e le
  | ClightLang.Core_Callstate fd args k =>
      Clight_core.Callstate fd args k
  | ClightLang.Core_Returnstate v k =>
      Clight_core.Returnstate v k
  end.

Lemma CAM_core_local_roundtrip score :
  CAM_local_core_to_event (CAM_core_to_local score) = score.
Proof. destruct score; reflexivity. Qed.

Lemma CAM_local_core_roundtrip tcore :
  CAM_core_to_local (CAM_local_core_to_event tcore) = tcore.
Proof. destruct tcore; reflexivity. Qed.

(** ** Concrete same-thread local Clight machine *)

Record CAM_local_config : Type := {
  CAM_target_threads : gmap nat ClightLang.core;
  CAM_target_memory : mem
}.

(** This is a concurrent lifting of CASCompCert's actual local Clight step.
    It pairs the footprint step with an event-semantics derivation having the
    same core and memory endpoints, thereby retaining the ordered trace
    needed by the atomic machine.  The index is operational: only [ttp !! i]
    is replaced, and there is no scheduler field or atomic bit which the
    relation could accidentally constrain. *)
Inductive CAM_local_step (tge : Clight.genv) (i : nat) :
    CAM_local_config -> CAM_trace -> CAM_local_config -> Prop :=
| CAM_local_core_step : forall
    (ttp : gmap nat ClightLang.core) (tm : mem)
    (tcore : ClightLang.core) (T : CAM_trace)
    (fp : FP.t) (tcore' : ClightLang.core) (tm' : mem)
    (Hget : ttp !! i = Some tcore)
    (Hlocal : LocalClight.step2 tge tcore tm fp tcore' tm')
    (Hevents : ev_step_with_mem_ev (Clight_evsem.CLC_evsem tge)
      (CAM_local_core_to_event tcore) tm T
      (CAM_local_core_to_event tcore') tm'),
    CAM_local_step tge i
      (Build_CAM_local_config ttp tm) T
      (Build_CAM_local_config (<[i := tcore']> ttp) tm').

Lemma CAM_local_step_is_local tge i tc T tc' :
  CAM_local_step tge i tc T tc' ->
  exists ttp tm tcore fp tcore' tm',
    tc = Build_CAM_local_config ttp tm /\
    tc' = Build_CAM_local_config (<[i := tcore']> ttp) tm' /\
    ttp !! i = Some tcore /\
    LocalClight.step2 tge tcore tm fp tcore' tm'.
Proof.
  intros Hstep. inversion Hstep; subst.
  do 6 eexists. repeat split; eauto.
Qed.

Lemma CAM_local_step_other_thread tge i tc T tc' other :
  CAM_local_step tge i tc T tc' ->
  other <> i ->
  CAM_target_threads tc' !! other = CAM_target_threads tc !! other.
Proof.
  intros Hstep Hne. inversion Hstep; subst; cbn.
  apply lookup_insert_ne. congruence.
Qed.

(** Same-thread reflexive-transitive and nonempty closures, following the
    trace-concatenating shape of [Smallstep.star] and [Smallstep.plus]. *)
Inductive CAM_local_star_at (tge : Clight.genv) (i : nat) :
    CAM_local_config -> CAM_trace -> CAM_local_config -> Prop :=
| CAM_local_star_refl tc : CAM_local_star_at tge i tc [] tc
| CAM_local_star_step tc1 T1 tc2 T2 tc3
    (Hstep : CAM_local_step tge i tc1 T1 tc2)
    (Hstar : CAM_local_star_at tge i tc2 T2 tc3) :
    CAM_local_star_at tge i tc1 (T1 ++ T2) tc3.

Definition CAM_local_plus_at (tge : Clight.genv) (i : nat)
    (tc1 : CAM_local_config) (T : CAM_trace)
    (tc3 : CAM_local_config) : Prop :=
  exists tc2 T1 T2,
    CAM_local_step tge i tc1 T1 tc2 /\
    CAM_local_star_at tge i tc2 T2 tc3 /\
    T = T1 ++ T2.

Lemma CAM_local_plus_one tge i tc T tc' :
  CAM_local_step tge i tc T tc' ->
  CAM_local_plus_at tge i tc T tc'.
Proof.
  intros Hstep. exists tc', T, [].
  split; [exact Hstep |]. split; [constructor |].
  now rewrite app_nil_r.
Qed.

Lemma CAM_local_star_trans tge i tc1 T1 tc2 T2 tc3 :
  CAM_local_star_at tge i tc1 T1 tc2 ->
  CAM_local_star_at tge i tc2 T2 tc3 ->
  CAM_local_star_at tge i tc1 (T1 ++ T2) tc3.
Proof.
  intros Hstar1 Hstar2. induction Hstar1.
  - exact Hstar2.
  - rewrite <- app_assoc. econstructor; eauto.
Qed.

Lemma CAM_local_star_step_star_plus tge i
    tc Tpre tc_before Tlin tc_after Tpost tc' :
  CAM_local_star_at tge i tc Tpre tc_before ->
  CAM_local_step tge i tc_before Tlin tc_after ->
  CAM_local_star_at tge i tc_after Tpost tc' ->
  CAM_local_plus_at tge i tc (Tpre ++ Tlin ++ Tpost) tc'.
Proof.
  intros Hpre Hlin Hpost.
  destruct Hpre as [tc0 | tc0 T1 tc2 T2 tc_before Hfirst Hrest].
  - simpl. exists tc_after, Tlin, Tpost. auto.
  - exists tc2, T1, (T2 ++ Tlin ++ Tpost).
    split; [exact Hfirst |]. split.
    + eapply CAM_local_star_trans; [exact Hrest |].
      econstructor; [exact Hlin | exact Hpost].
    + symmetry. apply app_assoc.
Qed.

(** ** Concrete linearization steps *)

Inductive CAM_linearization_kind : Type :=
| CAM_lin_load (l : address) (v : val)
| CAM_lin_store (l : address) (v : val)
| CAM_lin_CAS_success
    (l : address) (expected new current : val)
| CAM_lin_CAS_failure
    (l : address) (expected new current : val).

(** The redex identifies the actual read or store statement in the local
    wrapper.  In particular, successful CAS linearizes at its assignment,
    not at entry to the wrapper or at an atomic-bit transition. *)
Inductive CAM_linearization_redex :
    CAM_linearization_kind -> ClightLang.core -> Prop :=
| CAM_load_redex : forall b ofs v k e le,
    Maps.PTree.get Wrappers.target_temp le = Some (Vptr b ofs) ->
    CAM_linearization_redex
      (CAM_lin_load (b, Ptrofs.unsigned ofs) v)
      (ClightLang.Core_State CAM_local_atomic_load_function
        (Clight.Sset Wrappers.old_temp Wrappers.target_lvalue) k e le)
| CAM_store_redex : forall b ofs v k e le,
    Maps.PTree.get Wrappers.target_temp le = Some (Vptr b ofs) ->
    Maps.PTree.get Wrappers.new_temp le = Some v ->
    CAM_linearization_redex
      (CAM_lin_store (b, Ptrofs.unsigned ofs) v)
      (ClightLang.Core_State CAM_local_atomic_store_function
        (Clight.Sassign Wrappers.target_lvalue Wrappers.new_expr) k e le)
| CAM_CAS_success_redex : forall b ofs expected new current k e le,
    Maps.PTree.get Wrappers.target_temp le = Some (Vptr b ofs) ->
    Maps.PTree.get Wrappers.expected_temp le = Some expected ->
    Maps.PTree.get Wrappers.new_temp le = Some new ->
    Maps.PTree.get Wrappers.old_temp le = Some current ->
    CAM_linearization_redex
      (CAM_lin_CAS_success (b, Ptrofs.unsigned ofs)
        expected new current)
      (ClightLang.Core_State CAM_local_atomic_CAS_function
        (Clight.Sassign Wrappers.target_lvalue Wrappers.new_expr) k e le)
| CAM_CAS_failure_redex : forall b ofs expected new current k e le,
    Maps.PTree.get Wrappers.target_temp le = Some (Vptr b ofs) ->
    Maps.PTree.get Wrappers.expected_temp le = Some expected ->
    Maps.PTree.get Wrappers.new_temp le = Some new ->
    CAM_linearization_redex
      (CAM_lin_CAS_failure (b, Ptrofs.unsigned ofs)
        expected new current)
      (ClightLang.Core_State CAM_local_atomic_CAS_function
        (Clight.Sset Wrappers.old_temp Wrappers.target_lvalue) k e le).

Definition CAM_linearization_memory
    (kind : CAM_linearization_kind) (tm tm' : mem) : Prop :=
  match kind with
  | CAM_lin_load l v => load tm l Mint32 = Some v /\ tm' = tm
  | CAM_lin_store l v => store tm l Mint32 v = Some tm'
  | CAM_lin_CAS_success l _ new _ => store tm l Mint32 new = Some tm'
  | CAM_lin_CAS_failure l _ _ current =>
      load tm l Mint32 = Some current /\ tm' = tm
  end.

Inductive CAM_local_linearization (tge : Clight.genv)
    (kind : CAM_linearization_kind) (i : nat) :
    CAM_local_config -> CAM_trace -> CAM_local_config -> Prop :=
| CAM_local_linearization_intro : forall
    (ttp : gmap nat ClightLang.core) (tm : mem)
    (tcore : ClightLang.core) (T : CAM_trace) (fp : FP.t)
    (tcore' : ClightLang.core) (tm' : mem)
    (Hget : ttp !! i = Some tcore)
    (Hredex : CAM_linearization_redex kind tcore)
    (Hlocal : LocalClight.step2 tge tcore tm fp tcore' tm')
    (Hevents : ev_step_with_mem_ev (Clight_evsem.CLC_evsem tge)
      (CAM_local_core_to_event tcore) tm T
      (CAM_local_core_to_event tcore') tm')
    (Hmemory : CAM_linearization_memory kind tm tm'),
    CAM_local_linearization tge kind i
      (Build_CAM_local_config ttp tm) T
      (Build_CAM_local_config (<[i := tcore']> ttp) tm').

Lemma CAM_local_linearization_step tge kind i tc T tc' :
  CAM_local_linearization tge kind i tc T tc' ->
  CAM_local_step tge i tc T tc'.
Proof. intros Hlin; inversion Hlin; subst; econstructor; eauto. Qed.

(** A target atomic path is split immediately around its concrete local
    linearization step.  These boundary memories are simulation obligations,
    never alternate constructors of the state-matching relation. *)
Inductive CAM_linearization_path {J : Type}
    (tge : Clight.genv)
    (memory_match : J -> mem -> mem -> Prop)
    (kind : CAM_linearization_kind) (i : nat)
    (j_before j_after : J) (sm_before sm_after : mem) :
    CAM_local_config -> CAM_trace -> CAM_local_config -> Prop :=
| CAM_linearization_path_intro :
    forall tc tc_before tc_after tc' Tpre Tlin Tpost,
      CAM_local_star_at tge i tc Tpre tc_before ->
      memory_match j_before sm_before (CAM_target_memory tc_before) ->
      CAM_local_linearization tge kind i tc_before Tlin tc_after ->
      memory_match j_after sm_after (CAM_target_memory tc_after) ->
      CAM_local_star_at tge i tc_after Tpost tc' ->
      CAM_linearization_path tge memory_match kind i
        j_before j_after sm_before sm_after
        tc (Tpre ++ Tlin ++ Tpost) tc'.

Lemma CAM_linearization_path_plus {J : Type}
    (tge : Clight.genv) (memory_match : J -> mem -> mem -> Prop)
    kind i j j' sm sm' tc T tc' :
  CAM_linearization_path tge memory_match kind i
    j j' sm sm' tc T tc' ->
  CAM_local_plus_at tge i tc T tc'.
Proof.
  intros Hpath. inversion Hpath; subst.
  eapply CAM_local_star_step_star_plus; eauto.
  eapply CAM_local_linearization_step; eauto.
Qed.

(** ** The single bit-independent configuration relation *)

Definition CAM_source_thread_state (sge : Clight.genv) : Type :=
  @tstate address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language sge).

Definition CAM_running {sge : Clight.genv}
    (score : Clight_core.CC_core) (pending : CAM_trace) :
    CAM_source_thread_state sge :=
  @Running address val _ _ mem memory_chunk clight_mem_mixin
    (Clight_language sge) score pending.

Inductive CAM_option_thread_match
    {sge : Clight.genv} {J : Type}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop) (j : J) :
    option (CAM_source_thread_state sge) ->
    option ClightLang.core -> Prop :=
| CAM_thread_absent : CAM_option_thread_match core_match j None None
| CAM_thread_running : forall score pending tcore,
    core_match j score tcore ->
    CAM_option_thread_match core_match j
      (Some (CAM_running score pending)) (Some tcore).

(** Pending source events and the reservation map are ghost state.  No target
    atomic bit exists here, and no critical/uncritical cases occur. *)
Record CAM_match_state {J : Type} {sge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    (j : J) (sc : CAM_config sge) (tc : CAM_local_config) : Prop := {
  CAM_match_memory :
    memory_match j (CAM_memory sc) (CAM_target_memory tc);
  CAM_match_threads : forall i,
    CAM_option_thread_match core_match j (CAM_threads sc !! i)
      (CAM_target_threads tc !! i)
}.

Lemma CAM_match_state_commit {J : Type} {sge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    j stp sm mu i score pending mu' tc :
  stp !! i = Some (CAM_running score pending) ->
  CAM_match_state core_match memory_match j
    (Build_CAM_config sge stp sm mu) tc ->
  CAM_match_state core_match memory_match j
    (Build_CAM_config sge (<[i := CAM_running score []]> stp) sm mu') tc.
Proof.
  intros Hget Hmatch.
  change (gmap nat (CAM_source_thread_state sge)) in stp.
  destruct Hmatch as [Hmemory Hthreads].
  constructor; [exact Hmemory |].
  intros other.
  change (CAM_option_thread_match core_match j
    ((<[i := CAM_running score []]> stp) !! other)
    (CAM_target_threads tc !! other)).
  destruct (Nat.eq_dec other i) as [-> | Hne].
  - specialize (Hthreads i).
    cbn [CAM_threads] in Hthreads.
    rewrite Hget in Hthreads. inversion Hthreads; subst.
    assert (Hlookup :
      (<[i := CAM_running score []]> stp) !! i =
        Some (CAM_running score [])) by apply lookup_insert_eq.
    rewrite Hlookup. constructor; assumption.
  - assert (Hlookup :
      (<[i := CAM_running score []]> stp) !! other = stp !! other).
    { apply lookup_insert_ne. congruence. }
    rewrite Hlookup. apply Hthreads.
Qed.

(** ** Safe source steps and commit stuttering *)

Definition CAM_safe_step (sge : Clight.genv) i sc T sc' : Prop :=
  CAM_step sge i sc T sc' /\
  CAM_assign_loc_value_syntax sc /\
  CAM_no_explicit_stuck sc'.

Lemma CAM_execution_head_is_safe sge sc sc' final i T :
  CAM_assign_loc_value_syntax sc ->
  CAM_step sge i sc T sc' ->
  CAM_execution sge sc' final ->
  CAM_safe_step sge i sc T sc'.
Proof.
  intros Hsyntax Hstep Hexec.
  split; [exact Hstep |]. split; [exact Hsyntax |].
  eapply CAM_execution_source_no_explicit_stuck_1; eauto.
Qed.

Inductive CAM_commit_transition (sge : Clight.genv) :
    nat -> CAM_config sge -> CAM_trace -> CAM_config sge -> Prop :=
| CAM_commit_transition_intro : forall stp sm mu i score pending mu'
    (Hget : stp !! i = Some (CAM_running score pending))
    (Hne : pending <> [])
    (Hcommit : fin pending mu = Some mu'),
    CAM_commit_transition sge i
      (Build_CAM_config sge stp sm mu) []
      (Build_CAM_config sge
        (<[i := CAM_running score []]> stp) sm mu').

Lemma CAM_commit_transition_is_step sge i sc T sc' :
  CAM_commit_transition sge i sc T sc' -> CAM_step sge i sc T sc'.
Proof.
  intros Hcommit.
  destruct Hcommit as [stp sm mu i score pending mu' Hget Hne Hcommit].
  eapply CAM_core_commit; eauto.
Qed.

(** ** Constructor-local simulation obligations *)

Record CAM_local_simulation_cases
    {J : Type} {sge tge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    (index_incr : J -> J -> Prop) : Prop := {
  CAM_sim_core_try :
    forall stp sm mu i score T score' sm' mu'
      (Hget : stp !! i = Some (CAM_running score []))
      (Hstep : ev_step_with_mem_ev (Clight_evsem.CLC_evsem sge)
        score sm T score' sm')
      (Hreserve : rsv T mu = Some mu')
      (Hsyntax : clight_core_assign_loc_value_syntax sge score)
      j tc,
      CAM_match_state core_match memory_match j
        (Build_CAM_config sge stp sm mu) tc ->
      exists j' tc',
        index_incr j j' /\
        CAM_local_step tge i tc T tc' /\
        CAM_match_state core_match memory_match j'
          (Build_CAM_config sge
            (<[i := CAM_running score' T]> stp) sm' mu') tc';

  CAM_sim_atomic_load :
    forall stp sm mu i score ly l v K
      (Hget : stp !! i = Some (CAM_running score []))
      (Hext : clight_at_external score = Some (ALoad ly l, K))
      (Hmu : readable mu (layout_to_locs l ly))
      (Hload : load sm l ly = Some v)
      (Hdefined : clight_val_defined v)
      j tc,
      CAM_match_state core_match memory_match j
        (Build_CAM_config sge stp sm mu) tc ->
      exists j' tc',
        index_incr j j' /\
        CAM_linearization_path tge memory_match (CAM_lin_load l v) i
          j j' sm sm tc (CAM_read_trace l ly) tc' /\
        CAM_match_state core_match memory_match j'
          (Build_CAM_config sge
            (<[i := CAM_running (K (Some v)) []]> stp) sm mu) tc';

  CAM_sim_atomic_store :
    forall stp sm mu i score ly l v sm' K
      (Hget : stp !! i = Some (CAM_running score []))
      (Hext : clight_at_external score = Some (AStore ly l v, K))
      (Hmu : writable mu (layout_to_locs l ly))
      (Hstore : store sm l ly v = Some sm')
      (Hdefined : clight_val_defined v)
      j tc,
      CAM_match_state core_match memory_match j
        (Build_CAM_config sge stp sm mu) tc ->
      exists j' tc',
        index_incr j j' /\
        CAM_linearization_path tge memory_match (CAM_lin_store l v) i
          j j' sm sm' tc (CAM_write_trace l ly) tc' /\
        CAM_match_state core_match memory_match j'
          (Build_CAM_config sge
            (<[i := CAM_running (K None) []]> stp) sm' mu) tc';

  CAM_sim_atomic_CAS_success :
    forall stp sm mu i score ly l expected new current sm' K
      (Hget : stp !! i = Some (CAM_running score []))
      (Hext : clight_at_external score =
        Some (ACAS ly l expected new, K))
      (Hmu : writable mu (layout_to_locs l ly))
      (Hload : load sm l ly = Some current)
      (Hdefined_current : clight_val_defined current)
      (Heq : clight_ValEq score sm current expected)
      (Hstore : store sm l ly new = Some sm')
      (Hdefined_new : clight_val_defined new)
      j tc,
      CAM_match_state core_match memory_match j
        (Build_CAM_config sge stp sm mu) tc ->
      exists j' tc',
        index_incr j j' /\
        CAM_linearization_path tge memory_match
          (CAM_lin_CAS_success l expected new current) i
          j j' sm sm' tc
          (CAM_read_trace l ly ++ CAM_write_trace l ly) tc' /\
        CAM_match_state core_match memory_match j'
          (Build_CAM_config sge
            (<[i := CAM_running (K (Some Vtrue)) []]> stp) sm' mu) tc';

  CAM_sim_atomic_CAS_failure :
    forall stp sm mu i score ly l expected new current K
      (Hget : stp !! i = Some (CAM_running score []))
      (Hext : clight_at_external score =
        Some (ACAS ly l expected new, K))
      (Hmu : readable mu (layout_to_locs l ly))
      (Hload : load sm l ly = Some current)
      (Hdefined_current : clight_val_defined current)
      (Hneq : clight_ValNEq score sm current expected)
      j tc,
      CAM_match_state core_match memory_match j
        (Build_CAM_config sge stp sm mu) tc ->
      exists j' tc',
        index_incr j j' /\
        CAM_linearization_path tge memory_match
          (CAM_lin_CAS_failure l expected new current) i
          j j' sm sm tc (CAM_read_trace l ly) tc' /\
        CAM_match_state core_match memory_match j'
          (Build_CAM_config sge
            (<[i := CAM_running (K (Some Vfalse)) []]> stp) sm mu) tc'
}.

(** The generic Smallstep-style diagram below deliberately forgets which
    nonempty target path implements a source rule.  These two lemmas retain
    the sharper facts needed by clients of the atomic-machine simulation:
    [Core_Try] is exactly one local core step on [i], while [Core_Commit]
    leaves the target configuration unchanged.  The four atomic projections
    of [CAM_local_simulation_cases] analogously retain their distinguished
    [CAM_linearization_path]. *)
Lemma CAM_core_try_simulates_one_from_cases
    {J : Type} {sge tge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    (index_incr : J -> J -> Prop)
    (Hcases : @CAM_local_simulation_cases J sge tge
      core_match memory_match index_incr)
    (stp : CAM_tpool sge) (sm : mem) (mu : CAM_rw_map) (i : nat)
    (score : Clight_core.CC_core) (T : CAM_trace)
    (score' : Clight_core.CC_core) (sm' : mem) (mu' : CAM_rw_map)
    (Hget : stp !! i = Some (CAM_running score []))
    (Hstep : ev_step_with_mem_ev (Clight_evsem.CLC_evsem sge)
      score sm T score' sm')
    (Hreserve : rsv T mu = Some mu')
    (Hsyntax : clight_core_assign_loc_value_syntax sge score)
    (j : J) (tc : CAM_local_config)
    (Hmatch : CAM_match_state core_match memory_match j
      (Build_CAM_config sge stp sm mu) tc) :
  exists j' tc',
    index_incr j j' /\
    CAM_local_step tge i tc T tc' /\
    CAM_match_state core_match memory_match j'
      (Build_CAM_config sge
        (<[i := CAM_running score' T]> stp) sm' mu') tc'.
Proof.
  eapply CAM_sim_core_try; eauto.
Qed.

Lemma CAM_core_commit_simulates_zero
    {J : Type} {sge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    (j : J) (stp : CAM_tpool sge) (sm : mem) (mu : CAM_rw_map)
    (i : nat) (score : Clight_core.CC_core) (pending : CAM_trace)
    (mu' : CAM_rw_map) (tc : CAM_local_config)
    (Hget : stp !! i = Some (CAM_running score pending))
    (Hne : pending <> [])
    (Hcommit : fin pending mu = Some mu')
    (Hmatch : CAM_match_state core_match memory_match j
      (Build_CAM_config sge stp sm mu) tc) :
  CAM_commit_transition sge i
      (Build_CAM_config sge stp sm mu) []
      (Build_CAM_config sge
        (<[i := CAM_running score []]> stp) sm mu') /\
  CAM_match_state core_match memory_match j
      (Build_CAM_config sge
        (<[i := CAM_running score []]> stp) sm mu') tc.
Proof.
  split.
  - econstructor; eauto.
  - eapply CAM_match_state_commit; eauto.
Qed.

(** ** Smallstep-style forward-simulation diagram *)

Definition CAM_forward_simulation_diagram
    {J : Type} {sge tge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    (index_incr : J -> J -> Prop) : Prop :=
  forall i sc T sc' j tc,
    CAM_safe_step sge i sc T sc' ->
    CAM_match_state core_match memory_match j sc tc ->
    (exists j' tc',
      index_incr j j' /\
      CAM_local_plus_at tge i tc T tc' /\
      CAM_match_state core_match memory_match j' sc' tc') \/
    (CAM_commit_transition sge i sc T sc' /\
      CAM_match_state core_match memory_match j sc' tc).

Theorem CAM_forward_simulation_from_cases
    {J : Type} {sge tge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    (index_incr : J -> J -> Prop) :
  @CAM_local_simulation_cases J sge tge
    core_match memory_match index_incr ->
  @CAM_forward_simulation_diagram J sge tge
    core_match memory_match index_incr.
Proof.
  intros Hcases. destruct Hcases as
    [Htry Hload_case Hstore_case HCAS_success_case HCAS_failure_case].
  intros i sc T sc' j tc
    [Hsource_step [Hsyntax Hnot_stuck]] Hmatch.
  destruct Hsource_step.
  - left.
    edestruct Htry as (j' & tc' & Hincr & Htarget_step & Hmatch'); eauto.
    exists j', tc'. split; [exact Hincr |]. split.
    + now apply CAM_local_plus_one.
    + exact Hmatch'.
  - right. split.
    + econstructor; eauto.
    + eapply CAM_match_state_commit; eauto.
  - left.
    edestruct Hload_case as (j' & tc' & Hincr & Hpath & Hmatch'); eauto.
    exists j', tc'. split; [exact Hincr |]. split.
    + exact (CAM_linearization_path_plus tge memory_match
        (CAM_lin_load l v) i j j' sm sm tc
        (CAM_read_trace l ly) tc' Hpath).
    + exact Hmatch'.
  - left.
    edestruct Hstore_case as (j' & tc' & Hincr & Hpath & Hmatch'); eauto.
    exists j', tc'. split; [exact Hincr |]. split.
    + exact (CAM_linearization_path_plus tge memory_match
        (CAM_lin_store l v) i j j' sm sm' tc
        (CAM_write_trace l ly) tc' Hpath).
    + exact Hmatch'.
  - left.
    edestruct HCAS_success_case as
      (j' & tc' & Hincr & Hpath & Hmatch'); eauto.
    exists j', tc'. split; [exact Hincr |]. split.
    + exact (CAM_linearization_path_plus tge memory_match
        (CAM_lin_CAS_success l expected new current) i
        j j' sm sm' tc
        (CAM_read_trace l ly ++ CAM_write_trace l ly) tc' Hpath).
    + exact Hmatch'.
  - left.
    edestruct HCAS_failure_case as
      (j' & tc' & Hincr & Hpath & Hmatch'); eauto.
    exists j', tc'. split; [exact Hincr |]. split.
    + exact (CAM_linearization_path_plus tge memory_match
        (CAM_lin_CAS_failure l expected new current) i
        j j' sm sm tc (CAM_read_trace l ly) tc' Hpath).
    + exact Hmatch'.
  - exfalso. apply (Hnot_stuck i).
    change (gmap nat (CAM_source_thread_state sge)) in stp.
    cbn [CAM_threads CAM_stuck_state].
    exact (lookup_insert_eq stp i
      (@StuckState address val _ _ mem memory_chunk clight_mem_mixin
        (Clight_language sge))).
Qed.

(** The explicit first-step/suffix form requested by the CompCert diagram.
    The first target step and every suffix step use the source thread [i],
    and the observations satisfy [T = T1 ++ T2].  The only zero-step case
    carries evidence that the source transition was [Core_Commit]. *)
Corollary CAM_forward_simulation_step_split
    {J : Type} {sge tge : Clight.genv}
    (core_match : J -> Clight_core.CC_core ->
      ClightLang.core -> Prop)
    (memory_match : J -> mem -> mem -> Prop)
    (index_incr : J -> J -> Prop)
    (Hsim : @CAM_forward_simulation_diagram J sge tge
      core_match memory_match index_incr) :
  forall i sc T sc' j tc,
    CAM_safe_step sge i sc T sc' ->
    CAM_match_state core_match memory_match j sc tc ->
    (exists j' tc1 T1 tc2 T2,
      index_incr j j' /\
      CAM_local_step tge i tc T1 tc1 /\
      CAM_local_star_at tge i tc1 T2 tc2 /\
      T = T1 ++ T2 /\
      CAM_match_state core_match memory_match j' sc' tc2) \/
    (CAM_commit_transition sge i sc T sc' /\
      CAM_match_state core_match memory_match j sc' tc).
Proof.
  intros i sc T sc' j tc Hstep Hmatch.
  destruct (Hsim i sc T sc' j tc Hstep Hmatch)
    as [(j' & tc' & Hincr & Hplus & Hmatch') | Hstutter].
  - left. destruct Hplus as (tc1 & T1 & T2 & Hfirst & Hrest & Heq).
    exists j', tc1, T1, tc', T2. auto.
  - right; exact Hstutter.
Qed.

(** ** Program-level packaging *)

Record CAM_local_program_pair
    (P : ClightLang.clight_comp_unit) (ids : Wrappers.wrapper_ids)
    (sge tge : Clight.genv) : Prop := {
  CAM_program_ids_wf : Wrappers.wrapper_ids_wf ids;
  CAM_program_atomic_declarations :
    ClientInit.client_atomic_declarations ids P;
  CAM_program_def_ids_norepet :
    list_norepet (map fst (ClightLang.cu_defs P));
  CAM_program_source_initialized :
    CAM_source_program_initialized P sge;
  CAM_program_target_initialized :
    CAM_local_program_initialized (CAM_local_translated_program P ids) tge;
  CAM_program_block_alignment : CAM_program_blocks_aligned sge tge;
  CAM_program_source_fragment : CAM_source_fragment P;
  CAM_program_external_restriction :
    CAM_program_only_atomic_externals ids P
}.

Section CAMProgramForwardSimulation.

  Context {sge tge : Clight.genv}.
  Variable P : ClightLang.clight_comp_unit.
  Variable ids : Wrappers.wrapper_ids.
  Context {J : Type}.
  Variable core_match : J -> Clight_core.CC_core ->
    ClightLang.core -> Prop.
  Variable memory_match : J -> mem -> mem -> Prop.
  Variable index_incr : J -> J -> Prop.

  (** The constructor-local cases are the remaining semantic proof boundary,
      including the concrete core/memory relations, ordinary Clight
      lockstep, and marker-free wrapper paths.  This theorem only packages
      those cases; its [_from_cases] name is intentional. *)
  Theorem CAM_program_forward_simulation_from_cases
      (Hprograms : CAM_local_program_pair P ids sge tge)
      (Hlocal_cases : CAM_local_program_pair P ids sge tge ->
        @CAM_local_simulation_cases J sge tge
          core_match memory_match index_incr) :
    @CAM_forward_simulation_diagram J sge tge
      core_match memory_match index_incr.
  Proof.
    apply CAM_forward_simulation_from_cases.
    now apply Hlocal_cases.
  Qed.

End CAMProgramForwardSimulation.
