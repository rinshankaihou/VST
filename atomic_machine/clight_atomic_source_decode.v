(** Structural facts about the source atomic-call decoder.

    These lemmas deliberately expose everything that
    [clight_at_external] learned from a Clight core.  In particular, the
    decoder fixes the complete external declaration, derives the access chunk
    from that declaration's result/object type, and exposes the pointer-shaped
    first argument, byte address, integer store/CAS operands, and
    continuation.  For the canonical integer declarations the derived chunk
    computes to [Mint32]. *)

Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Clight.

From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Require Import stdpp.decidable.

Require Import VST.veric.Clight_evsem.
Require Import VST.veric.val_lemmas.
Require Import compcert.concurrency.common.clight_val_casted.
Require Import atomic_machine.atomic_machine.
Require Import atomic_machine.clight_atomic_specs.
Require Import atomic_machine.clight_at_mach.

Import Address Values.

(** Destruct a runtime argument list, pruning shapes that contradict a
    decoder equation. *)
Ltac destruct_atomic_args args H :=
  destruct args as [|v args];
  [ cbn in H; try discriminate
  | destruct v; cbn in H; try discriminate;
      try destruct_atomic_args args H ].

(** Resolve the three reserved names before inspecting dynamic arguments.
    This keeps decoder inversions from branching over every value shape in
    every name/declaration branch. *)
Ltac destruct_atomic_name name H :=
  destruct (string_dec name ("atomic_load"%string)) as [Hload | Hload];
  [ subst name
  | destruct (string_dec name ("atomic_store"%string))
      as [Hstore | Hstore];
    [ subst name
    | destruct (string_dec name ("atomic_CAS"%string)) as [HCAS | HCAS];
      [ subst name | discriminate ] ] ].

Ltac destruct_atomic_declaration H :=
  case_decide as Hdeclaration;
  [ inversion Hdeclaration; subst
  | discriminate ].

(** ** Canonical forward computations *)

Lemma clight_decode_atomic_rejects_wrong_load_signature sg b ofs :
  sg <> ClightAtomicSpecs.atomic_load_signature ->
  clight_decode_atomic
    (Ctypes.External (EF_external ("atomic_load"%string) sg)
      [ClightAtomicSpecs.atomic_pointer_type]
      ClightAtomicSpecs.tint cc_default)
    [Vptr b ofs] = None.
Proof.
  intros Hneq. cbn [clight_decode_atomic].
  rewrite dec_eq_true.
  case_decide as Hdeclaration; [| reflexivity].
  unfold ClightAtomicSpecs.client_atomic_load_external in Hdeclaration.
  inversion Hdeclaration. contradiction.
Qed.

Lemma clight_at_external_atomic_load b ofs k :
  clight_at_external
    (Clight_core.Callstate
      ClightAtomicSpecs.client_atomic_load_external
      [Vptr b ofs] k) =
  Some
    (ALoad Mint32 (b, Ptrofs.unsigned ofs),
      fun ov => Clight_core.Returnstate (force_val ov) k).
Proof.
  cbn [clight_at_external clight_decode_atomic
    ClightAtomicSpecs.client_atomic_load_external].
  rewrite ! dec_eq_true. reflexivity.
Qed.

Lemma clight_at_external_atomic_store b ofs n k :
  clight_at_external
    (Clight_core.Callstate
      ClightAtomicSpecs.client_atomic_store_external
      [Vptr b ofs; Vint n] k) =
  Some
    (AStore Mint32 (b, Ptrofs.unsigned ofs) (Vint n),
      fun _ => Clight_core.Returnstate Vundef k).
Proof.
  cbn [clight_at_external clight_decode_atomic
    ClightAtomicSpecs.client_atomic_store_external].
  rewrite ! dec_eq_true. reflexivity.
Qed.

Lemma clight_at_external_atomic_CAS b ofs expected new k :
  clight_at_external
    (Clight_core.Callstate
      ClightAtomicSpecs.client_atomic_CAS_external
      [Vptr b ofs; Vint expected; Vint new] k) =
  Some
    (ACAS Mint32 (b, Ptrofs.unsigned ofs) (Vint expected) (Vint new),
      fun ov => Clight_core.Returnstate (force_val ov) k).
Proof.
  cbn [clight_at_external clight_decode_atomic
    ClightAtomicSpecs.client_atomic_CAS_external].
  rewrite ! dec_eq_true. reflexivity.
Qed.

(** ** Exact inversion of decoded calls *)

Lemma clight_at_external_load_inv c ly l K :
  clight_at_external c = Some (ALoad ly l, K) ->
  exists b ofs k,
    c = Clight_core.Callstate
          ClightAtomicSpecs.client_atomic_load_external [Vptr b ofs] k /\
    ly = Mint32 /\
    l = (b, Ptrofs.unsigned ofs) /\
    K = (fun ov => Clight_core.Returnstate (force_val ov) k).
Proof.
  intros H.
  destruct c; cbn [clight_at_external] in H; try discriminate.
  destruct f; cbn [clight_decode_atomic] in H; try discriminate.
  destruct e; cbn [clight_decode_atomic] in H; try discriminate.
  destruct_atomic_name name H.
  all: destruct_atomic_declaration H.
  all: destruct_atomic_args l0 H.
  all: inversion H; subst.
  all: repeat eexists; reflexivity.
Qed.

Lemma clight_at_external_store_inv c ly l stored K :
  clight_at_external c = Some (AStore ly l stored, K) ->
  exists b ofs n k,
    c = Clight_core.Callstate
          ClightAtomicSpecs.client_atomic_store_external
          [Vptr b ofs; Vint n] k /\
    ly = Mint32 /\
    l = (b, Ptrofs.unsigned ofs) /\
    stored = Vint n /\
    K = (fun _ => Clight_core.Returnstate Vundef k).
Proof.
  intros H.
  destruct c; cbn [clight_at_external] in H; try discriminate.
  destruct f; cbn [clight_decode_atomic] in H; try discriminate.
  destruct e; cbn [clight_decode_atomic] in H; try discriminate.
  destruct_atomic_name name H.
  all: destruct_atomic_declaration H.
  all: destruct_atomic_args l0 H.
  all: inversion H; subst.
  all: repeat eexists; reflexivity.
Qed.

Lemma clight_at_external_CAS_inv c ly l v_exp v_new K :
  clight_at_external c = Some (ACAS ly l v_exp v_new, K) ->
  exists b ofs expected new k,
    c = Clight_core.Callstate
          ClightAtomicSpecs.client_atomic_CAS_external
          [Vptr b ofs; Vint expected; Vint new] k /\
    ly = Mint32 /\
    l = (b, Ptrofs.unsigned ofs) /\
    v_exp = Vint expected /\
    v_new = Vint new /\
    K = (fun ov => Clight_core.Returnstate (force_val ov) k).
Proof.
  intros H.
  destruct c; cbn [clight_at_external] in H; try discriminate.
  destruct f; cbn [clight_decode_atomic] in H; try discriminate.
  destruct e; cbn [clight_decode_atomic] in H; try discriminate.
  destruct_atomic_name name H.
  all: destruct_atomic_declaration H.
  all: destruct_atomic_args l0 H.
  all: inversion H; subst.
  all: repeat eexists; reflexivity.
Qed.

(** ** Side conditions used by the concrete target wrappers

    The source decoder recovers a pointer-shaped, in-range byte address,
    [Mint32], and [Vint] store/CAS payloads.  The atomic-machine rules reject
    [Vundef] memory transfers.  A defined load result can be returned by the
    wrapper at the declaration-derived type; for CAS, the typed comparison
    additionally forces the current value to be [Vint] whenever either
    branch is taken. *)

Definition clight_wrapper_integer (v : val) : Prop :=
  exists n, v = Vint n.

Definition clight_source_pointer_address (l : address) : Prop :=
  exists b ofs, l = (b, Ptrofs.unsigned ofs).

Definition clight_atomic_wrapper_args_ready
    (op : @atomic_op address val memory_chunk) : Prop :=
  match op with
  | ALoad ly l =>
      ly = Mint32 /\ clight_source_pointer_address l
  | AStore ly l v =>
      ly = Mint32 /\ clight_source_pointer_address l /\
      clight_wrapper_integer v
  | ACAS ly l v_exp v_new =>
      ly = Mint32 /\ clight_source_pointer_address l /\
      clight_wrapper_integer v_exp /\ clight_wrapper_integer v_new
  end.

Lemma clight_at_external_load_args_ready c ly l K :
  clight_at_external c = Some (ALoad ly l, K) ->
  clight_atomic_wrapper_args_ready (ALoad ly l).
Proof.
  intros Hext.
  destruct (clight_at_external_load_inv _ _ _ _ Hext)
    as (b & ofs & k & Hc & Hly & Hl & HK).
  subst ly l.
  split; [reflexivity |].
  exists b, ofs. reflexivity.
Qed.

Lemma clight_at_external_store_args_ready c ly l stored K :
  clight_at_external c = Some (AStore ly l stored, K) ->
  clight_atomic_wrapper_args_ready (AStore ly l stored).
Proof.
  intros Hext.
  destruct (clight_at_external_store_inv _ _ _ _ _ Hext)
    as (b & ofs & n & k & Hc & Hly & Hl & Hstored & HK).
  subst ly l stored.
  repeat split; try reflexivity.
  - exists b, ofs. reflexivity.
  - exists n. reflexivity.
Qed.

Lemma clight_at_external_CAS_args_ready c ly l v_exp v_new K :
  clight_at_external c = Some (ACAS ly l v_exp v_new, K) ->
  clight_atomic_wrapper_args_ready (ACAS ly l v_exp v_new).
Proof.
  intros Hext.
  destruct (clight_at_external_CAS_inv _ _ _ _ _ _ Hext)
    as (b & ofs & expected & new & k & Hc & Hly & Hl &
        Hv_exp & Hv_new & HK).
  subst ly l v_exp v_new.
  repeat split; try reflexivity.
  - exists b, ofs. reflexivity.
  - exists expected. reflexivity.
  - exists new. reflexivity.
Qed.

Lemma clight_wrapper_integer_defined v :
  clight_wrapper_integer v -> v <> Vundef.
Proof.
  intros (n & ->). discriminate.
Qed.

Lemma clight_atomic_load_source_args_defined b ofs :
  clight_val_casted.vals_defined [Vptr b ofs] = true.
Proof. reflexivity. Qed.

Lemma clight_atomic_store_source_args_defined b ofs stored :
  clight_wrapper_integer stored ->
  clight_val_casted.vals_defined [Vptr b ofs; stored] = true.
Proof. intros (n & ->). reflexivity. Qed.

Lemma clight_atomic_CAS_source_args_defined b ofs v_exp v_new :
  clight_wrapper_integer v_exp ->
  clight_wrapper_integer v_new ->
  clight_val_casted.vals_defined [Vptr b ofs; v_exp; v_new] = true.
Proof. intros (expected & ->) (new & ->). reflexivity. Qed.

Lemma clight_atomic_store_source_args_defined_iff b ofs stored :
  clight_val_casted.vals_defined [Vptr b ofs; stored] = true <->
  stored <> Vundef.
Proof.
  destruct stored; cbn; split; intros H; try discriminate; congruence.
Qed.

Lemma clight_atomic_CAS_source_args_defined_iff b ofs v_exp v_new :
  clight_val_casted.vals_defined [Vptr b ofs; v_exp; v_new] = true <->
  v_exp <> Vundef /\ v_new <> Vundef.
Proof.
  destruct v_exp, v_new; cbn; split; intros H;
    try discriminate; try (split; discriminate); tauto.
Qed.
