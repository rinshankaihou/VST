(** The atomic-machine language interface instantiated with Clight's event
    semantics. *)

Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Cop.

From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.BinInt.
Import ListNotations.

Require Import stdpp.base.

Require Import VST.sepcomp.event_semantics.
Set Warnings "-custom-entry-overridden".
Require Import VST.veric.Clight_evsem.
Require Import VST.veric.val_lemmas.
Set Warnings "custom-entry-overridden".
Require Import atomic_machine.atomic_machine.
Require Import atomic_machine.clight_atomic_specs.

Import Address Values.

Section ClightInstantiation.

  (** Clight-specialized atomic-machine types. *)
  Local Notation clight_mem_ev := (@mem_ev address).

  (** Decide whether an arbitrary Clight fundef is one particular external
      declaration.  This is the only fundef equality needed by the decoder;
      deciding equality of internal fundefs would additionally require
      equality for recursive Clight function bodies. *)
  #[local] Instance clight_external_fundef_dec
      (fd : Clight.fundef) (ef : external_function)
      (targs : list Ctypes.type) (tres : Ctypes.type)
      (cc : calling_convention) :
      Decision (fd = Ctypes.External ef targs tres cc).
  Proof.
    destruct fd as [f | ef' targs' tres' cc'];
      [right; discriminate |].
    destruct (external_function_eq ef' ef);
      [subst ef' | right; congruence].
    destruct (Ctypes.typelist_eq targs' targs);
      [subst targs' | right; congruence].
    destruct (Ctypes.type_eq tres' tres);
      [subst tres' | right; congruence].
    destruct (calling_convention_eq cc' cc);
      [subst cc' | right; congruence].
    left; reflexivity.
  Defined.

  (** Recover the memory chunk from the Clight type which is actually
      accessed.  Atomic declarations are rejected when that type is not a
      by-value Clight type; the decoder never chooses a chunk independently
      of the declaration. *)
  Definition clight_value_chunk (ty : Ctypes.type) : option memory_chunk :=
    match Ctypes.access_mode ty with
    | Ctypes.By_value chunk => Some chunk
    | _ => None
    end.

  (** For a load, the declared result type is also the pointed-to object
      type.  Keep that type, rather than only its chunk, because it also
      determines which values and casts the source-level operation supports. *)
  Definition clight_atomic_load_type (fd : Clight.fundef) :
      option Ctypes.type :=
    match fd with
    | Ctypes.External _ [Ctypes.Tpointer pointee _] result _ =>
        if Ctypes.type_eq pointee result then
          match clight_value_chunk result with
          | Some _ => Some result
          | None => None
          end
        else None
    | _ => None
    end.

  Definition clight_atomic_load_chunk (fd : Clight.fundef) :
      option memory_chunk :=
    match clight_atomic_load_type fd with
    | Some ty => clight_value_chunk ty
    | None => None
    end.

  (** A store returns [void], so its access layout comes from the declared
      value parameter and must agree with the pointer's pointee type. *)
  Definition clight_atomic_store_type (fd : Clight.fundef) :
      option Ctypes.type :=
    match fd with
    | Ctypes.External _
        [Ctypes.Tpointer pointee _; stored_type] Ctypes.Tvoid _ =>
        if Ctypes.type_eq pointee stored_type then
          match clight_value_chunk stored_type with
          | Some _ => Some stored_type
          | None => None
          end
        else None
    | _ => None
    end.

  Definition clight_atomic_store_chunk (fd : Clight.fundef) :
      option memory_chunk :=
    match clight_atomic_store_type fd with
    | Some ty => clight_value_chunk ty
    | None => None
    end.

  (** A CAS returns a success flag rather than the accessed object.  Its
      layout therefore comes from the declared expected/new value type,
      checked against both the pointee type and the other value parameter. *)
  Definition clight_atomic_CAS_type (fd : Clight.fundef) :
      option Ctypes.type :=
    match fd with
    | Ctypes.External _
        [Ctypes.Tpointer pointee _; expected_type; new_type] _ _ =>
        if Ctypes.type_eq pointee expected_type then
          if Ctypes.type_eq expected_type new_type then
            match clight_value_chunk expected_type with
            | Some _ => Some expected_type
            | None => None
            end
          else None
        else None
    | _ => None
    end.

  Definition clight_atomic_CAS_chunk (fd : Clight.fundef) :
      option memory_chunk :=
    match clight_atomic_CAS_type fd with
    | Some ty => clight_value_chunk ty
    | None => None
    end.

  (** Decode only the three canonical atomic client declarations.  Both the
      external ABI signature and the Clight argument/result declaration are
      checked.  The access chunk is recovered from that declaration: from
      the result type for load, and from the object/value type for store and
      CAS.  Store and CAS operands must also have their dynamically expected
      [Vint] shape.  Consequently, a reserved name with a malformed
      declaration or argument list is not an atomic-machine operation. *)
  Definition clight_decode_atomic (fd : Clight.fundef) (args : list val)
      : option (@atomic_op address val memory_chunk) :=
    match fd with
    | Ctypes.External (EF_external name _) _ _ _ =>
        if string_dec name ("atomic_load"%string) then
          if decide
              (fd = ClightAtomicSpecs.client_atomic_load_external) then
            match args, clight_atomic_load_chunk fd with
            | [Vptr b ofs], Some chunk =>
                Some (ALoad chunk (b, Ptrofs.unsigned ofs))
            | _, _ => None
            end
          else None
        else if string_dec name ("atomic_store"%string) then
          if decide
              (fd = ClightAtomicSpecs.client_atomic_store_external) then
            match args, clight_atomic_store_chunk fd with
            | [Vptr b ofs; Vint n], Some chunk =>
                Some (AStore chunk (b, Ptrofs.unsigned ofs) (Vint n))
            | _, _ => None
            end
          else None
        else if string_dec name ("atomic_CAS"%string) then
          if decide
              (fd = ClightAtomicSpecs.client_atomic_CAS_external) then
            match args, clight_atomic_CAS_chunk fd with
            | [Vptr b ofs; Vint expected; Vint new], Some chunk =>
                Some (ACAS chunk (b, Ptrofs.unsigned ofs)
                  (Vint expected) (Vint new))
            | _, _ => None
            end
          else None
        else None
    | _ => None
    end.

  Definition clight_val_defined (v : val) : Prop := v <> Vundef.

  (** Recover the operand type of a pending CAS from the declaration that
      [clight_decode_atomic] inspected.  The CAS result type is a success
      flag; the comparison type is instead the common pointee/argument type. *)
  Definition clight_pending_CAS_type
      (c : Clight_core.CC_core) : option Ctypes.type :=
    match c with
    | Clight_core.Callstate fd _ _ => clight_atomic_CAS_type fd
    | _ => None
    end.

  (** Use Clight's typed comparison, not the untyped representation-level
      [Val.cmpu_bool].  In particular, on a 32-bit target a pointer-shaped
      value may be returned through [int], but an [int == int] expression
      whose runtime operand is that pointer has no result; CAM therefore has
      no CAS branch in exactly the same case as the concrete wrapper. *)
  Definition clight_ValEq
      (c : Clight_core.CC_core) (m : mem) (v1 v2 : val) : Prop :=
    match clight_pending_CAS_type c with
    | Some ty => Cop.sem_cmp Ceq v1 ty v2 ty m = Some Vtrue
    | None => False
    end.

  Definition clight_ValNEq
      (c : Clight_core.CC_core) (m : mem) (v1 v2 : val) : Prop :=
    match clight_pending_CAS_type c with
    | Some ty => Cop.sem_cmp Ceq v1 ty v2 ty m = Some Vfalse
    | None => False
    end.

  Local Definition byte_addresses
      (l : address) (len : nat) : list address :=
    let '(b, ofs) := l in
    map (fun i => (b, ofs + Z.of_nat i)) (seq 0 len).

  Local Definition into_bytes
      (mk_ev : address -> clight_mem_ev) (b : block) (ofs : Z)
      (bytes : list memval) : list clight_mem_ev :=
    map mk_ev (byte_addresses (b, ofs) (length bytes)).

  Local Definition into_range
      (mk_ev : address -> clight_mem_ev)
      (b : block) (ofs : Z) (len : nat) : list clight_mem_ev :=
    map mk_ev (byte_addresses (b, ofs) len).

  Local Definition into_alloc (b : block) (lo hi : Z)
      : list clight_mem_ev :=
    into_range Alloc b lo (Z.to_nat (hi - lo)).

  Local Definition into_free_range (r : block * Z * Z)
      : list clight_mem_ev :=
    let '(b, lo, hi) := r in
    into_range Free b lo (Z.to_nat (hi - lo)).

  (** Expand each evsem event into byte-granular atomic-machine events. *)
  Definition clight_into_ev (ev : mem_event) : list clight_mem_ev :=
    match ev with
    | event_semantics.Read b ofs _ bytes => into_bytes Read b ofs bytes
    | event_semantics.Write b ofs bytes => into_bytes Write b ofs bytes
    | event_semantics.Alloc b lo hi => into_alloc b lo hi
    | event_semantics.Free ranges => flat_map into_free_range ranges
    end.

  Definition clight_into_evs (trace : list mem_event) : list clight_mem_ev :=
    flat_map clight_into_ev trace.

  (** Classify a pending atomic call and compute its continuation.  This does
      not execute an external function: the atomic-machine read, write, and
      CAS rules consume the decoded operation and continuation directly. *)
  Definition clight_at_external
      (c : Clight_core.CC_core)
      : option (atomic_op * (option val -> Clight_core.CC_core)) :=
    match c with
    | Clight_core.Callstate fd args k =>
        match clight_decode_atomic fd args with
        | Some (ALoad ly l) =>
            Some (ALoad ly l, fun ov =>
              Clight_core.Returnstate (force_val ov) k)
        | Some (AStore ly l v) =>
            Some (AStore ly l v, fun _ => Clight_core.Returnstate Vundef k)
        | Some (ACAS ly l v_exp v_new) =>
            Some (ACAS ly l v_exp v_new, fun ov =>
              Clight_core.Returnstate (force_val ov) k)
        | None => None
        end
    | _ => None
    end.

  #[global] Instance clight_mem_mixin :
      MemMixin (Loc := address) (Val := val)
        (Mem := mem) (Layout := memory_chunk) :=
    {| load := fun m l chunk =>
        let '(b, ofs) := l in Mem.load chunk m b ofs;
      store := fun m l chunk v =>
        let '(b, ofs) := l in Mem.store chunk m b ofs v;
      layout_to_locs := fun l chunk =>
        byte_addresses l (size_chunk_nat chunk) |}.

  (** An [event_semantics.ev_step] with its trace expanded to byte-granular
      atomic-machine events. *)
  Inductive ev_step_with_mem_ev
      (evsem_inst : @event_semantics.EvSem Clight_core.CC_core) :
      Clight_core.CC_core -> mem -> list clight_mem_ev ->
      Clight_core.CC_core -> mem -> Prop :=
  | ev_step_with_mem_ev_intro c m T c' m' :
      event_semantics.ev_step evsem_inst c m T c' m' ->
      ev_step_with_mem_ev evsem_inst c m (clight_into_evs T) c' m'.

  #[global] Instance Clight_language (ge : Clight.genv)
      : @sqlang address val _ _ mem memory_chunk clight_mem_mixin :=
    {| sqlang_thrd_st := Clight_core.CC_core;
      sqlang_true_val := Values.Vtrue;
      sqlang_false_val := Values.Vfalse;
      sqlang_step := ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge);
      sqlang_at_external := clight_at_external;
      sqlang_val_defined := clight_val_defined;
      sqlang_ValEq := clight_ValEq;
      sqlang_ValNEq := clight_ValNEq |}.

End ClightInstantiation.
