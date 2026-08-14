(** Canonical Clight declarations for the atomic-machine primitives.

    This small module is shared by the source decoder and the target wrapper
    construction.  Keeping the declarations here makes a successful source
    decode definitionally identify the same external fundef that is linked to
    the wrapper implementation on the target side. *)

Require Import compcert.common.AST.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.

From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Local Open Scope string_scope.

Module ClightAtomicSpecs.

  Definition tint : type := Tint I32 Signed noattr.
  Definition tvoid : type := Tvoid.
  Definition atomic_pointer_type : type := Tpointer tint noattr.

  Definition atomic_load_signature : signature :=
    signature_of_type [atomic_pointer_type] tint cc_default.

  Definition atomic_store_signature : signature :=
    signature_of_type [atomic_pointer_type; tint] tvoid cc_default.

  Definition atomic_CAS_signature : signature :=
    signature_of_type [atomic_pointer_type; tint; tint] tint cc_default.

  Definition client_atomic_load_external : Clight.fundef :=
    External (EF_external "atomic_load" atomic_load_signature)
      [atomic_pointer_type] tint cc_default.

  Definition client_atomic_store_external : Clight.fundef :=
    External (EF_external "atomic_store" atomic_store_signature)
      [atomic_pointer_type; tint] tvoid cc_default.

  Definition client_atomic_CAS_external : Clight.fundef :=
    External (EF_external "atomic_CAS" atomic_CAS_signature)
      [atomic_pointer_type; tint; tint] tint cc_default.

End ClightAtomicSpecs.
