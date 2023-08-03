(* This is a modified [Cop.v] file built on top of FMemory.v 
   Since the FMemory has similar APIs, this file need not to be modified except for
   [Require Import FMemory].
   Definitions not related to memory are removed from this file.
*)


(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Arithmetic and logical operators for the Compcert C and Clight languages *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import FMemory.
Require Import Ctypes.
Require Archi.
Require Import Cop.

Definition sem_cast (v: val) (t1 t2: type) (m: mem): option val :=
  match classify_cast t1 t2 with
  | cast_case_pointer =>
      match v with
      | Vptr _ _ => Some v
      | Vint _ => if Archi.ptr64 then None else Some v
      | Vlong _ => if Archi.ptr64 then Some v else None
      | _ => None
      end
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f =>
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end
  | cast_case_s2s =>
      match v with
      | Vsingle f => Some (Vsingle f)
      | _ => None
      end
  | cast_case_s2f =>
      match v with
      | Vsingle f => Some (Vfloat (Float.of_single f))
      | _ => None
      end
  | cast_case_f2s =>
      match v with
      | Vfloat f => Some (Vsingle (Float.to_single f))
      | _ => None
      end
  | cast_case_i2f si1 =>
      match v with
      | Vint i => Some (Vfloat (cast_int_float si1 i))
      | _ => None
      end
  | cast_case_i2s si1 =>
      match v with
      | Vint i => Some (Vsingle (cast_int_single si1 i))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_s2i sz2 si2 =>
      match v with
      | Vsingle f =>
          match cast_single_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_i2bool =>
      match v with
      | Vint n =>
          Some(Vint(if Int.eq n Int.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None
      | _ => None
      end
  | cast_case_l2bool =>
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None

      | _ => None
      end
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_s2bool =>
      match v with
      | Vsingle f =>
          Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_l2l =>
      match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end
  | cast_case_i2l si =>
      match v with
      | Vint n => Some(Vlong (cast_int_long si n))
      | _ => None
      end
  | cast_case_l2i sz si =>
      match v with
      | Vlong n => Some(Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end
  | cast_case_l2f si1 =>
      match v with
      | Vlong i => Some (Vfloat (cast_long_float si1 i))
      | _ => None
      end
  | cast_case_l2s si1 =>
      match v with
      | Vlong i => Some (Vsingle (cast_long_single si1 i))
      | _ => None
      end
  | cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
          match cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_s2l si2 =>
      match v with
      | Vsingle f =>
          match cast_single_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_struct id1 id2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end
  | cast_case_union id1 id2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end
  | cast_case_void =>
      Some v
  | cast_case_default =>
      None
  end.

Definition bool_val (v: val) (t: type) (m: mem) : option bool :=
  match classify_bool t with
  | bool_case_i =>
      match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | Vptr b ofs =>
          if Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
      | _ => None
      end
  | bool_case_l =>
      match v with
      | Vlong n => Some (negb (Int64.eq n Int64.zero))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_case_s =>
      match v with
      | Vsingle f => Some (negb (Float32.cmp Ceq f Float32.zero))
      | _ => None
      end
  | bool_default => None
  end.

Definition sem_notbool (v: val) (ty: type) (m: mem): option val :=
  option_map (fun b => Val.of_bool (negb b)) (bool_val v ty m).

Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    (v1: val) (t1: type) (v2: val) (t2: type) (m: mem): option val :=
  let c := classify_binarith t1 t2 in
  let t := binarith_type c in
  match sem_cast v1 t1 t m with
  | None => None
  | Some v1' =>
  match sem_cast v2 t2 t m with
  | None => None
  | Some v2' =>
  match c with
  | bin_case_i sg =>
      match v1', v2' with
      | Vint n1, Vint n2 => sem_int sg n1 n2
      | _,  _ => None
      end
  | bin_case_f =>
      match v1', v2' with
      | Vfloat n1, Vfloat n2 => sem_float n1 n2
      | _,  _ => None
      end
  | bin_case_s =>
      match v1', v2' with
      | Vsingle n1, Vsingle n2 => sem_single n1 n2
      | _,  _ => None
      end
  | bin_case_l sg =>
      match v1', v2' with
      | Vlong n1, Vlong n2 => sem_long sg n1 n2
      | _,  _ => None
      end
  | bin_default => None
  end end end.

Definition sem_add (cenv: composite_env) (v1:val) (t1:type) (v2: val) (t2:type) (m: mem): option val :=
  match classify_add t1 t2 with
  | add_case_pi ty si =>             (**r pointer plus integer *)
      sem_add_ptr_int cenv ty si v1 v2
  | add_case_pl ty =>                (**r pointer plus long *)
      sem_add_ptr_long cenv ty v1 v2
  | add_case_ip si ty =>             (**r integer plus pointer *)
      sem_add_ptr_int cenv ty si v2 v1
  | add_case_lp ty =>                (**r long plus pointer *)
      sem_add_ptr_long cenv ty v2 v1
  | add_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
        v1 t1 v2 t2 m
  end.

Definition sem_sub (cenv: composite_env) (v1:val) (t1:type) (v2: val) (t2:type) (m:mem): option val :=
  match classify_sub t1 t2 with
  | sub_case_pi ty si =>            (**r pointer minus integer *)
      match v1, v2 with
      | Vptr b1 ofs1, Vint n2 =>
          let n2 := ptrofs_of_int si n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | Vint n1, Vint n2 =>
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
      | Vlong n1, Vint n2 =>
          let n2 := cast_int_long si n2 in
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
      | _,  _ => None
      end
  | sub_case_pl ty =>            (**r pointer minus long *)
      match v1, v2 with
      | Vptr b1 ofs1, Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | Vint n1, Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2) in
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
      | Vlong n1, Vlong n2 =>
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if eq_block b1 b2 then
            let sz := sizeof cenv ty in
            if zlt 0 sz && zle sz Ptrofs.max_signed
            then Some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else None
          else None
      | _, _ => None
      end
  | sub_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
        v1 t1 v2 t2 m
  end.

(** *** Multiplication, division, modulus *)

Definition sem_mul (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
    v1 t1 v2 t2 m.

Definition sem_div (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.divs n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.divu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.divs n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.divu n1 n2))
      end)
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
    v1 t1 v2 t2 m.

Definition sem_mod (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.mods n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.modu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.mods n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.modu n1 n2))
      end)
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.

Definition sem_and (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.

Definition sem_or (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.

Definition sem_xor (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.

Definition cmp_ptr (m: mem) (c: comparison) (v1 v2: val): option val :=
  option_map Val.of_bool
   (if Archi.ptr64
    then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
    else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2).

Definition sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_pp =>
      cmp_ptr m c v1 v2
  | cmp_case_pi si =>
      match v2 with
      | Vint n2 =>
          let v2' := Vptrofs (ptrofs_of_int si n2) in
          cmp_ptr m c v1 v2'
      | Vptr b ofs =>
          if Archi.ptr64 then None else cmp_ptr m c v1 v2
      | _ =>
          None
      end
  | cmp_case_ip si =>
      match v1 with
      | Vint n1 =>
          let v1' := Vptrofs (ptrofs_of_int si n1) in
          cmp_ptr m c v1' v2
      | Vptr b ofs =>
          if Archi.ptr64 then None else cmp_ptr m c v1 v2
      | _ =>
          None
      end
  | cmp_case_pl =>
      match v2 with
      | Vlong n2 =>
          let v2' := Vptrofs (Ptrofs.of_int64 n2) in
          cmp_ptr m c v1 v2'
      | Vptr b ofs =>
          if Archi.ptr64 then cmp_ptr m c v1 v2 else None
      | _ =>
          None
      end
  | cmp_case_lp =>
      match v1 with
      | Vlong n1 =>
          let v1' := Vptrofs (Ptrofs.of_int64 n1) in
          cmp_ptr m c v1' v2
      | Vptr b ofs =>
          if Archi.ptr64 then cmp_ptr m c v1 v2 else None
      | _ =>
          None
      end
  | cmp_default =>
      sem_binarith
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float.cmp c n1 n2)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float32.cmp c n1 n2)))
        v1 t1 v2 t2 m
  end.

Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type) (m: mem): option val :=
  match op with
  | Onotbool => sem_notbool v ty m
  | Onotint => sem_notint v ty
  | Oneg => sem_neg v ty
  | Oabsfloat => sem_absfloat v ty
  end.

Definition sem_binary_operation
    (cenv: composite_env)
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type)
    (m: mem): option val :=
  match op with
  | Oadd => sem_add cenv v1 t1 v2 t2 m
  | Osub => sem_sub cenv v1 t1 v2 t2 m
  | Omul => sem_mul v1 t1 v2 t2 m
  | Omod => sem_mod v1 t1 v2 t2 m
  | Odiv => sem_div v1 t1 v2 t2 m
  | Oand => sem_and v1 t1 v2 t2 m
  | Oor  => sem_or v1 t1 v2 t2 m
  | Oxor  => sem_xor v1 t1 v2 t2 m
  | Oshl => sem_shl v1 t1 v2 t2
  | Oshr  => sem_shr v1 t1 v2 t2
  | Oeq => sem_cmp Ceq v1 t1 v2 t2 m
  | One => sem_cmp Cne v1 t1 v2 t2 m
  | Olt => sem_cmp Clt v1 t1 v2 t2 m
  | Ogt => sem_cmp Cgt v1 t1 v2 t2 m
  | Ole => sem_cmp Cle v1 t1 v2 t2 m
  | Oge => sem_cmp Cge v1 t1 v2 t2 m
  end.

Definition sem_incrdecr (cenv: composite_env) (id: incr_or_decr) (v: val) (ty: type) (m: mem) :=
  match id with
  | Incr => sem_add cenv v ty (Vint Int.one) type_int32s m
  | Decr => sem_sub cenv v ty (Vint Int.one) type_int32s m
  end.

(** * Compatibility with extensions and injections *)

Section GENERIC_INJECTION.

Variable f: meminj.
Variables m m': mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Remark val_inject_vtrue: forall f, Val.inject f Vtrue Vtrue.
Proof. unfold Vtrue; auto. Qed.

Remark val_inject_vfalse: forall f, Val.inject f Vfalse Vfalse.
Proof. unfold Vfalse; auto. Qed.

Remark val_inject_of_bool: forall f b, Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof. intros. unfold Val.of_bool. destruct b; [apply val_inject_vtrue|apply val_inject_vfalse].
Qed.

Remark val_inject_vptrofs: forall n, Val.inject f (Vptrofs n) (Vptrofs n).
Proof. intros. unfold Vptrofs. destruct Archi.ptr64; auto. Qed.

Hint Resolve val_inject_vtrue val_inject_vfalse val_inject_of_bool val_inject_vptrofs.

Ltac TrivialInject :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; TrivialInject
  | [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x; TrivialInject
  | [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; TrivialInject
  | [ |- exists v', Some ?v = Some v' /\ _ ] => exists v; split; auto
  | _ => idtac
  end.

Lemma sem_cast_inj:
  forall v1 ty1 ty v tv1,
  sem_cast v1 ty1 ty m = Some v ->
  Val.inject f v1 tv1 ->
  exists tv, sem_cast tv1 ty1 ty m'= Some tv /\ Val.inject f v tv.
Proof.
  unfold sem_cast; intros; destruct (classify_cast ty1 ty); inv H0; TrivialInject.
- econstructor; eauto.
- erewrite weak_valid_pointer_inj by eauto. TrivialInject. 
- erewrite weak_valid_pointer_inj by eauto. TrivialInject. 
- destruct (ident_eq id1 id2); TrivialInject. econstructor; eauto.
- destruct (ident_eq id1 id2); TrivialInject. econstructor; eauto.
- econstructor; eauto.
Qed.

Lemma bool_val_inj:
  forall v ty b tv,
  bool_val v ty m = Some b ->
  Val.inject f v tv ->
  bool_val tv ty m' = Some b.
Proof.
  unfold bool_val; intros.
  destruct (classify_bool ty); inv H0; try congruence.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1)) eqn:VP; inv H.
  erewrite weak_valid_pointer_inj by eauto. auto.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1)) eqn:VP; inv H.
  erewrite weak_valid_pointer_inj by eauto. auto.
Qed.

Lemma sem_unary_operation_inj:
  forall op v1 ty v tv1,
  sem_unary_operation op v1 ty m = Some v ->
  Val.inject f v1 tv1 ->
  exists tv, sem_unary_operation op tv1 ty m' = Some tv /\ Val.inject f v tv.
Proof.
  unfold sem_unary_operation; intros. destruct op.
- (* notbool *)
  unfold sem_notbool in *. destruct (bool_val v1 ty m) as [b|] eqn:BV; simpl in H; inv H.
  erewrite bool_val_inj by eauto. simpl. TrivialInject.
- (* notint *)
  unfold sem_notint in *; destruct (classify_notint ty); inv H0; inv H; TrivialInject.
- (* neg *)
  unfold sem_neg in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
- (* absfloat *)
  unfold sem_absfloat in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
Qed.

Definition optval_self_injects (ov: option val) : Prop :=
  match ov with
  | Some (Vptr b ofs) => False
  | _ => True
  end.

Remark sem_binarith_inject:
  forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 v v1' v2',
  sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m = Some v ->
  Val.inject f v1 v1' -> Val.inject f v2 v2' ->
  (forall sg n1 n2, optval_self_injects (sem_int sg n1 n2)) ->
  (forall sg n1 n2, optval_self_injects (sem_long sg n1 n2)) ->
  (forall n1 n2, optval_self_injects (sem_float n1 n2)) ->
  (forall n1 n2, optval_self_injects (sem_single n1 n2)) ->
  exists v', sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 m' = Some v' /\ Val.inject f v v'.
Proof.
  intros.
  assert (SELF: forall ov v, ov = Some v -> optval_self_injects ov -> Val.inject f v v).
  {
    intros. subst ov; simpl in H7. destruct v0; contradiction || constructor.
  }
  unfold sem_binarith in *.
  set (c := classify_binarith t1 t2) in *.
  set (t := binarith_type c) in *.
  destruct (sem_cast v1 t1 t m) as [w1|] eqn:C1; try discriminate.
  destruct (sem_cast v2 t2 t m) as [w2|] eqn:C2; try discriminate.
  exploit (sem_cast_inj v1); eauto. intros (w1' & C1' & INJ1).
  exploit (sem_cast_inj v2); eauto. intros (w2' & C2' & INJ2).
  rewrite C1'; rewrite C2'.
  destruct c; inv INJ1; inv INJ2; discriminate || eauto.
Qed.

Remark sem_shift_inject:
  forall sem_int sem_long v1 t1 v2 t2 v v1' v2',
  sem_shift sem_int sem_long v1 t1 v2 t2 = Some v ->
  Val.inject f v1 v1' -> Val.inject f v2 v2' ->
  exists v', sem_shift sem_int sem_long v1' t1 v2' t2 = Some v' /\ Val.inject f v v'.
Proof.
  intros. exists v.
  unfold sem_shift in *; destruct (classify_shift t1 t2); inv H0; inv H1; try discriminate.
  destruct (Int.ltu i0 Int.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 Int64.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 (Int64.repr 32)); inv H; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); inv H; auto.
Qed.

Remark sem_cmp_ptr_inj:
  forall c v1 v2 v tv1 tv2,
  cmp_ptr m c v1 v2 = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  exists tv, cmp_ptr m' c tv1 tv2 = Some tv /\ Val.inject f v tv.
Proof.
  unfold cmp_ptr; intros. 
  remember (if Archi.ptr64
       then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
       else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as ob.
  destruct ob as [b|]; simpl in H; inv H.
  exists (Val.of_bool b); split; auto.
  destruct Archi.ptr64. 
  erewrite Val.cmplu_bool_inject by eauto. auto.
  erewrite Val.cmpu_bool_inject by eauto. auto.
Qed.

Remark sem_cmp_inj:
  forall cmp v1 tv1 ty1 v2 tv2 ty2 v,
  sem_cmp cmp v1 ty1 v2 ty2 m = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  exists tv, sem_cmp cmp tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof.
  intros.
  unfold sem_cmp in *; destruct (classify_cmp ty1 ty2).
- (* pointer - pointer *)
  eapply sem_cmp_ptr_inj; eauto.
- (* pointer - int *)
  inversion H1; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* int - pointer *)
  inversion H0; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* pointer - long *)
  inversion H1; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* long - pointer *)
  inversion H0; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* numerical - numerical *)
  assert (SELF: forall b, optval_self_injects (Some (Val.of_bool b))).
  {
    destruct b; exact I.
  }
  eapply sem_binarith_inject; eauto.
Qed.

Lemma sem_binary_operation_inj:
  forall cenv op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation cenv op v1 ty1 v2 ty2 m = Some v ->
  Val.inject f v1 tv1 -> Val.inject f v2 tv2 ->
  exists tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof.
  unfold sem_binary_operation; intros; destruct op.
- (* add *)
  assert (A: forall cenv ty si v1' v2' tv1' tv2',
             Val.inject f v1' tv1' -> Val.inject f v2' tv2' ->
             sem_add_ptr_int cenv ty si v1' v2' = Some v ->
             exists tv, sem_add_ptr_int cenv ty si tv1' tv2' = Some tv /\ Val.inject f v tv).
  { intros. unfold sem_add_ptr_int in *; inv H2; inv H3; TrivialInject.
    econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. }
  assert (B: forall cenv ty v1' v2' tv1' tv2',
             Val.inject f v1' tv1' -> Val.inject f v2' tv2' ->
             sem_add_ptr_long cenv ty v1' v2' = Some v ->
             exists tv, sem_add_ptr_long cenv ty tv1' tv2' = Some tv /\ Val.inject f v tv).
  { intros. unfold sem_add_ptr_long in *; inv H2; inv H3; TrivialInject.
    econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. }
  unfold sem_add in *; destruct (classify_add ty1 ty2); eauto.
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* sub *)
  unfold sem_sub in *; destruct (classify_sub ty1 ty2).
  + inv H0; inv H1; TrivialInject.
    econstructor. eauto. rewrite Ptrofs.sub_add_l. auto. 
  + inv H0; inv H1; TrivialInject.
    destruct (eq_block b1 b0); try discriminate. subst b1.
    rewrite H0 in H2; inv H2. rewrite dec_eq_true.
    destruct (zlt 0 (sizeof cenv ty) && zle (sizeof cenv ty) Ptrofs.max_signed); inv H.
    rewrite Ptrofs.sub_shifted. TrivialInject.
  + inv H0; inv H1; TrivialInject.
    econstructor. eauto. rewrite Ptrofs.sub_add_l. auto. 
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* mul *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* div *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
  exact I.
- (* mod *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
  exact I.
- (* and *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* or *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* xor *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* shl *)
  eapply sem_shift_inject; eauto.
- (* shr *)
  eapply sem_shift_inject; eauto.
  (* comparisons *)
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
Qed.

End GENERIC_INJECTION.

Lemma sem_cast_inject:
  forall f v1 ty1 ty m v tv1 tm,
  sem_cast v1 ty1 ty m = Some v ->
  Val.inject f v1 tv1 ->
  Mem.inject f m tm ->
  exists tv, sem_cast tv1 ty1 ty tm = Some tv /\ Val.inject f v tv.
Proof.
  intros. eapply sem_cast_inj; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

Lemma sem_unary_operation_inject:
  forall f m m' op v1 ty1 v tv1,
  sem_unary_operation op v1 ty1 m = Some v ->
  Val.inject f v1 tv1 ->
  Mem.inject f m m' ->
  exists tv, sem_unary_operation op tv1 ty1 m' = Some tv /\ Val.inject f v tv.
Proof.
  intros. eapply sem_unary_operation_inj; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

Lemma sem_binary_operation_inject:
  forall f m m' cenv op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation cenv op v1 ty1 v2 ty2 m = Some v ->
  Val.inject f v1 tv1 -> Val.inject f v2 tv2 ->
  Mem.inject f m m' ->
  exists tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof.
  intros. eapply sem_binary_operation_inj; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.

Lemma bool_val_inject:
  forall f m m' v ty b tv,
  bool_val v ty m = Some b ->
  Val.inject f v tv ->
  Mem.inject f m m' ->
  bool_val tv ty m' = Some b.
Proof.
  intros. eapply bool_val_inj; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

(** * Some properties of operator semantics *)

(** This section collects some common-sense properties about the type
  classification and semantic functions above.  Some properties are used
  in the CompCert semantics preservation proofs.  Others are not, but increase
  confidence in the specification and its relation with the ISO C99 standard. *)

(** Relation between Boolean value and casting to [_Bool] type. *)

Lemma cast_bool_bool_val:
  forall v t m,
  sem_cast v t (Tint IBool Signed noattr) m =
  match bool_val v t m with None => None | Some b => Some(Val.of_bool b) end.
  intros.
  assert (A: classify_bool t =
    match t with
    | Tint _ _ _ => bool_case_i
    | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ => if Archi.ptr64 then bool_case_l else bool_case_i
    | Tfloat F64 _ => bool_case_f
    | Tfloat F32 _ => bool_case_s
    | Tlong _ _ => bool_case_l
    | _ => bool_default
    end).
  {
    unfold classify_bool; destruct t; simpl; auto. destruct i; auto.
  }
  unfold bool_val. rewrite A.
  unfold sem_cast, classify_cast; remember Archi.ptr64 as ptr64; destruct t; simpl; auto; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)); auto.
  destruct (Int64.eq i Int64.zero); auto.
  destruct (negb ptr64); auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct f; auto.
  destruct f; auto.
  destruct f; auto.
  destruct f; auto.
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct f; auto.
  destruct (Float32.cmp Ceq f0 Float32.zero); auto.
  destruct f; auto. 
  destruct ptr64; auto.
  destruct (Int.eq i Int.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Int.eq i Int.zero); auto.
  destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Int.eq i Int.zero); auto.
  destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
Qed.

(** Relation between Boolean value and Boolean negation. *)

Lemma notbool_bool_val:
  forall v t m,
  sem_notbool v t m =
  match bool_val v t m with None => None | Some b => Some(Val.of_bool (negb b)) end.
Proof.
  intros. unfold sem_notbool. destruct (bool_val v t m) as [[] | ]; reflexivity.
Qed.

(** Properties of values obtained by casting to a given type. *)

Section VAL_CASTED.

Ltac DestructCases :=
  match goal with
  | [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: Some _ = Some _ |- _ ] => inv H; DestructCases
  | [H: None = Some _ |- _ ] => discriminate H
  | [H: @eq intsize _ _ |- _ ] => discriminate H || (clear H; DestructCases)
  | [ |- val_casted (Vint (if ?x then Int.zero else Int.one)) _ ] =>
       try (constructor; destruct x; reflexivity)
  | [ |- val_casted (Vint _) (Tint ?sz ?sg _) ] =>
       try (constructor; apply (cast_int_int_idem sz sg))
  | _ => idtac
  end.

Lemma cast_val_is_casted:
  forall v ty ty' v' m, sem_cast v ty ty' m = Some v' -> val_casted v' ty'.
Proof.
  unfold sem_cast; intros.
  destruct ty, ty'; simpl in H; DestructCases; constructor; auto.
Qed.

End VAL_CASTED.

(** As a consequence, casting twice is equivalent to casting once. *)

Lemma cast_val_casted:
  forall v ty m, val_casted v ty -> sem_cast v ty ty m = Some v.
Proof.
  intros. unfold sem_cast; inversion H; clear H; subst v ty; simpl.
- destruct Archi.ptr64; [ | destruct (intsize_eq sz I32)].
+ destruct sz; f_equal; f_equal; assumption.
+ subst sz; auto.
+ destruct sz; f_equal; f_equal; assumption.
- auto.
- auto.
- destruct Archi.ptr64; auto.
- auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite dec_eq_true; auto.
- rewrite dec_eq_true; auto.
- auto. 
Qed.

Lemma cast_idempotent:
  forall v ty ty' v' m, sem_cast v ty ty' m = Some v' -> sem_cast v' ty' ty' m = Some v'.
Proof.
  intros. apply cast_val_casted. eapply cast_val_is_casted; eauto.
Qed.

(* This module seems not related to memory *)
(* 
(** Relation with the arithmetic conversions of ISO C99, section 6.3.1 *)

Module ArithConv.

(** This is the ISO C algebra of arithmetic types, without qualifiers.
    [S] stands for "signed" and [U] for "unsigned".  *)

Inductive int_type : Type :=
  | _Bool
  | Char | SChar | UChar
  | Short | UShort
  | Int | UInt
  | Long | ULong
  | Longlong | ULonglong.

Inductive arith_type : Type :=
  | I (it: int_type)
  | Float
  | Double
  | Longdouble.

Definition eq_int_type: forall (x y: int_type), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition is_unsigned (t: int_type) : bool :=
  match t with
  | _Bool => true
  | Char => false    (**r as in most of CompCert's target ABIs *)
  | SChar => false
  | UChar => true
  | Short => false
  | UShort => true
  | Int => false
  | UInt => true
  | Long => false
  | ULong => true
  | Longlong => false
  | ULonglong => true
  end.

Definition unsigned_type (t: int_type) : int_type :=
  match t with
  | Char => UChar
  | SChar => UChar
  | Short => UShort
  | Int => UInt
  | Long => ULong
  | Longlong => ULonglong
  | _ => t
  end.

Definition int_sizeof (t: int_type) : Z :=
  match t with
  | _Bool | Char | SChar | UChar => 1
  | Short | UShort => 2
  | Int | UInt | Long | ULong => 4
  | Longlong | ULonglong => 8
  end.

(** 6.3.1.1 para 1: integer conversion rank *)

Definition rank (t: int_type) : Z :=
  match t with
  | _Bool => 1
  | Char | SChar | UChar => 2
  | Short | UShort => 3
  | Int | UInt => 4
  | Long | ULong => 5
  | Longlong | ULonglong => 6
  end.

(** 6.3.1.1 para 2: integer promotions, a.k.a. usual unary conversions *)

Definition integer_promotion (t: int_type) : int_type :=
  if zlt (rank t) (rank Int) then Int else t.

(** 6.3.1.8: Usual arithmetic conversions, a.k.a. binary conversions.
  This function returns the type to which the two operands must be
  converted. *)

Definition usual_arithmetic_conversion (t1 t2: arith_type) : arith_type :=
  match t1, t2 with
  (* First, if the corresponding real type of either operand is long
     double, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is long double. *)
  | Longdouble, _ | _, Longdouble => Longdouble
  (* Otherwise, if the corresponding real type of either operand is
     double, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is double. *)
  | Double, _ | _, Double => Double
  (* Otherwise, if the corresponding real type of either operand is
     float, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is float. *)
  | Float, _ | _, Float => Float
  (* Otherwise, the integer promotions are performed on both operands. *)
  | I i1, I i2 =>
    let j1 := integer_promotion i1 in
    let j2 := integer_promotion i2 in
    (* Then the following rules are applied to the promoted operands:
       If both operands have the same type, then no further conversion
       is needed. *)
    if eq_int_type j1 j2 then I j1 else
    match is_unsigned j1, is_unsigned j2 with
    (* Otherwise, if both operands have signed integer types or both
       have unsigned integer types, the operand with the type of lesser
       integer conversion rank is converted to the type of the operand with
       greater rank. *)
    | true, true | false, false =>
        if zlt (rank j1) (rank j2) then I j2 else I j1
    | true, false =>
    (* Otherwise, if the operand that has unsigned integer type has
       rank greater or equal to the rank of the type of the other operand,
       then the operand with signed integer type is converted to the type of
       the operand with unsigned integer type. *)
        if zle (rank j2) (rank j1) then I j1 else
    (* Otherwise, if the type of the operand with signed integer type
       can represent all of the values of the type of the operand with
       unsigned integer type, then the operand with unsigned integer type is
       converted to the type of the operand with signed integer type. *)
        if zlt (int_sizeof j1) (int_sizeof j2) then I j2 else
    (* Otherwise, both operands are converted to the unsigned integer type
       corresponding to the type of the operand with signed integer type. *)
        I (unsigned_type j2)
    | false, true =>
    (* Same logic as above, swapping the roles of j1 and j2 *)
        if zle (rank j1) (rank j2) then I j2 else
        if zlt (int_sizeof j2) (int_sizeof j1) then I j1 else
        I (unsigned_type j1)
    end
  end.

(** Mapping ISO arithmetic types to CompCert types *)

Definition proj_type (t: arith_type) : type :=
  match t with
  | I _Bool => Tint IBool Unsigned noattr
  | I Char => Tint I8 Unsigned noattr
  | I SChar => Tint I8 Signed noattr
  | I UChar => Tint I8 Unsigned noattr
  | I Short => Tint I16 Signed noattr
  | I UShort => Tint I16 Unsigned noattr
  | I Int => Tint I32 Signed noattr
  | I UInt => Tint I32 Unsigned noattr
  | I Long => Tint I32 Signed noattr
  | I ULong => Tint I32 Unsigned noattr
  | I Longlong => Tlong Signed noattr
  | I ULonglong => Tlong Unsigned noattr
  | Float => Tfloat F32 noattr
  | Double => Tfloat F64 noattr
  | Longdouble => Tfloat F64 noattr
  end.

(** Relation between [typeconv] and integer promotion. *)

Lemma typeconv_integer_promotion:
  forall i, typeconv (proj_type (I i)) = proj_type (I (integer_promotion i)).
Proof.
  destruct i; reflexivity.
Qed.

(** Relation between [classify_binarith] and arithmetic conversion. *)

Lemma classify_binarith_arithmetic_conversion:
  forall t1 t2,
  binarith_type (classify_binarith (proj_type t1) (proj_type t2)) =
  proj_type (usual_arithmetic_conversion t1 t2).
Proof.
  destruct t1; destruct t2; try reflexivity.
- destruct it; destruct it0; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
Qed.

End ArithConv.
*)




