Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.

Require Import Cminor.
Require Import Footprint Memory MemOpFP.


Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.

Require Import Cop_fp_local ValFP.

(** TODO: move to, say, Val_op_fp.v *)

Definition cmpu_fp (m: mem) (c: comparison) (arg1 arg2: val) : footprint :=
  cmpu_bool_fp_total m c arg1 arg2.

Definition cmplu_fp := cmplu_bool_fp.

Definition eval_binop_fp
            (op: binary_operation) (arg1 arg2: val) (m: mem): option footprint :=
  match op with
  | Odiv => if Val.divs arg1 arg2 then Some empfp else None
  | Odivu => if Val.divu arg1 arg2 then Some empfp else None
  | Omod => if Val.mods arg1 arg2 then Some empfp else None
  | Omodu => if Val.modu arg1 arg2 then Some empfp else None
  | Odivl => if Val.divls arg1 arg2 then Some empfp else None
  | Odivlu => if Val.divlu arg1 arg2 then Some empfp else None
  | Omodl => if Val.modls arg1 arg2 then Some empfp else None
  | Omodlu => if Val.modlu arg1 arg2 then Some empfp else None
  | Ocmpl c => if Val.cmpl c arg1 arg2 then Some empfp else None
  | Ocmpu c => Some (cmpu_fp m c arg1 arg2)
  | Ocmplu c => cmplu_fp m c arg1 arg2
  | _ => Some empfp
  end.