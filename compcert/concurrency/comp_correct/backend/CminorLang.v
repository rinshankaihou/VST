(* This file is adapted from [backend/Cminor.v] of CompCert,
   with support for our interaction semantics. *)

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

(** Abstract syntax and semantics for the Cminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.


Require Import Footprint GMemory MemAux FMemory InteractionSemantics CUAST.

Require Import FMemOpFP val_casted.

Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.

Require Import Cminor Cop_fp Cminor_local.

(** * Abstract syntax *)

(** syntax of Cimnor adapted from CompCert *)

(** * Operational semantics (small-step) *)

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

(** States *)
Section RELSEM.

Variable ge: genv.

(** Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. *)

Definition eval_binop
            (op: binary_operation) (arg1 arg2: val) (m: mem): option val :=
  match op with
  | Oadd => Some (Val.add arg1 arg2)
  | Osub => Some (Val.sub arg1 arg2)
  | Omul => Some (Val.mul arg1 arg2)
  | Odiv => Val.divs arg1 arg2
  | Odivu => Val.divu arg1 arg2
  | Omod => Val.mods arg1 arg2
  | Omodu => Val.modu arg1 arg2
  | Oand => Some (Val.and arg1 arg2)
  | Oor => Some (Val.or arg1 arg2)
  | Oxor => Some (Val.xor arg1 arg2)
  | Oshl => Some (Val.shl arg1 arg2)
  | Oshr => Some (Val.shr arg1 arg2)
  | Oshru => Some (Val.shru arg1 arg2)
  | Oaddf => Some (Val.addf arg1 arg2)
  | Osubf => Some (Val.subf arg1 arg2)
  | Omulf => Some (Val.mulf arg1 arg2)
  | Odivf => Some (Val.divf arg1 arg2)
  | Oaddfs => Some (Val.addfs arg1 arg2)
  | Osubfs => Some (Val.subfs arg1 arg2)
  | Omulfs => Some (Val.mulfs arg1 arg2)
  | Odivfs => Some (Val.divfs arg1 arg2)
  | Oaddl => Some (Val.addl arg1 arg2)
  | Osubl => Some (Val.subl arg1 arg2)
  | Omull => Some (Val.mull arg1 arg2)
  | Odivl => Val.divls arg1 arg2
  | Odivlu => Val.divlu arg1 arg2
  | Omodl => Val.modls arg1 arg2
  | Omodlu => Val.modlu arg1 arg2
  | Oandl => Some (Val.andl arg1 arg2)
  | Oorl => Some (Val.orl arg1 arg2)
  | Oxorl => Some (Val.xorl arg1 arg2)
  | Oshll => Some (Val.shll arg1 arg2)
  | Oshrl => Some (Val.shrl arg1 arg2)
  | Oshrlu => Some (Val.shrlu arg1 arg2)
  | Ocmp c => option_map Val.of_bool (Val.cmp_bool c arg1 arg2)
  | Ocmpu c => option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c arg1 arg2)
  | Ocmpf c => option_map Val.of_bool (Val.cmpf_bool c arg1 arg2)
  | Ocmpfs c => option_map Val.of_bool (Val.cmpfs_bool c arg1 arg2)
  | Ocmpl c => Val.cmpl c arg1 arg2
  | Ocmplu c => option_map Val.of_bool (Val.cmplu_bool (Mem.valid_pointer m) c arg1 arg2)
  end.

Definition cmpu_bool_fp_total (m: mem) (c: comparison) (v1 v2: val) : footprint :=
  match v1, v2 with
  | Vint _, Vint _ => empfp
  | Vint n1, Vptr b2 ofs2 =>
    if Archi.ptr64 then empfp
    else if Int.eq n1 Int.zero
         then if Val.cmp_different_blocks c                   
              then (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2))
              else empfp
         else empfp
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if Archi.ptr64 then empfp
    else if eq_block b1 b2
         then (FP.union (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                             (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else empfp
  | Vptr b1 ofs1, Vint n2 =>
    if Archi.ptr64 then empfp
    else if Int.eq n2 Int.zero
         then if Val.cmp_different_blocks c
              then (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
              else empfp
         else empfp
  | _, _ => empfp
  end.

Definition cmplu_bool_fp_total (m: mem) (c: comparison) (v1 v2: val) : footprint :=
  match v1, v2 with
  | Vlong n1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then empfp
    else if Int64.eq n1 Int64.zero
         then if Val.cmp_different_blocks c
              then (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2))
              else empfp
         else empfp
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then empfp
    else if eq_block b1 b2
         then (FP.union (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                                  (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else empfp
  | Vptr b1 ofs1, Vlong n2 =>
    if negb Archi.ptr64 then empfp
    else if Int64.eq n2 Int64.zero
         then if Val.cmp_different_blocks c
              then (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
              else empfp
         else empfp
  | Vptr b1 ofs1, Vundef =>
    if negb Archi.ptr64 then empfp
    else (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
  | Vundef, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then empfp
    else (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2))
  | _, _ => empfp
  end.

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
  | Ocmpu c => Some (cmpu_bool_fp_total m c arg1 arg2)
  | Ocmplu c => cmplu_bool_fp m c arg1 arg2
  | _ => Some empfp
  end.

(** Evaluation of an expression: [eval_expr ge sp e m a v]
  states that expression [a] evaluates to value [v].
  [ge] is the global environment, [e] the local environment,
  and [m] the current memory state.  They are unchanged during evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
*)

Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id v,
      PTree.get id e = Some v ->
      eval_expr (Evar id) v
  | eval_Econst: forall cst v,
      eval_constant ge sp cst = Some v ->
      eval_expr (Econst cst) v
  | eval_Eunop: forall op a1 v1 v,
      eval_expr a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr (Eunop op a1) v
  | eval_Ebinop: forall op a1 a2 v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr (Ebinop op a1 a2) v
  | eval_Eload: forall chunk addr vaddr v,
      eval_expr addr vaddr ->
      Mem.loadv chunk m vaddr = Some v ->
      eval_expr (Eload chunk addr) v.

Inductive eval_exprlist: list expr -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr a1 v1 -> eval_exprlist al vl ->
      eval_exprlist (a1 :: al) (v1 :: vl).

Inductive eval_expr_fp: expr -> footprint -> Prop :=
  | eval_Evar_fp: forall id,
      eval_expr_fp (Evar id) empfp
  | eval_Econst_fp: forall cst v,
      eval_constant ge sp cst = Some v ->
      eval_expr_fp (Econst cst) empfp
  | eval_Eunop_fp: forall op a1 v1 v fp,
      eval_expr a1 v1 ->
      eval_expr_fp a1 fp ->
      eval_unop op v1 = Some v ->
      eval_expr_fp (Eunop op a1) fp
  | eval_Ebinop_fp: forall op a1 a2 v1 v2 v fp1 fp2 fp3 fp,
      eval_expr a1 v1 ->
      eval_expr_fp a1 fp1 ->
      eval_expr a2 v2 ->
      eval_expr_fp a2 fp2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_binop_fp op v1 v2 m = Some fp3 ->
      FP.union (FP.union fp1 fp2) fp3 = fp ->
      eval_expr_fp (Ebinop op a1 a2) fp
  | eval_Eload_fp: forall chunk addr vaddr v fp1 fp2 fp,
      eval_expr addr vaddr ->
      eval_expr_fp addr fp1 ->
      Mem.loadv chunk m vaddr = Some v ->
      loadv_fp chunk vaddr = fp2 ->
      FP.union fp1 fp2 = fp ->
      eval_expr_fp (Eload chunk addr) fp.

Inductive eval_exprlist_fp: list expr -> footprint -> Prop :=
| eval_Enil_fp:
    eval_exprlist_fp nil empfp
| eval_Econs_fp: forall a1 al v1 vl fp1 fp2 fp,
    eval_expr a1 v1 ->
    eval_expr_fp a1 fp1 ->
    eval_exprlist al vl ->
    eval_exprlist_fp al fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_exprlist_fp (a1 :: al) fp.

End EVAL_EXPR.

(** Pop continuation until a call or stop *)

(** Find the statement and manufacture the continuation
  corresponding to a label *)

(** One step of execution *)
Inductive step: core -> mem -> footprint -> core -> mem -> Prop :=
  
| step_skip_seq: forall f s k sp e m,
    step (Core_State f Sskip (Kseq s k) sp e) m
         empfp (Core_State f s k sp e) m
| step_skip_block: forall f k sp e m,
    step (Core_State f Sskip (Kblock k) sp e) m
         empfp (Core_State f Sskip k sp e) m
| step_skip_call: forall f k sp e m m' fp,
    is_call_cont k ->
    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
    free_fp sp 0 f.(fn_stackspace) = fp ->
    step (Core_State f Sskip k (Vptr sp Ptrofs.zero) e) m
         fp (Core_Returnstate Vundef k) m'

| step_assign: forall f id a k sp e m v fp,
    eval_expr sp e m a v ->
    eval_expr_fp sp e m a fp ->
    step (Core_State f (Sassign id a) k sp e) m
         fp (Core_State f Sskip k sp (PTree.set id v e)) m

| step_store: forall f chunk addr a k sp e m vaddr v m' fp1 fp2 fp3 fp,
    eval_expr sp e m addr vaddr ->
    eval_expr_fp sp e m addr fp1 ->
    eval_expr sp e m a v ->
    eval_expr_fp sp e m a fp2 ->
    Mem.storev chunk m vaddr v = Some m' ->
    storev_fp chunk vaddr = fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    step (Core_State f (Sstore chunk addr a) k sp e) m
         fp (Core_State f Sskip k sp e) m'

| step_call: forall f optid sig a bl k sp e m vf vargs fd fp1 fp2 fp,
    eval_expr sp e m a vf ->
    eval_expr_fp sp e m a fp1 ->
    eval_exprlist sp e m bl vargs ->
    eval_exprlist_fp sp e m bl fp2 ->
    Genv.find_funct ge vf = Some fd ->
    funsig fd = sig ->
    FP.union fp1 fp2 = fp ->
    step (Core_State f (Scall optid sig a bl) k sp e) m
         fp (Core_Callstate fd vargs (Kcall optid f sp e k)) m

| step_tailcall: forall f sig a bl k sp e m vf vargs fd m' fp1 fp2 fp3 fp,
    eval_expr (Vptr sp Ptrofs.zero) e m a vf ->
    eval_expr_fp (Vptr sp Ptrofs.zero) e m a fp1 ->
    eval_exprlist (Vptr sp Ptrofs.zero) e m bl vargs ->
    eval_exprlist_fp (Vptr sp Ptrofs.zero) e m bl fp2 ->
    Genv.find_funct ge vf = Some fd ->
    funsig fd = sig ->
    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
    free_fp sp 0 f.(fn_stackspace) = fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    step (Core_State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e) m
         fp (Core_Callstate fd vargs (call_cont k)) m'
(*
  | step_builtin: forall f optid ef bl k sp e m vargs t vres m',
      eval_exprlist sp e m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef bl) k sp e m)
         t (State f Sskip k sp (set_optvar optid vres e) m')
 *)
| step_seq: forall f s1 s2 k sp e m,
    step (Core_State f (Sseq s1 s2) k sp e) m
         empfp (Core_State f s1 (Kseq s2 k) sp e) m

| step_ifthenelse: forall f a s1 s2 k sp e m v b fp,
    eval_expr sp e m a v ->
    eval_expr_fp sp e m a fp ->
    Val.bool_of_val v b ->
    step (Core_State f (Sifthenelse a s1 s2) k sp e) m
         fp (Core_State f (if b then s1 else s2) k sp e) m

| step_loop: forall f s k sp e m,
    step (Core_State f (Sloop s) k sp e) m
         empfp (Core_State f s (Kseq (Sloop s) k) sp e) m

| step_block: forall f s k sp e m,
    step (Core_State f (Sblock s) k sp e) m
         empfp (Core_State f s (Kblock k) sp e) m

| step_exit_seq: forall f n s k sp e m,
    step (Core_State f (Sexit n) (Kseq s k) sp e) m
         empfp (Core_State f (Sexit n) k sp e) m
| step_exit_block_0: forall f k sp e m,
    step (Core_State f (Sexit O) (Kblock k) sp e) m
         empfp (Core_State f Sskip k sp e) m
| step_exit_block_S: forall f n k sp e m,
    step (Core_State f (Sexit (S n)) (Kblock k) sp e) m
         empfp (Core_State f (Sexit n) k sp e) m

| step_switch: forall f islong a cases default k sp e m v n fp ,
    eval_expr sp e m a v ->
    eval_expr_fp sp e m a fp ->
    switch_argument islong v n ->
    step (Core_State f (Sswitch islong a cases default) k sp e) m
         fp (Core_State f (Sexit (switch_target n default cases)) k sp e) m

| step_return_0: forall f k sp e m m' fp,
    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
    free_fp sp 0 f.(fn_stackspace) = fp ->
    step (Core_State f (Sreturn None) k (Vptr sp Ptrofs.zero) e) m
         fp (Core_Returnstate Vundef (call_cont k)) m'
| step_return_1: forall f a k sp e m v m' fp1 fp2 fp,
    eval_expr (Vptr sp Ptrofs.zero) e m a v ->
    eval_expr_fp (Vptr sp Ptrofs.zero) e m a fp1 ->
    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
    free_fp sp 0 f.(fn_stackspace) = fp2 ->
    FP.union fp1 fp2 = fp ->
    step (Core_State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e) m
         fp (Core_Returnstate v (call_cont k)) m'

| step_label: forall f lbl s k sp e m,
    step (Core_State f (Slabel lbl s) k sp e) m
         empfp (Core_State f s k sp e) m

| step_goto: forall f lbl k sp e m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
    step (Core_State f (Sgoto lbl) k sp e) m
         empfp (Core_State f s' k' sp e) m

| step_internal_function: forall f vargs k m m' sp e fp,
    Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
    alloc_fp m 0 f.(fn_stackspace) = fp ->
    set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
    step (Core_Callstate (Internal f) vargs k) m
         fp (Core_State f f.(fn_body) k (Vptr sp Ptrofs.zero) e) m'
(*  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')
*)
  | step_return: forall v optid f sp e k m,
      step (Core_Returnstate v (Kcall optid f sp e k)) m
           empfp (Core_State f Sskip k sp (set_optvar optid v e)) m.

End RELSEM.


Definition cminor_comp_unit : Type := @comp_unit_generic fundef unit.

Definition init_genv (cu: cminor_comp_unit) (ge G: genv): Prop :=
  G = ge /\ ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).


Definition init_mem : genv -> gmem -> Prop := init_gmem_generic.

Definition at_external (ge: Genv.t fundef unit) (c: core) :
  option (ident * signature * list val) :=
  match c with
  | Core_State _ _ _ _ _ => None
  | Core_Callstate fd args k =>
    match fd with
    | External (EF_external name sig) =>
      match invert_symbol_from_string ge name with
      | Some fnid =>
        if peq fnid GAST.ent_atom || peq fnid GAST.ext_atom
        then None
        else Some (fnid, sig, args)
      | _ => None
      end
    | _ => None
    end
  | Core_Returnstate v k => None
 end.

Definition after_external (c: core) (vret: option val) : option core :=
  match c with
    Core_Callstate fd args k =>
    match fd with
    | External (EF_external _ sg)
      => match vret, sig_res sg with
          None, None => Some (Core_Returnstate Vundef k)
        | Some v, Some ty =>
          if val_has_type_func v ty
          then Some (Core_Returnstate v k)
          else None
        | _, _ => None
        end
    | _ => None
    end
  | _ => None
  end.

Definition halted (c : core): option val :=
  match c with
  | Core_Returnstate v Kstop => Some v
  | _ => None
  end.


(** Copied from compcomp *)
Definition fundef_init (cfd: fundef) (args: list val) : option core :=
  match cfd with
  | Internal fd =>
    if wd_args args (sig_args (funsig cfd))
    then Some (Core_Callstate cfd args Kstop)
    else None
  | External _=> None
  end.

Definition init_core (ge : Genv.t fundef unit) (fnid: ident) (args: list val): option core :=
  generic_init_core fundef_init ge fnid args.

(** wraping steps *)

Inductive step_gmem (ge: genv) (fl: freelist): core -> gmem -> FP.t -> core -> gmem -> Prop :=
  Step_intro: forall c gm m fp c' gm' m',
    embed gm fl m ->
    step ge c m fp c' m' ->
    strip m' = gm' ->
    step_gmem ge fl c gm fp c' gm'.

Definition CminorLang: Language :=
  Build_Language fundef unit genv cminor_comp_unit core 
                 init_core step_gmem at_external after_external halted 
                 CUAST.internal_fn init_genv init_mem.

