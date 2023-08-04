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

(** Abstract syntax and semantics for the Cminor language.
 Mostly copied from compcert *)
Require Import Coqlib Maps AST Integers Floats Events Values.
Require Import Memory Globalenvs Smallstep Switch.

Require Import Cminor.


Require Import CUAST Footprint MemOpFP String val_casted Cminor_op_footprint.
Require GAST IS_local.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** * Abstract syntax: unchanged *)


(** * Operational semantics (small-step) *)

(** Core States *)
Inductive core: Type :=
| Core_State:                      (**r Execution within a function *)
    forall (f: function)              (**r currently executing function  *)
      (s: stmt)                  (**r statement under consideration *)
      (k: cont)                  (**r its continuation -- what to do next *)
      (sp: val)                  (**r current stack pointer *)
      (e: env),                   (**r current local environment *)
      core
| Core_Callstate:                  (**r Invocation of a function *)
    forall (f: fundef)                (**r function to invoke *)
      (args: list val)           (**r arguments provided by caller *)
      (k: cont),                  (**r what to do next  *)
      core
| Core_Returnstate:                (**r Return from a function *)
    forall (v: val)                   (**r Return value *)
      (k: cont),                  (**r what to do next *)
      core.

Section RELSEM.

Variable ge: genv.

Local Notation eval_constant := (eval_constant ge).
Local Notation eval_expr := (eval_expr ge).
Local Notation eval_exprlist := (eval_exprlist ge).

Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Inductive eval_expr_fp: expr -> footprint -> Prop :=
  | eval_Evar_fp: forall id,
      eval_expr_fp (Evar id) empfp
  | eval_Econst_fp: forall cst v,
      eval_constant sp cst = Some v ->
      eval_expr_fp (Econst cst) empfp
  | eval_Eunop_fp: forall op a1 v1 v fp,
      eval_expr sp e m a1 v1 ->
      eval_expr_fp a1 fp ->
      eval_unop op v1 = Some v ->
      eval_expr_fp (Eunop op a1) fp
  | eval_Ebinop_fp: forall op a1 a2 v1 v2 v fp1 fp2 fp3 fp,
      eval_expr sp e m a1 v1 ->
      eval_expr_fp a1 fp1 ->
      eval_expr sp e m a2 v2 ->
      eval_expr_fp a2 fp2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_binop_fp op v1 v2 m = Some fp3 ->
      FP.union (FP.union fp1 fp2) fp3 = fp ->
      eval_expr_fp (Ebinop op a1 a2) fp
  | eval_Eload_fp: forall chunk addr vaddr v fp1 fp2 fp,
      eval_expr sp e m addr vaddr ->
      eval_expr_fp addr fp1 ->
      Mem.loadv chunk m vaddr = Some v ->
      loadv_fp chunk vaddr = fp2 ->
      FP.union fp1 fp2 = fp ->
      eval_expr_fp (Eload chunk addr) fp.

Inductive eval_exprlist_fp: list expr -> footprint -> Prop :=
| eval_Enil_fp:
    eval_exprlist_fp nil empfp
| eval_Econs_fp: forall a1 al v1 vl fp1 fp2 fp,
    eval_expr sp e m a1 v1 ->
    eval_expr_fp a1 fp1 ->
    eval_exprlist sp e m al vl ->
    eval_exprlist_fp al fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_exprlist_fp (a1 :: al) fp.

End EVAL_EXPR.


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
  ge = G /\ globalenv_generic cu ge.

Definition init_mem : genv -> mem -> Prop := init_mem_generic.

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

Definition Cminor_IS :=
  IS_local.Build_sem_local fundef unit genv cminor_comp_unit core init_genv init_mem
                           init_core halted step at_external after_external.


Section EVALDET.
  Lemma eval_expr_det:
    forall ge sp e m a v,
      Cminor.eval_expr ge sp e m a v ->
      forall v', Cminor.eval_expr ge sp e m a v' -> v = v'.
  Proof.
    induction 1; intros v' EVAL; inv EVAL; try congruence.
    apply IHeval_expr in H3. subst. congruence.
    apply IHeval_expr1 in H5. apply IHeval_expr2 in H7. subst. congruence.
    apply IHeval_expr in H3. subst. congruence.
  Qed.
  Lemma eval_exprlist_det:
    forall ge sp e m al vl,
      Cminor.eval_exprlist ge sp e m al vl ->
      forall vl', Cminor.eval_exprlist ge sp e m al vl' -> vl = vl'.
  Proof.
    induction al; intros vl1 EVAL1 vl2 EVAL2;
      inv EVAL1; inv EVAL2; auto.
    eapply IHal in H3; eauto. subst. exploit eval_expr_det. exact H1. exact H2. intro. subst. auto.
  Qed.
End EVALDET.
  