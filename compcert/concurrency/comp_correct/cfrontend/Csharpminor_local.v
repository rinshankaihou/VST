(* This file is adapted from [cfrontend/Cshapminor.v] of CompCert,
   with support for our interaction semantics *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for the Csharpminor language. 
    Mostly copied from original CompCert.
*)
Require Import Coqlib Maps AST Integers Floats Values.
Require Import Memory Events Globalenvs Switch Smallstep.
Require Cminor.

Require Import Csharpminor.

Require Import CUAST Footprint MemOpFP String val_casted Cminor_op_footprint.
Require IS_local.


Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** Abstract syntax: unchanged *)

(** * Operational semantics *)

(** States *)
(** In our case, [core] type, which is compcert state without memory *)
Inductive core: Type :=
| Core_State:                      (**r Execution within a function *)
    forall (f: function)              (**r currently executing function  *)
      (s: stmt)                  (**r statement under consideration *)
      (k: cont)                  (**r its continuation -- what to do next *)
      (e: env)                   (**r current local environment *)
      (le: temp_env),             (**r current temporary environment *)
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

(** need to define binary operation footprints for Cminor.eval_binop *)
Definition eval_binop_fp := Cminor_op_footprint.eval_binop_fp.

(** footprint for allocation of local variables  at function entry *)
Inductive alloc_variables_fp: mem -> list (ident * Z) -> footprint -> Prop :=
| alloc_variables_fp_nil:
    forall m, alloc_variables_fp m nil empfp
| alloc_variables_fp_cons:
    forall m id sz vars m1 b1 fp fp',
      Mem.alloc m 0 sz = (m1, b1) ->
      alloc_fp m 0 sz = fp ->
      alloc_variables_fp m1 vars fp' ->
      alloc_variables_fp m ((id, sz) :: vars) (FP.union fp fp').
      
Lemma alloc_variables_extends:
  forall a e m te m' Lm fp,
    alloc_variables e m a te m'->
    alloc_variables_fp m a fp->
    Mem.extends m Lm ->
    exists  Hm, alloc_variables e Lm a te Hm /\ alloc_variables_fp Lm a fp /\ Mem.extends m' Hm.
Proof.
  induction a;intros.
  inv H. exists Lm. constructor. constructor. inv H0. constructor. constructor. auto.
  inv H. inv H0.
  rewrite H6 in H5;inv H5.
  eapply Mem.alloc_extends with(lo2:=0)(hi2:=sz) in H6 as ?;eauto;try Lia.lia.
  destruct H as [?[]].
  eapply IHa in H0 as [?[?[]]];eauto.
  exists x0. econstructor;eauto. econstructor;eauto.
  econstructor;eauto.
  econstructor;eauto.
  unfold MemOpFP.alloc_fp.
  Transparent Mem.alloc.
  unfold Mem.alloc in *.
  inv H;inv H6. auto.
  Opaque Mem.alloc.
Qed.
Section RELSEM.

Variable ge: genv.

Local Notation eval_var_addr := (eval_var_addr ge).
Local Notation eval_expr := (eval_expr ge).
Local Notation eval_exprlist := (eval_exprlist ge).
(** footprint for evaluation of an expression *)
Section EVAL_EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive eval_expr_fp: expr -> footprint -> Prop :=
| eval_Evar_fp: forall id,
    eval_expr_fp (Evar id) empfp
| eval_Eaddrof: forall id b,
    eval_var_addr e id b ->
    eval_expr_fp (Eaddrof id) empfp
| eval_Econst: forall cst v,
    eval_constant cst = Some v ->
    eval_expr_fp (Econst cst) empfp
| eval_Eunop: forall op a1 v1 fp1 v,
    eval_expr e le m a1 v1 ->
    eval_expr_fp a1 fp1 ->
    eval_unop op v1 = Some v ->
    eval_expr_fp (Eunop op a1) fp1
| eval_Ebinop: forall op a1 a2 v1 v2 fp1 fp2 v fp3 fp,
    eval_expr e le m a1 v1 ->
    eval_expr_fp a1 fp1 ->
    eval_expr e le m a2 v2 ->
    eval_expr_fp a2 fp2 ->
    eval_binop op v1 v2 m = Some v ->
    eval_binop_fp op v1 v2 m = Some fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    eval_expr_fp (Ebinop op a1 a2) fp
| eval_Eload: forall chunk a v1 fp1 v fp2 fp,
    eval_expr e le m a v1 ->
    eval_expr_fp a fp1 ->
    Mem.loadv chunk m v1 = Some v ->
    loadv_fp chunk v1 = fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp (Eload chunk a) fp.


(** footprint for evaluation of a list of expressions *)
Inductive eval_exprlist_fp: list expr -> footprint -> Prop :=
| eval_Enil:
    eval_exprlist_fp nil empfp
| eval_Econs: forall a1 al fp1 fp2 fp,
    eval_expr_fp a1 fp1 ->
    eval_exprlist_fp al fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_exprlist_fp (a1 :: al) fp.

End EVAL_EXPR.


(** One step of execution, with footprint *)

Inductive step: core -> mem -> footprint -> core -> mem -> Prop :=
| step_skip_seq: forall f s k e le m,
    step (Core_State f Sskip (Kseq s k) e le) m
         empfp (Core_State f s k e le) m
| step_skip_block: forall f k e le m,
    step (Core_State f Sskip (Kblock k) e le) m
         empfp (Core_State f Sskip k e le) m
| step_skip_call: forall f k e le m m' fp,
    is_call_cont k ->
    Mem.free_list m (blocks_of_env e) = Some m' ->
    free_list_fp (blocks_of_env e) = fp ->
    step (Core_State f Sskip k e le) m
         fp (Core_Returnstate Vundef k) m'

| step_set: forall f id a k e le m v fp,
    eval_expr e le m a v ->
    eval_expr_fp e le m a fp ->
    step (Core_State f (Sset id a) k e le) m
         fp (Core_State f Sskip k e (PTree.set id v le)) m

| step_store: forall f chunk addr a k e le m vaddr v m' fp1 fp2 fp3 fp,
    eval_expr e le m addr vaddr ->
    eval_expr_fp e le m addr fp1 ->
    eval_expr e le m a v ->
    eval_expr_fp e le m a fp2 ->
    Mem.storev chunk m vaddr v = Some m' ->
    storev_fp chunk vaddr = fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    step (Core_State f (Sstore chunk addr a) k e le) m
         fp (Core_State f Sskip k e le) m'

| step_call: forall f optid sig a bl k e le m vf vargs fd fp1 fp2 fp,
    eval_expr e le m a vf ->
    eval_expr_fp e le m a fp1 ->
    eval_exprlist e le m bl vargs ->
    eval_exprlist_fp e le m bl fp2 ->
    Genv.find_funct ge vf = Some fd ->
    funsig fd = sig ->
    FP.union fp1 fp2 = fp ->
    step (Core_State f (Scall optid sig a bl) k e le) m
         fp (Core_Callstate fd vargs (Kcall optid f e le k)) m
(*
| step_builtin: forall f optid ef bl k e le m vargs t vres m',
    eval_exprlist e le m bl vargs ->
    external_call ef ge vargs m t vres m' ->
    step (State f (Sbuiltin optid ef bl) k e le m)
         t (State f Sskip k e (Cminor.set_optvar optid vres le) m')
*)
| step_seq: forall f s1 s2 k e le m,
    step (Core_State f (Sseq s1 s2) k e le) m
         empfp (Core_State f s1 (Kseq s2 k) e le) m

| step_ifthenelse: forall f a s1 s2 k e le m v b fp,
    eval_expr e le m a v ->
    eval_expr_fp e le m a fp ->
    Val.bool_of_val v b ->
    step (Core_State f (Sifthenelse a s1 s2) k e le) m
         fp (Core_State f (if b then s1 else s2) k e le) m

| step_loop: forall f s k e le m,
    step (Core_State f (Sloop s) k e le) m
         empfp (Core_State f s (Kseq (Sloop s) k) e le) m

| step_block: forall f s k e le m,
    step (Core_State f (Sblock s) k e le) m
         empfp (Core_State f s (Kblock k) e le) m

| step_exit_seq: forall f n s k e le m,
    step (Core_State f (Sexit n) (Kseq s k) e le) m
         empfp (Core_State f (Sexit n) k e le) m
| step_exit_block_0: forall f k e le m,
    step (Core_State f (Sexit O) (Kblock k) e le) m
         empfp (Core_State f Sskip k e le) m
| step_exit_block_S: forall f n k e le m,
    step (Core_State f (Sexit (S n)) (Kblock k) e le) m
         empfp (Core_State f (Sexit n) k e le) m

| step_switch: forall f islong a cases k e le m v n fp,
    eval_expr e le m a v ->
    eval_expr_fp e le m a fp ->
    switch_argument islong v n ->
    step (Core_State f (Sswitch islong a cases) k e le) m
         fp (Core_State f (seq_of_lbl_stmt (select_switch n cases)) k e le) m

| step_return_0: forall f k e le m m' fp,
    Mem.free_list m (blocks_of_env e) = Some m' ->
    free_list_fp (blocks_of_env e) = fp ->
    step (Core_State f (Sreturn None) k e le) m
         fp (Core_Returnstate Vundef (call_cont k)) m'
| step_return_1: forall f a k e le m v m' fp1 fp2 fp,
    eval_expr e le m a v ->
    eval_expr_fp e le m a fp1 ->
    Mem.free_list m (blocks_of_env e) = Some m' ->
    free_list_fp (blocks_of_env e) = fp2 ->
    FP.union fp1 fp2 = fp ->
    step (Core_State f (Sreturn (Some a)) k e le) m
         fp (Core_Returnstate v (call_cont k)) m'
| step_label: forall f lbl s k e le m,
    step (Core_State f (Slabel lbl s) k e le) m
         empfp (Core_State f s k e le) m

| step_goto: forall f lbl k e le m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
    step (Core_State f (Sgoto lbl) k e le) m
         empfp (Core_State f s' k' e le) m

| step_internal_function: forall f vargs k m m1 e le fp,
    list_norepet (map fst f.(fn_vars)) ->
    list_norepet f.(fn_params) ->
    list_disjoint f.(fn_params) f.(fn_temps) ->
    alloc_variables empty_env m (fn_vars f) e m1 ->
    alloc_variables_fp m (fn_vars f) fp ->
    bind_parameters f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
    step (Core_Callstate (Internal f) vargs k) m
         fp (Core_State f f.(fn_body) k e le) m1
(*
| step_external_function: forall ef vargs k m t vres m',
    external_call ef ge vargs m t vres m' ->
    step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')
*)
| step_return: forall v optid f e le k m,
    step (Core_Returnstate v (Kcall optid f e le k)) m
         empfp (Core_State f Sskip k e (Cminor.set_optvar optid v le)) m.

End RELSEM.



(* should lift to beginning *)
(** TODO: comp_units in all languages could be abstracted *)
Definition comp_unit := @comp_unit_generic fundef unit.
Definition init_genv (cu: comp_unit) (ge G: genv) := ge = G /\ globalenv_generic cu ge.
Definition init_mem := @init_mem_generic fundef unit.

(** Copied from compcomp *)
Definition fundef_init (cfd: fundef) (args: list val) : option core :=
  match cfd with
  | Internal fd =>
    if val_has_type_list_func args (sig_args (funsig cfd))
                              && vals_defined args
                              && zlt (4*(2*(Zlength args))) Int.max_unsigned
    then Some (Core_Callstate cfd args Kstop)
    else None
  | External _=> None
  end.

Definition init_core (ge : Genv.t fundef unit) (fnid: ident) (args: list val): option core :=
  generic_init_core fundef_init ge fnid args.

Require GAST.
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


(** Wrap all these definitions into sem_local *)
Definition Csharpminor_IS :=
  IS_local.Build_sem_local fundef unit genv comp_unit core init_genv init_mem
                           init_core halted step at_external after_external.
