(* This file is adapted from [backend/RTL.v] of CompCert,
   with support for our interaction semantics. *)

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

Require Import Coqlib Maps AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.

Require Import RTL.


Require Import Footprint MemOpFP Op_fp String val_casted helpers.
Require IS_local.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** * Operational semantics *)


(** The dynamic semantics of RTL is given in small-step style, as a
  set of transitions between states.  A state captures the current
  point in the execution.  Three kinds of states appear in the transitions:

- [State cs f sp pc rs m] describes an execution point within a function.
  [f] is the current function.
  [sp] is the pointer to the stack block for its current activation
     (as in Cminor).
  [pc] is the current program point (CFG node) within the code [c].
  [rs] gives the current values for the pseudo-registers.
  [m] is the current memory state.
- [Callstate cs f args m] is an intermediate state that appears during
  function calls.
  [f] is the function definition that we are calling.
  [args] (a list of values) are the arguments for this call.
  [m] is the current memory state.
- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.
  [v] is the return value and [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res f sp pc rs].  Each frame represents
a function call in progress.
[res] is the pseudo-register that will receive the result of the call.
[f] is the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

Inductive core : Type :=
| Core_State:
    forall (stack: list stackframe) (**r call stack *)
      (f: function)            (**r current function *)
      (sp: val)                (**r stack pointer *)
      (pc: node)               (**r current program point in [c] *)
      (rs: regset),             (**r register state *)
      core
| Core_Callstate:
    forall (stack: list stackframe) (**r call stack *)
      (f: fundef)              (**r function to call *)
      (args: list val),         (**r arguments to the call *)
      core
| Core_Returnstate:
    forall (stack: list stackframe) (**r call stack *)
      (v: val),                 (**r return value for the call *)
      core.


Section RELSEM.

Variable ge: genv.

Local Notation find_function := (find_function ge).

(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive step: core -> mem -> footprint -> core -> mem -> Prop :=
| exec_Inop:
    forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      step (Core_State s f sp pc rs) m
           empfp (Core_State s f sp pc' rs) m
| exec_Iop:
    forall s f sp pc rs m op args res pc' v fp,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      eval_operation_fp ge sp op rs##args m = Some fp ->
      step (Core_State s f sp pc rs) m
           fp (Core_State s f sp pc' (rs#res <- v)) m
| exec_Iload:
    forall s f sp pc rs m chunk addr args dst pc' a v fp,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      loadv_fp chunk a = fp ->
      step (Core_State s f sp pc rs) m
           fp (Core_State s f sp pc' (rs#dst <- v)) m
| exec_Istore:
    forall s f sp pc rs m chunk addr args src pc' a m' fp,
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      storev_fp chunk a = fp ->
      step (Core_State s f sp pc rs) m
           fp (Core_State s f sp pc' rs) m'
| exec_Icall:
    forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step (Core_State s f sp pc rs) m
           empfp (Core_Callstate (Stackframe res f sp pc' rs :: s) fd rs##args) m

| exec_Itailcall:
    forall s f stk pc rs m sig ros args fd m' fp,
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      free_fp stk 0 f.(fn_stacksize) = fp ->
      step (Core_State s f (Vptr stk Ptrofs.zero) pc rs) m
           fp (Core_Callstate s fd rs##args) m'
           
| exec_Ibuiltin:
    forall s f sp pc rs m ef args res pc' vargs vres fp,
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      eval_builtin_args_fp ge (fun r => rs#r) sp args fp ->
      i64ext ef ->
      external_call ef ge vargs m E0 vres m ->
      step (Core_State s f sp pc rs) m
           fp (Core_State s f sp pc' (regmap_setres res vres rs)) m
           
| exec_Icond:
    forall s f sp pc rs m cond args ifso ifnot b pc' fp,
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      eval_condition_fp cond rs##args m = Some fp ->
      pc' = (if b then ifso else ifnot) ->
      step (Core_State s f sp pc rs) m
           fp (Core_State s f sp pc' rs) m
| exec_Ijumptable:
    forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (Core_State s f sp pc rs) m
           empfp (Core_State s f sp pc' rs) m
| exec_Ireturn:
    forall s f stk pc rs m or m' fp,
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      free_fp stk 0 f.(fn_stacksize) = fp ->
      step (Core_State s f (Vptr stk Ptrofs.zero) pc rs) m
           fp (Core_Returnstate s (regmap_optget or Vundef rs)) m'
| exec_function_internal:
    forall s f args m m' stk fp,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      alloc_fp m 0 f.(fn_stacksize) = fp ->
      step (Core_Callstate s (Internal f) args) m
           fp (Core_State s
                          f
                          (Vptr stk Ptrofs.zero)
                          f.(fn_entrypoint)
                              (init_regs args f.(fn_params))) m'
(** support i64 runtime helpers only *)
| exec_function_external:
    forall s ef args res m ,
      i64ext ef ->
      external_call ef ge args m E0 res m ->
      step (Core_Callstate s (External ef) args) m
           empfp (Core_Returnstate s res) m

| exec_return:
    forall res f sp pc rs s vres m,
      step (Core_Returnstate (Stackframe res f sp pc rs :: s) vres) m
           empfp (Core_State s f sp pc (rs#res <- vres)) m.

Lemma exec_Iop':
  forall s f sp pc rs m op args res pc' rs' v fp,
  (fn_code f)!pc = Some(Iop op args res pc') ->
  eval_operation ge sp op rs##args m = Some v ->
  eval_operation_fp ge sp op rs##args m = Some fp ->
  rs' = (rs#res <- v) ->
  step (Core_State s f sp pc rs) m
       fp (Core_State s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
  forall s f sp pc rs m chunk addr args dst pc' rs' a v fp,
  (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  loadv_fp chunk a = fp ->
  rs' = (rs#dst <- v) ->
  step (Core_State s f sp pc rs) m
       fp (Core_State s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply exec_Iload; eauto.
Qed.

End RELSEM.

Require Import CUAST.
Require GAST.

Definition RTL_comp_unit := @comp_unit_generic fundef unit.

Definition init_genv (cu: RTL_comp_unit) (ge G: genv): Prop :=
  ge = G /\ globalenv_generic cu ge.

Definition init_mem : genv -> mem -> Prop := init_mem_generic.

Definition at_external (ge: Genv.t fundef unit) (c: core) :
  option (ident * signature * list val) :=
  match c with
  | Core_Callstate s (External ef) args =>
    match ef with
    | (EF_external name sig) =>
      match invert_symbol_from_string ge name with
      | Some fnid =>
        if peq fnid GAST.ent_atom || peq fnid GAST.ext_atom
        then None
        else Some (fnid, sig, args)
      | _ => None
      end
    | _ => None
    end
  | _ => None
 end.

Definition after_external (c: core) (vret: option val) : option core :=
  match c with
    Core_Callstate s (External ef) args =>
    match ef with
    | (EF_external _ sg)
      => match vret, sig_res sg with
          None, None => Some (Core_Returnstate s Vundef)
        | Some v, Some ty =>
          if val_has_type_func v ty
          then Some (Core_Returnstate s v)
          else None
        | _, _ => None
        end
    | _ => None
    end
  | _ => None
  end.

Definition halted (c : core): option val :=
  match c with
  | Core_Returnstate nil v => Some v
  | _ => None
  end.


(** Copied from compcomp *)
Definition fundef_init (cfd: fundef) (args: list val) : option core :=
  match cfd with
  | Internal fd =>
    let tyl := sig_args (funsig cfd) in
    if wd_args args tyl
    then Some (Core_Callstate nil cfd args)
    else None
  | External _=> None
  end.

Definition init_core (ge : Genv.t fundef unit) (fnid: ident) (args: list val): option core :=
  generic_init_core fundef_init ge fnid args.

Definition RTL_IS :=
  IS_local.Build_sem_local fundef unit genv RTL_comp_unit core init_genv init_mem
                           init_core halted step at_external after_external.
