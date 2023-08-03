(* This file is adapted from [backend/LTL.v] of CompCert,
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

(** The LTL intermediate language: abstract syntax and semantics.

  LTL (``Location Transfer Language'') is the target language
  for register allocation and the source language for linearization. *)

Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Locations Conventions.

Require Import LTL.

Require Import CUAST Footprint MemOpFP helpers Op_fp String val_casted.
Require IS_local GAST.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.


(** Calling conventions are reflected at the level of location sets
  (environments mapping locations to values) by the following two
  functions.

  [call_regs caller] returns the location set at function entry,
  as a function of the location set [caller] of the calling function.
- Machine registers have the same values as in the caller.
- Incoming stack slots (used for parameter passing) have the same
  values as the corresponding outgoing stack slots (used for argument
  passing) in the caller.
- Local and outgoing stack slots are initialized to undefined values.
*)


(** [return_regs caller callee] returns the location set after
  a call instruction, as a function of the location set [caller]
  of the caller before the call instruction and of the location
  set [callee] of the callee at the return instruction.
- Callee-save machine registers have the same values as in the caller
  before the call.
- Caller-save machine registers have the same values as in the callee.
- Stack slots have the same values as in the caller.
*)


(** LTL execution states. *)

(**
    additional information about return type:
    [halted] need to return a [val], while original LTL records return value in locset, 
    and let caller decode [val] from locset using signature of callee. 

    Here we don't have caller information, 
    thus need to record the return type during the execution of callee,
    and decode val from locset when halted.

    Note [sigres] is the overall return type when a module halts, instead of the return type of current function.
    I.e. [sigres] is initialized at [initial_core], and won't change during execution.
 *)
    

Inductive core : Type :=
| Core_State:
    forall (stack: list stackframe) (**r call stack *)
      (f: function)            (**r function currently executing *)
      (sp: val)                (**r stack pointer *)
      (pc: node)               (**r current program point *)
      (ls: locset)             (**r location state *)
      (sigres: option typ),
      core
| Core_Block:
    forall (stack: list stackframe) (**r call stack *)
      (f: function)            (**r function currently executing *)
      (sp: val)                (**r stack pointer *)
      (bb: bblock)             (**r current basic block *)
      (ls: locset)             (**r location state *)
      (sigres: option typ),
      core
| Core_Callstate:
    forall (stack: list stackframe) (**r call stack *)
      (f: fundef)              (**r function to call *)
      (ls: locset)             (**r location state of caller *)
      (sigres: option typ),
      core
| Core_Returnstate:
    forall (stack: list stackframe) (**r call stack *)
      (ls: locset)             (**r location state of callee *)
      (sigres: option typ),
      core.


Section RELSEM.

Variable ge: genv.

Local Notation find_function := (find_function ge).

Inductive step: core -> mem -> footprint -> core -> mem -> Prop :=
| exec_start_block: forall s f sp pc rs m bb sigres,
    (fn_code f)!pc = Some bb ->
    step (Core_State s f sp pc rs sigres) m
         empfp (Core_Block s f sp bb rs sigres) m
| exec_Lop: forall s f sp op args res bb rs m v rs' fp sigres,
    eval_operation ge sp op (reglist rs args) m = Some v ->
    eval_operation_fp ge sp op (reglist rs args) m = Some fp ->
    rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
    step (Core_Block s f sp (Lop op args res :: bb) rs sigres) m
         fp (Core_Block s f sp bb rs' sigres) m
| exec_Lload: forall s f sp chunk addr args dst bb rs m a v rs' fp sigres,
    eval_addressing ge sp addr (reglist rs args) = Some a ->
    Mem.loadv chunk m a = Some v ->
    loadv_fp chunk a = fp ->
    rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
    step (Core_Block s f sp (Lload chunk addr args dst :: bb) rs sigres) m
         fp (Core_Block s f sp bb rs' sigres) m
| exec_Lgetstack: forall s f sp sl ofs ty dst bb rs m rs' sigres,
    rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
    step (Core_Block s f sp (Lgetstack sl ofs ty dst :: bb) rs sigres) m
         empfp (Core_Block s f sp bb rs' sigres) m
| exec_Lsetstack: forall s f sp src sl ofs ty bb rs m rs' sigres,
    rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
    step (Core_Block s f sp (Lsetstack src sl ofs ty :: bb) rs sigres) m
         empfp (Core_Block s f sp bb rs' sigres) m
| exec_Lstore: forall s f sp chunk addr args src bb rs m a rs' m' fp sigres,
    eval_addressing ge sp addr (reglist rs args) = Some a ->
    Mem.storev chunk m a (rs (R src)) = Some m' ->
    storev_fp chunk a = fp ->
    rs' = undef_regs (destroyed_by_store chunk addr) rs ->
    step (Core_Block s f sp (Lstore chunk addr args src :: bb) rs sigres) m
         fp (Core_Block s f sp bb rs' sigres) m'
| exec_Lcall: forall s f sp sig ros bb rs m fd sigres,
    find_function ros rs = Some fd ->
    funsig fd = sig ->
    step (Core_Block s f sp (Lcall sig ros :: bb) rs sigres) m
         empfp (Core_Callstate (Stackframe f sp rs bb :: s) fd rs sigres) m
| exec_Ltailcall: forall s f sp sig ros bb rs m fd rs' m' fp sigres,
    rs' = return_regs (parent_locset s) rs ->
    find_function ros rs' = Some fd ->
    funsig fd = sig ->
    Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
    free_fp sp 0 f.(fn_stacksize) = fp ->
    step (Core_Block s f (Vptr sp Ptrofs.zero) (Ltailcall sig ros :: bb) rs sigres) m
         fp (Core_Callstate s fd rs' sigres) m'
| exec_Lbuiltin: forall s f sp ef args res bb rs m vargs fp vres rs' sigres,
    eval_builtin_args ge rs sp m args vargs ->
    eval_builtin_args_fp ge rs sp args fp ->
    i64ext ef ->
    external_call ef ge vargs m E0 vres m ->
    rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
    step (Core_Block s f sp (Lbuiltin ef args res :: bb) rs sigres) m
         fp (Core_Block s f sp bb rs' sigres) m

| exec_Lbranch: forall s f sp pc bb rs m sigres,
    step (Core_Block s f sp (Lbranch pc :: bb) rs sigres) m
         empfp (Core_State s f sp pc rs sigres) m
| exec_Lcond: forall s f sp cond args pc1 pc2 bb rs b pc rs' m fp sigres,
    eval_condition cond (reglist rs args) m = Some b ->
    eval_condition_fp cond (reglist rs args) m = Some fp ->
    pc = (if b then pc1 else pc2) ->
    rs' = undef_regs (destroyed_by_cond cond) rs ->
    step (Core_Block s f sp (Lcond cond args pc1 pc2 :: bb) rs sigres) m
         fp (Core_State s f sp pc rs' sigres) m
| exec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs' sigres,
    rs (R arg) = Vint n ->
    list_nth_z tbl (Int.unsigned n) = Some pc ->
    rs' = undef_regs (destroyed_by_jumptable) rs ->
    step (Core_Block s f sp (Ljumptable arg tbl :: bb) rs sigres) m
         empfp (Core_State s f sp pc rs' sigres) m
| exec_Lreturn: forall s f sp bb rs m m' fp sigres,
    Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
    free_fp sp 0 f.(fn_stacksize) = fp ->
    step (Core_Block s f (Vptr sp Ptrofs.zero) (Lreturn :: bb) rs sigres) m
         fp (Core_Returnstate s (return_regs (parent_locset s) rs) sigres) m'
| exec_function_internal: forall s f rs m m' sp rs' fp sigres,
    Mem.alloc m 0 f.(fn_stacksize) = (m', sp) ->
    alloc_fp m 0 f.(fn_stacksize) = fp ->
    rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
    step (Core_Callstate s (Internal f) rs sigres) m
         fp (Core_State s f (Vptr sp Ptrofs.zero) f.(fn_entrypoint) rs' sigres) m'
         
| exec_function_external: forall s ef t args res rs m rs' sigres,
    args = map (fun p => Locmap.getpair p rs) (loc_arguments (ef_sig ef)) ->
    i64ext ef ->
    external_call ef ge args m t res m ->
    rs' = Locmap.setpair (loc_result (ef_sig ef)) res rs ->
    step (Core_Callstate s (External ef) rs sigres) m
         empfp (Core_Returnstate s rs' sigres) m

| exec_return: forall f sp rs1 bb s rs m sigres,
    step (Core_Returnstate (Stackframe f sp rs1 bb :: s) rs sigres) m
         empfp (Core_Block s f sp bb rs sigres) m.

End RELSEM.

(** TODO: be careful with initial_core and at_external, because we need to allocate additional blocks storing parameters, in order to avoid shared memory. *)


Definition LTL_comp_unit := @comp_unit_generic fundef unit.

Definition init_genv (cu: LTL_comp_unit) (ge G: genv): Prop :=
  ge = G /\ globalenv_generic cu ge.

Definition init_mem : genv -> mem -> Prop := init_mem_generic.


(** Copied from compcomp *)
(** In CompCert 3.0.1, LTL do not record return type in Callstate... *)
(** arguments reside in mreg? *)
                      
Definition fundef_init (cfd: fundef) (args: list val) : option core :=
  match cfd with
  | External _ => None
  | Internal fd =>
    let tyl := sig_args (funsig cfd) in
    if wd_args args tyl 
    then Some (Core_Callstate nil cfd
                              (set_arguments
                                 (loc_arguments (funsig cfd))
                                 (args)
                                 (Locmap.init Vundef))
                              (sig_res (funsig cfd))
              )
    else None
  end.

Definition init_core (ge : Genv.t fundef unit) (fnid: ident) (args: list val): option core :=
  generic_init_core fundef_init ge fnid args.

Definition at_external (ge: Genv.t fundef unit) (c: core) :
  option (ident * signature * list val) :=
  match c with
  | Core_Callstate s (External ef) ls sigres =>
    match ef with
    | (EF_external name sig) =>
      match invert_symbol_from_string ge name with
        (** following operational semantics of LTL, get arguments from locset & function signature *)
      | Some fnid =>
        if peq fnid GAST.ent_atom || peq fnid GAST.ext_atom
        then None
        else Some (fnid, sig, map (fun p => Locmap.getpair p ls) (loc_arguments sig)) 
      | _ => None
      end
    | _ => None
    end
  | _ => None
 end.

Definition after_external (c: core) (vret: option val) : option core :=
  match c with
    Core_Callstate s (External ef) ls sigres =>
    match ef with
    | (EF_external name sig)
      => match vret, (sig_res sig) with
          (** following operational semantics of LTL, set registers in locset to return value *)
          None, None => Some (Core_Returnstate s (Locmap.setpair (loc_result sig) Vundef ls) sigres)
        | Some v, Some ty =>
          if val_has_type_func v ty
          then Some (Core_Returnstate s (Locmap.setpair (loc_result sig) v ls) sigres)
          else None
        | _, _ => None
        end
    | _ => None
    end
  | _ => None
  end.

Definition halted (c : core): option val :=
  match c with
  | Core_Returnstate nil ls sigres =>
    Some (get_result (loc_result (mksignature nil sigres cc_default)) ls)
  | _ => None
  end.


Definition LTL_IS :=
  IS_local.Build_sem_local fundef unit genv LTL_comp_unit core init_genv init_mem
                           init_core halted step at_external after_external.
