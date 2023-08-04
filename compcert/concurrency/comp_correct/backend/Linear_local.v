(* This file is adapted from [backend/Linear.v] of CompCert,
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


(** The Linear language is a variant of LTL where control-flow is not
    expressed as a graph of basic blocks, but as a linear list of
    instructions with explicit labels and ``goto'' instructions. *)

Require Import Coqlib.
Require Import AST Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Locations LTL Conventions.

Require Import Linear.

Require Import CUAST Footprint MemOpFP Op_fp String val_casted helpers.
Require IS_local GAST.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** * Operational semantics *)

Section RELSEM.

Variable ge: genv.

Local Notation find_function := (find_function ge).



(*** Warning *)
(** TODO: 
    in compcomp, they made a dummy state to facilitate the stacking proof.
    I wonder if we need it here.
 *)
Inductive load_frame: Type :=
| mk_load_frame:
    forall (rs0: Linear.locset)  (**r location state at program entry *)
      (f: Linear.function), (**r initial function *)
      load_frame.

Definition parent_locset0 (ls0: Linear.locset) (stack: list stackframe) : Linear.locset :=
  match stack with
  | nil => ls0
  | Stackframe _ _ ls _ :: _ => ls
  end.

Goal forall stack, parent_locset0 (Locmap.init Vundef) stack = parent_locset stack.
Proof. intro. case stack; auto. Qed.
      
  
(** record sig_res for the same reason as LTL_local *)
Inductive core: Type :=
| Core_State:
    forall (stack: list stackframe) (**r call stack *)
      (f: function)            (**r function currently executing *)
      (sp: val)                (**r stack pointer *)
      (c: code)                (**r current program point *)
      (rs: locset)             (**r location state *)
      (lf: load_frame),
      core
| Core_Callstate:
    forall (stack: list stackframe) (**r call stack *)
      (f: fundef)              (**r function to call *)
      (rs: locset)             (**r location state at point of call *)
      (lf: load_frame),
      core
| Core_CallstateIn:
    forall (stack: list stackframe)
      (f: fundef)
      (rs: locset)
      (lf: load_frame),
      core
| Core_Returnstate:
    forall (stack: list stackframe) (**r call stack *)
      (rs: locset)             (**r location state at point of return *)
      (lf: load_frame),
      core.

Inductive step: core -> mem -> footprint -> core -> mem -> Prop :=
| exec_Lgetstack:
    forall s f sp sl ofs ty dst b rs m rs' lf,
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      step (Core_State s f sp (Lgetstack sl ofs ty dst :: b) rs lf) m
           empfp (Core_State s f sp b rs' lf) m
| exec_Lsetstack:
    forall s f sp src sl ofs ty b rs m rs' lf,
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      step (Core_State s f sp (Lsetstack src sl ofs ty :: b) rs lf) m
           empfp (Core_State s f sp b rs' lf) m
| exec_Lop:
    forall s f sp op args res b rs m v rs' fp lf,
      eval_operation ge sp op (reglist rs args) m = Some v ->
      eval_operation_fp ge sp op (reglist rs args) m = Some fp ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      step (Core_State s f sp (Lop op args res :: b) rs lf) m
           fp (Core_State s f sp b rs' lf) m
| exec_Lload:
    forall s f sp chunk addr args dst b rs m a v rs' fp lf ,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      loadv_fp chunk a = fp ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step (Core_State s f sp (Lload chunk addr args dst :: b) rs lf) m
           fp (Core_State s f sp b rs' lf) m
| exec_Lstore:
    forall s f sp chunk addr args src b rs m m' a rs' fp lf,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      storev_fp chunk a = fp ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (Core_State s f sp (Lstore chunk addr args src :: b) rs lf) m
           fp (Core_State s f sp b rs' lf) m'
| exec_Lcall:
    forall s f sp sig ros b rs m f' lf,
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      step (Core_State s f sp (Lcall sig ros :: b) rs lf) m
           empfp (Core_Callstate (Stackframe f sp rs b:: s) f' rs lf) m
| exec_Ltailcall:
    forall s f stk sig ros b rs m rs' f' m' fp fd0 rs0,
      rs' = return_regs (parent_locset0 rs0 s) rs ->
      find_function ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      free_fp stk 0 f.(fn_stacksize) = fp ->
      step (Core_State s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: b) rs (mk_load_frame rs0 fd0)) m
           fp (Core_Callstate s f' rs' (mk_load_frame rs0 fd0)) m'
| exec_Lbuiltin:
    forall s f sp rs m ef args res b vargs fp vres rs' lf,
      eval_builtin_args ge rs sp m args vargs ->
      eval_builtin_args_fp ge rs sp args fp ->      
      i64ext ef ->
      external_call ef ge vargs m E0 vres m ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (Core_State s f sp (Lbuiltin ef args res :: b) rs lf) m
           fp (Core_State s f sp b rs' lf) m
| exec_Llabel:
    forall s f sp lbl b rs m lf,
      step (Core_State s f sp (Llabel lbl :: b) rs lf) m
           empfp (Core_State s f sp b rs lf) m
| exec_Lgoto:
    forall s f sp lbl b rs m b' lf,
      find_label lbl f.(fn_code) = Some b' ->
      step (Core_State s f sp (Lgoto lbl :: b) rs lf) m
           empfp (Core_State s f sp b' rs lf) m
| exec_Lcond_true:
    forall s f sp cond args lbl b rs m rs' b' fp lf,
      eval_condition cond (reglist rs args) m = Some true ->
      eval_condition_fp cond (reglist rs args) m = Some fp ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      step (Core_State s f sp (Lcond cond args lbl :: b) rs lf) m
           fp (Core_State s f sp b' rs' lf) m
| exec_Lcond_false:
    forall s f sp cond args lbl b rs m rs' fp lf,
      eval_condition cond (reglist rs args) m = Some false ->
      eval_condition_fp cond (reglist rs args) m = Some fp ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (Core_State s f sp (Lcond cond args lbl :: b) rs lf) m
           fp (Core_State s f sp b rs' lf) m
| exec_Ljumptable:
    forall s f sp arg tbl b rs m n lbl b' rs' lf,
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step (Core_State s f sp (Ljumptable arg tbl :: b) rs lf) m
           empfp (Core_State s f sp b' rs' lf) m
| exec_Lreturn:
    forall s f stk b rs m m' fp fd0 rs0,
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      free_fp stk 0 f.(fn_stacksize) = fp ->
      step (Core_State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs (mk_load_frame rs0 fd0)) m
           fp (Core_Returnstate s (return_regs (parent_locset0 rs0 s) rs) (mk_load_frame rs0 fd0)) m'
| exec_function_internal:
    forall s f rs m rs' m' stk fp lf,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      alloc_fp m 0 f.(fn_stacksize) = fp ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step (Core_Callstate s (Internal f) rs lf) m
           fp (Core_State s f (Vptr stk Ptrofs.zero) f.(fn_code) rs' lf) m'
| exec_function_internal0:
    forall s f rs m rs0 f0,
      step (Core_CallstateIn s (Internal f) rs (mk_load_frame rs0 f0)) m
           empfp (Core_Callstate s (Internal f) rs (mk_load_frame rs0 f0)) m
| exec_function_external:
    forall s ef args res rs1 rs2 m lf,
      args = map (fun p => Locmap.getpair p rs1) (loc_arguments (ef_sig ef)) ->
      i64ext ef ->
      external_call ef ge args m E0 res m ->
      rs2 = Locmap.setpair (loc_result (ef_sig ef)) res rs1 ->
      step (Core_Callstate s (External ef) rs1 lf) m
           empfp (Core_Returnstate s rs2 lf) m
           
| exec_return:
    forall s f sp rs0 c rs m lf,
      step (Core_Returnstate (Stackframe f sp rs0 c :: s) rs lf) m
           empfp (Core_State s f sp c rs lf) m.

End RELSEM.





Definition Linear_comp_unit := @comp_unit_generic fundef unit.

Definition init_genv (cu: Linear_comp_unit) (ge G: genv): Prop :=
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
    then
      let ls0 := set_arguments (loc_arguments (funsig cfd)) args (Locmap.init Vundef) in
      Some (Core_CallstateIn nil cfd ls0 (mk_load_frame ls0 fd))
    else None
  end.

Definition init_core (ge : Genv.t fundef unit) (fnid: ident) (args: list val): option core :=
  generic_init_core fundef_init ge fnid args.

Definition at_external (ge: Genv.t fundef unit) (c: core) :
  option (ident * signature * list val) :=
  match c with
  | Core_Callstate s (External ef) ls lf =>
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
    Core_Callstate s (External ef) ls lf =>
    match ef with
    | (EF_external name sig)
      => match vret, (sig_res sig) with
          (** following operational semantics of LTL, set registers in locset to return value *)
          None, None => Some (Core_Returnstate s (Locmap.setpair (loc_result sig) Vundef ls) lf)
        | Some v, Some ty =>
          if val_has_type_func v ty
          then Some (Core_Returnstate s (Locmap.setpair (loc_result sig) v ls) lf)
          else None
        | _, _ => None
        end
    | _ => None
    end
  | _ => None
  end.

Definition halted (c : core): option val :=
  match c with
  | Core_Returnstate nil ls (mk_load_frame ls0 fd) =>
    Some (get_result (loc_result (fn_sig fd)) ls)
  | _ => None
  end.


Definition Linear_IS :=
  IS_local.Build_sem_local fundef unit genv Linear_comp_unit core init_genv init_mem
                           init_core halted step at_external after_external.
