(* This file is adapted from [backend/CminorSel.v] of CompCert,
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

(** The Cminor language after instruction selection. *)

Require Import Coqlib Maps AST Integers Events Values Memory.
Require Import Cminor Op Globalenvs Smallstep.

Require Import Cminor_local CminorSel helpers.
Require Import CUAST Footprint MemOpFP Op_fp String val_casted.
Require IS_local.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** * Operational semantics *)

(** States *)

Inductive core: Type :=
| Core_State:                              (**r execution within a function *)
    forall (f: function)              (**r currently executing function  *)
      (s: stmt)                  (**r statement under consideration *)
      (k: cont)                  (**r its continuation -- what to do next *)
      (sp: val)                  (**r current stack pointer *)
      (e: env),                   (**r current local environment *)
      core
| Core_Callstate:                          (**r invocation of a fundef  *)
    forall (f: fundef)                (**r fundef to invoke *)
      (args: list val)           (**r arguments provided by caller *)
      (k: cont),                  (**r what to do next  *)
      core
| Core_Returnstate:
    forall (v: val)                   (**r return value *)
      (k: cont),                  (**r what to do next *)
      core.

Section RELSEM.

Variable ge: genv.

Local Notation eval_expr := (eval_expr ge).
Local Notation eval_exprlist := (eval_exprlist ge).
Local Notation eval_condexpr := (eval_condexpr ge).
Local Notation eval_exitexpr := (eval_exitexpr ge).
Local Notation eval_expr_or_symbol := (eval_expr_or_symbol ge).

(** The evaluation predicates have the same general shape as those
    of Cminor.  Refer to the description of Cminor semantics for
    the meaning of the parameters of the predicates. *)

Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Inductive eval_expr_fp: letenv -> expr -> footprint -> Prop :=
| eval_Evar_fp: forall le id v,
    PTree.get id e = Some v ->
    eval_expr_fp le (Evar id) empfp
| eval_Eop_fp: forall le op al vl v fp1 fp2 fp,
    eval_exprlist sp e m le al vl ->
    eval_exprlist_fp le al fp1 ->
    eval_operation ge sp op vl m = Some v ->
    eval_operation_fp ge sp op vl m = Some fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp le (Eop op al) fp
| eval_Eload_fp: forall le chunk addr al vl vaddr v fp1 fp2 fp,
    eval_exprlist sp e m le al vl ->
    eval_exprlist_fp le al fp1 ->
    eval_addressing ge sp addr vl = Some vaddr ->
    Mem.loadv chunk m vaddr = Some v ->
    loadv_fp chunk vaddr = fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp le (Eload chunk addr al) fp
| eval_Econdition_fp: forall le a b c va v fp1 fp2 fp,
    eval_condexpr sp e m le a va ->
    eval_condexpr_fp le a fp1 ->
    eval_expr sp e m le (if va then b else c) v ->
    eval_expr_fp le (if va then b else c) fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp le (Econdition a b c) fp
| eval_Elet_fp: forall le a b v1 v2 fp1 fp2 fp,
    eval_expr sp e m le a v1 ->
    eval_expr_fp le a fp1 ->      
    eval_expr sp e m (v1 :: le) b v2 ->
    eval_expr_fp (v1 :: le) b fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp le (Elet a b) fp
| eval_Eletvar_fp: forall le n v,
    nth_error le n = Some v ->
    eval_expr_fp le (Eletvar n) empfp
(** we allow only evaluation of i64 helpers, which has empty footprint and no memory effect *)
| eval_Ebuiltin_fp: forall le ef al vl fp v,
    i64ext ef ->
    eval_exprlist sp e m le al vl ->
    eval_exprlist_fp le al fp ->      
    external_call ef ge vl m E0 v m ->
    eval_expr_fp le (Ebuiltin ef al) fp
| eval_Eexternal_fp: forall le id sg al b ef vl fp v,
    i64ext ef ->
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some (External ef) ->
    ef_sig ef = sg ->
    eval_exprlist sp e m le al vl ->
    eval_exprlist_fp le al fp ->    
    external_call ef ge vl m E0 v m ->
    eval_expr_fp le (Eexternal id sg al) fp 

with eval_exprlist_fp: letenv -> exprlist -> footprint -> Prop :=
     | eval_Enil_fp: forall le,
         eval_exprlist_fp  le Enil empfp
     | eval_Econs_fp: forall le a1 al v1 vl fp1 fp2 fp,
         eval_expr sp e m le a1 v1 ->
         eval_expr_fp le a1 fp1 ->
         eval_exprlist sp e m le al vl ->
         eval_exprlist_fp le al fp2 ->
         FP.union fp1 fp2 = fp ->
         eval_exprlist_fp le (Econs a1 al) fp

with eval_condexpr_fp: letenv -> condexpr -> footprint -> Prop :=
     | eval_CEcond_fp: forall le cond al vl vb fp1 fp2 fp,
         eval_exprlist sp e m le al vl ->
         eval_exprlist_fp le al fp1 ->
         eval_condition cond vl m = Some vb ->
         eval_condition_fp cond vl m = Some fp2 ->
         FP.union fp1 fp2 = fp ->
         eval_condexpr_fp le (CEcond cond al) fp
     | eval_CEcondition_fp: forall le a b c va v fp1 fp2 fp,
         eval_condexpr sp e m le a va ->
         eval_condexpr_fp le a fp1 ->         
         eval_condexpr sp e m le (if va then b else c) v ->
         eval_condexpr_fp le (if va then b else c) fp2 ->
         FP.union fp1 fp2 = fp ->
         eval_condexpr_fp le (CEcondition a b c) fp
     | eval_CElet_fp: forall le a b v1 v2 fp1 fp2 fp,
         eval_expr sp e m le a v1 ->
         eval_expr_fp le a fp1 ->
         eval_condexpr sp e m (v1 :: le) b v2 ->
         eval_condexpr_fp (v1 :: le) b fp2 ->
         FP.union fp1 fp2 = fp ->
         eval_condexpr_fp le (CElet a b) fp.

Scheme eval_expr_fp_ind3 := Minimality for eval_expr_fp Sort Prop
  with eval_exprlist_fp_ind3 := Minimality for eval_exprlist_fp Sort Prop
  with eval_condexpr_fp_ind3 := Minimality for eval_condexpr_fp Sort Prop.

Inductive eval_exitexpr_fp: letenv -> exitexpr -> footprint -> Prop :=
| eval_XEexit_fp: forall le x,
    eval_exitexpr_fp le (XEexit x) empfp
| eval_XEjumptable_fp: forall le a tbl n x fp,
    eval_expr sp e m le a (Vint n) ->
    eval_expr_fp le a fp ->    
    list_nth_z tbl (Int.unsigned n) = Some x ->
    eval_exitexpr_fp le (XEjumptable a tbl) fp
| eval_XEcondition_fp: forall le a b c va x fp1 fp2 fp,
    eval_condexpr sp e m le a va ->
    eval_condexpr_fp le a fp1 ->    
    eval_exitexpr sp e m le (if va then b else c) x ->
    eval_exitexpr_fp le (if va then b else c) fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_exitexpr_fp le (XEcondition a b c) fp
| eval_XElet: forall le a b v x fp1 fp2 fp,
    eval_expr sp e m le a v ->
    eval_expr_fp le a fp1 ->    
    eval_exitexpr sp e m (v :: le) b x ->
    eval_exitexpr_fp (v :: le) b fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_exitexpr_fp le (XElet a b) fp.

Inductive eval_expr_or_symbol_fp: letenv -> expr + ident -> footprint -> Prop :=
| eval_eos_e_fp: forall le E v fp,
    eval_expr sp e m le E v ->
    eval_expr_fp le E fp ->    
    eval_expr_or_symbol_fp le (inl _ E) fp
| eval_eos_s_fp: forall le id b,
    Genv.find_symbol ge id = Some b ->
    eval_expr_or_symbol_fp le (inr _ id) empfp.


Inductive eval_builtin_arg_fp: builtin_arg expr -> footprint -> Prop :=
| eval_BA_fp: forall a v fp,
    eval_expr sp e m nil a v ->
    eval_expr_fp nil a fp ->
    eval_builtin_arg_fp (BA a) fp
| eval_BA_int_fp: forall n,
    eval_builtin_arg_fp (BA_int n) empfp
| eval_BA_long_fp: forall n,
    eval_builtin_arg_fp (BA_long n) empfp
| eval_BA_float_fp: forall n,
    eval_builtin_arg_fp (BA_float n) empfp
| eval_BA_single_fp: forall n,
    eval_builtin_arg_fp (BA_single n) empfp
| eval_BA_loadstack_fp: forall chunk ofs v fp,
    Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
    loadv_fp chunk (Val.offset_ptr sp ofs) = fp ->
    eval_builtin_arg_fp (BA_loadstack chunk ofs) fp
| eval_BA_addrstack_fp: forall ofs,
    eval_builtin_arg_fp (BA_addrstack ofs) empfp
| eval_BA_loadglobal_fp: forall chunk id ofs v fp,
    Mem.loadv chunk m (Genv.symbol_address ge id ofs) = Some v ->
    loadv_fp chunk (Genv.symbol_address ge id ofs) = fp ->
    eval_builtin_arg_fp (BA_loadglobal chunk id ofs) fp
| eval_BA_addrglobal_fp: forall id ofs,
    eval_builtin_arg_fp (BA_addrglobal id ofs) empfp
| eval_BA_splitlong: forall a1 a2 v1 v2 fp1 fp2,
    eval_expr sp e m nil a1 v1 -> eval_expr_fp nil a1 fp1 ->
    eval_expr sp e m nil a2 v2 -> eval_expr_fp nil a2 fp2 ->
    eval_builtin_arg_fp (BA_splitlong (BA a1) (BA a2)) (FP.union fp1 fp2).


End EVAL_EXPR.


(** One step of execution *)

Inductive step: core -> mem -> footprint -> core -> mem  -> Prop :=

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
    eval_expr sp e m nil a v ->
    eval_expr_fp sp e m nil a fp ->
    step (Core_State f (Sassign id a) k sp e) m
         fp (Core_State f Sskip k sp (PTree.set id v e)) m

| step_store: forall f chunk addr al b k sp e m vl v vaddr m' fp1 fp2 fp3 fp,
    eval_exprlist sp e m nil al vl ->
    eval_exprlist_fp sp e m nil al fp1 ->
    eval_expr sp e m nil b v ->
    eval_expr_fp sp e m nil b fp2 ->
    eval_addressing ge sp addr vl = Some vaddr ->
    Mem.storev chunk m vaddr v = Some m' ->
    storev_fp chunk vaddr = fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    step (Core_State f (Sstore chunk addr al b) k sp e) m
         fp (Core_State f Sskip k sp e) m'

| step_call: forall f optid sig a bl k sp e m vf vargs fd fp1 fp2 fp,
    eval_expr_or_symbol sp e m nil a vf ->
    eval_expr_or_symbol_fp sp e m nil a fp1 ->    
    eval_exprlist sp e m nil bl vargs ->
    eval_exprlist_fp sp e m nil bl fp2 ->
    FP.union fp1 fp2 = fp ->
    Genv.find_funct ge vf = Some fd ->
    funsig fd = sig ->
    step (Core_State f (Scall optid sig a bl) k sp e) m
         fp (Core_Callstate fd vargs (Kcall optid f sp e k)) m

| step_tailcall: forall f sig a bl k sp e m vf vargs fd m' fp1 fp2 fp3 fp,
    eval_expr_or_symbol (Vptr sp Ptrofs.zero) e m nil a vf ->
    eval_expr_or_symbol_fp (Vptr sp Ptrofs.zero) e m nil a fp1 ->    
    eval_exprlist (Vptr sp Ptrofs.zero) e m nil bl vargs ->
    eval_exprlist_fp (Vptr sp Ptrofs.zero) e m nil bl fp2 ->
    Genv.find_funct ge vf = Some fd ->
    funsig fd = sig ->
    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
    free_fp sp 0 f.(fn_stackspace) = fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    step (Core_State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e) m
         fp (Core_Callstate fd vargs (call_cont k)) m'
(*
| step_builtin: forall f res ef al k sp e m vl t v m',
    list_forall2 (eval_builtin_arg sp e m) al vl ->
    external_call ef ge vl m t v m' ->
    step (State f (Sbuiltin res ef al) k sp e m)
         t (State f Sskip k sp (set_builtin_res res v e) m')
 *)
| step_seq: forall f s1 s2 k sp e m,
    step (Core_State f (Sseq s1 s2) k sp e) m
         empfp (Core_State f s1 (Kseq s2 k) sp e) m

| step_ifthenelse: forall f c s1 s2 k sp e m b fp,
    eval_condexpr sp e m nil c b ->
    eval_condexpr_fp sp e m nil c fp ->      
    step (Core_State f (Sifthenelse c s1 s2) k sp e) m
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

| step_switch: forall f a k sp e m n fp,
    eval_exitexpr sp e m nil a n ->
    eval_exitexpr_fp sp e m nil a fp ->    
    step (Core_State f (Sswitch a) k sp e) m
         fp (Core_State f (Sexit n) k sp e) m

| step_return_0: forall f k sp e m m' fp,
    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
    free_fp sp 0 f.(fn_stackspace) = fp ->
    step (Core_State f (Sreturn None) k (Vptr sp Ptrofs.zero) e) m
         fp (Core_Returnstate Vundef (call_cont k)) m'
| step_return_1: forall f a k sp e m v m' fp1 fp2 fp,
    eval_expr (Vptr sp Ptrofs.zero) e m nil a v ->
    eval_expr_fp (Vptr sp Ptrofs.zero) e m nil a fp1 ->
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
(*           
  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')
 *)
  | step_return: forall v optid f sp e k m,
      step (Core_Returnstate v (Kcall optid f sp e k)) m
           empfp (Core_State f Sskip k sp (set_optvar optid v e)) m.

End RELSEM.

Definition cminorsel_comp_unit : Type := @comp_unit_generic fundef unit.

Definition init_genv (cu: cminorsel_comp_unit) (ge G: genv): Prop :=
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
    Core_Callstate (External ef) args k =>
    match ef with
    | (EF_external _ sg)
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
    let tyl := sig_args (funsig cfd) in
    if wd_args args tyl
    then Some (Core_Callstate cfd args Kstop)
    else None
  | External _=> None
  end.

Definition init_core (ge : Genv.t fundef unit) (fnid: ident) (args: list val): option core :=
  generic_init_core fundef_init ge fnid args.

Definition CminorSel_IS :=
  IS_local.Build_sem_local fundef unit genv cminorsel_comp_unit core init_genv init_mem
                           init_core halted step at_external after_external.

Hint Constructors eval_expr_fp eval_exprlist_fp eval_condexpr_fp: evalexprfp.

(** * Lifting of let-bound variables *)

Lemma eval_lift_exprlist:
  forall ge sp e m w le al vl,
    eval_exprlist ge sp e m le al vl ->
    forall p le', insert_lenv le p w le' ->
             eval_exprlist ge sp e m le' (lift_exprlist p al) vl.
Proof.
  intros until w.
  apply (eval_exprlist_ind3 ge sp e m
    (fun le a v =>
      forall p le', insert_lenv le p w le' ->
      eval_expr ge sp e m le' (lift_expr p a) v)
    (fun le al vl =>
      forall p le', insert_lenv le p w le' ->
      eval_exprlist ge sp e m le' (lift_exprlist p al) vl)
    (fun le a b =>
      forall p le', insert_lenv le p w le' ->
      eval_condexpr ge sp e m le' (lift_condexpr p a) b));
  simpl; intros; eauto with evalexpr.

  eapply eval_Econdition; eauto. destruct va; eauto.

  eapply eval_Elet. eauto. apply H2. apply insert_lenv_S; auto.

  case (le_gt_dec p n); intro.
  apply eval_Eletvar. eapply insert_lenv_lookup2; eauto.
  apply eval_Eletvar. eapply insert_lenv_lookup1; eauto.

  eapply eval_CEcondition; eauto. destruct va; eauto.
  eapply eval_CElet; eauto. apply H2. constructor; auto.
Qed.

Lemma eval_lift_condexpr:
  forall ge sp e m w le a b,
    eval_condexpr ge sp e m le a b ->
    forall p le', insert_lenv le p w le' ->
             eval_condexpr ge sp e m le' (lift_condexpr p a) b.
Proof.
  intros until w.
  apply (eval_condexpr_ind3 ge sp e m
    (fun le a v =>
      forall p le', insert_lenv le p w le' ->
      eval_expr ge sp e m le' (lift_expr p a) v)
    (fun le al vl =>
      forall p le', insert_lenv le p w le' ->
      eval_exprlist ge sp e m le' (lift_exprlist p al) vl)
    (fun le a b =>
      forall p le', insert_lenv le p w le' ->
      eval_condexpr ge sp e m le' (lift_condexpr p a) b));
  simpl; intros; eauto with evalexpr.

  eapply eval_Econdition; eauto. destruct va; eauto.

  eapply eval_Elet. eauto. apply H2. apply insert_lenv_S; auto.

  case (le_gt_dec p n); intro.
  apply eval_Eletvar. eapply insert_lenv_lookup2; eauto.
  apply eval_Eletvar. eapply insert_lenv_lookup1; eauto.

  eapply eval_CEcondition; eauto. destruct va; eauto.
  eapply eval_CElet; eauto. apply H2. constructor; auto.
Qed.
  
Lemma eval_lift_expr_fp:
  forall ge sp e m w le a fp,
    eval_expr_fp ge sp e m le a fp ->
    forall p le', insert_lenv le p w le' ->
             eval_expr_fp ge sp e m le' (lift_expr p a) fp.
Proof.
  intros until w.
  apply (eval_expr_fp_ind3 ge sp e m
    (fun le a fp =>
      forall p le', insert_lenv le p w le' ->
      eval_expr_fp ge sp e m le' (lift_expr p a) fp)
    (fun le al fp =>
      forall p le', insert_lenv le p w le' ->
      eval_exprlist_fp ge sp e m le' (lift_exprlist p al) fp)
    (fun le a fp =>
      forall p le', insert_lenv le p w le' ->
      eval_condexpr_fp ge sp e m le' (lift_condexpr p a) fp));
    simpl; intros; eauto with evalexprfp.
  
  econstructor; eauto. eapply eval_lift_exprlist; eauto.
  
  econstructor; eauto. eapply eval_lift_exprlist; eauto.
  
  econstructor; eauto. eapply eval_lift_condexpr; eauto.
  destruct va; eapply eval_lift_expr; eauto.
  destruct va; eauto.
  
  econstructor; eauto. eapply eval_lift_expr; eauto. eapply eval_lift_expr; eauto. apply insert_lenv_S; eauto.
  eapply H4. apply insert_lenv_S; auto.

  case (le_gt_dec p n); intro.
  eapply eval_Eletvar_fp. eapply insert_lenv_lookup2; eauto.
  eapply eval_Eletvar_fp. eapply insert_lenv_lookup1; eauto.

  econstructor; eauto.
  eapply eval_lift_exprlist; eauto.

  econstructor; eauto.
  eapply eval_lift_exprlist; eauto.
  
  econstructor; eauto.
  eapply eval_lift_expr; eauto. eapply eval_lift_exprlist; eauto.

  econstructor; eauto. eapply eval_lift_exprlist; eauto.
  
  eapply eval_CEcondition_fp; eauto. eapply eval_lift_condexpr; eauto.
  destruct va; eapply eval_lift_condexpr; eauto.
  destruct va; eauto.
  
  eapply eval_CElet_fp; eauto. eapply eval_lift_expr; eauto. eapply eval_lift_condexpr; eauto.
  eapply insert_lenv_S; eauto. eapply H4. constructor; auto.
Qed.

Lemma eval_lift_fp:
  forall ge sp e m le a fp w,
    eval_expr_fp ge sp e m le a fp ->
    eval_expr_fp ge sp e m (w::le) (lift a) fp.
Proof.
  intros. unfold lift. eapply eval_lift_expr_fp.
  eexact H. apply insert_lenv_0.
Qed.

Hint Resolve eval_lift_fp: evalexprfp.



Lemma eval_expr_det:
  forall ge sp e m le a v,
    eval_expr ge sp e m le a v ->
    (forall v', eval_expr ge sp e m le a v' -> v = v').
Proof.
  clear. intros until m.
  eapply (eval_expr_ind3
            ge sp e m
            (fun le a v => forall v', eval_expr ge sp e m le a v' -> v = v')
            (fun le a v => forall v', eval_exprlist ge sp e m le a v' -> v = v')
            (fun le a v => forall v', eval_condexpr ge sp e m le a v' -> v = v')); intros.
  { inv H0. congruence. }
  { inv H2. apply H0 in H6. congruence. }
  { inv H3. exploit H0; eauto. congruence. }
  { inv H3. exploit H0; eauto. intro; subst. exploit H2. eauto. auto. }
  { inv H3. apply H0 in H7. subst. apply H2 in H9. auto. }
  { inv H0. congruence. }
  { inv H2. apply H0 in H6. subst. exploit external_call_determ. exact H1. exact H8.
    intros []. tauto. }
  { inv H5. rewrite H in H9; inv H9. rewrite H0 in H10; inv H10. inv H12. apply H3 in H14. subst.
    exploit external_call_determ. exact H4. exact H15. intros []. tauto. }
  { inv H. auto. }
  { inv H3. apply H0 in H7; subst. apply H2 in H9. subst. auto. }
  { inv H2. apply H0 in H6. subst. congruence. }
  { inv H3. apply H0 in H9. subst. apply H2 in H10. auto. }
  { inv H3. apply H0 in H7. subst. apply H2 in H9. auto. }
Qed.

Lemma eval_exprlist_det:
  forall ge sp e m le al vl,
    eval_exprlist ge sp e m le al vl ->
    (forall vl', eval_exprlist ge sp e m le al vl' -> vl = vl').
Proof.
  clear. intros until m.
  eapply (eval_exprlist_ind3
            ge sp e m
            (fun le a v => forall v', eval_expr ge sp e m le a v' -> v = v')
            (fun le a v => forall v', eval_exprlist ge sp e m le a v' -> v = v')
            (fun le a v => forall v', eval_condexpr ge sp e m le a v' -> v = v')); intros.
  { inv H0. congruence. }
  { inv H2. apply H0 in H6. congruence. }
  { inv H3. exploit H0; eauto. congruence. }
  { inv H3. exploit H0; eauto. intro; subst. exploit H2. eauto. auto. }
  { inv H3. apply H0 in H7. subst. apply H2 in H9. auto. }
  { inv H0. congruence. }
  { inv H2. apply H0 in H6. subst. exploit external_call_determ. exact H1. exact H8.
    intros []. tauto. }
  { inv H5. rewrite H in H9; inv H9. rewrite H0 in H10; inv H10. inv H12. apply H3 in H14. subst.
    exploit external_call_determ. exact H4. exact H15. intros []. tauto. }
  { inv H. auto. }
  { inv H3. apply H0 in H7; subst. apply H2 in H9. subst. auto. }
  { inv H2. apply H0 in H6. subst. congruence. }
  { inv H3. apply H0 in H9. subst. apply H2 in H10. auto. }
  { inv H3. apply H0 in H7. subst. apply H2 in H9. auto. }
Qed.

Lemma eval_condexpr_det:
  forall ge sp e m le a b,
    eval_condexpr ge sp e m le a b ->
    (forall b', eval_condexpr ge sp e m le a b' -> b = b').
Proof.
  clear. intros until m.
  eapply (eval_condexpr_ind3
            ge sp e m
            (fun le a v => forall v', eval_expr ge sp e m le a v' -> v = v')
            (fun le a v => forall v', eval_exprlist ge sp e m le a v' -> v = v')
            (fun le a v => forall v', eval_condexpr ge sp e m le a v' -> v = v')); intros.
  { inv H0. congruence. }
  { inv H2. apply H0 in H6. congruence. }
  { inv H3. exploit H0; eauto. congruence. }
  { inv H3. exploit H0; eauto. intro; subst. exploit H2. eauto. auto. }
  { inv H3. apply H0 in H7. subst. apply H2 in H9. auto. }
  { inv H0. congruence. }
  { inv H2. apply H0 in H6. subst. exploit external_call_determ. exact H1. exact H8.
    intros []. tauto. }
  { inv H5. rewrite H in H9; inv H9. rewrite H0 in H10; inv H10. inv H12. apply H3 in H14. subst.
    exploit external_call_determ. exact H4. exact H15. intros []. tauto. }
  { inv H. auto. }
  { inv H3. apply H0 in H7; subst. apply H2 in H9. subst. auto. }
  { inv H2. apply H0 in H6. subst. congruence. }
  { inv H3. apply H0 in H9. subst. apply H2 in H10. auto. }
  { inv H3. apply H0 in H7. subst. apply H2 in H9. auto. }
Qed.

Lemma eval_exitexpr_det:
  forall ge sp e m le a b,
    eval_exitexpr ge sp e m le a b ->
    (forall b', eval_exitexpr ge sp e m le a b' -> b = b').
Proof.
  clear. induction 1; intros.
  inv H; auto.
  inv H1. exploit eval_expr_det. exact H. exact H5. intros. inv H1. congruence.
  inv H1. exploit eval_condexpr_det. exact H. exact H7. intros; subst. eauto.
  inv H1. exploit eval_expr_det. exact H. exact H5. intro; subst. eauto.
Qed.  


Ltac eqexpr :=
  match goal with
  | H: eval_expr ?ge ?sp ?e ?m ?le ?a ?v1, H': eval_expr ?ge ?sp ?e ?m ?le ?a ?v2 |- _ =>
    pose proof (eval_expr_det ge sp e m le a v1 H v2 H') as TMP; inv TMP; clear H'; eqexpr
  | H: eval_exprlist ?ge ?sp ?e ?m ?le ?a ?v1, H': eval_exprlist ?ge ?sp ?e ?m ?le ?a ?v2 |- _ =>
    pose proof (eval_exprlist_det ge sp e m le a v1 H v2 H') as TMP; inv TMP; clear H'; eqexpr
  | H: eval_condexpr ?ge ?sp ?e ?m ?le ?a ?v1, H': eval_condexpr ?ge ?sp ?e ?m ?le ?a ?v2 |- _ =>
    pose proof (eval_condexpr_det ge sp e m le a v1 H v2 H') as TMP; inv TMP; clear H'; eqexpr
  | H: eval_exitexpr ?ge ?sp ?e ?m ?le ?a ?v1, H': eval_exitexpr ?ge ?sp ?e ?m ?le ?a ?v2 |- _ =>
    pose proof (eval_exitexpr_det ge sp e m le a v1 H v2 H') as TMP; inv TMP; clear H'; eqexpr
  | H: ?x = Some ?y, H': ?x = Some ?z |- _ =>
    rewrite H in H'; inv H'; eqexpr
  | _ => subst
  end.

Section EVAL_PRESERVED.
  Variables ge1 ge2: genv.
  Hypothesis SENV: Senv.equiv ge1 ge2.
  Hypothesis FINDSYMB: forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.
  Hypothesis FINDFUNCTPTR: forall b, Genv.find_funct_ptr ge2 b = Genv.find_funct_ptr ge1 b.
  Lemma eval_expr_preserved:
    forall sp e m le a v,
      eval_expr ge1 sp e m le a v -> eval_expr ge2 sp e m le a v.
  Proof.
    intros until v.
    eapply (eval_expr_ind3 ge1 sp e m (fun le a v => eval_expr ge2 sp e m le a v)); intros; try (econstructor; eauto).
    erewrite eval_operation_preserved; eauto. inv SENV; auto.
    erewrite eval_addressing_preserved; eauto. 
    eapply external_call_symbols_preserved; eauto. 
    rewrite FINDSYMB. eauto. rewrite FINDFUNCTPTR. auto.
    eapply external_call_symbols_preserved; eauto.
  Qed.
  Lemma eval_exprlist_preserved:
    forall sp e m le al vl,
      eval_exprlist ge1 sp e m le al vl -> eval_exprlist ge2 sp e m le al vl.
  Proof.
    intros until vl.
    eapply (eval_exprlist_ind3 ge1 sp e m (fun le a v => eval_expr ge2 sp e m le a v)); intros; try (econstructor; eauto).
    erewrite eval_operation_preserved; eauto. inv SENV; auto.
    erewrite eval_addressing_preserved; eauto. 
    eapply external_call_symbols_preserved; eauto. 
    rewrite FINDSYMB. eauto. rewrite FINDFUNCTPTR. auto.
    eapply external_call_symbols_preserved; eauto.
  Qed.
  Lemma eval_condexpr_preserved:
    forall sp e m le a b,
      eval_condexpr ge1 sp e m le a b -> eval_condexpr ge2 sp e m le a b.
  Proof.
    intros until b.
    eapply (eval_condexpr_ind3 ge1 sp e m (fun le a v => eval_expr ge2 sp e m le a v)); intros; try (econstructor; eauto).
    erewrite eval_operation_preserved; eauto. inv SENV; auto.
    erewrite eval_addressing_preserved; eauto. 
    eapply external_call_symbols_preserved; eauto. 
    rewrite FINDSYMB. eauto. rewrite FINDFUNCTPTR. auto.
    eapply external_call_symbols_preserved; eauto.
  Qed.
  Lemma eval_exitexpr_preserved:
    forall sp e m le a n,
      eval_exitexpr ge1 sp e m le a n -> eval_exitexpr ge2 sp e m le a n.
  Proof.
    intros until n. induction 1; econstructor; eauto.
    apply eval_expr_preserved. auto.
    apply eval_condexpr_preserved. auto.
    apply eval_expr_preserved. auto.
  Qed.
End EVAL_PRESERVED.