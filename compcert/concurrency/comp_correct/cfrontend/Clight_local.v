(* An adapted version of CompCert file [cfrontend/Clight.v],
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

Require Import Coqlib Errors Maps String.
Require Import Integers Floats Values AST Events Globalenvs Smallstep Ctypes Cop Clight.
Require Import Memory Footprint IS_local MemOpFP Cop_fp_local. 
Require Import val_casted.

Require ClightLang GAST.

Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.

(** * Some definitions ported from CompCert Clight *)

(** ** Clight Syntax *)
(** The Clight Syntax stays unchanged *)

Local Notation clight_comp_unit := ClightLang.clight_comp_unit.
Local Notation cu_defs := ClightLang.cu_defs.
Local Notation cu_public := ClightLang.cu_public.
Local Notation cu_types := ClightLang.cu_types.
Local Notation cu_comp_env := ClightLang.cu_comp_env.
Local Notation cu_comp_env_eq := ClightLang.cu_comp_env_eq.

Local Notation core := ClightLang.core.
Local Notation Core_State := ClightLang.Core_State.
Local Notation Core_Callstate := ClightLang.Core_Callstate.
Local Notation Core_Returnstate := ClightLang.Core_Returnstate.

(** Auxilliary function to get a core state from original Clight state *)
Local Notation get_core := ClightLang.get_core.

(** The function table built from [clight_comp_unit] *)
Local Notation is_function := ClightLang.is_function.
Local Notation internal_fn := ClightLang.internal_fn.

(** ** Operational Semantics *)
(** Since we use a different memory model, these functions need to be redefined, 
    but syntactically the same.
    - [deref_loc], [assign_loc]
    - [alloc_variables], [bind_parameters]
    - [eval_expr], [eval_lvalue], [eval_exprlist]
    - [function entries]
 *)

(** [deref_loc] *)
Inductive deref_loc_fp ty b ofs : footprint -> Prop :=
| deref_loc_value_fp : forall chunk fp,
    access_mode ty = By_value chunk ->
    loadv_fp chunk (Vptr b ofs) = fp ->
    deref_loc_fp ty b ofs fp
| deref_loc_reference_fp : 
    access_mode ty = By_reference ->
    deref_loc_fp ty b ofs empfp
| deref_loc_copy_fp :
    access_mode ty = By_copy ->
    deref_loc_fp ty b ofs empfp.

Lemma deref_loc_fp_exists:
  forall ty m b ofs v,
    deref_loc ty m b ofs v ->
    exists fp, deref_loc_fp ty b ofs fp.
Proof.
  induction 1; eexists; econstructor; eauto; fail.
Qed.

(** [assign_loc] *)
Inductive assign_loc_fp (ce:composite_env) ty b ofs : val -> footprint -> Prop :=
  | assign_loc_value_fp: forall v chunk fp,
      access_mode ty = By_value chunk ->
      storev_fp chunk (Vptr b ofs) = fp ->
      assign_loc_fp ce ty b ofs v fp.
(*  | assign_loc_copy_fp: forall b' ofs' fp_load fp_store fp,
      access_mode ty = By_copy ->
      loadbytes_fp b' (Ptrofs.unsigned ofs') (sizeof ce ty) = fp_load ->
      storebytes_fp b (Ptrofs.unsigned ofs) (sizeof ce ty) = fp_store ->
      FP.union fp_load fp_store = fp ->
      assign_loc_fp ce ty b ofs (Vptr b' ofs') fp.*)
Lemma assign_loc_fp_exists:
  forall ce ty m b ofs v m',
    assign_loc ce ty m b ofs v m' ->
    exists fp, assign_loc_fp ce ty b ofs v fp.
Proof.
  induction 1.
  eexists. econstructor; eauto; fail.
(*  eexists. econstructor; eauto; fail.*)
Qed.




Section SEMANTICS.

Variable ge: genv.

(** [alloc_variables] *)
Local Notation alloc_variables := (alloc_variables ge).
Local Notation alloc_variables_nil := (alloc_variables_nil ge).
Local Notation alloc_variables_cons := (alloc_variables_cons ge).

Inductive alloc_variables_fp: mem -> list (ident * type) -> footprint -> Prop :=
| alloc_variables_fp_nil: forall m, alloc_variables_fp m nil empfp
| alloc_variables_fp_cons: forall m id ty fp vars m1 b1 fp',
    Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
    alloc_fp m 0 (sizeof ge ty) = fp ->
    alloc_variables_fp m1 vars fp' ->
    alloc_variables_fp m ((id,ty) :: vars) (FP.union fp fp').

Lemma alloc_variables_fp_exists:
  forall e m vars e' m',
    alloc_variables e m vars e' m' ->
    exists fp, alloc_variables_fp m vars fp.
Proof.
  intros until vars.
  generalize e m; clear.
  induction vars; intros.
  eexists. econstructor.
  inversion H. subst.
  eapply IHvars in H7. destruct H7.
  eexists. econstructor; eauto.
Qed.

(** [bind_parameters] *)
Local Notation bind_parameters := (bind_parameters ge).
Local Notation bind_parameters_nil := (bind_parameters_nil ge).
Local Notation bind_parameters_cons := (bind_parameters_cons ge).

Inductive bind_parameters_fp (e: env) :
  list (ident * type) -> list val -> footprint -> Prop :=
| bind_parameters_fp_nil: bind_parameters_fp e nil nil empfp
| bind_parameters_fp_cons:
    forall id ty params v1 vl b fp fp',
      PTree.get id e = Some (b, ty) ->
      assign_loc_fp ge ty b Ptrofs.zero v1 fp ->
      bind_parameters_fp e params vl fp' ->
      bind_parameters_fp e ((id, ty) :: params) (v1 :: vl) (FP.union fp fp').

Lemma bind_parameters_fp_exists:
  forall e m params vl m',
    bind_parameters e m params vl m' ->
    exists fp, bind_parameters_fp e params vl fp.
Proof.
  induction 1.
  - eexists; econstructor.
  - apply assign_loc_fp_exists in H0. destruct H0.
    destruct IHbind_parameters.
    eexists; econstructor; eauto.
Qed.

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

(** reuse Clight [eval_expr], [eval_exprlist] *)
Local Notation eval_expr := (Clight.eval_expr ge e le m).
Local Notation eval_lvalue := (Clight.eval_lvalue ge e le m).

Inductive eval_expr_fp: expr -> footprint -> Prop :=
| eval_Econst_int_fp: forall i ty,
    eval_expr_fp (Econst_int i ty) empfp
| eval_Econst_float_fp: forall f ty,
    eval_expr_fp (Econst_float f ty) empfp
| eval_Econst_single_fp:   forall f ty,
    eval_expr_fp (Econst_single f ty) empfp
| eval_Econst_long_fp:   forall i ty,
    eval_expr_fp (Econst_long i ty) empfp
| eval_Etempvar_fp: forall id ty,
    eval_expr_fp (Etempvar id ty) empfp
| eval_Eaddrof_fp: forall a ty fp,
    eval_lvalue_fp a fp ->
    eval_expr_fp (Eaddrof a ty) fp
| eval_Eunop_fp: forall op a ty v1 fp1 v1' fp2 fp,
    eval_expr a v1 ->
    eval_expr_fp a fp1 ->
    sem_unary_operation op v1 (typeof a) m = Some v1' ->
    sem_unary_operation_fp op v1 (typeof a) m = Some fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp (Eunop op a ty) fp
| eval_Ebinop_fp: forall op a1 a2 ty v1 v2 fp1 fp2 v' fp3 fp,
    eval_expr a1 v1 ->
    eval_expr_fp a1 fp1 ->
    eval_expr a2 v2 ->
    eval_expr_fp a2 fp2 ->
    sem_binary_operation ge.(genv_cenv) op v1 (typeof a1) v2 (typeof a2) m = Some v' ->
    sem_binary_operation_fp ge.(genv_cenv) op v1 (typeof a1) v2 (typeof a2) m = Some fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    eval_expr_fp (Ebinop op a1 a2 ty) fp
| eval_Ecast_fp: forall a ty v1 fp1 v1' fp2 fp,
    eval_expr a v1 ->
    eval_expr_fp a fp1 ->
    sem_cast v1 (typeof a) ty m = Some v1' ->
    sem_cast_fp v1 (typeof a) ty m = Some fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp (Ecast a ty) fp
| eval_Esizeof_fp: forall ty1 ty,
    eval_expr_fp (Esizeof ty1 ty) empfp
| eval_Ealignof_fp: forall ty1 ty,
    eval_expr_fp (Ealignof ty1 ty) empfp
| eval_Elvalue_fp: forall a loc ofs fp1 v fp2 fp,
    eval_lvalue a loc ofs ->
    eval_lvalue_fp a fp1 ->
    deref_loc (typeof a) m loc ofs v ->
    deref_loc_fp (typeof a) loc ofs fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_expr_fp a fp

with eval_lvalue_fp: expr -> footprint -> Prop :=
  | eval_Evar_fp: forall id ty,
      eval_lvalue_fp (Evar id ty) empfp
  | eval_Ederef_fp: forall a v ty fp,
      eval_expr a v ->
      eval_expr_fp a fp ->
      eval_lvalue_fp (Ederef a ty) fp
  | eval_Efield_composite_fp: forall a v i ty fp,
      eval_expr a v ->
      eval_expr_fp a fp ->
      eval_lvalue_fp (Efield a i ty) fp.

Scheme eval_expr_fp_ind2 := Minimality for eval_expr_fp Sort Prop
  with eval_lvalue_fp_ind2 := Minimality for eval_lvalue_fp Sort Prop.
Combined Scheme eval_expr_lvalue_fp_ind from eval_expr_fp_ind2, eval_lvalue_fp_ind2.

Lemma eval_expr_lvalue_fp_exists:
  (forall a v, eval_expr a v -> exists fp, eval_expr_fp a fp)
  /\ (forall a l ofs, eval_lvalue a l ofs -> exists fp, eval_lvalue_fp a fp).
Proof.
  apply eval_expr_lvalue_ind; intros;
    repeat match goal with H: exists _,_|-_ => destruct H end;
    try match goal with
        | [H: deref_loc _ _ _ _ _ |- _] => exploit deref_loc_fp_exists; eauto; intros [? ?]
        end;
    try (eexists; econstructor; eauto; fail).
  exploit sem_unary_operation_sem_unary_operation_fp; eauto. intros [fp A].
  eexists; econstructor; eauto.
  exploit sem_binary_operation_sem_binary_operation_fp; eauto. intros [fp A].
  eexists; econstructor; eauto.
  exploit sem_cast_sem_cast_fp; eauto. intros [fp A].
  eexists; econstructor; eauto.
Qed.

Lemma eval_expr_fp_exists:
  forall a v, eval_expr a v -> exists fp, eval_expr_fp a fp.
Proof proj1 eval_expr_lvalue_fp_exists.

Lemma eval_lvalue_fp_exists:
  forall a l ofs, eval_lvalue a l ofs -> exists fp, eval_lvalue_fp a fp.
Proof proj2 eval_expr_lvalue_fp_exists.

(** [eval_exprlist ge e m al tyl vl] evaluates a list of r-value
  expressions [al], cast their values to the types given in [tyl],
  and produces the list of cast values [vl].  It is used to
  evaluate the arguments of function calls. *)

Local Notation eval_exprlist := (Clight.eval_exprlist ge e le m).
Inductive eval_exprlist_fp : list expr -> typelist -> footprint -> Prop :=
| eval_fp_Enil:
    eval_exprlist_fp nil Tnil empfp
| eval_fp_Econs: forall a bl ty tyl v1 fp1 v2 fp2 fp3 fp,
    eval_expr a v1 ->
    eval_expr_fp a fp1 ->
    sem_cast v1 (typeof a) ty m = Some v2 ->
    sem_cast_fp v1 (typeof a) ty m = Some fp2 ->
    eval_exprlist_fp bl tyl fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp ->
    eval_exprlist_fp (a :: bl) (Tcons ty tyl) fp.
              
Lemma eval_exprlist_fp_exists:
  forall bl tyl vl,
    eval_exprlist bl tyl vl ->
    exists fp, eval_exprlist_fp bl tyl fp.
Proof.
  induction 1.
  eexists. econstructor; eauto.
  destruct IHeval_exprlist. 
  exploit eval_expr_fp_exists; eauto; intros [? ?].
  exploit sem_cast_sem_cast_fp; eauto; intros [? ?].
  eexists; econstructor; eauto.
Qed.

End EXPR.

(** Transition relation w.r.t. FMemory*)
(** We excluded rules for external functions and builtins *)
(** [Fstep] relation is instrumented with footprint *)
Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable function_entry_fp: function -> list val -> mem -> env -> footprint -> Prop.

Local Notation eval_expr := (Clight.eval_expr ge).
Local Notation eval_lvalue := (Clight.eval_lvalue ge).
Local Notation eval_exprlist := (Clight.eval_exprlist ge).

Inductive step: core -> mem -> footprint -> core -> mem -> Prop :=
| step_assign:   forall f a1 a2 k e le m loc ofs v2 v m' fp1 fp2 fp3 fp4 fp,
    eval_lvalue e le m a1 loc ofs ->
    eval_expr e le m a2 v2 ->
    sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
    assign_loc ge (typeof a1) m loc ofs v m' ->
    (* fp *)
    eval_lvalue_fp e le m a1 fp1 ->
    eval_expr_fp e le m a2 fp2 ->
    sem_cast_fp v2 (typeof a2) (typeof a1) m = Some fp3 ->
    assign_loc_fp ge (typeof a1) loc ofs v fp4 ->
    FP.union (FP.union (FP.union fp1 fp2) fp3) fp4 = fp ->
    
    step (Core_State f (Sassign a1 a2) k e le) m fp
         (Core_State f Sskip k e le) m'

| step_set:   forall f id a k e le m v fp,
    eval_expr e le m a v ->
    eval_expr_fp e le m a fp ->
    step (Core_State f (Sset id a) k e le) m fp
         (Core_State f Sskip k e (PTree.set id v le)) m

| step_call:   forall f optid a al k e le m tyargs tyres cconv vf vargs fd fp1 fp2 fp,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr e le m a vf ->
    eval_exprlist e le m al tyargs vargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cconv ->
    (* fp *)
    eval_expr_fp e le m a fp1 ->
    eval_exprlist_fp e le m al tyargs fp2 ->
    FP.union fp1 fp2 = fp ->

    step (Core_State f (Scall optid a al) k e le) m fp
         (Core_Callstate fd vargs (Kcall optid f e le k)) m
(*
  | step_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      Fstep (Core_State f (Sbuiltin optid ef tyargs al) k e le m)
         t (Core_State f Sskip k e (set_opttemp optid vres le) m')
 *)
| step_seq:  forall f s1 s2 k e le m,
    step (Core_State f (Ssequence s1 s2) k e le) m empfp
         (Core_State f s1 (Kseq s2 k) e le) m
| step_skip_seq: forall f s k e le m,
    step (Core_State f Sskip (Kseq s k) e le) m empfp
         (Core_State f s k e le) m
| step_continue_seq: forall f s k e le m,
    step (Core_State f Scontinue (Kseq s k) e le) m empfp
         (Core_State f Scontinue k e le) m
| step_break_seq: forall f s k e le m,
    step (Core_State f Sbreak (Kseq s k) e le) m empfp
         (Core_State f Sbreak k e le) m

| step_ifthenelse:  forall f a s1 s2 k e le m v1 b fp1 fp2 fp,
    eval_expr e le m a v1 ->
    bool_val v1 (typeof a) m = Some b ->
    (* fp *)
    eval_expr_fp e le m a fp1 ->
    bool_val_fp v1 (typeof a) m = Some fp2 ->
    FP.union fp1 fp2 = fp ->
    
    step (Core_State f (Sifthenelse a s1 s2) k e le) m fp
         (Core_State f (if b then s1 else s2) k e le) m

| step_loop: forall f s1 s2 k e le m,
    step (Core_State f (Sloop s1 s2) k e le) m empfp
         (Core_State f s1 (Kloop1 s1 s2 k) e le) m
| step_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
    x = Sskip \/ x = Scontinue ->
    step (Core_State f x (Kloop1 s1 s2 k) e le) m empfp
         (Core_State f s2 (Kloop2 s1 s2 k) e le) m
| step_break_loop1:  forall f s1 s2 k e le m,
    step (Core_State f Sbreak (Kloop1 s1 s2 k) e le) m empfp
         (Core_State f Sskip k e le) m
| step_skip_loop2: forall f s1 s2 k e le m,
    step (Core_State f Sskip (Kloop2 s1 s2 k) e le) m empfp
         (Core_State f (Sloop s1 s2) k e le) m
| step_break_loop2: forall f s1 s2 k e le m,
    step (Core_State f Sbreak (Kloop2 s1 s2 k) e le) m empfp
         (Core_State f Sskip k e le) m

| step_return_0: forall f k e le m m' fp,
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    (* fp *)
    free_list_fp (blocks_of_env ge e) = fp ->
    step (Core_State f (Sreturn None) k e le) m fp
         (Core_Returnstate Vundef (call_cont k)) m'
| step_return_1: forall f a k e le m v v' m' fp1 fp2 fp3 fp,
    eval_expr e le m a v ->
    sem_cast v (typeof a) f.(fn_return) m = Some v' ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    (* fp *)
    eval_expr_fp e le m a fp1 ->
    sem_cast_fp v (typeof a) f.(fn_return) m = Some fp2 ->
    free_list_fp (blocks_of_env ge e) = fp3 ->
    FP.union (FP.union fp1 fp2) fp3 = fp->
    step (Core_State f (Sreturn (Some a)) k e le) m fp
         (Core_Returnstate v' (call_cont k)) m'
| step_skip_call: forall f k e le m m' fp,
    is_call_cont k ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    (* fp *)
    free_list_fp (blocks_of_env ge e) = fp ->
    step (Core_State f Sskip k e le) m fp
         (Core_Returnstate Vundef k) m'

| step_switch: forall f a sl k e le m v fp n,
    eval_expr e le m a v ->
    eval_expr_fp e le m a fp ->
    sem_switch_arg v (typeof a) = Some n ->
    step (Core_State f (Sswitch a sl) k e le) m fp
         (Core_State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le) m
| step_skip_break_switch: forall f x k e le m,
    x = Sskip \/ x = Sbreak ->
    step (Core_State f x (Kswitch k) e le) m empfp
         (Core_State f Sskip k e le) m
| step_continue_switch: forall f k e le m,
    step (Core_State f Scontinue (Kswitch k) e le) m empfp
         (Core_State f Scontinue k e le) m

| step_label: forall f lbl s k e le m,
    step (Core_State f (Slabel lbl s) k e le) m empfp
         (Core_State f s k e le) m

| step_goto: forall f lbl k e le m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
    step (Core_State f (Sgoto lbl) k e le) m empfp
         (Core_State f s' k' e le) m

| step_internal_function: forall f vargs k m e le m1 fp,
    function_entry f vargs m e le m1 ->
    (* fp *)
    function_entry_fp f vargs m e fp ->
    step (Core_Callstate (Internal f) vargs k) m fp
         (Core_State f f.(fn_body) k e le) m1
(*
  | step_external_function: forall ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      Fstep (Core_Callstate (External ef targs tres cconv) vargs k) m
         t (Core_Returnstate vres k m')
 *)
| step_returnstate: forall v optid f e le k m,
    step (Core_Returnstate v (Kcall optid f e le k)) m empfp
         (Core_State f Sskip k e (set_opttemp optid v le)) m.


End SEMANTICS.


(** [function_entry] *)

(** The two semantics for function parameters.  First, parameters as local variables. *)

Inductive function_entry1 (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
| function_entry1_intro: forall m1,
    list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
    alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
    bind_parameters ge e m1 f.(fn_params) vargs m' ->
    le = create_undef_temps f.(fn_temps) ->
    function_entry1 ge f vargs m e le m'.

Inductive function_entry1_fp ge f vargs m e : footprint -> Prop :=
| function_entry1_fp_intro: forall fp1 fp2 fp,
    alloc_variables_fp ge m (f.(fn_params) ++ f.(fn_vars)) fp1 ->
    bind_parameters_fp ge e f.(fn_params) vargs fp2 ->
    FP.union fp1 fp2 = fp ->
    function_entry1_fp ge f vargs m e fp.

Definition step1 (ge: genv) := step ge (function_entry1 ge) (function_entry1_fp ge).

(** Second, parameters as temporaries. *)

Inductive function_entry2 (ge: genv)  (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
| function_entry2_intro:
    list_norepet (var_names f.(fn_vars)) ->
    list_norepet (var_names f.(fn_params)) ->
    list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
    alloc_variables ge empty_env m f.(fn_vars) e m' ->
    bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
    function_entry2 ge f vargs m e le m'.

Inductive function_entry2_fp ge f (vargs:list val) m (e: env) : footprint -> Prop :=
| function_entry2_fp_intro: forall fp,
    alloc_variables_fp ge m f.(fn_vars) fp ->
    function_entry2_fp ge f vargs m e fp.

Definition step2 (ge: genv) := step ge (function_entry2 ge) (function_entry2_fp ge).



(** * Building Interactionsemantics from Clight *)
(** The initial global environment. *)
Definition init_genv(cu:clight_comp_unit) (ge:Genv.t fundef type)(G: genv): Prop:=
G = Build_genv ge (cu_comp_env cu)  /\ CUAST.globalenv_generic (CUAST.Build_comp_unit_generic _ _ cu.(cu_defs) cu.(cu_public)) ge.
(** The initial memory w.r.t. initial ge *)
Definition init_mem: Genv.t fundef type -> mem -> Prop:=CUAST.init_mem_generic.
(** The [init_core] interface *)

Definition init_core (ge : Genv.t fundef type) (fnid: ident) (args: list val): option core :=
  match Genv.find_symbol ge fnid with
  | Some b =>
    match Genv.find_funct_ptr ge b with
    | Some cfd =>
      match cfd with
      | Internal fd =>
        match type_of_fundef cfd with
        | Tfunction targs tres cc =>
          if val_casted_list_func args targs
                                  && tys_nonvoid targs
                                  && vals_defined args
                                  && zlt (4*(2*(Zlength args))) Int.max_unsigned
          then Some (Core_Callstate cfd args Kstop)
          else None
        | _ => None
        end
      | External _ _ _ _ => None
      end
    | _ => None
    end
  | None => None
  end.

(** * A helper function to get the ident from a EF_function name *)
(** should be moved to another file *)
Definition invert_symbol_from_string :=ClightLang.invert_symbol_from_string.

Definition trans_c_fundef_ast (f:Clight.fundef): (AST.fundef Clight.function):=
  match f with
    Ctypes.Internal x => AST.Internal x
  | Ctypes.External x _ _ _ => AST.External x
  end.

Definition trans_fun_name (gd:globdef Clight.fundef Ctypes.type):=
  match gd with
  | Gfun x => Gfun (trans_c_fundef_ast x)
  | Gvar x => Gvar x
  end.

Lemma gd_ef_fun_name_eq:
  forall gd ,
    ClightLang.gd_ef_fun_name gd = CUAST.gd_ef_fun_name (trans_fun_name gd).
Proof.
  destruct gd;auto;destruct f;auto.
Qed.


Definition trans_genv_defs (defs:PTree.t (globdef Clight.fundef Ctypes.type)):PTree.t (globdef (AST.fundef Clight.function) type):=
  PTree.map (fun i=>trans_fun_name) defs.

Lemma genv_trans_defs_range:
  forall ge b g,
    (trans_genv_defs (Genv.genv_defs ge)) ! b = Some g->
    Plt b (Genv.genv_next ge).
Proof.
  unfold trans_genv_defs.
  intros.
  rewrite PTree.gmap in H.
  unfold option_map in H.
  destruct (Genv.genv_defs ge)!b eqn:?;inv H.
  destruct ge.
  simpl in *. 
  eapply genv_defs_range;eauto.
Qed.

Definition trans_ge ge:=
  let GENV:= genv_genv ge in
  {|Genv.genv_public:=GENV.(Genv.genv_public);
    Genv.genv_symb:=GENV.(Genv.genv_symb);
    Genv.genv_defs:=trans_genv_defs GENV.(Genv.genv_defs);
    Genv.genv_next:=GENV.(Genv.genv_next);
    Genv.genv_symb_range:= GENV.(Genv.genv_symb_range);
    Genv.genv_defs_range:= genv_trans_defs_range GENV;
    Genv.genv_vars_inj:= GENV.(Genv.genv_vars_inj);|}.

Lemma fold_elements {A B C:Type}{dec:forall x y:A,{x=y}+{x<>y}}:
  forall (f1: B -> option A)(f2:C->option A) g t t' n default
    (MATCH:forall id,option_rel (fun a b=> g a = b) t!id t'!id)
    (REL: forall a b, g a = b -> f1 a = f2 b),
    PTree.fold (fun a b c=> match f1 c with
                       | Some x => if dec n x then Some b else a
                       | None => a
                          end) t default =
    PTree.fold (fun a b c=> match f2 c with
                       | Some x => if dec n x then Some b else a
                       | None => a
                       end) t' default.
Proof.
  intros.
  do 2 rewrite PTree.fold_spec.
  apply Maps.PTree.elements_canonical_order' in MATCH.
  revert MATCH.
  generalize (Maps.PTree.elements t) (Maps.PTree.elements t') default.
  clear t t'.
  induction l; intro l'; intros.
  inv MATCH. auto.
  inv MATCH. destruct a as [id1 gd1]; destruct b1 as [id2 gd2].
  destruct H1. simpl in H, H0. subst id2. simpl. apply REL in H0. rewrite H0.
  apply IHl. auto.
Qed.
Lemma invert_symbol_trans_preserved:
  forall ge name,
    let ge_trans := trans_ge ge in 
    invert_symbol_from_string ge name = CUAST.invert_symbol_from_string ge_trans name.
Proof.
  intros.
  enough(ClightLang.invert_block_from_string ge name = CUAST.invert_block_from_string ge_trans name).
  unfold ge_trans.
  unfold invert_symbol_from_string,CUAST.invert_symbol_from_string,ClightLang.invert_symbol_from_string.
  unfold Genv.invert_symbol. simpl.
  rewrite H;auto.

  unfold ClightLang.invert_block_from_string,CUAST.invert_block_from_string.
  unfold ge_trans.
  simpl.
  eapply fold_elements;eauto.
  instantiate(1:=trans_fun_name).
  intros.
  unfold ge_trans; simpl.
  unfold trans_genv_defs. rewrite PTree.gmap.
  unfold option_map.
  destruct (Genv.genv_defs ge)!id;constructor;auto.
  
  pose proof gd_ef_fun_name_eq.
  intros. rewrite <- H0;eauto.
Qed.

Definition at_external (ge: genv) (c: core) : option (ident * signature * list val) :=
  match c with
  | Core_Callstate fd args k =>
    match fd with
    | External (EF_external name sig) targs tres cc => 
      if vals_defined args
      then
        match invert_symbol_from_string ge name with
        | Some fnid =>
          if peq fnid GAST.ent_atom || peq fnid GAST.ext_atom
          then None
          else Some (fnid, sig, args)
        | None => None
        end
      else None
    | _ => None
    end
  | _ => None
  end.

Definition after_external (c: core) (rv: option val) : option core :=
  match c with
    Core_Callstate fd vargs k =>
    match fd with
    | External (EF_external name sig) tps tp cc =>
      match rv, sig_res sig with
        Some v, Some ty =>
        if val_has_type_func v ty then  Some(Core_Returnstate v k)
        else None
      | None, None  => Some(Core_Returnstate Vundef k)
      | _,_ => None
      end
    | _ => None
    end
  | _ => None
  end.


Definition halted (q : core): option val :=
  match q with 
    Core_Returnstate v Kstop => 
    if vals_defined (v::nil) then Some v
    else None
  | _ => None
  end.

Definition Clight_IS_local: sem_local
  := (Build_sem_local
        fundef type genv clight_comp_unit core
        init_genv init_mem init_core halted step1 at_external after_external).

Definition Clight_IS_2_local: sem_local
  := (Build_sem_local
        fundef type genv clight_comp_unit core
        init_genv init_mem init_core halted step2 at_external after_external).