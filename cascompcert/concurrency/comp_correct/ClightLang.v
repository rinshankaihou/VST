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

Require Import CUAST Footprint GMemory MemAux FMemory InteractionSemantics.

Require Import FMemOpFP FCop Cop_fp val_casted.

Require GAST.

Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.


Record clight_comp_unit :=
  { cu_defs: list (ident * globdef fundef type);
    cu_public: list ident;
    cu_types: list composite_definition;
    cu_comp_env: composite_env;
    cu_comp_env_eq: build_composite_env cu_types = Errors.OK cu_comp_env }.

Inductive core : Type :=
| Core_State: function -> statement -> cont -> env -> temp_env -> core
| Core_Callstate: fundef -> list val -> cont -> core
| Core_Returnstate: val -> cont -> core.


(** Auxilliary function to get a core state from original Clight state *)
Definition get_core (s: state) : core :=
  match s with
  | State fn stmt k le te _ => Core_State fn stmt k le te
  | Callstate fdef vl k _ => Core_Callstate fdef vl k
  | Returnstate v k _ => Core_Returnstate v k
  end.


(** The function table built from [clight_comp_unit] *)
Fixpoint is_internal (cu_defs: list (ident * globdef Clight.fundef Ctypes.type)) (id: ident) : bool :=
  match cu_defs with
  | (id', gdef) :: cu_defs' =>
    if (ident_eq id id') then
      match gdef with
      | Gfun (Internal _) => true
      | _ => is_internal cu_defs' id
      end
    else is_internal cu_defs' id
  | nil => false
  end.

Fixpoint is_function {F V: Type} (cu_defs: list (ident * globdef F V)) (id: ident) : bool :=
  match cu_defs with
  | (id', gdef) :: cu_defs' =>
    if (ident_eq id id') then
      match gdef with
      | Gfun _ => true
      | _ => is_function cu_defs' id
      end
    else is_function cu_defs' id
  | nil => false
  end.

Definition internal_fn (cu: clight_comp_unit): list ident :=
  filter (is_internal (cu_defs cu)) (cu_public cu).


(** * Some definitions ported from CompCert Clight *)

(** ** Clight Syntax *)
(** The Clight Syntax stays unchanged *)

(** ** Operational Semantics *)
(** Since we use a different memory model, these functions need to be redefined, 
    but syntactically the same.
    - [deref_loc], [assign_loc]
    - [alloc_variables], [bind_parameters]
    - [eval_expr], [eval_lvalue], [eval_exprlist]
    - [function entries]
 *)

(** [deref_loc] *)
Inductive deref_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs)
  : val -> Prop :=
| deref_loc_value : forall chunk v,
    access_mode ty = By_value chunk ->
    Mem.loadv chunk m (Vptr b ofs) = Some v ->
    deref_loc ty m b ofs v
| deref_loc_reference :
    access_mode ty = By_reference ->
    deref_loc ty m b ofs (Vptr b ofs)
| deref_loc_copy :
    access_mode ty = By_copy ->
    deref_loc ty m b ofs (Vptr b ofs).

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
Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                                            val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs v m'.
(*  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs (Vptr b' ofs') m'.*)

Inductive assign_loc_fp (ce: composite_env) ty b ofs : val -> footprint -> Prop :=
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
Qed.

Section SEMANTICS.

Variable ge: genv.
(** [alloc_variables] *)
Inductive alloc_variables: env -> mem ->
                           list (ident * type) ->
                           env -> mem -> Prop :=
| alloc_variables_nil:
    forall e m,
      alloc_variables e m nil e m
| alloc_variables_cons:
    forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

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
Inductive bind_parameters (e: env):
  mem -> list (ident * type) -> list val ->
  mem -> Prop :=
| bind_parameters_nil:
    forall m,
      bind_parameters e m nil nil m
| bind_parameters_cons:
    forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ge ty m b Ptrofs.zero v1 m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

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

(** [eval_expr], [eval_exprlist] *)
Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Vsingle f)
  | eval_Econst_long:   forall i ty,
      eval_expr (Econst_long i ty) (Vlong i)
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs ->
      eval_expr (Eaddrof a ty) (Vptr loc ofs)
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) m = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Esizeof: forall ty1 ty,
      eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | eval_Ealignof: forall ty1 ty,
      eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | eval_Elvalue: forall a loc ofs v,
      eval_lvalue a loc ofs ->
      deref_loc (typeof a) m loc ofs v ->
      eval_expr a v

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

with eval_lvalue: expr -> block -> ptrofs -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Ptrofs.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Evar id ty) l Ptrofs.zero
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs
 | eval_Efield_struct:   forall a i ty l ofs id co att delta,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tstruct id att ->
      ge.(genv_cenv)!id = Some co ->
      field_offset ge i (co_members co) = OK delta ->
      eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta))
 | eval_Efield_union:   forall a i ty l ofs id co att,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tunion id att ->
      ge.(genv_cenv)!id = Some co ->
      eval_lvalue (Efield a i ty) l ofs.

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

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.

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

Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil Tnil nil
  | eval_Econs:   forall a bl ty tyl v1 v2 vl,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v2 ->
      eval_exprlist bl tyl vl ->
      eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

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

Inductive Fstep: core -> mem -> footprint -> core -> mem -> Prop :=
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
      
      Fstep (Core_State f (Sassign a1 a2) k e le) m fp
            (Core_State f Sskip k e le) m'

  | step_set:   forall f id a k e le m v fp,
      eval_expr e le m a v ->

      eval_expr_fp e le m a fp ->
      
      Fstep (Core_State f (Sset id a) k e le) m fp
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

      Fstep (Core_State f (Scall optid a al) k e le) m fp
            (Core_Callstate fd vargs (Kcall optid f e le k)) m
(*
  | step_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      Fstep (Core_State f (Sbuiltin optid ef tyargs al) k e le m)
         t (Core_State f Sskip k e (set_opttemp optid vres le) m')
*)
  | step_seq:  forall f s1 s2 k e le m,
      Fstep (Core_State f (Ssequence s1 s2) k e le) m empfp
            (Core_State f s1 (Kseq s2 k) e le) m
  | step_skip_seq: forall f s k e le m,
      Fstep (Core_State f Sskip (Kseq s k) e le) m empfp
            (Core_State f s k e le) m
  | step_continue_seq: forall f s k e le m,
      Fstep (Core_State f Scontinue (Kseq s k) e le) m empfp
            (Core_State f Scontinue k e le) m
  | step_break_seq: forall f s k e le m,
      Fstep (Core_State f Sbreak (Kseq s k) e le) m empfp
            (Core_State f Sbreak k e le) m

  | step_ifthenelse:  forall f a s1 s2 k e le m v1 b fp1 fp2 fp,
      eval_expr e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      (* fp *)
      eval_expr_fp e le m a fp1 ->
      bool_val_fp v1 (typeof a) m = Some fp2 ->
      FP.union fp1 fp2 = fp ->
      
      Fstep (Core_State f (Sifthenelse a s1 s2) k e le) m fp
            (Core_State f (if b then s1 else s2) k e le) m

  | step_loop: forall f s1 s2 k e le m,
      Fstep (Core_State f (Sloop s1 s2) k e le) m empfp
            (Core_State f s1 (Kloop1 s1 s2 k) e le) m
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      Fstep (Core_State f x (Kloop1 s1 s2 k) e le) m empfp
            (Core_State f s2 (Kloop2 s1 s2 k) e le) m
  | step_break_loop1:  forall f s1 s2 k e le m,
      Fstep (Core_State f Sbreak (Kloop1 s1 s2 k) e le) m empfp
            (Core_State f Sskip k e le) m
  | step_skip_loop2: forall f s1 s2 k e le m,
      Fstep (Core_State f Sskip (Kloop2 s1 s2 k) e le) m empfp
            (Core_State f (Sloop s1 s2) k e le) m
  | step_break_loop2: forall f s1 s2 k e le m,
      Fstep (Core_State f Sbreak (Kloop2 s1 s2 k) e le) m empfp
            (Core_State f Sskip k e le) m

  | step_return_0: forall f k e le m m' fp,
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      (* fp *)
      free_list_fp (blocks_of_env ge e) = fp ->
      Fstep (Core_State f (Sreturn None) k e le) m fp
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
      Fstep (Core_State f (Sreturn (Some a)) k e le) m fp
            (Core_Returnstate v' (call_cont k)) m'
  | step_skip_call: forall f k e le m m' fp,
      is_call_cont k ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      (* fp *)
      free_list_fp (blocks_of_env ge e) = fp ->
      Fstep (Core_State f Sskip k e le) m fp
            (Core_Returnstate Vundef k) m'

  | step_switch: forall f a sl k e le m v fp n,
      eval_expr e le m a v ->
      eval_expr_fp e le m a fp ->
      sem_switch_arg v (typeof a) = Some n ->
      Fstep (Core_State f (Sswitch a sl) k e le) m fp
            (Core_State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le) m
  | step_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      Fstep (Core_State f x (Kswitch k) e le) m empfp
            (Core_State f Sskip k e le) m
  | step_continue_switch: forall f k e le m,
      Fstep (Core_State f Scontinue (Kswitch k) e le) m empfp
            (Core_State f Scontinue k e le) m

  | step_label: forall f lbl s k e le m,
      Fstep (Core_State f (Slabel lbl s) k e le) m empfp
            (Core_State f s k e le) m

  | step_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      Fstep (Core_State f (Sgoto lbl) k e le) m empfp
            (Core_State f s' k' e le) m

  | step_internal_function: forall f vargs k m e le m1 fp,
      function_entry f vargs m e le m1 ->
      (* fp *)
      function_entry_fp f vargs m e fp ->
      Fstep (Core_Callstate (Internal f) vargs k) m fp
            (Core_State f f.(fn_body) k e le) m1
(*
  | step_external_function: forall ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      Fstep (Core_Callstate (External ef targs tres cconv) vargs k) m
         t (Core_Returnstate vres k m')
*)
  | step_returnstate: forall v optid f e le k m,
      Fstep (Core_Returnstate v (Kcall optid f e le k)) m empfp
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

Definition Fstep1 (ge: genv) := Fstep ge (function_entry1 ge) (function_entry1_fp ge).

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

Definition Fstep2 (ge: genv) := Fstep ge (function_entry2 ge) (function_entry2_fp ge).





(** * Building Interactionsemantics from Clight *)
(** The initial global environment. *)
Definition init_genv (cu: clight_comp_unit) (ge:Genv.t fundef type) (G: genv): Prop :=
  G = Build_genv ge (cu_comp_env cu)  /\ ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).
(** The initial memory w.r.t. initial ge *)
Definition init_gmem :Genv.t fundef type ->gmem->Prop := init_gmem_generic.
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
Definition gd_ef_fun_name (gd: globdef fundef type) : option string :=
  match gd with
  | Gfun fd =>
    match fd with
    | External ef _ _ _ =>
      match ef with
      | EF_external name _ => Some name
      | _ => None
      end
    | _ => None
    end
  | Gvar _ => None
  end.

Definition invert_block_from_string (ge: Genv.t fundef type) (name: string) : option block :=
  PTree.fold
    (fun res b gd =>
       match gd_ef_fun_name gd with
       | Some name' => if string_dec name name' then Some b else res
       | None => res
       end)
    ge.(Genv.genv_defs) None.

Definition invert_symbol_from_string (ge: Genv.t fundef type) (name: string) : option ident :=
  match invert_block_from_string ge name with
  | Some b => Genv.invert_symbol ge b
  | None => None
  end.

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


(** * Core step relation *)

(** To build core step on GMemory from Fstep on FMemory, we define these two relations to 
    embed / strip freelists *)

Inductive step1 (ge: genv) (fl: freelist): core -> gmem -> FP.t -> core -> gmem -> Prop :=
  Step1_intro: forall c gm m fp c' gm' m',
    embed gm fl m ->
    Fstep1 ge c m fp c' m' ->
    strip m' = gm' ->
    step1 ge fl c gm fp c' gm'.

Inductive step2 (ge: genv) (fl: freelist): core -> gmem -> FP.t -> core -> gmem -> Prop :=
  Step2_intro: forall c gm m fp c' gm' m',
    embed gm fl m ->
    Fstep2 ge c m fp c' m' ->
    strip m' = gm' ->
    step2 ge fl c gm fp c' gm'.

Definition Clight_IS: Language
  := Build_Language fundef type genv clight_comp_unit core 
                    init_core step1 at_external after_external halted 
                    internal_fn init_genv init_gmem.

Definition Clight_IS_2: Language
  := Build_Language fundef type genv clight_comp_unit core 
                    init_core step2 at_external after_external halted 
                    internal_fn init_genv init_gmem .



Definition norep_ef_name ge :=
  forall b b' gd gd' name name',
    b <> b'->
    Genv.find_def ge b = Some gd ->
    Genv.find_def ge b' = Some gd' ->
    gd_ef_fun_name gd = Some name ->
    gd_ef_fun_name gd' = Some name' ->
    name <> name'.

Lemma invert_block_from_string_eq:
  forall (ge ge_local: Genv.t fundef type)
    (NOREPEF: norep_ef_name ge_local),
    (forall b gd, (Genv.genv_defs ge_local) ! b = Some gd -> exists id, (Genv.genv_symb ge_local) ! id = Some b) ->
    ge_related ge ge_local ->
    forall name, option_rel (fun b b' => exists id, Genv.find_symbol ge id = Some b /\ Genv.find_symbol ge_local id = Some b')
                       (invert_block_from_string ge name)
                       (invert_block_from_string ge_local name).
Proof.
  intros. unfold invert_block_from_string.
  remember (fun p : positive * globdef fundef type =>
              match gd_ef_fun_name (snd p) with
              | Some name' => if String.string_dec name name' then Some (fst p) else None
              | None => None
              end) as FILTER.
  assert ((fun ob a => if FILTER a then FILTER a else ob) =
          (fun a p => match gd_ef_fun_name (snd p) with
                   | Some name' => if String.string_dec name name' then Some (fst p) else a
                   | None => a
                   end)).
  { subst. do 2 (apply Axioms.functional_extensionality; intro).
    destruct x0. destruct g; simpl; auto. destruct f; auto.
    destruct e; auto. destruct String.string_dec; auto. }
  repeat rewrite PTree.fold_spec. rewrite <- H1 in *. clear H1. rename HeqFILTER into HFUNC.
  destruct (fold_left) eqn:FOLD.
  apply fold_in in FOLD. destruct FOLD as [[[b [f|v]] [IN NAME]]|C]; try discriminate. 
  2: subst; simpl in *; discriminate.
  rewrite HFUNC in NAME. simpl in NAME.
  destruct f; try discriminate. destruct e; try discriminate. destruct String.string_dec; try discriminate.
  inversion NAME. subst name0 p. clear NAME.
  apply PTree.elements_complete in IN.
  destruct H0. exploit H5. eauto. intros [b' INJ]. exploit H0. eauto. intros [gd' DEF].
  exploit H6. eauto. rewrite DEF, IN. intro A. inversion A. subst gd'. clear A.
  destruct fold_left eqn:FOLD'.
  apply fold_in in FOLD'. destruct FOLD' as [[[b'' [f'|v']] [IN' NAME']]|C]; try discriminate. 
  2: subst; simpl in *; discriminate.
  rewrite HFUNC in NAME'. simpl in NAME'.
  destruct f'; try discriminate. destruct e; try discriminate. destruct String.string_dec; try discriminate.
  inversion NAME'. subst name0 p. clear NAME'.
  assert (b'' = b').
  { apply PTree.elements_complete in IN'. revert DEF IN' NOREPEF; clear; intros.
    destruct (peq b' b''); auto.
    exploit NOREPEF; eauto; simpl; eauto. contradiction.
  }
  subst b''. exploit H. eauto. intros[id FIND].
  specialize (H3 id). unfold Genv.find_symbol in *. rewrite FIND in H3. inversion H3.
  rewrite INJ in H11. inversion H11. subst bj b0 b'0. clear H11.
  constructor. exists id. auto.
  
  exfalso. apply PTree.elements_correct in DEF.
  eapply fold_in' in DEF. rewrite FOLD' in DEF. destruct DEF. discriminate.
  subst. simpl. destruct String.string_dec; try contradiction; eauto.

  destruct (fold_left _ (PTree.elements (Genv.genv_defs ge_local)) None) eqn:FOLD';[|constructor].
  exfalso.
  apply fold_in in FOLD'. destruct FOLD' as [[[b'' [f'|v']] [IN' NAME']]|C]; try discriminate. 
  2: subst; simpl in *; discriminate.
  rewrite HFUNC in NAME'. simpl in NAME'.
  destruct f'; try discriminate. destruct e; try discriminate. destruct String.string_dec; try discriminate.
  inversion NAME'. subst name0 p. clear NAME'.
  apply PTree.elements_complete in IN'.
  destruct H0. exploit H4. eauto. intros [b INJ]. exploit H6. eauto.
  rewrite IN'. intro A. symmetry in A. eapply PTree.elements_correct in A. eapply fold_in' in A.
  rewrite FOLD in A. destruct A; discriminate.
  subst; simpl. destruct String.string_dec; try contradiction; eauto.
Qed.
