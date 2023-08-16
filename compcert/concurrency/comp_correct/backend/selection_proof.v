(* Extended the original CompCert's correctness proof for supporting concurrency. *)

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

(** Correctness of instruction selection *)

Require Import Coqlib Maps.
Require Import AST Linking Errors Integers Values Memory Events Globalenvs Smallstep.
Require Import Switch Cminor Op CminorSel.
Require Import SelectOp SelectDiv SplitLong SelectLong Selection.
Require Import SelectOpproof SelectDivproof SplitLongproof SelectLongproof.


Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        MemOpFP Op_fp Cminor_op_footprint Cminor_local CminorSel_local
        selectop_proof selectdiv_proof splitlong_proof selectlong_proof
        selection.

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.

(** * Relational specification of instruction selection *)
Definition match_fundef (scu: cminor_comp_unit) (f: Cminor.fundef) (tf: CminorSel.fundef) : Prop :=
  exists hf, helper_functions_declared scu hf /\ sel_fundef (comp_unit_defmap scu) hf f = OK tf.

Definition match_cu (scu: cminor_comp_unit) (tcu: cminorsel_comp_unit) :=
  match_comp_unit_gen (match_fundef scu) eq scu tcu.

Lemma record_globdefs_sound:
  forall dm id gd, (record_globdefs dm)!id = Some gd -> dm!id = Some gd.
Proof.
  intros. 
  set (f := fun m id gd => if globdef_of_interest gd then PTree.set id gd m else m) in *.
  set (P := fun m m' => m'!id = Some gd -> m!id = Some gd).
  assert (X: P dm (PTree.fold f dm (PTree.empty _))).
  { apply PTree_Properties.fold_rec.
  - unfold P; intros. rewrite <- H0; auto.
  - red. rewrite ! PTree.gempty. auto.
  - unfold P; intros. rewrite PTree.gsspec. unfold f in H3. 
    destruct (globdef_of_interest v).
    + rewrite PTree.gsspec in H3. destruct (peq id k); auto.
    + apply H2 in H3. destruct (peq id k). congruence. auto. }
  apply X. auto.
Qed.

Lemma lookup_helper_correct_1:
  forall globs name sg id,
  lookup_helper globs name sg = OK id ->
  globs!id = Some (Gfun (External (EF_runtime name sg))).
Proof.
  intros.
  set (P := fun (m: PTree.t globdef) res => res = Some id -> m!id = Some(Gfun(External (EF_runtime name sg)))).
  assert (P globs (PTree.fold (lookup_helper_aux name sg) globs None)).
  { apply PTree_Properties.fold_rec; red; intros.
  - rewrite <- H0. apply H1; auto.
  - discriminate.
  - assert (EITHER: k = id /\ v = Gfun (External (EF_runtime name sg))
                \/  a = Some id).
    { unfold lookup_helper_aux in H3. destruct v; auto. destruct f; auto. destruct e; auto.
      destruct (String.string_dec name name0); auto.
      destruct (signature_eq sg sg0); auto.
      inversion H3. left; split; auto. repeat f_equal; auto. }
    destruct EITHER as [[X Y] | X].
    subst k v. apply PTree.gss.
    apply H2 in X. rewrite PTree.gso by congruence. auto.
  }
  red in H0. unfold lookup_helper in H.
  destruct (PTree.fold (lookup_helper_aux name sg) globs None); inv H. auto.
Qed.

Lemma lookup_helper_correct:
  forall cu name sg id,
  lookup_helper (record_globdefs (comp_unit_defmap cu)) name sg = OK id ->
  helper_declared cu id name sg.
Proof.
  intros. apply lookup_helper_correct_1 in H. apply record_globdefs_sound in H. auto.
Qed.


Lemma get_helpers_correct:
  forall cu hf,
  get_helpers (comp_unit_defmap cu) = OK hf -> helper_functions_declared cu hf.
Proof.
  intros. monadInv H. red; simpl. auto 20 using lookup_helper_correct.
Qed.

Theorem transf_program_match:
  forall scu tcu, transf_program scu = OK tcu -> match_cu scu tcu.
Proof.
  intros. intros. monadInv H.
  eapply match_transform_partial_cunit2; eauto; simpl; intros.
  exists x; split; auto. apply get_helpers_correct; auto.
  monadInv H; auto.
Qed.

(** * Correctness of the instruction selection functions for expressions *)

Section PRESERVATION.

Variable scu: cminor_comp_unit.
Variable tcu: cminorsel_comp_unit.
Variable sge: Cminor.genv.
Variable tge: CminorSel.genv.
Hypothesis SGEINIT: globalenv_generic scu sge.
Hypothesis TGEINIT: globalenv_generic tcu tge.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).

Hypothesis TRANSF: match_cu scu tcu.

Lemma ge_match: ge_match_strict sge tge.
Proof. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma genv_match: Genv.match_genvs (match_globdef (fun f tf => match_fundef scu f tf) eq) sge tge.
Proof. eapply match_cu_match_genv; eauto. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof. destruct genv_match. auto. Qed.

Lemma senv_preserved:
  Senv.equiv sge tge.
Proof. eapply match_cu_senv_preserved; eauto. Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr sge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ match_fundef scu f tf.
Proof.
  destruct genv_match.
  unfold Cminor.fundef, fundef in *. simpl in *.
  unfold Genv.find_funct_ptr, Genv.find_def; intros.
  specialize (mge_defs b). inv mge_defs.
  rewrite <- H1 in H. discriminate.
  rewrite <- H0 in H. destruct x; inv H.
  inv H2. eauto.
Qed.

Lemma functions_translated:
  forall v v' f,
    Genv.find_funct sge v = Some f ->
    Val.lessdef v v' ->
    exists tf, Genv.find_funct tge v' = Some tf /\ match_fundef scu f tf.
Proof.
  destruct v; simpl; intros; try discriminate. inv H0. simpl.
  destruct Ptrofs.eq_dec; [|discriminate]. 
  apply function_ptr_translated; auto.
Qed.

Lemma sig_function_translated:
  forall f tf, match_fundef scu f tf -> funsig tf = Cminor.funsig f.
Proof.
  intros. destruct H as (hf & P & Q). destruct f; monadInv Q; auto. monadInv EQ; auto.
Qed.

Lemma stackspace_function_translated:
  forall dm hf f tf, sel_function dm hf f = OK tf -> fn_stackspace tf = Cminor.fn_stackspace f.
Proof. intros. monadInv H. auto. Qed.

Lemma helper_functions_preserved:
  forall hf, helper_functions_declared scu hf -> helper_functions_declared tcu hf.
Proof.
  assert (X: forall id name sg, helper_declared scu id name sg -> helper_declared tcu id name sg).
  { unfold helper_declared; intros. 
    generalize (match_comp_unit_defmap _ _ _ _ TRANSF id).
    unfold Cminor.fundef; rewrite H; intros R; inv R. inv H2.
    destruct H3 as (hf & A & B). monadInv B. auto. }
  unfold helper_functions_declared; intros. decompose [Logic.and] H; clear H. auto 20. 
Qed.

Section CMCONSTR.
Variable hf: helper_functions.
Hypothesis HF: helper_functions_declared scu hf.
Let HF': helper_functions_declared tcu hf.
Proof. apply helper_functions_preserved. auto. Qed.

Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_condexpr_of_expr_fp:
  forall a le v fp b,
    eval_expr tge sp e m le a v ->
    eval_expr_fp tge sp e m le a fp ->
    Val.bool_of_val v b ->
    eval_condexpr tge sp e m le (condexpr_of_expr a) b /\
    eval_condexpr_fp tge sp e m le (condexpr_of_expr a) fp.
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
(* compare *)
  inv H. inv H0. eqexpr. simpl in H7, H9. destruct (eval_condition) eqn:EC;[inv H7|discriminate]. 
  assert (b0 = b) by (destruct b0; inv H1; auto). subst.
  split; econstructor; eauto. 
(* condition *)
  inv H. inv H0. eqexpr.
  destruct va0; [exploit IHc|exploit IHc0]; eauto; intros [EC ECFP];
    split; econstructor; eauto.
(* let *)
  inv H. inv H0. eqexpr. exploit IHc; eauto. intros [EC ECFP]. split; econstructor; eauto.
(* default *)
  inv H1. split; repeat econstructor; simpl; eauto. simpl. eauto. simpl. eauto. TrivFP.
Qed.

Lemma eval_load_fp:
  forall le a v fp chunk v',
  eval_expr tge sp e m le a v ->
  eval_expr_fp tge sp e m le a fp ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v' /\
  eval_expr_fp tge sp e m le (load chunk a) (FP.union (loadv_fp chunk v) fp).
Proof.
  intros. generalize H1; destruct v; simpl; intro; try discriminate.
  unfold load.
  generalize (eval_addressing_fp _ _ _ _ _ chunk _ _ _ _ _ H H0 (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV [EF EQ]]]. split.
  eapply eval_Eload; simpl; eauto.
  eapply eval_Eload_fp; simpl; eauto. unfold loadv_fp. apply FP.union_comm_eq.
Qed.

Lemma eval_store_fp:
  forall chunk a1 a2 v1 v2 fp1 fp2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr_fp tge sp e m nil a1 fp1 ->
  eval_expr tge sp e m nil a2 v2 ->
  eval_expr_fp tge sp e m nil a2 fp2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step tge (Core_State f (store chunk a1 a2) k sp e) m
       (FP.union (FP.union fp1 fp2) (storev_fp chunk v1)) (Core_State f Sskip k sp e) m'.
Proof.
  intros. generalize H3; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing_fp _ _ _ _ _ chunk _ _ _ _ _ H H0 (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV [EF EQ]]].
  eapply step_store; eauto.
Qed.

(** Correctness of instruction selection for operators *)
Ltac uopexploit H1 H2:=
  let v := fresh in
  let A := fresh in
  let B := fresh in
  exploit H1; try exacteval H2; eauto; intros [v [A B]]; evalge A.

Lemma eval_sel_unop_fp:
  forall le op a1 v1 fp v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr_fp tge sp e m le a1 fp ->
  eval_unop op v1 = Some v ->
  (exists v', eval_expr tge sp e m le (sel_unop op a1) v' /\ Val.lessdef v v') /\
  (exists fp', eval_expr_fp tge sp e m le (sel_unop op a1) fp' /\ FP.subset fp' fp).
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  split. eapply eval_cast8unsigned; eauto. eapply eval_cast8unsigned_fp; eauto.
  split. eapply eval_cast8signed; eauto. eapply eval_cast8signed_fp; eauto.
  split. eapply eval_cast16unsigned; eauto. eapply eval_cast16unsigned_fp; eauto.
  split. eapply eval_cast16signed; eauto. eapply eval_cast16signed_fp; eauto.
  split. eapply eval_negint; eauto. eapply eval_negint_fp; eauto.
  split. eapply eval_notint; eauto. eapply eval_notint_fp; eauto.
  split. eapply eval_negf; eauto. eapply eval_negf_fp; eauto.
  split. eapply eval_absf; eauto. eapply eval_absf_fp; eauto.
  split. eapply eval_negfs; eauto. eapply eval_negfs_fp; eauto.
  split. eapply eval_absfs; eauto. eapply eval_absfs_fp; eauto.
  split. eapply eval_singleoffloat; eauto. eapply eval_singleoffloat_fp; eauto.
  split. eapply eval_floatofsingle; eauto. eapply eval_floatofsingle_fp; eauto.
  split. eapply eval_intoffloat; eauto. eapply eval_intoffloat_fp; eauto.
  split. eapply eval_intuoffloat; eauto. eapply eval_intuoffloat_fp; eauto.
  split. eapply eval_floatofint; eauto. eapply eval_floatofint_fp; eauto.
  split. eapply eval_floatofintu; eauto. eapply eval_floatofintu_fp; eauto.
  split. eapply eval_intofsingle; eauto. eapply eval_intofsingle_fp; eauto.
  split. eapply eval_intuofsingle; eauto. eapply eval_intuofsingle_fp; eauto.
  split. eapply eval_singleofint; eauto. eapply eval_singleofint_fp; eauto.
  split. eapply eval_singleofintu; eauto. eapply eval_singleofintu_fp; eauto.
  uopexploit eval_negl H. split. eauto. eapply eval_negl_fp; eauto.
  uopexploit eval_notl H. split; eauto. eapply eval_notl_fp; eauto.
  uopexploit eval_intoflong H. split; eauto. eapply eval_intoflong_fp; eauto.
  uopexploit eval_longofint H. split; eauto. eapply eval_longofint_fp; eauto.
  uopexploit eval_longofintu H. split; eauto. eapply eval_longofintu_fp; eauto.
  uopexploit eval_longoffloat H. split; eauto. eapply eval_longoffloat_fp; eauto.
  uopexploit eval_longuoffloat H. split; eauto.  eapply eval_longuoffloat_fp; eauto.
  uopexploit eval_floatoflong H. split; eauto. eapply eval_floatoflong_fp; eauto.
  uopexploit eval_floatoflongu H. split; eauto. eapply eval_floatoflongu_fp; eauto.
  uopexploit eval_longofsingle H. split; eauto. eapply eval_longofsingle_fp; eauto.
  uopexploit eval_longuofsingle H. split; eauto. eapply eval_longuofsingle_fp; eauto.
  uopexploit eval_singleoflong H. split; eauto. eapply eval_singleoflong_fp; eauto.
  uopexploit eval_singleoflongu H. split; eauto. eapply eval_singleoflongu_fp; eauto.
Qed.

Let tprog := mkprogram (cu_defs tcu) (cu_public tcu) 1%positive.


Ltac bexploit1 T1 H1 H2 :=
  (exploit T1; [exact H1|exact H2|]) || (exploit T1; [exact H1|exact H2| |]).
Ltac bexploit2 T1 H1 H2 :=
  ((exploit (T1 tprog); subst tprog; [exacteval H1|exacteval H2|])
  || (exploit (T1 tprog); subst tprog; [exacteval H1|exacteval H2| | ])
  || (exploit (T1 tprog); subst tprog; [|exacteval H1|exacteval H2| ])
  || (exploit (T1 tprog); subst tprog; [|exacteval H1|exacteval H2| | ])).
Ltac bexploit T1 T2:=
  match goal with
  | [ H1: (eval_expr _ _ _ _ _ ?a1 _),
          H2: (eval_expr _ _ _ _ _ ?a2 _)
      |- context[(_ ?a1 ?a2)] ]
    => (((bexploit2 T1 H1 H2); eauto; intros [?v [?A ?B]]; evalge A)
       || ((bexploit1 T1 H1 H2); eauto; intros [?v [?A ?B]]));
      split; [eauto| try eapply T2; eauto];
      try (exploit T2; [exact H1|eauto|exact H2|eauto|eauto|]; simpl; TrivFP; fail)
  end.

Lemma eval_sel_binop_fp:
  forall le op a1 a2 v1 v2 fp1 fp2 v fp,
    eval_expr tge sp e m le a1 v1 ->
    eval_expr_fp tge sp e m le a1 fp1 ->
    eval_expr tge sp e m le a2 v2 ->
    eval_expr_fp tge sp e m le a2 fp2 ->
    eval_binop op v1 v2 m = Some v ->
    eval_binop_fp op v1 v2 m = Some fp ->
    (exists v', eval_expr tge sp e m le (sel_binop op a1 a2) v' /\ Val.lessdef v v') /\
    (exists fp', eval_expr_fp tge sp e m le (sel_binop op a1 a2) fp' /\ FP.subset fp' (FP.union (FP.union fp1 fp2) fp)).
Proof.
  destruct op; simpl; intros;
    try match goal with | [H1: ?x = _, H: match ?x with _ => _ end = Some _ |- _] => rewrite H1 in H  end;
    FuncInv; subst; TrivFP. 
  bexploit eval_add eval_add_fp. 
  bexploit eval_sub eval_sub_fp.
  bexploit eval_mul eval_mul_fp.
  bexploit eval_divs eval_divs_fp.
  bexploit eval_divu eval_divu_fp.
  bexploit eval_mods eval_mods_fp.
  bexploit eval_modu eval_modu_fp.
  bexploit eval_and eval_and_fp.
  bexploit eval_or eval_or_fp.
  bexploit eval_xor eval_xor_fp.
  bexploit eval_shl eval_shl_fp.
  bexploit eval_shr eval_shr_fp.
  bexploit eval_shru eval_shru_fp.
  bexploit eval_addf eval_addf_fp.
  bexploit eval_subf eval_subf_fp.
  bexploit eval_mulf eval_mulf_fp.
  bexploit eval_divf eval_divf_fp.
  bexploit eval_addfs eval_addfs_fp.
  bexploit eval_subfs eval_subfs_fp.
  bexploit eval_mulfs eval_mulfs_fp.
  bexploit eval_divfs eval_divfs_fp.
  bexploit eval_addl eval_addl_fp. 
  bexploit eval_subl eval_subl_fp. 
  bexploit eval_mull eval_mull_fp.
  bexploit eval_divls eval_divls_fp.
  bexploit eval_divlu eval_divlu_fp.
  bexploit eval_modls eval_modls_fp.
  bexploit eval_modlu eval_modlu_fp.
  bexploit eval_andl eval_andl_fp.
  bexploit eval_orl eval_orl_fp. 
  bexploit eval_xorl eval_xorl_fp. 
  bexploit eval_shll eval_shll_fp.
  bexploit eval_shrl eval_shrl_fp.
  bexploit eval_shrlu eval_shrlu_fp.
  bexploit eval_comp_opt eval_comp_opt_fp.
  bexploit eval_compu_opt eval_compu_opt_fp.
  bexploit eval_compf_opt eval_compf_opt_fp.
  bexploit eval_compfs_opt eval_compfs_opt_fp.
  bexploit2 eval_cmpl H H1; eauto. intro A; evalge A. split; [eauto|eapply eval_cmpl_fp; eauto].
  bexploit2 eval_cmplu H H1; eauto. intro A. evalge A. split; [eauto|eapply eval_cmplu_fp; eauto].
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)
(** TODO: modified spec.. could be useless *)
Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident.
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Ptrofs.eq Ptrofs.eq_spec i0 Ptrofs.zero; congruence.
Qed.

Lemma classify_call_correct:
  forall sp e m a v fd,
  Cminor.eval_expr sge sp e m a v ->
  Genv.find_funct sge v = Some fd ->
  match classify_call (comp_unit_defmap scu) a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol sge id = Some b /\ v = Vptr b Ptrofs.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  unfold classify_call; intros.
  destruct (expr_is_addrof_ident a) as [id|] eqn:EA; auto.
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H. inv H2. unfold Genv.symbol_address in *.
  destruct (Genv.find_symbol sge id) as [b|] eqn:FS; try discriminate.
  rewrite Genv.find_funct_find_funct_ptr in H0. 
  assert (DFL: exists b1, Genv.find_symbol sge id = Some b1 /\ Vptr b Ptrofs.zero = Vptr b1 Ptrofs.zero) by (exists b; auto).
  unfold globdef; destruct (comp_unit_defmap scu)!id as [[[f|ef] |gv] |] eqn:G; auto.
  destruct (ef_inline ef) eqn:INLINE; auto.
  eapply find_def_symbol in G; eauto. 
  rewrite Genv.find_funct_ptr_iff in H0.
  destruct G as [b' [A B]]. congruence.
Qed.

(** Translation of [switch] statements *)
Inductive Rint: Z -> val -> Prop :=
  | Rint_intro: forall n, Rint (Int.unsigned n) (Vint n).

Inductive Rlong: Z -> val -> Prop :=
| Rlong_intro: forall n, Rlong (Int64.unsigned n) (Vlong n).

Section SEL_SWITCH.

Variable make_cmp_eq: expr -> Z -> expr.
Variable make_cmp_ltu: expr -> Z -> expr.
Variable make_sub: expr -> Z -> expr.
Variable make_to_int: expr -> expr.
Variable modulus: Z.
Variable R: Z -> val -> Prop.

Hypothesis no_ptr: forall z v b i, R z v -> v <> Vptr b i.

Hypothesis eval_make_cmp_eq: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_eq a n) (Val.of_bool (zeq i n)).
Hypothesis eval_make_cmp_eq_fp: forall sp e m le a v fp i n,
  eval_expr tge sp e m le a v ->
  eval_expr_fp tge sp e m le a fp ->
  R i v -> 0 <= n < modulus ->
  exists fp', eval_expr_fp tge sp e m le (make_cmp_eq a n) fp' /\ FP.subset fp' fp.
Hypothesis eval_make_cmp_ltu: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_ltu a n) (Val.of_bool (zlt i n)).
Hypothesis eval_make_cmp_ltu_fp: forall sp e m le a v fp i n,
  eval_expr tge sp e m le a v -> 
  eval_expr_fp tge sp e m le a fp ->
  R i v -> 0 <= n < modulus ->
  exists fp', eval_expr_fp tge sp e m le (make_cmp_ltu a n) fp' /\ FP.subset fp' fp.
Hypothesis eval_make_sub: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  exists v', eval_expr tge sp e m le (make_sub a n) v' /\ R ((i - n) mod modulus) v'.
Hypothesis eval_make_sub_fp: forall sp e m le a v fp i n,
  eval_expr tge sp e m le a v ->
  eval_expr_fp tge sp e m le a fp ->
  R i v -> 0 <= n < modulus ->
  exists fp', eval_expr_fp tge sp e m le (make_sub a n) fp' /\ FP.subset fp' fp.
Hypothesis eval_make_to_int: forall sp e m le a v i,
  eval_expr tge sp e m le a v -> R i v ->
  exists v', eval_expr tge sp e m le (make_to_int a) v' /\ Rint (i mod Int.modulus) v'.
Hypothesis eval_make_to_int_fp: forall sp e m le a v fp i,
  eval_expr tge sp e m le a v -> 
  eval_expr_fp tge sp e m le a fp ->
  R i v ->    
  exists fp', eval_expr_fp tge sp e m le (make_to_int a) fp' /\ FP.subset fp' fp.

Ltac exactcond A := eapply eval_condexpr_preserved; try exact A; try gegen; eauto with gegen.

Lemma sel_switch_correct_rec_fp:
  forall sp e m varg i x,
  R i varg ->
  forall t arg le,
  wf_comptree modulus t ->
  nth_error le arg = Some varg ->
  comptree_match modulus i t = Some x ->
  eval_exitexpr tge sp e m le (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t) x /\
  eval_exitexpr_fp tge sp e m le (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t) empfp.
Proof.
  intros until x; intros Ri. induction t; simpl; intros until le; intros WF ARG MATCH; inv WF.
  - (* base case *)
    inv MATCH; split; constructor.
  - (* eq test *)
    assert (eval_expr tge sp e m le (make_cmp_eq (Eletvar arg) key) (Val.of_bool (zeq i key))).
    { eapply eval_make_cmp_eq; eauto. constructor; auto. }
    exploit (eval_make_cmp_eq_fp sp e m le (Eletvar arg)).
    constructor; eauto. econstructor; eauto. eauto. eauto. intros [fp' [H0 B]]. apply subset_emp_emp in B; subst.
    exploit (eval_condexpr_of_expr_fp sp e m (make_cmp_eq (Eletvar arg) key)); eauto.
    instantiate (1:= (zeq i key)). destruct zeq; simpl; try constructor. intros [A B].
    destruct (zeq i key); inv MATCH; simpl.
    + split; econstructor; eauto; simpl; econstructor. 
    + exploit IHt; eauto. intros [A' B']. split; econstructor; eauto.
  - (* lt test *)
    assert (eval_expr tge sp e m le (make_cmp_ltu (Eletvar arg) key) (Val.of_bool (zlt i key))).
    { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
    exploit (eval_make_cmp_ltu_fp sp e m le (Eletvar arg)); try (econstructor; eauto; fail); eauto.
    intros [fp' [? B]]. apply subset_emp_emp in B; subst.
    exploit (eval_condexpr_of_expr_fp sp e m (make_cmp_ltu (Eletvar arg) key)); eauto.
    instantiate (1:= (zlt i key)). destruct zlt; constructor. intros [A B].
    destruct (zlt i key); simpl in *.
    + exploit IHt1; eauto. intros [A' B']. split; econstructor; eauto.
    + exploit IHt2; eauto. intros [A' B']. split; econstructor; eauto.
  - (* jump table *)
    exploit (eval_make_sub sp e m le). eapply eval_Eletvar. eauto. eauto.
    instantiate (1 := ofs). auto. intros (v' & A & B).
    exploit (eval_make_sub_fp sp e m le). eapply eval_Eletvar. eauto. econstructor; eauto. eauto.
    instantiate (1 := ofs). auto. intros (fp' & A' & B'). apply subset_emp_emp in B'; subst.
    set (i' := (i - ofs) mod modulus) in *.
    assert (eval_expr tge sp e m (v' :: le) (make_cmp_ltu (Eletvar O) sz) (Val.of_bool (zlt i' sz))).
    { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
    exploit (eval_make_cmp_ltu_fp sp e m (v' :: le) (Eletvar 0)); eauto.
    econstructor; eauto. econstructor; simpl; eauto. intros [fp' [? B']]. apply subset_emp_emp in B'; subst.
    exploit (eval_condexpr_of_expr_fp sp e m (make_cmp_ltu (Eletvar 0) sz) (v' :: le)); eauto.
    instantiate (1:= zlt i' sz); destruct zlt; constructor. intros [E F].
    exploit (eval_make_to_int sp e m (v' :: le) (Eletvar O)).
    constructor. simpl; eauto. eauto. intros (v'' & C & D). inv D.
    exploit (eval_make_to_int_fp sp e m (v' :: le) (Eletvar O)).
    constructor. simpl; eauto. econstructor; simpl; eauto. eauto. intros [fp' [C' D']]. apply subset_emp_emp in D'; subst.
    destruct (zlt i' sz); simpl in *.
    + { split; repeat (simpl; econstructor; eauto). all: rewrite H3; eauto. }
    + exploit (IHt (S arg)); eauto. instantiate (1:= v' :: le). eauto. intros [G I].
      split; repeat (simpl; econstructor; eauto; simpl).
Qed.

Lemma sel_switch_correct_fp:
  forall dfl cases arg sp e m varg fp i t le,
  validate_switch modulus dfl cases t = true ->
  eval_expr tge sp e m le arg varg ->
  eval_expr_fp tge sp e m le arg fp ->
  R i varg ->
  0 <= i < modulus ->
  eval_exitexpr tge sp e m le
     (XElet arg (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int O t))
     (switch_target i dfl cases) /\
  eval_exitexpr_fp tge sp e m le
     (XElet arg (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int O t)) fp .
Proof.
  intros. exploit validate_switch_correct; eauto. Lia.lia. intros [A B].
  exploit sel_switch_correct_rec_fp; eauto.
  instantiate (2:= varg :: le). instantiate (1:= 0%nat). auto. intros [C D].
  split; econstructor; eauto; TrivFP.
Qed.

End SEL_SWITCH.

Lemma sel_switch_int_correct_fp:
  forall dfl cases arg sp e m i fp t le,
  validate_switch Int.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vint i) ->
  eval_expr_fp tge sp e m le arg fp ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_int O t)) (switch_target (Int.unsigned i) dfl cases) /\
  eval_exitexpr_fp tge sp e m le (XElet arg (sel_switch_int O t)) fp.
Proof.
  assert (INTCONST: forall n sp e m le,
            eval_expr tge sp e m le (Eop (Ointconst n) Enil) (Vint n)).
  { intros. econstructor. constructor. auto. }
  intros. eapply sel_switch_correct_fp with (R := Rint); eauto.
- intros until n; intros EVAL R RANGE. inv R.
  exploit eval_comp_opt. eexact EVAL. apply (INTCONST (Int.repr n)).
  simpl. eauto.
  instantiate (1 := Ceq). intros (vb & A & B).
  unfold Val.cmp in B. simpl in B. revert B.
  predSpec Int.eq Int.eq_spec n0 (Int.repr n); intros B; inv B.
  rewrite Int.unsigned_repr. unfold proj_sumbool; rewrite zeq_true; auto.
  unfold Int.max_unsigned; Lia.lia.
  unfold proj_sumbool; rewrite zeq_false; auto.
  red; intros; elim H2. rewrite <- (Int.repr_unsigned n0). congruence.
- clear. intros. inv H1.
  exploit (eval_comp_opt tge sp e m Ceq); simpl. exact H. instantiate (2:= Eop (Ointconst (Int.repr n)) Enil).
  repeat econstructor; eauto. simpl; eauto. intros [vc [A B]].
  exploit (eval_comp_opt_fp tge sp e m Ceq); simpl. exact H. exact H0.
  4: instantiate (1:=empfp); TrivFP; eauto. 1,2: repeat econstructor; eauto. eauto.
- intros until n; intros EVAL R RANGE. inv R.
  exploit eval_compu_opt. eexact EVAL. apply (INTCONST (Int.repr n)). simpl. eauto.
  instantiate (1 := Clt). intros (vb & A & B).
  unfold Val.cmpu in B. simpl in B.
  unfold Int.ltu in B. rewrite Int.unsigned_repr in B.
  destruct (zlt (Int.unsigned n0) n); inv B; auto.
  unfold Int.max_unsigned; Lia.lia.
- clear; intros. inv H1. exploit eval_compu_opt. exact H. instantiate (2:=  Eop (Ointconst (Int.repr n)) Enil).
  repeat econstructor; eauto. simpl. eauto. intros [vc [A B]].
  inv B. exploit (eval_compu_opt_fp tge sp e m Clt). exact H. eauto. 3: exact A.
  1,2: repeat econstructor; eauto. eauto. TrivFP.
  inv H3. unfold Val.of_bool in H4. destruct Int.ltu; discriminate.
- intros until n; intros EVAL R RANGE. inv R.
  exploit eval_sub. eexact EVAL. apply (INTCONST (Int.repr n)). intros (vb & A & B).
  simpl in B. inv B. econstructor; split; eauto.
  replace ((Int.unsigned n0 - n) mod Int.modulus)
     with (Int.unsigned (Int.sub n0 (Int.repr n))).
  constructor.
  unfold Int.sub. rewrite Int.unsigned_repr_eq. f_equal. f_equal.
  apply Int.unsigned_repr. unfold Int.max_unsigned; Lia.lia.
- clear. intros. inv H1. exploit eval_sub. exact H. instantiate (2:= (Eop (Ointconst (Int.repr n)) Enil)).
  repeat econstructor; eauto. intros [vb [A B]].
  exploit eval_sub_fp. exact H. eauto. instantiate (2:= (Eop (Ointconst (Int.repr n)) Enil)).
  1-2: repeat econstructor; eauto. TrivFP. 
- intros until i0; intros EVAL R. exists v; split; auto.
  inv R. rewrite Zmod_small by (apply Int.unsigned_range). constructor.
- clear. intros. inv H1. Triv.
- constructor.
- apply Int.unsigned_range.
Qed.

Lemma sel_switch_long_correct_fp:
  forall dfl cases arg sp e m i fp t le,
  validate_switch Int64.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vlong i) ->
  eval_expr_fp tge sp e m le arg fp ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_long O t)) (switch_target (Int64.unsigned i) dfl cases) /\
  eval_exitexpr_fp tge sp e m le (XElet arg (sel_switch_long O t)) fp.
Proof.
  intros. eapply sel_switch_correct_fp with (R := Rlong); eauto.
- intros until n; intros EVAL R RANGE. eapply eval_expr_preserved. 4: eapply eval_cmpl.
  1-3:try gegen; eauto with gegen. exacteval EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmpl. simpl. f_equal; f_equal. unfold Int64.eq.
  rewrite Int64.unsigned_repr. destruct (zeq (Int64.unsigned n0) n); auto.
  unfold Int64.max_unsigned; Lia.lia.
- intros until n. intros EVAL EVALFP R RANGE. inv R.
  exploit (eval_cmpl_fp tcu tge TGEINIT); simpl. exact EVAL. eauto. instantiate (2:= longconst (Int64.repr n)).
  1-2: repeat econstructor; eauto. instantiate (2:= Ceq). unfold Val.cmpl. simpl; eauto. TrivFP.
- intros until n; intros EVAL R RANGE. eapply eval_expr_preserved. 4: eapply eval_cmplu.
  1-3:try gegen; eauto with gegen. exacteval EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmplu. simpl. f_equal; f_equal. unfold Int64.ltu.
  rewrite Int64.unsigned_repr. destruct (zlt (Int64.unsigned n0) n); auto.
  unfold Int64.max_unsigned; Lia.lia.
- intros until n. intros EVAL EVALFP R RANGE. inv R.
  exploit (eval_cmplu_fp tcu tge TGEINIT); simpl. exact EVAL. eauto. instantiate (2:= longconst (Int64.repr n)).
  1-2: repeat econstructor; eauto. instantiate (2:= Clt). unfold Val.cmplu. simpl; eauto. simpl. eauto. TrivFP.
- intros until n; intros EVAL R RANGE. 
  exploit eval_subl; auto. exacteval EVAL. apply eval_longconst with (n := Int64.repr n).
  intros (vb & A & B). evalge A.
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace ((Int64.unsigned n0 - n) mod Int64.modulus)
     with (Int64.unsigned (Int64.sub n0 (Int64.repr n))).
  constructor.
  unfold Int64.sub. rewrite Int64.unsigned_repr_eq. f_equal. f_equal.
  apply Int64.unsigned_repr. unfold Int64.max_unsigned; Lia.lia.
- intros until n; intros EVAL EVALFP R RANGE.
  exploit eval_subl; auto. exacteval EVAL. apply eval_longconst with (n := Int64.repr n).
  intros (vb & A & B). evalge A.
  exploit eval_subl_fp; auto. 5: exact A. 1-2: eauto.
  eapply eval_expr_preserved. 4: apply eval_longconst with (n:= Int64.repr n). 1-3: try gegen; eauto with gegen.
  eapply eval_longconst_fp with (n := Int64.repr n). TrivFP. 
- intros until i0; intros EVAL R.
  exploit eval_lowlong. exacteval EVAL. intros (vb & A & B). evalge A.
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace (Int64.unsigned n mod Int.modulus) with (Int.unsigned (Int64.loword n)).
  constructor.
  unfold Int64.loword. apply Int.unsigned_repr_eq.
- intros until i0; intros EVAL EVALFP R.
  exploit eval_lowlong. exacteval EVAL. intros (vb & A & B). evalge A.
  eapply eval_lowlong_fp; eauto. 
- constructor.
- apply Int64.unsigned_range.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD.
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.

Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v ->
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  { inv LD1. inv LD2. exists v; auto. 
    destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
    destruct op; simpl in *; inv EV; TrivialExists. }
  assert (CMPU: forall c,
    eval_binop (Ocmpu c) v1 v2 m = Some v ->
    exists v' : val, eval_binop (Ocmpu c) v1' v2' m' = Some v' /\ Val.lessdef v v').
  { intros c A. simpl in *.
    inv LD1; inv LD2; try (unfold Val.cmpu_bool in A; try destruct v1'; try destruct v2'; inv A; fail).
    exists v; split; auto. destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1' v2') eqn:R; [|discriminate] .
    inv A. eapply Val.cmpu_bool_lessdef with (valid_ptr':= Mem.valid_pointer m')in R.
    rewrite R; auto.
    intros; eapply Mem.valid_pointer_extends; eauto.
    auto. auto. }
  assert (CMPLU: forall c,
    eval_binop (Ocmplu c) v1 v2 m = Some v ->
    exists v' : val, eval_binop (Ocmplu c) v1' v2' m' = Some v' /\ Val.lessdef v v').
  { intros c A. simpl in *. unfold Val.cmplu in *.
    destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:C; simpl in A; inv A.
    eapply Val.cmplu_bool_lessdef with (valid_ptr' := (Mem.valid_pointer m')) in C;
    eauto using Mem.valid_pointer_extends.
    rewrite C. exists (Val.of_bool b); auto. }
  destruct op; auto.
Qed.

Lemma eval_binop_lessdef_fp:
  forall op v1 v1' v2 v2' v fp m m',
    eval_binop op v1 v2 m = Some v ->    
    eval_binop_fp op v1 v2 m = Some fp ->    
    Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
    exists fp', eval_binop_fp op v1' v2' m' = Some fp' /\ FP.subset fp' fp.
Proof.
  intros until m'; intros EV EF LD1 LD2 ME.
  inv LD1. inv LD2.
  { destruct op; destruct v1'; simpl in *; inv EV; TrivialExists; TrivFP;
      destruct v2'; try discriminate; TrivialExists; TrivFP;
        try match goal with
            | |- context[match ?x with _ => _ end] => destruct x; try discriminate; TrivialExists; TrivFP
            end.
    (** TODO: lemma, mem_extend -> weak_valid_pointer_fp/valid_pointer_fp subset *)
    destruct Int.eq, Val.cmp_different_blocks; inv EF; TrivFP. 
    apply weak_valid_pointer_extend_subset; auto. 
    destruct Int.eq, Val.cmp_different_blocks; inv EF; TrivFP.
    apply weak_valid_pointer_extend_subset. auto. 
    destruct eq_block. inv EF. apply subset2_union.
    apply FP.subset_union_subset. apply weak_valid_pointer_extend_subset. auto.
    rewrite FP.union_comm_eq. apply FP.subset_union_subset, weak_valid_pointer_extend_subset. auto.
    inv EF. TrivFP. }
  { destruct op; destruct v1'; inv EV; simpl; TrivialExists; TrivFP. }
  { destruct op; simpl; TrivialExists; TrivFP; destruct v2'; inv EV. }
Qed.

(** * Semantic preservation for instruction selection. *)

(** Relationship between the local environments. *)
Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.

Lemma set_optvar_lessdef:
  forall e1 e2 optid v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (set_optvar optid v1 e1) (set_optvar optid v2 e2).
Proof.
  unfold set_optvar; intros. destruct optid; auto. apply set_var_lessdef; auto.
Qed.

Lemma set_params_lessdef:
  forall il vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.

Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.

(** Semantic preservation for expressions. *)

Section EXPRESSIONS.
Variable hf: helper_functions.
Hypothesis HF: helper_functions_declared scu hf.

Ltac TrivEval := do 2 eexists; split;[repeat econstructor; eauto|split;[eauto|split;[repeat econstructor; eauto|TrivFP]]].
Lemma sel_expr_correct_fp:
  forall sp e m a fp,
    Cminor_local.eval_expr_fp sge sp e m a fp ->    
    forall v, Cminor.eval_expr sge sp e m a v ->
    forall e' le m',
      env_lessdef e e' -> Mem.extends m m' ->
      exists v' fp',
        eval_expr tge sp e' m' le (sel_expr a) v' /\ Val.lessdef v v' /\
        eval_expr_fp tge sp e' m' le (sel_expr a) fp' /\ FP.subset fp' fp.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  inv H. exploit H0; eauto. intros [v' [A B]]. TrivEval.
  (* Econst *)
  destruct cst; inv H0; simpl in *; FuncInv; subst; try (TrivEval; fail).
  exists (Vlong i), empfp. split. exploit eval_longconst. intro. evalge H; eauto with gegen.
  split; auto. split. apply eval_longconst_fp. TrivFP.
  unfold Genv.symbol_address; rewrite <- symbols_preserved; fold (Genv.symbol_address tge i i0).
  exploit eval_addrsymbol. intros [v' [A B]]. exists v', empfp. split. eauto. split; auto.
  split. eapply eval_addrsymbol_fp. TrivFP.
  (* Eunop *)
  exploit IHeval_expr_fp; eauto. intros (v1' & fp' & A & B & A' & B').
  exploit eval_unop_lessdef; eauto. intros [v' [C D]]. 
  exploit eval_sel_unop_fp; eauto. intros [[vo [E F]] [fpo [E' F']]]. TrivEval.
  (** TODO: Cminor.eval_expr det *)
  inv H2. assert (v2 = v1) by (eapply Cminor_local.eval_expr_det; eauto). subst. rewrite H1 in H9. inv H9.
  eapply Val.lessdef_trans; eauto. apply subset_trans with fp'; auto.
  (* Ebinop *)
  exploit IHeval_expr_fp1; eauto. intros (v1' & fp1' & A & B & A' & B').
  exploit IHeval_expr_fp2; eauto. intros (v2' & fp2' & C & D & C' & D').
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  exploit eval_binop_lessdef_fp; try exact H3; eauto. intros [fp' [E' F']].
  exploit eval_sel_binop_fp. 2: eexact A. 3: eexact C. 1-5: eauto. intros [[vo [G I]] [fpo [G' I']]]. TrivEval.
  inv H6. assert (v3 = v1) by (eapply Cminor_local.eval_expr_det; eauto). subst.
  assert (v4 = v2) by (eapply Cminor_local.eval_expr_det; eauto). subst. rewrite H3 in H15. inv H15.
  eapply Val.lessdef_trans; eauto. apply subset_trans with (FP.union (FP.union fp1' fp2') fp'); subst; auto.
  repeat apply subset2_union.
  rewrite <- FP.fp_union_assoc. apply FP.subset_union_subset; auto.
  rewrite <- FP.fp_union_assoc, (FP.union_comm_eq fp1), <- FP.fp_union_assoc. apply FP.subset_union_subset; auto.
  rewrite <- (FP.union_comm_eq fp3). apply FP.subset_union_subset; auto.
  (* Eload *)
  destruct vaddr; try discriminate. 
  exploit IHeval_expr_fp; eauto. intros (vaddr' & fpaddr' & A & B & A' & B'). inv B.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exploit eval_load_fp. exact A. exact A'. eauto. intros [E F]. TrivEval.
  inv H4. assert (vaddr = Vptr b i) by (eapply Cminor_local.eval_expr_det; eauto). subst. rewrite H1 in H9; inv H9. auto.
  simpl. apply subset2_union; TrivFP.
Qed.

Lemma sel_exprlist_correct_fp:
  forall sp e m a fp,
    Cminor_local.eval_exprlist_fp sge sp e m a fp ->
    forall v, Cminor.eval_exprlist sge sp e m a v ->
    forall e' le m',
      env_lessdef e e' -> Mem.extends m m' ->
      exists v' fp', eval_exprlist tge sp e' m' le (sel_exprlist a) v' /\ Val.lessdef_list v v' /\
                eval_exprlist_fp tge sp e' m' le (sel_exprlist a) fp' /\ FP.subset fp' fp.
Proof.
  induction 1; intros; simpl.
  inv H. exists (@nil val), empfp. split;[|split;[auto|split;[|TrivFP]]]; constructor.
  exploit sel_expr_correct_fp; eauto. intros (v1' & fp1' & A & B & A' & B').
  exploit IHeval_exprlist_fp; eauto. intros (vl' & fpl' & C & D & C' & D').
  exists (v1' :: vl'), (FP.union fp1' fpl'); split. constructor; eauto.
  split. inv H4. assert (v0 = v1) by (eapply Cminor_local.eval_expr_det; eauto).
  assert (vl0 = vl) by (eapply Cminor_local.eval_exprlist_det; eauto). subst. auto.
  split; subst. econstructor; eauto. apply subset2_union; TrivFP.
Qed.

Lemma sel_builtin_arg_correct_fp:
  forall sp e e' m m' a v fp c,
    env_lessdef e e' -> Mem.extends m m' ->
    Cminor.eval_expr sge sp e m a v ->
    Cminor_local.eval_expr_fp sge sp e m a fp ->
  exists v' fp',
    CminorSel.eval_builtin_arg tge sp e' m' (sel_builtin_arg a c) v' /\ Val.lessdef v v' /\
    CminorSel_local.eval_builtin_arg_fp tge sp e' m' (sel_builtin_arg a c) fp' /\ FP.subset fp' fp.
Proof.
  intros. unfold sel_builtin_arg.
  exploit sel_expr_correct_fp; eauto. intros (v1 & fp1 & A & B & A' & B').
  exists v1, fp1.
  destruct (builtin_arg_ok (builtin_arg (sel_expr a)) c).
  * split. apply eval_builtin_arg; eauto. split; auto.
    split; auto. eapply eval_builtin_arg_fp; eauto.
  * split. constructor; auto. 
    split; auto. split; auto. econstructor; eauto.
Qed.

Lemma sel_builtin_args_correct_fp:
  forall sp e e' m m',
    env_lessdef e e' -> Mem.extends m m' ->
    forall al fp,
      Cminor_local.eval_exprlist_fp sge sp e m al fp ->
      forall vl, Cminor.eval_exprlist sge sp e m al vl ->
            forall cl, exists vl' fpl',
                list_forall2 (CminorSel.eval_builtin_arg tge sp e' m')
                             (sel_builtin_args al cl) vl'
                /\ Val.lessdef_list vl vl'
                /\ list_forall2 (CminorSel_local.eval_builtin_arg_fp tge sp e' m')
                               (sel_builtin_args al cl) fpl'
                /\ FP.subset (fold_right (fun fph fpt => FP.union fph fpt) empfp fpl') fp.
Proof.
  induction 3; intros; simpl.
  - exists (@nil val), nil; split; constructor. inv H1. auto.
    split. constructor. simpl. TrivFP.
  - exploit sel_builtin_arg_correct_fp; eauto. intros (v1' & fp1' & A & B & A' & B').
    edestruct IHeval_exprlist_fp as (vl' & fpl' & C & D & C' & D'). eauto.
    inv H6.
    assert (v0 = v1) by (eapply Cminor_local.eval_expr_det; eauto).
    assert (vl = vl1) by (eapply Cminor_local.eval_exprlist_det; eauto).
    subst. clear H9 H11. exists (v1' :: vl'), (fp1' :: fpl').
    split. constructor; eauto. split. auto.
    split. constructor; eauto. simpl. apply FP.subset_parallel_union; TrivFP.
Qed.

End EXPRESSIONS.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: helper_functions -> Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop: forall hf,
      match_cont hf Cminor.Kstop Kstop
  | match_cont_seq: forall hf s s' k k',
      sel_stmt (comp_unit_defmap scu) s = OK s' ->
      match_cont hf k k' ->
      match_cont hf (Cminor.Kseq s k) (Kseq s' k')
  | match_cont_block: forall hf k k',
      match_cont hf k k' ->
      match_cont hf (Cminor.Kblock k) (Kblock k')
  | match_cont_call: forall hf hf' id f sp e k f' e' k',
      helper_functions_declared scu hf ->
      sel_function (comp_unit_defmap scu) hf f = OK f' ->
      match_cont hf k k' -> env_lessdef e e' ->
      match_cont hf' (Cminor.Kcall id f sp e k) (Kcall id f' sp e' k').

Definition match_call_cont (k: Cminor.cont) (k': CminorSel.cont) : Prop :=
  forall hf, match_cont hf k k'.

Definition union_fp_list (fpl: list FP.t) : FP.t :=
  (fold_right (fun fph fpt => FP.union fph fpt) empfp fpl).

Inductive match_state: FP.t -> FP.t ->
                       Cminor_local.core * mem -> CminorSel_local.core * mem -> Prop :=
| match_state_intro:
    forall fp fp' hf f f' s k s' k' sp e m e' m'
      (HF: helper_functions_declared scu hf)
      (TF: sel_function (comp_unit_defmap scu) hf f = OK f')
      (TS: sel_stmt (comp_unit_defmap scu) s = OK s')
      (MC: match_cont hf k k')
      (LD: env_lessdef e e')
      (ME: Mem.extends m m')
      (** NEW *)
      (FPMATCH: FP.subset fp' fp),
      match_state fp fp'
                  (Cminor_local.Core_State f s k sp e, m)
                  (Core_State f' s' k' sp e', m')
| match_callstate:
    forall fp fp' f f' args args' k k' m m'
      (TF: match_fundef scu f f')
      (MC: match_call_cont k k')
      (LD: Val.lessdef_list args args')
      (ME: Mem.extends m m')
      (** NEW *)
      (FPMATCH: FP.subset fp' fp),
      match_state fp fp'
                  (Cminor_local.Core_Callstate f args k, m)
                  (Core_Callstate f' args' k', m')
| match_returnstate:
    forall fp fp' v v' k k' m m'
      (MC: match_call_cont k k')
      (LD: Val.lessdef v v')
      (ME: Mem.extends m m')
      (** NEW *)
      (FPMATCH: FP.subset fp' fp),
      match_state fp fp'
                  (Cminor_local.Core_Returnstate v k, m)
                  (Core_Returnstate v' k', m')

| match_builtin_1:
    forall fp fp' fpl hf ef args args' optid f sp e k m al f' e' k' m'
      (TF: sel_function (comp_unit_defmap scu) hf f = OK f')
      (MC: match_cont hf k k')
      (LDA: Val.lessdef_list args args')
      (LDE: env_lessdef e e')
      (ME: Mem.extends m m')
      (EA: list_forall2 (CminorSel.eval_builtin_arg tge sp e' m') al args')
      (INLINE: ef_inline ef = true) 
      (** NEW *)
      (EAFP: list_forall2 (CminorSel_local.eval_builtin_arg_fp tge sp e' m') al fpl)
      (FPMATCH: FP.subset (FP.union fp' (union_fp_list fpl)) fp),
      match_state fp fp'
                  (Cminor_local.Core_Callstate (External ef) args (Cminor.Kcall optid f sp e k), m)
                  (Core_State f' (Sbuiltin (sel_builtin_res optid) ef al) k' sp e', m').

Definition MS b n mu fp fp' cm cm': Prop :=
  match_state fp fp' cm cm' /\
  let (c, m) := cm in
  let (c', m') := cm' in
  (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
  (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
  (proper_mu sge tge inject_id mu) /\
  (MemClosures_local.unmapped_closed mu m m') /\
  match c with
  | Cminor_local.Core_State _ _ _ _ _ => n = 1%nat /\ b = true
  | Cminor_local.Core_Callstate _ _ _ => n = 0%nat
  | Cminor_local.Core_Returnstate _ _ => n = 2%nat
  end.

Ltac invMS :=
  match goal with
  | H: MS _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    destruct cm1 as [sc Hm]; destruct cm2 as [tc Lm];
    unfold MS in H; simpl in H;
    destruct H as [MS [SVALID [TVALID [AGMU [RCPRESV INDEX]]]]]
  | H: MS _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    unfold MS in H; simpl in H;
    destruct H as [MS [SVALID [TVALID [AGMU [RCPRESV INDEX]]]]]
  end.


Remark call_cont_commut:
  forall hf k k', match_cont hf k k' -> match_call_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto; red; intros.
- constructor.
- eapply match_cont_call with (hf := hf); eauto. 
Qed.

Remark match_is_call_cont:
  forall hf k k', match_cont hf k k' -> Cminor.is_call_cont k -> match_call_cont k k'.
Proof.
  destruct 1; intros; try contradiction; red; intros.
- constructor.
- eapply match_cont_call with (hf := hf); eauto. 
Qed.

Remark match_call_cont_cont:
  forall k k', match_call_cont k k' -> exists hf, match_cont hf k k'.
Proof.
  intros. 
  simple refine (let hf : helper_functions := _ in _).
  econstructor; apply xH.
  exists hf; auto.
Qed.

Remark find_label_commut:
  forall hf lbl s k s' k',
  match_cont hf k k' ->
  sel_stmt (comp_unit_defmap scu) s = OK s' ->
  match Cminor.find_label lbl s k, find_label lbl s' k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => sel_stmt (comp_unit_defmap scu) s1 = OK s1' /\ match_cont hf k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros until k'; simpl; intros MC SE; try (monadInv SE); simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr e)); simpl; auto.
(* call *)
  destruct (classify_call (comp_unit_defmap scu) e); simpl; auto.
(* tailcall *)
  destruct (classify_call (comp_unit_defmap scu) e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)). constructor; eauto. eauto.
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl x (Kseq x0 k')) as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* ifthenelse *)
  exploit (IHs1 k); eauto.
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl x k') as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* loop *)
  apply IHs. constructor; auto. simpl; rewrite EQ; auto. auto.
(* block *)
  apply IHs. constructor; auto. auto.
(* switch *)
  destruct b.
  destruct (validate_switch Int64.modulus n l (compile_switch Int64.modulus n l)); inv SE.
  simpl; auto.
  destruct (validate_switch Int.modulus n l (compile_switch Int.modulus n l)); inv SE.
  simpl; auto.
(* return *)
  destruct o; inv SE; simpl; auto.
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.


Ltac Ex_index :=
  match goal with
  | |- context[Cminor_local.Core_State] => exists 1%nat
  | |- context[Cminor_local.Core_Callstate] => exists 0%nat
  | |- context[Cminor_local.Core_Returnstate] => exists 2%nat
  end.

Ltac resolvfp:=
  match goal with
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union ?fp1 _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union (FP.union ?fp1' _) _) (FP.union (FP.union ?fp1 _) _)=> 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp1 ?fp') =>
    rewrite FP.union_comm_eq; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp' _) =>
    apply FP.subset_union_subset; auto
  | |- Injections.FPMatch' _ _ empfp => apply Injections.fp_match_emp'
  | H: FP.subset ?fp1 ?fp2 |- Injections.FPMatch' _ ?fp2 ?fp1 =>
    apply Injections.fp_match_subset_T' with fp2; try exact H; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) ?fp2 =>
    apply Injections.fp_match_union_S'; resolvfp
  | |- FP.subset ?fp ?fp => apply FP.subset_refl
  | H: proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp => inv H; eapply fp_match_id; eauto
  | _ => idtac
  end.

Ltac eresolvfp:= resolvfp; eauto.

Ltac resvalid:=
  match goal with
  (** valid blocks *)
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.free ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_free_1; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.alloc ?m1 _ _ = (?m2,_)
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_alloc; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.store _ ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.store_valid_block_1; eauto
  (** Mem inv *)
  | H1: Mem.store _ ?m1 _ _ _ = Some ?m2,
        H2: Mem.store _ ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.store_val_inject_unmapped_closed_preserved;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.free ?m1 _ _ _ = Some ?m2,
        H2: Mem.free ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.alloc ?m1 _ _ = (?m2, _),
        H2: Mem.alloc ?m1' _ _ = (?m2', _),
            H3: proper_mu _ _ _ _
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto;
      try (eapply Mem.alloc_unchanged_on; eauto; fail)
  | _ => idtac
  end.

Ltac Right := right; Ex_index; do 3 eexists; split; [apply plus_one|resolvfp].
Ltac FP:= match goal with |- ?P /\ _ => assert P; [eresolvfp| try (split;[auto; fail|])] end.
Ltac Left := left; Ex_index; split; [auto|eresolvfp].
Ltac splitMS :=
  split;
  [econstructor; eresolvfp |split;
   [try resvalid; auto |split; [try resvalid; auto
                         |split; [auto| split; try resvalid; eauto]]]].

Theorem TRANSF_local_ldsim:
  @local_ldsim Cminor_IS CminorSel_IS sge tge sge tge.
Proof.
  eapply (@Local_ldsim Cminor_IS CminorSel_IS _ _ _ _ _ lt%nat MS).
  constructor.
  (* index wf *)
  - apply lt_wf.
  (* wd_mu *)
  - intros. invMS. eapply proper_mu_inject; eauto.
  (* inj ge *)
  - intros. invMS; eapply proper_mu_ge_init_inj; eauto.
  (* ge match *)
  - apply ge_match.
  (* initial call *)
  - intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    unfold init_core_local in *. simpl in *.
    unfold Cminor_local.init_core, init_core in *.
    unfold generic_init_core in INITCORE |- * .
    rewrite symbols_preserved.
    destruct (Genv.find_symbol sge fid) eqn: FIND; try discriminate.
    destruct (Genv.find_funct_ptr sge b) eqn: FINDB; try discriminate.
    exploit function_ptr_translated; eauto. intros (tf & FINDB' & (hf & HF & MATCHF)).
    rewrite FINDB'. 
    unfold Cminor_local.fundef_init in INITCORE.
    destruct f; try discriminate. 
    assert (exists tfd, tf = Internal tfd)  as [tfd INTERNAL] by (monadInv MATCHF; eauto). subst tf.
    unfold fundef_init. erewrite sig_function_translated;[|eexists; eauto].
    destruct (wd_args args (sig_args (Cminor.funsig (Internal f)))) eqn: WDARGS; [|discriminate].
    erewrite wd_args_inject; eauto. eexists. split. eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ]. exists 0%nat. inv INITCORE.
    (** This could be a general purposed lemma... *)
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. induction args; intros args' REL G MEMREL; inv REL.
      auto. inv G. f_equal. inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. }
    subst args'.
    exploit sig_function_translated; [eexists;eauto|]. simpl.
    split.
    econstructor; eauto.
    { eexists. eauto. }
    { constructor. }
    { clear; induction args; auto. }
    { inv MEMINITINJ. inv HRELY. inv LRELY.
      eapply inject_implies_extends; eauto.
      intros b0 A. unfold Mem.valid_block in A; rewrite EQNEXT, <- dom_eq_src in A. eapply Bset.inj_dom in A; eauto.
      destruct A as [b' A]. unfold Bset.inj_to_meminj. rewrite A. eauto.
      inv GE_INIT_INJ. rewrite mu_shared_src in dom_eq_src. rewrite mu_shared_tgt in dom_eq_tgt. rewrite S_EQ in dom_eq_src.
      assert (forall b, Plt b (Mem.nextblock sm0) <-> Plt b (Mem.nextblock tm0)).
      { intro. rewrite <- dom_eq_src, <- dom_eq_tgt. tauto. }
      rewrite EQNEXT, EQNEXT0.
      destruct (Pos.lt_total (Mem.nextblock sm0) (Mem.nextblock tm0)) as [LT | [EQ | LT]]; auto;
        (generalize H4 LT; clear; intros; exfalso; apply H4 in LT; eapply Pos.lt_irrefl; eauto). }
    apply FP.subset_emp.
    split.
    inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_src; auto.
    split.
    inv MEMINITINJ. inv LRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto.    
    split.
    inv MEMINITINJ; econstructor; eauto. simpl. intro.
    intros ? ? ? ? ? . exploit inj_inject_id. exact H0. intro. inv H1.
    intro A. inv A. auto.
    split; auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
    
  - (* tau step*)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP. simpl in STEP.
    revert i mu Hfp Lfp Lcore Lm MS.
    induction STEP; intros until Lm; intros MS'; invMS; inv MS; try (monadInv TS).
    + (* skip seq *)
      inv MC. Right. econstructor. FP. splitMS.
    + (* skip block *)
      inv MC. Right. econstructor. FP. splitMS.
    + (* skip call *)
      exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
      Right. econstructor; eauto. inv MC; simpl in H; auto. erewrite stackspace_function_translated; eauto.
      erewrite stackspace_function_translated; eauto. FP. 
      splitMS. eapply match_is_call_cont; eauto. 
    + (* assign *)
      exploit sel_expr_correct_fp; eauto. intros (v' & fp' & A & B & A' & B').
      Right. econstructor; eauto. FP. splitMS. apply set_var_lessdef; auto.
    + (* store *)
      exploit sel_expr_correct_fp; try exact H; eauto. intros (vaddr' & fp1' & A & B & A' & B').
      exploit sel_expr_correct_fp; try exact H1; eauto. intros (v' & fp2' & C & D & C' & D').
      exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
      Right. eapply eval_store_fp; eauto.
      destruct vaddr; try discriminate. inv B. simpl in H3, P.
      FP. repeat apply Injections.fp_match_union'; resolvfp.
      splitMS. 
    + (* Scall *)
      exploit classify_call_correct; eauto.
      destruct (classify_call (comp_unit_defmap scu) a) as [ | id | ef] eqn:CC.
      ++ (* indirect *)
        exploit sel_expr_correct_fp; eauto. intros (vf' & fp1' & A & B & A' & B').
        exploit sel_exprlist_correct_fp; eauto. intros (vargs' & fp2' & C & D & C' & D').
        exploit functions_translated; eauto. intros (fd' & U & V ).
        Right. econstructor; eauto. econstructor; eauto. econstructor; eauto.
        eapply sig_function_translated; eauto.
        FP. splitMS. red; intros. eapply match_cont_call with (hf := hf); eauto. 
      ++ (* direct *)
        intros [b [U V]].
        exploit sel_exprlist_correct_fp; eauto. intros (vargs' & fp2' & C & D & C' & D').
        exploit functions_translated; eauto. intros (fd' & X & Y).
        Right. econstructor; eauto. subst vf. econstructor; eauto. rewrite symbols_preserved; eauto.
        econstructor; eauto. rewrite symbols_preserved; eauto.
        eapply sig_function_translated; eauto.
        FP. rewrite FP.union_comm_eq. apply Injections.fp_match_union_S'; resolvfp.
        splitMS. red; intros; eapply match_cont_call with (hf := hf); eauto.
      ++ (* turned into Sbuiltin *)
        (* which we do not support currently *)
        intros EQ. subst fd.
        assert (INLINE: ef_inline ef = true).
        { revert CC; clear. unfold classify_call, ef_inline.
          do 4 match goal with | |- context[match ?x with _ => _ end] => destruct x eqn:?; try discriminate end.
          destruct e, ef; try discriminate; auto. }
        exploit sel_builtin_args_correct_fp; eauto. intros (vargs' & fp2' & C & D & C' & D').
        Left. destruct INDEX. subst. auto.
        splitMS. rewrite (FP.union_comm_eq); resolvfp.
    + (* Stailcall *)
      exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
      erewrite <- stackspace_function_translated in P by eauto.
      exploit sel_expr_correct_fp; eauto. intros (vf' & fp1' & A & B & A' & B').
      exploit sel_exprlist_correct_fp; eauto. intros (vargs' & fp2' & C & D & C' & D').
      exploit functions_translated; eauto. intros (fd' & E & F).
      Right. exploit classify_call_correct. eauto. eauto. 
      destruct (classify_call (comp_unit_defmap scu)) as [ | id | ef] eqn:CC; intros.
      (* *)repeat econstructor; eauto. eapply sig_function_translated; eauto.
      (* *) destruct H4 as [b [U V]]. subst vf. inv B.
      econstructor. econstructor. rewrite symbols_preserved; eauto.
      econstructor. rewrite symbols_preserved; eauto. eauto. eauto. eauto.
      eapply sig_function_translated; eauto. eauto. eauto.
      assert (fp1' = empfp).
      { generalize CC A'; clear; intros.
        unfold classify_call in CC. destruct a; simpl in CC; try discriminate.
        repeat match goal with
                 CC: context[match ?x with _ => _ end] |- _ =>
                 destruct x eqn:?; try discriminate; unfold addrsymbol, Olea_ptr in *;
                   InvEvalFP; InvEval; simpl in *; FuncInv; subst; TrivFP
               end. }
      subst. TrivFP.
      (* *) econstructor; eauto. econstructor; eauto. econstructor; eauto.
      eapply sig_function_translated; eauto.
      erewrite stackspace_function_translated; eauto.
      FP. repeat apply Injections.fp_match_union'; resolvfp.
      splitMS. eapply call_cont_commut; eauto.
      erewrite stackspace_function_translated; eauto. Lia.lia.
    + (* Seq *)
      Right. constructor. FP. splitMS. econstructor; eauto. 
    + (* Sifthenelse *)
      exploit sel_expr_correct_fp; eauto. intros (v' & fp' & A & B & A' & B').
      assert (Val.bool_of_val v' b). inv B. auto. inv H1.
      exploit eval_condexpr_of_expr_fp; eauto. intros [C C'].
      Right. econstructor; eauto. FP.
      splitMS. destruct b; auto.
    + (* Sloop *)
      Right. econstructor. FP. splitMS.
      constructor; auto. simpl; rewrite EQ; auto.
    + (* Sblock *)
      Right. econstructor. FP. splitMS. constructor; auto.
    + (* Sexit seq *)
      inv MC. Right. econstructor. FP. splitMS.
    + (* Sexit0 block *)
      inv MC. Right. econstructor. FP. splitMS.
    + (* SexitS block *)
      inv MC. Right. econstructor. FP. splitMS.
    + (* Sswitch *)
      inv H1; simpl in TS.
      ++ set (ct := compile_switch Int.modulus default cases) in *.
         destruct (validate_switch Int.modulus default cases ct) eqn:VALID; inv TS.
         exploit sel_expr_correct_fp; eauto. intros (v' & fp' & A & B & A' & B'). inv B.
         exploit sel_switch_int_correct_fp; eauto. intros [C C'].
         Right. econstructor; eauto. FP. splitMS.
      ++ set (ct := compile_switch Int64.modulus default cases) in *.
         destruct (validate_switch Int64.modulus default cases ct) eqn:VALID; inv TS.
         exploit sel_expr_correct_fp; eauto. intros (v' & fp' & A & B & A' & B'). inv B.
         exploit sel_switch_long_correct_fp; eauto. intros [C C'].
         Right. econstructor; eauto. FP. splitMS.
    + (* Sreturn None *)
      exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
      erewrite <- stackspace_function_translated in * by eauto.
      Right. econstructor; simpl; eauto. FP. splitMS.
      eapply call_cont_commut; eauto.
    + (* Sreturn Some *)
      exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
      erewrite <- stackspace_function_translated in * by eauto.
      exploit sel_expr_correct_fp; eauto. intros [v' [fp' [A [B [A' B']]]]].
      Right. econstructor; eauto. FP. splitMS.
      eapply call_cont_commut; eauto.
    + (* Slabel *)
      Right. econstructor; eauto. FP. splitMS.
    + (* Sgoto *)
      assert (sel_stmt (comp_unit_defmap scu) (Cminor.fn_body f) = OK (fn_body f')).
      { monadInv TF; simpl; auto. }
      exploit (find_label_commut hf lbl (Cminor.fn_body f) (Cminor.call_cont k)).
      eapply call_cont_commut; eauto. eauto. rewrite H.
      destruct (find_label lbl (fn_body f') (call_cont k'0))
        as [[s'' k'']|] eqn:?; intros; try contradiction.
      destruct H1. Right. econstructor; eauto. FP. splitMS.
    + (* internal function *)
      destruct TF as (hf & HF & TF). specialize (MC hf). 
      monadInv TF. generalize EQ; intros TF; monadInv TF.
      exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. intros [m2' [A B]].
      Right. econstructor; simpl; eauto. FP. unfold alloc_fp. erewrite Mem.mext_next; eauto. resolvfp.
      splitMS. apply set_locals_lessdef. apply set_params_lessdef; auto.
      unfold alloc_fp. erewrite <- Mem.mext_next; eauto. resolvfp.
    
    + (* return *)
      apply match_call_cont_cont in MC. destruct MC as (hf0 & MC). inv MC.
      Right. econstructor. FP. splitMS.
      destruct optid; simpl; auto. apply set_var_lessdef; auto.
      
  - (* at external *)
    simpl in *. unfold Cminor_local.at_external, at_external.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MS ATEXT RC GARG.
    destruct Hcore; try discriminate. destruct f0; try discriminate. destruct e eqn:?; try discriminate.
    destruct (invert_symbol_from_string sge name) eqn:SYMBNAME; try discriminate.
    destruct peq; simpl in *. discriminate.
    destruct peq; simpl in *. discriminate. inv ATEXT.
    invMS; inv MS; try discriminate.
    destruct TF as [hf0 [HF0 SEL]]. simpl in SEL. inv SEL. 
    erewrite match_genvs_invert_symbol_from_string_preserved; eauto.
    Ex_index. destruct peq; try contradiction. destruct peq; try contradiction.
    eexists. simpl. split; auto. split.
    { simpl in *. unfold LDSimDefs.arg_rel. revert args' AGMU LD GARG; clear.
      (** should be extracted as a lemma ... *)
      induction argSrc; intros. simpl. inv LD. auto. inv LD. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto. destruct v2; auto.
      simpl in H2. eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H; eauto.
      intro. inv H0. econstructor. unfold Bset.inj_to_meminj; rewrite H. eauto. rewrite Ptrofs.add_zero; auto. }
    split. eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    split; eresolvfp. split.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    splitMS. eexists; eauto. eapply match_cu_match_genv; eauto.
    intros. inv H; auto. destruct H0 as [hf' [HF' SEL']]. destruct f1; monadInv SEL'; auto.
    
  - (* after external *)
    simpl. unfold Cminor_local.after_external, after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    destruct Hcore; try discriminate. destruct f; try discriminate. destruct e; try discriminate.
    invMS; inv MS; try discriminate. destruct TF as [hf0 [HF0 TF]]. monadInv TF. 
    assert (Hcore' = Cminor_local.Core_Returnstate (match oresSrc with Some v => v | None => Vundef end) k).
    { destruct oresSrc, (sig_res sg); inv AFTEXT; auto. 
      destruct (val_has_type_func v t); inv H0. auto. } 
    assert (match oresSrc, (sig_res sg) with
            | None, None => True
            | Some v, Some ty => Val.has_type v ty
            | _, _ => False
            end) as HRES.
    { destruct oresSrc, (sig_res sg); inv AFTEXT; auto.
      destruct (val_has_type_func v t) eqn:A; inv H1. apply val_has_type_funcP; auto. }
    clear AFTEXT. rename H into AFTEXT.
    exists (Core_Returnstate (match oresTgt with Some v => v | None => Vundef end) k'). split.
    { destruct oresSrc, oresTgt, (sig_res sg); try contradiction; auto.
      inv RESREL; destruct t; try contradiction; simpl in *; auto. rewrite HRES. auto. }
    intros Hm' Lm' [HRELY LRELY INV]. subst. Ex_index. splitMS.
    { destruct oresSrc, (sig_res sg), oresTgt; simpl in *; try contradiction; auto.
      inv RESREL; auto. inv AGMU. apply proper_mu_inject_incr in H. inv H. rewrite Ptrofs.add_zero. auto. }
    inv AGMU; eapply extends_rely_extends; eauto. econstructor; eauto.
    intros ? S. apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT; auto.
    intros ? T. apply TVALID in T. unfold Mem.valid_block in *. inv LRELY. rewrite EQNEXT; auto.
    inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
  - (* halt *)
    simpl. unfold Cminor_local.halted, halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES. destruct Hcore, k; try discriminate.
    inv HALT. invMS; inv MS.  apply match_call_cont_cont in MC. destruct MC as (hf0 & MC). inv MC. exists resSrc. 
    split. { f_equal. inv LD; auto. contradiction. } split.
    { revert AGMU GRES. clear; intros. (** should be extracted to lemma *)
      destruct resSrc; try constructor. econstructor. simpl in GRES. inv AGMU.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. inv A. unfold Bset.inj_to_meminj; rewrite INJ; eauto. rewrite Ptrofs.add_zero; auto. }
    split. inv AGMU; eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto.
    split. resolvfp. inv AGMU; eapply extends_reach_closed_implies_inject; eauto.
Qed.

End PRESERVATION.

Theorem transf_local_ldsim:
  forall scu tcu,
    selection.transf_program scu = OK tcu ->
    forall sge sG tge tG,
      init_genv_local Cminor_IS scu sge sG ->
      init_genv_local CminorSel_IS tcu tge tG ->
      Genv.genv_next sge = Genv.genv_next tge ->
      local_ldsim sG tG sge tge.
Proof.
  intros. inv H0. inv H1. eapply TRANSF_local_ldsim; eauto.
  apply transf_program_match. auto.
Qed.