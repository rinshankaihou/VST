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

(** Correctness proof for RTL generation. *)

Require Import Coqlib Maps AST Linking.
Require Import Integers Values Memory Events Smallstep Globalenvs.
Require Import Switch Registers Cminor Op CminorSel RTL.
Require Import RTLgen RTLgenspec.

Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        MemOpFP Op_fp helpers CminorSel_local RTL_local rtlgen.

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.

(** * Correspondence between Cminor environments and RTL register sets *)

(** A compilation environment (mapping) is well-formed if
  the following properties hold:
- Two distinct Cminor local variables are mapped to distinct pseudo-registers.
- A Cminor local variable and a let-bound variable are mapped to
  distinct pseudo-registers.
*)

Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.

Lemma init_mapping_wf:
  map_wf init_mapping.
Proof.
  unfold init_mapping; split; simpl.
  intros until r. rewrite PTree.gempty. congruence.
  tauto.
Qed.

Lemma add_var_wf:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  intros. monadInv H.
  apply mk_map_wf; simpl.
  intros until r0. repeat rewrite PTree.gsspec.
  destruct (peq id1 name); destruct (peq id2 name).
  congruence.
  intros. inv H. elimtype False.
  apply valid_fresh_absurd with r0 s1.
  apply H1. left; exists id2; auto.
  eauto with rtlg.
  intros. inv H2. elimtype False.
  apply valid_fresh_absurd with r0 s1.
  apply H1. left; exists id1; auto.
  eauto with rtlg.
  inv H0. eauto.
  intros until r0. rewrite PTree.gsspec.
  destruct (peq id name).
  intros. inv H.
  apply valid_fresh_absurd with r0 s1.
  apply H1. right; auto.
  eauto with rtlg.
  inv H0; eauto.
Qed.

Lemma add_vars_wf:
  forall names s1 s2 map map' rl i,
  add_vars map names s1 = OK (rl,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  induction names; simpl; intros; monadInv H.
  auto.
  exploit add_vars_valid; eauto. intros [A B].
  eapply add_var_wf; eauto.
Qed.

Lemma add_letvar_wf:
  forall map r,
  map_wf map -> ~reg_in_map map r -> map_wf (add_letvar map r).
Proof.
  intros. inv H. unfold add_letvar; constructor; simpl.
  auto.
  intros. elim H1; intro. subst r0. elim H0. left; exists id; auto.
  eauto.
Qed.

(** An RTL register environment matches a CminorSel local environment and
  let-environment if the value of every local or let-bound variable in
  the CminorSel environments is identical to the value of the
  corresponding pseudo-register in the RTL register environment. *)

Record match_env
      (map: mapping) (e: env) (le: letenv) (rs: regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ Val.lessdef v rs#r);
    me_letvars:
      Val.lessdef_list le rs##(map.(map_letvars))
  }.

Lemma match_env_find_var:
  forall map e le rs id v r,
  match_env map e le rs ->
  e!id = Some v ->
  map.(map_vars)!id = Some r ->
  Val.lessdef v rs#r.
Proof.
  intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
  replace r with r'. auto. congruence.
Qed.

Lemma match_env_find_letvar:
  forall map e le rs idx v r,
  match_env map e le rs ->
  List.nth_error le idx = Some v ->
  List.nth_error map.(map_letvars) idx = Some r ->
  Val.lessdef v rs#r.
Proof.
  intros. exploit me_letvars; eauto.
  clear H. revert le H0 H1. generalize (map_letvars map). clear map.
  induction idx; simpl; intros.
  inversion H; subst le; inversion H0. subst v1.
  destruct l; inversion H1. subst r0.
  inversion H2. subst v2. auto.
  destruct l; destruct le; try discriminate.
  eapply IHidx; eauto.
  inversion H. auto.
Qed.

Lemma match_env_invariant:
  forall map e le rs rs',
  match_env map e le rs ->
  (forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
  match_env map e le rs'.
Proof.
  intros. inversion H. apply mk_match_env.
  intros. exploit me_vars0; eauto. intros [r [A B]].
  exists r; split. auto. rewrite H0; auto. left; exists id; auto.
  replace (rs'##(map_letvars map)) with (rs ## (map_letvars map)). auto.
  apply list_map_exten. intros. apply H0. right; auto.
Qed.

(** Matching between environments is preserved when an unmapped register
  (not corresponding to any Cminor variable) is assigned in the RTL
  execution. *)

Lemma match_env_update_temp:
  forall map e le rs r v,
  match_env map e le rs ->
  ~(reg_in_map map r) ->
  match_env map e le (rs#r <- v).
Proof.
  intros. apply match_env_invariant with rs; auto.
  intros. case (Reg.eq r r0); intro.
  subst r0; contradiction.
  apply Regmap.gso; auto.
Qed.
Hint Resolve match_env_update_temp: rtlg.

(** Matching between environments is preserved by simultaneous
  assignment to a Cminor local variable (in the Cminor environments)
  and to the corresponding RTL pseudo-register (in the RTL register
  environment). *)

Lemma match_env_update_var:
  forall map e le rs id r v tv,
  Val.lessdef v tv ->
  map_wf map ->
  map.(map_vars)!id = Some r ->
  match_env map e le rs ->
  match_env map (PTree.set id v e) le (rs#r <- tv).
Proof.
  intros. inversion H0. inversion H2. apply mk_match_env.
  intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
  subst id'. inv H3. exists r; split. auto. rewrite PMap.gss. auto.
  exploit me_vars0; eauto. intros [r' [A B]].
  exists r'; split. auto. rewrite PMap.gso; auto.
  red; intros. subst r'. elim n. eauto.
  erewrite list_map_exten. eauto.
  intros. symmetry. apply PMap.gso. red; intros. subst x. eauto.
Qed.

(** A variant of [match_env_update_var] where a variable is optionally
  assigned to, depending on the [dst] parameter. *)

Lemma match_env_update_dest:
  forall map e le rs dst r v tv,
  Val.lessdef v tv ->
  map_wf map ->
  reg_map_ok map r dst ->
  match_env map e le rs ->
  match_env map (set_optvar dst v e) le (rs#r <- tv).
Proof.
  intros. inv H1; simpl.
  eapply match_env_update_temp; eauto.
  eapply match_env_update_var; eauto.
Qed.
Hint Resolve match_env_update_dest: rtlg.

(** A variant of [match_env_update_var] corresponding to the assignment
  of the result of a builtin. *)

Lemma match_env_update_res:
  forall map res v e le tres tv rs,
  Val.lessdef v tv ->
  map_wf map ->
  tr_builtin_res map res tres ->
  match_env map e le rs ->
  match_env map (set_builtin_res res v e) le (regmap_setres tres tv rs).
Proof.
  intros. inv H1; simpl.
- eapply match_env_update_var; eauto.
- auto.
- eapply match_env_update_temp; eauto.
Qed.

(** Matching and [let]-bound variables. *)

Lemma match_env_bind_letvar:
  forall map e le rs r v,
  match_env map e le rs ->
  Val.lessdef v rs#r ->
  match_env (add_letvar map r) e (v :: le) rs.
Proof.
  intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed.

Lemma match_env_unbind_letvar:
  forall map e le rs r v,
  match_env (add_letvar map r) e (v :: le) rs ->
  match_env map e le rs.
Proof.
  unfold add_letvar; intros. inv H. simpl in *.
  constructor. auto. inversion me_letvars0. auto.
Qed.

(** Matching between initial environments. *)

Lemma match_env_empty:
  forall map,
  map.(map_letvars) = nil ->
  match_env map (PTree.empty val) nil (Regmap.init Vundef).
Proof.
  intros. apply mk_match_env.
  intros. rewrite PTree.gempty in H0. discriminate.
  rewrite H. constructor.
Qed.

(** The assignment of function arguments to local variables (on the Cminor
  side) and pseudo-registers (on the RTL side) preserves matching
  between environments. *)

Lemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl tvl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  Val.lessdef_list vl tvl ->
  match_env map2 (set_params vl il) nil (init_regs tvl rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs tvl rl)#r = Vundef).
Proof.
  induction il; intros.

  inv H. split. apply match_env_empty. auto. intros.
  simpl. apply Regmap.gi.

  monadInv H. simpl.
  exploit add_vars_valid; eauto. apply init_mapping_valid. intros [A B].
  exploit add_var_valid; eauto. intros [A' B']. clear B'.
  monadInv EQ1.
  destruct H0 as [ | v1 tv1 vs tvs].
  (* vl = nil *)
  destruct (IHil _ _ _ _ nil nil _ EQ) as [ME UNDEF]. constructor. inv ME. split.
  replace (init_regs nil x) with (Regmap.init Vundef) in me_vars0, me_letvars0.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. constructor.
  eauto.
  eauto.
  destruct x; reflexivity.
  intros. apply Regmap.gi.
  (* vl = v1 :: vs *)
  destruct (IHil _ _ _ _ _ _ _ EQ H0) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. inv H1. exists x1; split. auto. rewrite Regmap.gss. constructor.
  inv H1. eexists; eauto.
  exploit me_vars0; eauto. intros [r' [C D]].
  exists r'; split. auto. rewrite Regmap.gso. auto.
  apply valid_fresh_different with s.
  apply B. left; exists id; auto.
  eauto with rtlg.
  destruct (map_letvars x0). auto. simpl in me_letvars0. inversion me_letvars0.
  intros. rewrite Regmap.gso. apply UNDEF.
  apply reg_fresh_decr with s2; eauto with rtlg.
  apply sym_not_equal. apply valid_fresh_different with s2; auto.
Qed.

Lemma match_set_locals:
  forall map1 s1,
  map_wf map1 ->
  forall il rl map2 s2 e le rs i,
  match_env map1 e le rs ->
  (forall r, reg_fresh r s1 -> rs#r = Vundef) ->
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  match_env map2 (set_locals il e) le rs.
Proof.
  induction il; simpl in *; intros.

  inv H2. auto.

  monadInv H2.
  exploit IHil; eauto. intro.
  monadInv EQ1.
  constructor.
  intros id v. simpl. repeat rewrite PTree.gsspec.
  destruct (peq id a). subst a. intro.
  exists x1. split. auto. inv H3. constructor.
  eauto with rtlg.
  intros. eapply me_vars; eauto.
  simpl. eapply me_letvars; eauto.
Qed.

Lemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  Val.lessdef_list vparams tvparams ->
  match_env map2 (set_locals vars (set_params vparams params))
            nil (init_regs tvparams rparams).
Proof.
  intros.
  exploit match_set_params_init_regs; eauto. intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  apply init_mapping_valid.
Qed.

(** * The simulation argument *)

Require Import Errors.

Definition match_cu (scu: cminorsel_comp_unit) (tcu: RTL_comp_unit) :=
  match_comp_unit_gen (fun f tf => transl_fundef f = Errors.OK tf) eq scu tcu.

Lemma transf_program_match:
  forall scu tcu, transf_program scu = OK tcu -> match_cu scu tcu.
Proof.
  intros. eapply match_transform_partial_cunit; eauto.
Qed.


Section CORRECTNESS.

Variable scu: cminorsel_comp_unit.
Variable tcu: RTL_comp_unit.
Hypothesis TRANSL: match_cu scu tcu.

Variable sge sG: CminorSel.genv.
Variable tge tG: RTL.genv.

Hypothesis GE_INIT: CminorSel_IS.(init_genv_local) scu sge sG.
Hypothesis TGE_INIT: RTL_IS.(init_genv_local) tcu tge tG.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).


Lemma ge_match: ge_match_strict sge tge.
Proof. inv GE_INIT. inv TGE_INIT. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma genv_match: Genv.match_genvs (match_globdef (fun f tf => transl_fundef f = Errors.OK tf) eq) sge tge.
Proof. eapply match_cu_match_genv; eauto. inv GE_INIT; auto. inv TGE_INIT; auto. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof. destruct genv_match. auto. Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: CminorSel.fundef),
  Genv.find_funct_ptr sge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof.
  destruct genv_match.
  unfold CminorSel.fundef, RTL.fundef in *. simpl in *.
  unfold Genv.find_funct_ptr, Genv.find_def; intros. specialize (mge_defs b). inv mge_defs.
  rewrite <- H1 in H. discriminate.
  rewrite <- H0 in H. destruct x; inv H.
  inv H2. eauto.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct sge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof.
  destruct v; simpl; intros; try discriminate.
  destruct Ptrofs.eq_dec; [|discriminate].
  apply function_ptr_translated; auto.
Qed.

Lemma sig_transl_function:
  forall (f: CminorSel.fundef) (tf: RTL.fundef),
  transl_fundef f = OK tf ->
  RTL.funsig tf = CminorSel.funsig f.
Proof.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function.
  destruct (reserve_labels (fn_body f0) (PTree.empty node, init_state)) as [ngoto s0].
  case (transl_fun f0 ngoto s0); simpl; intros.
  discriminate.
  destruct p. simpl in H. inversion H. reflexivity.
  intro. inversion H. reflexivity.
Qed.

Lemma senv_preserved:
  Senv.equiv sge tge.
Proof. inv GE_INIT. inv TGE_INIT. eapply match_cu_senv_preserved; eauto. Qed.

(** Correctness of the code generated by [add_move]. *)

Lemma tr_move_correct:
  forall r1 ns r2 nd cs f sp rs m,
  tr_move f.(fn_code) ns r1 nd r2 ->
  exists rs',
    star (step tge) (Core_State cs f sp ns rs) m empfp (Core_State cs f sp nd rs') m /\
    rs'#r2 = rs#r1 /\
    (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H.
  exists rs; split. constructor. auto.
  exists (rs#r2 <- (rs#r1)); split.
  apply star_one. eapply exec_Iop. eauto. auto. auto.
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

(** ** Semantic preservation for the translation of expressions *)

Section CORRECTNESS_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

(** The proof of semantic preservation for the translation of expressions
  is a simulation argument based on diagrams of the following form:
<<
                    I /\ P
    e, le, m, a ------------- State cs code sp ns rs tm
         ||                      |
         ||                      |*
         ||                      |
         \/                      v
    e, le, m, v ------------ State cs code sp nd rs' tm'
                    I /\ Q
>>
  where [tr_expr code map pr a ns nd rd] is assumed to hold.
  The left vertical arrow represents an evaluation of the expression [a].
  The right vertical arrow represents the execution of zero, one or
  several instructions in the generated RTL flow graph [code].

  The invariant [I] is the agreement between Cminor environments and
  RTL register environment, as captured by [match_envs].

  The precondition [P] includes the well-formedness of the compilation
  environment [mut].

  The postconditions [Q] state that in the final register environment
  [rs'], register [rd] contains value [v], and the registers in
  the set of preserved registers [pr] are unchanged, as are the registers
  in the codomain of [map].

  We formalize this simulation property by the following predicate
  parameterized by the CminorSel evaluation (left arrow).  *)


(** Modification: 
    add constraints on footprints *)

Definition transl_expr_fp_prop
           (le: letenv) (a: expr) (v: val) (fp: footprint): Prop :=
  forall tm cs f map pr ns nd rd rs dst
    (MWF: map_wf map)
    (TE: tr_expr f.(fn_code) map pr a ns nd rd dst)
    (ME: match_env map e le rs)
    (EXT: Mem.extends m tm),
  exists rs', exists fp',
      star (step tge) (Core_State cs f sp ns rs) tm fp' (Core_State cs f sp nd rs') tm
      /\ match_env map (set_optvar dst v e) le rs'
      /\ Val.lessdef v rs'#rd
      /\ (forall r, In r pr -> rs'#r = rs#r)
      /\ FP.subset fp' fp.

Definition transl_exprlist_fp_prop
     (le: letenv) (al: exprlist) (vl: list val) (fp: footprint): Prop :=
  forall tm cs f map pr ns nd rl rs
    (MWF: map_wf map)
    (TE: tr_exprlist f.(fn_code) map pr al ns nd rl)
    (ME: match_env map e le rs)
    (EXT: Mem.extends m tm),
  exists rs', exists fp', 
     star (step tge) (Core_State cs f sp ns rs) tm fp' (Core_State cs f sp nd rs') tm
  /\ match_env map e le rs'
  /\ Val.lessdef_list vl rs'##rl
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ FP.subset fp' fp.

Definition transl_condexpr_fp_prop
     (le: letenv) (a: condexpr) (v: bool) (fp: footprint): Prop :=
  forall tm cs f map pr ns ntrue nfalse rs
    (MWF: map_wf map)
    (TE: tr_condition f.(fn_code) map pr a ns ntrue nfalse)
    (ME: match_env map e le rs)
    (EXT: Mem.extends m tm),
  exists rs', exists fp', 
     plus (step tge) (Core_State cs f sp ns rs) tm fp' (Core_State cs f sp (if v then ntrue else nfalse) rs') tm
  /\ match_env map e le rs'
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ FP.subset fp' fp.

(** The correctness of the translation is a huge induction over
  the CminorSel evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each CminorSel evaluation rule.
  It takes as hypotheses the premises of the CminorSel evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma transl_expr_fp_Evar_correct:
  forall (le : letenv) (id : positive) (v: val),
  e ! id = Some v ->
  transl_expr_fp_prop le (Evar id) v empfp.
Proof.
  intros; red; intros. inv TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit tr_move_correct; eauto. intros [rs' [A [B C]]].
  exists rs'; exists empfp; split. eauto. destruct H2 as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto.
  split. eapply match_env_invariant; eauto.
  split. congruence. split. auto. 
  constructor; cbv; discriminate.
  (* general case *)
  split. apply match_env_invariant with (rs#rd <- (rs#r)). apply match_env_update_dest; auto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto.
  split. congruence. split. intros. apply C. intuition congruence.
  constructor; cbv; discriminate.
Qed.

Lemma transl_expr_fp_Eop_correct:
  forall (le : letenv) (op : operation) (args : exprlist)
         (vargs : list val) fp1 (v : val) fp2,
  eval_exprlist sge sp e m le args vargs ->
  eval_exprlist_fp sge sp e m le args fp1 ->
  transl_exprlist_fp_prop le args vargs fp1 ->
  eval_operation sge sp op vargs m = Some v ->
  eval_operation_fp sge sp op vargs m = Some fp2 ->
  transl_expr_fp_prop le (Eop op args) v (FP.union fp1 fp2).
Proof.
  intros. red. intros. inv TE.
(* normal case *)
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [RR1 [RO1 HFP1]]]]]].
  edestruct eval_operation_lessdef as [v' []]; eauto.
  edestruct eval_operation_lessdef_fp as [fp2' []]; eauto.
  exists (rs1#rd <- v'); exists (FP.union fp1' fp2').
(* Exec *)
  split. eapply star_right. eexact EX1.
  eapply exec_Iop; eauto.
  rewrite (@eval_operation_preserved CminorSel.fundef _ _ _ sge tge). eauto.
  exact symbols_preserved.
  rewrite (@eval_operation_fp_preserved CminorSel.fundef _ _ _ sge tge). eauto.
  exact symbols_preserved. auto.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Footprint *)
  apply fp_inject_id_fp_subset in H9. apply FP.subset_parallel_union; auto.
Qed.

Lemma transl_expr_fp_Eload_correct:
  forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) fp1 (vargs : list val) (vaddr v : val),
  eval_exprlist sge sp e m le args vargs ->
  eval_exprlist_fp sge sp e m le args fp1 -> 
  transl_exprlist_fp_prop le args vargs fp1 ->
  Op.eval_addressing sge sp addr vargs = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  transl_expr_fp_prop le (Eload chunk addr args) v (FP.union fp1 (loadv_fp chunk vaddr)).
Proof.
  intros; red; intros. inv TE.
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [RES1 [OTHER1 HFP1]]]]]].
  edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
  edestruct Mem.loadv_extends as [v' []]; eauto.
  exists (rs1#rd <- v'); exists (FP.union fp1' (loadv_fp chunk vaddr')).
(* Exec *)
  split. eapply star_right. eexact EX1. eapply exec_Iload. eauto. 
  instantiate (1 := vaddr'). rewrite <- H4.
  apply eval_addressing_preserved. exact symbols_preserved.
  auto. eauto. auto.
(* Match-env *)
  split. eauto with rtlg.
(* Result *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Footprint *)
  destruct vaddr; simpl in H3; try discriminate. inv H5.
  apply FP.union2_subset; auto.
Qed.

Lemma transl_expr_fp_Econdition_correct:
  forall (le : letenv) (a: condexpr) (ifso ifnot : expr)
         (va : bool) fp1 (v : val) fp2,
  eval_condexpr sge sp e m le a va ->
  eval_condexpr_fp sge sp e m le a fp1 ->
  transl_condexpr_fp_prop le a va fp1 ->
  eval_expr sge sp e m le (if va then ifso else ifnot) v ->
  eval_expr_fp sge sp e m le (if va then ifso else ifnot) fp2 ->
  transl_expr_fp_prop le (if va then ifso else ifnot) v fp2 ->
  transl_expr_fp_prop le (Econdition a ifso ifnot) v (FP.union fp1 fp2).
Proof.
  intros; red; intros; inv TE.
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [OTHER1  HFP1]]]]].
  assert (tr_expr f.(fn_code) map pr (if va then ifso else ifnot) (if va then ntrue else nfalse) nd rd dst).
    destruct va; auto.
  exploit H4; eauto. intros [rs2 [fp2' [EX2 [ME2 [RES2 [OTHER2 HFP2]]]]]].
  exists rs2; exists (FP.union fp1' fp2').
(* Exec *)
  split. eapply star_trans. apply plus_star. eexact EX1. eexact EX2. traceEq.
(* Match-env *)
  split. assumption.
(* Result value *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r); auto.
(* Footprint *)
  apply FP.subset_parallel_union; auto.
Qed.

Lemma transl_expr_fp_Elet_correct:
  forall (le : letenv) (a1 a2 : expr) (v1 v2 : val) fp1 fp2,
  eval_expr sge sp e m le a1 v1 ->
  eval_expr_fp sge sp e m le a1 fp1 ->
  transl_expr_fp_prop le a1 v1 fp1 ->
  eval_expr sge sp e m (v1 :: le) a2 v2 ->
  eval_expr_fp sge sp e m (v1 :: le) a2 fp2 ->
  transl_expr_fp_prop (v1 :: le) a2 v2 fp2 ->
  transl_expr_fp_prop le (Elet a1 a2) v2 (FP.union fp1 fp2).
Proof.
  intros; red; intros; inv TE.
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [RES1 [OTHER1 HFP1]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H4; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [fp2' [EX2 [ME3 [RES2 [OTHER2 HFP2]]]]]].
  exists rs2; exists (FP.union fp1' fp2').
(* Exec *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r0); auto.
(* Footprint *)
  apply FP.subset_parallel_union; auto.
Qed.

Lemma transl_expr_fp_Eletvar_correct:
  forall (le : list val) (n : nat) (v : val),
  nth_error le n = Some v ->
  transl_expr_fp_prop le (Eletvar n) v empfp.
Proof.
  intros; red; intros; inv TE.
  exploit tr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
  exists rs1; exists empfp.
(* Exec *)
  split. eexact EX1.
(* Match-env *)
  split.
  destruct H2 as [[A B] | [A B]].
  subst r dst; simpl.
  apply match_env_invariant with rs. auto.
  intros. destruct (Reg.eq r rd). subst r. auto. auto.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  eapply match_env_find_letvar; eauto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
  congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto.
(* Other regs *)
  split. intros.
  destruct H2 as [[A B] | [A B]].
  destruct (Reg.eq r0 rd); subst; auto.
  apply OTHER1. intuition congruence.
(* Footprint *)
  clear; constructor; cbv; auto.
Qed.

Remark eval_builtin_args_trivial:
  forall (ge: RTL.genv) (rs: regset) sp m rl,
  eval_builtin_args ge (fun r => rs#r) sp m (List.map (@BA reg) rl) rs##rl.
Proof.
  induction rl; simpl.
- constructor.
- constructor; auto. constructor.
Qed.

Remark eval_builtin_args_fp_trivial:
  forall (ge: RTL.genv) (rs: regset) sp rl,
    eval_builtin_args_fp ge (fun r => rs#r) sp (List.map (@BA reg) rl) empfp.
Proof.
  clear. induction rl. constructor.
  econstructor; eauto. constructor. rewrite FP.fp_union_emp; auto.
Qed.

Lemma transl_expr_fp_Ebuiltin_correct:
  forall le ef al vl fp v,
    eval_exprlist sge sp e m le al vl ->
    eval_exprlist_fp sge sp e m le al fp ->
    transl_exprlist_fp_prop le al vl fp ->
    i64ext ef ->
    external_call ef sge vl m E0 v m ->
    transl_expr_fp_prop le (Ebuiltin ef al) v fp.
Proof.
  intros; red; intros. inv TE.
  exploit H1; eauto. intros [rs1 [fp1 [EX1 [ME1 [RR1 [RO1 HFP1]]]]]].
  exploit external_call_mem_extends; eauto.
  intros [v' [tm2 [A [B [_ _ ]]]]]. exploit i64ext_effects; eauto. intros [X _]; subst.
  exists (rs1#rd <- v'), fp1.
(* Exec *)
  split. eapply star_right. eexact EX1.
  change (rs1#rd <- v') with (regmap_setres (BR rd) v' rs1).
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_trivial.
  eapply eval_builtin_args_fp_trivial; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  rewrite FP.fp_union_emp; auto.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* FP *)
  auto.
Qed.

Lemma transl_expr_fp_Eexternal_correct:
  forall le id sg al b ef vl fp v,
  Genv.find_symbol sge id = Some b ->
  Genv.find_funct_ptr sge b = Some (External ef) ->
  ef_sig ef = sg ->
  eval_exprlist sge sp e m le al vl ->
  eval_exprlist_fp sge sp e m le al fp ->
  transl_exprlist_fp_prop le al vl fp ->
  i64ext ef ->
  external_call ef sge vl m E0 v m ->
  transl_expr_fp_prop le (Eexternal id sg al) v fp.
Proof.
  intros; red; intros. inv TE.
  exploit H4; eauto. intros [rs1 [fp1 [EX1 [ME1 [RR1 [RO1 HFP1]]]]]].
  exploit external_call_mem_extends; eauto.
  intros [v' [tm2 [A [B _]]]]. exploit i64ext_effects; eauto. intros [X _]; subst.
  exploit function_ptr_translated; eauto. simpl. intros [tf [P Q]]. inv Q.
  exists (rs1#rd <- v'); exists fp1.
(* Exec *)
  split. eapply star_trans. eexact EX1.
  eapply star_left. eapply exec_Icall; eauto.
  simpl. rewrite symbols_preserved. rewrite H. eauto. auto.
  eapply star_left. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  apply star_one. apply exec_return.
  reflexivity. reflexivity. repeat rewrite FP.fp_union_emp; reflexivity.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* FP *)
  auto.
Qed.

Lemma transl_exprlist_fp_Enil_correct:
  forall (le : letenv),
  transl_exprlist_fp_prop le Enil nil empfp.
Proof.
  intros; red; intros; inv TE.
  exists rs; exists empfp.
  split. apply star_refl.
  split. assumption.
  split. constructor.
  split. auto.
   constructor; cbv; auto.
Qed.

Lemma transl_exprlist_fp_Econs_correct:
  forall (le : letenv) (a1 : expr) (al : exprlist) (v1 : val) fp1
         (vl : list val) fp2,
  eval_expr sge sp e m le a1 v1 ->
  eval_expr_fp sge sp e m le a1 fp1 ->
  transl_expr_fp_prop le a1 v1 fp1 ->
  eval_exprlist sge sp e m le al vl ->
  eval_exprlist_fp sge sp e m le al fp2 ->
  transl_exprlist_fp_prop le al vl fp2 ->
  transl_exprlist_fp_prop le (Econs a1 al) (v1 :: vl) (FP.union fp1 fp2).
Proof.
  intros; red; intros; inv TE.
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [RES1 [OTHER1  HFP1]]]]]].
  exploit H4; eauto. intros [rs2 [fp2' [EX2 [ME2 [RES2 [OTHER2  HFP2]]]]]].
  exists rs2; exists (FP.union fp1' fp2').
(* Exec *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. constructor. rewrite OTHER2. auto.
  simpl; tauto.
  auto.
(* Other regs *)
  split. intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto.
  apply OTHER1; auto.
   apply FP.subset_parallel_union; auto.
Qed.

Lemma transl_condexpr_fp_CEcond_correct:
  forall le cond al vl fp1 vb fp2,
  eval_exprlist sge sp e m le al vl ->
  eval_exprlist_fp sge sp e m le al fp1 ->
  transl_exprlist_fp_prop le al vl fp1 ->
  eval_condition cond vl m = Some vb ->
  eval_condition_fp cond vl m = Some fp2 ->  
  transl_condexpr_fp_prop le (CEcond cond al) vb (FP.union fp1 fp2).
Proof.
  intros; red; intros. inv TE.
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [RES1 [OTHER1  HFP1]]]]]].
  exploit eval_condition_lessdef_fp; eauto. intros [fp2' [EVALC' HFP2']]. apply fp_inject_id_fp_subset in HFP2'.
  exists rs1; exists (FP.union fp1' fp2').
(* Exec *)
  split. eapply plus_right. eexact EX1. eapply exec_Icond. eauto.
  eapply eval_condition_lessdef; eauto. exact EVALC'. auto. auto.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. assumption.

   apply FP.subset_parallel_union; auto.
Qed.

Lemma transl_condexpr_fp_CEcondition_correct:
  forall le a b c va fp1 v fp2,
  eval_condexpr sge sp e m le a va ->
  eval_condexpr_fp sge sp e m le a fp1 ->
  transl_condexpr_fp_prop le a va fp1 ->
  eval_condexpr sge sp e m le (if va then b else c) v ->
  eval_condexpr_fp sge sp e m le (if va then b else c) fp2 ->
  transl_condexpr_fp_prop le (if va then b else c) v fp2 ->
  transl_condexpr_fp_prop le (CEcondition a b c) v (FP.union fp1 fp2).
Proof.
  intros; red; intros. inv TE.
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [OTHER1 HFP1]]]]].
  assert (tr_condition (fn_code f) map pr (if va then b else c) (if va then n2 else n3) ntrue nfalse).
    destruct va; auto.
  exploit H4; eauto. intros [rs2 [fp2' [EX2 [ME2 [OTHER2 HFP2]]]]].
  exists rs2; exists (FP.union fp1' fp2').
(* Exec *)
  split. eapply plus_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.
  apply FP.subset_parallel_union; auto.
Qed.

Lemma transl_condexpr_fp_CElet_correct:
  forall le a b v1 fp1 v2 fp2,
  eval_expr sge sp e m le a v1 ->
  eval_expr_fp sge sp e m le a fp1 ->
  transl_expr_fp_prop le a v1 fp1 ->
  eval_condexpr sge sp e m (v1 :: le) b v2 ->
  eval_condexpr_fp sge sp e m (v1 :: le) b fp2 ->
  transl_condexpr_fp_prop (v1 :: le) b v2 fp2 ->
  transl_condexpr_fp_prop le (CElet a b) v2 (FP.union fp1 fp2).
Proof.
  intros; red; intros. inv TE.
  exploit H1; eauto. intros [rs1 [fp1' [EX1 [ME1 [RES1 [OTHER1 HFP1]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H4; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [fp2' [EX2 [ME3 [OTHER2 HFP2]]]]].
  exists rs2; exists (FP.union fp1' fp2').
(* Exec *)
  split. eapply star_plus_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.

  apply FP.subset_parallel_union; auto.
Qed.


  
Theorem transl_expr_fp_correct:
  forall le a fp,
    eval_expr_fp sge sp e m le a fp ->
    forall v, eval_expr sge sp e m le a v ->
         transl_expr_fp_prop le a v fp.
Proof.
  intros le a fp.
  eapply (eval_expr_fp_ind3
            sge sp e m
            (fun le a fp => (forall v, eval_expr sge sp e m le a v -> transl_expr_fp_prop le a v fp))
            (fun le a fp => (forall vl, eval_exprlist sge sp e m le a vl -> transl_exprlist_fp_prop le a vl fp))
            (fun le a fp => (forall b, eval_condexpr sge sp e m le a b -> transl_condexpr_fp_prop le a b fp))).
  { intros. apply transl_expr_fp_Evar_correct; inv H0; auto. }
  { intros. inv H5. eqexpr. eapply transl_expr_fp_Eop_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Eload_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Econdition_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Elet_correct; eauto. }
  { intros. inv H0. eqexpr. eapply transl_expr_fp_Eletvar_correct; eauto. }
  { intros. inv H4. eqexpr. eapply transl_expr_fp_Ebuiltin_correct; eauto. }
  { intros. inv H7. eqexpr. eapply transl_expr_fp_Eexternal_correct; eauto. }
  { intros. inv H. eapply transl_exprlist_fp_Enil_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_exprlist_fp_Econs_correct; eauto. }
  { intros. inv H5; eqexpr. eapply transl_condexpr_fp_CEcond_correct; eauto. }
  { intros. inv H6; eqexpr. eapply transl_condexpr_fp_CEcondition_correct; eauto. }
  { intros. inv H6; eqexpr. eapply transl_condexpr_fp_CElet_correct; eauto. }
Qed.

Theorem transl_exprlist_fp_correct:
  forall le a fp,
    eval_exprlist_fp sge sp e m le a fp ->
    forall v, eval_exprlist sge sp e m le a v ->
         transl_exprlist_fp_prop le a v fp.
Proof.
  intros le a fp.
  eapply (eval_exprlist_fp_ind3
            sge sp e m
            (fun le a fp => (forall v, eval_expr sge sp e m le a v -> transl_expr_fp_prop le a v fp))
            (fun le a fp => (forall vl, eval_exprlist sge sp e m le a vl -> transl_exprlist_fp_prop le a vl fp))
            (fun le a fp => (forall b, eval_condexpr sge sp e m le a b -> transl_condexpr_fp_prop le a b fp))).
  { intros. apply transl_expr_fp_Evar_correct; inv H0; auto. }
  { intros. inv H5. eqexpr. eapply transl_expr_fp_Eop_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Eload_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Econdition_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Elet_correct; eauto. }
  { intros. inv H0. eqexpr. eapply transl_expr_fp_Eletvar_correct; eauto. }
  { intros. inv H4. eqexpr. eapply transl_expr_fp_Ebuiltin_correct; eauto. }
  { intros. inv H7. eqexpr. eapply transl_expr_fp_Eexternal_correct; eauto. }
  { intros. inv H. eapply transl_exprlist_fp_Enil_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_exprlist_fp_Econs_correct; eauto. }
  { intros. inv H5; eqexpr. eapply transl_condexpr_fp_CEcond_correct; eauto. }
  { intros. inv H6; eqexpr. eapply transl_condexpr_fp_CEcondition_correct; eauto. }
  { intros. inv H6; eqexpr. eapply transl_condexpr_fp_CElet_correct; eauto. }
Qed.

Theorem transl_condexpr_fp_correct:
  forall le a fp,
    eval_condexpr_fp sge sp e m le a fp ->
    forall v, eval_condexpr sge sp e m le a v ->  transl_condexpr_fp_prop le a v fp.
Proof.
  intros le a fp.
  eapply (eval_condexpr_fp_ind3
            sge sp e m
            (fun le a fp => (forall v, eval_expr sge sp e m le a v -> transl_expr_fp_prop le a v fp))
            (fun le a fp => (forall vl, eval_exprlist sge sp e m le a vl -> transl_exprlist_fp_prop le a vl fp))
            (fun le a fp => (forall b, eval_condexpr sge sp e m le a b -> transl_condexpr_fp_prop le a b fp))).
  { intros. apply transl_expr_fp_Evar_correct; inv H0; auto. }
  { intros. inv H5. eqexpr. eapply transl_expr_fp_Eop_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Eload_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Econdition_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_expr_fp_Elet_correct; eauto. }
  { intros. inv H0. eqexpr. eapply transl_expr_fp_Eletvar_correct; eauto. }
  { intros. inv H4. eqexpr. eapply transl_expr_fp_Ebuiltin_correct; eauto. }
  { intros. inv H7. eqexpr. eapply transl_expr_fp_Eexternal_correct; eauto. }
  { intros. inv H. eapply transl_exprlist_fp_Enil_correct; eauto. }
  { intros. inv H6. eqexpr. eapply transl_exprlist_fp_Econs_correct; eauto. }
  { intros. inv H5; eqexpr. eapply transl_condexpr_fp_CEcond_correct; eauto. }
  { intros. inv H6; eqexpr. eapply transl_condexpr_fp_CEcondition_correct; eauto. }
  { intros. inv H6; eqexpr. eapply transl_condexpr_fp_CElet_correct; eauto. }
Qed.


(** Exit expressions. *)

Definition transl_exitexpr_fp_prop
     (le: letenv) (a: exitexpr) (x: nat) (fp: footprint) : Prop :=
  forall tm cs f map ns nexits rs
    (MWF: map_wf map)
    (TE: tr_exitexpr f.(fn_code) map a ns nexits)
    (ME: match_env map e le rs)
    (EXT: Mem.extends m tm),
  exists nd, exists rs', exists fp',
     star (step tge) (Core_State cs f sp ns rs) tm fp' (Core_State cs f sp nd rs') tm
  /\ nth_error nexits x = Some nd
  /\ match_env map e le rs'
  /\ FP.subset fp' fp.

Theorem transl_exitexpr_fp_correct:
  forall le a fp x,
    eval_exitexpr_fp sge sp e m le a fp ->
    eval_exitexpr sge sp e m le a x ->
    transl_exitexpr_fp_prop le a x fp.
Proof.
  induction 1; red; intros; inv TE.
- (* XEexit *)
  exists ns, rs, empfp.
  split. apply star_refl.
  inv H. split. auto. split. auto.  constructor; cbv; auto.
- (* XEjumptable *)
  exploit H5; eauto. intros (nd & A & B).
  exploit transl_expr_fp_correct; eauto. intros (rs1 & fp' & EXEC1 & ME1 & RES1 & PRES1 & HFP).
  exists nd, rs1, fp'.
  split. eapply star_right. eexact EXEC1. eapply exec_Ijumptable; eauto. inv RES1; auto. rewrite FP.fp_union_emp; auto.
  inv H2. eqexpr. auto.
- (* XEcondition *)
  inv H4. eqexpr. 
  exploit transl_condexpr_fp_correct; eauto. intros (rs1 & fp1' & EXEC1 & ME1 & RES1 & HFP1').
  exploit IHeval_exitexpr_fp; eauto. 
  instantiate (2 := if va0 then n2 else n3). destruct va0; eauto.
  intros (nd & rs2 & fp2' & EXEC2 & EXIT2 & ME2 & HFP2').
  exists nd, rs2, (FP.union fp1' fp2').
  split. eapply star_trans. apply plus_star. eexact EXEC1. eexact EXEC2. auto.
  do 2 (split; auto). apply FP.subset_parallel_union; auto.
- (* XElet *)
  inv H4. eqexpr.
  exploit transl_expr_fp_correct; eauto. intros (rs1 & fp1' & EXEC1 & ME1 & RES1 & PRES1 & HFP1).
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit IHeval_exitexpr_fp; eauto. eapply match_env_bind_letvar; eauto.
  intros (nd & rs2 & fp2' & EXEC2 & EXIT2 & ME2  & HFP2).
  exists nd, rs2, (FP.union fp1' fp2').
  split. eapply star_trans. eexact EXEC1. eexact EXEC2. auto.
  split. auto.
  split. eapply match_env_unbind_letvar; eauto.
  apply FP.subset_parallel_union; auto.
Qed.

(** Builtin arguments. *)

Lemma eval_exprlist_append:
  forall le al1 vl1 al2 vl2,
  eval_exprlist sge sp e m le (exprlist_of_expr_list al1) vl1 ->
  eval_exprlist sge sp e m le (exprlist_of_expr_list al2) vl2 ->
  eval_exprlist sge sp e m le (exprlist_of_expr_list (al1 ++ al2)) (vl1 ++ vl2).
Proof.
  induction al1; simpl; intros vl1 al2 vl2 E1 E2; inv E1.
- auto.
- simpl. constructor; eauto.
Qed.

End CORRECTNESS_EXPR.

(** ** Measure over CminorSel states *)

Local Open Scope nat_scope.

Fixpoint size_stmt (s: stmt) : nat :=
  match s with
  | Sskip => 0
  | Sseq s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sifthenelse c s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sloop s1 => (size_stmt s1 + 1)
  | Sblock s1 => (size_stmt s1 + 1)
  | Sexit n => 0
  | Slabel lbl s1 => (size_stmt s1 + 1)
  | _ => 1
  end.

Fixpoint size_cont (k: cont) : nat :=
  match k with
  | Kseq s k1 => (size_stmt s + size_cont k1 + 1)
  | Kblock k1 => (size_cont k1 + 1)
  | _ => 0%nat
  end.

(*
Definition measure_state (S: CminorSel.state) :=
  match S with
  | CminorSel.State _ s k _ _ _ => (size_stmt s + size_cont k, size_stmt s)
  | _                           => (0, 0)
  end.
 *)

(* Definition lt_state (S1 S2: CminorSel.state) :=
  lex_ord lt lt (measure_state S1) (measure_state S2).  

Lemma lt_state_intro:
  forall f1 s1 k1 sp1 e1 m1 f2 s2 k2 sp2 e2 m2,
  size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (CminorSel.State f1 s1 k1 sp1 e1 m1)
           (CminorSel.State f2 s2 k2 sp2 e2 m2).
Proof.
  intros. unfold lt_state. simpl. destruct H as [A | [A B]].
  left. auto.
  rewrite A. right. auto.
Qed.

 *)

Definition index_gen (s: stmt) (k: cont) : nat * nat :=
  (size_stmt s + size_cont k, size_stmt s).

Definition index_order : nat * nat -> nat * nat -> Prop := lex_ord lt lt.

Lemma lt_index_intro:
  forall a1 a2 b1 b2,
    a1 + a2 < b1 + b2
    \/ (a1 + a2 = b1 + b2 /\ a1 < b1) ->
    index_order (a1 + a2, a1) (b1 + b2, b1).
Proof.
  clear; intros. destruct H as [A | [A B]].
  left; auto.
  rewrite A. right. auto.
Qed.

Ltac Ex_index :=
  match goal with
  | |- context[CminorSel_local.Core_State _ ?s ?k _ _] => exists (index_gen s k)
  | |- context[CminorSel_local.Core_Callstate] => exists (0,0)
  | |- context[CminorSel_local.Core_Returnstate] => exists (0,0)
  end.

Ltac Lt_index :=
  apply lt_index_intro; simpl; try Lia.lia.


(*Ltac Lt_state :=
  apply lt_state_intro; simpl; try Lia.lia.
*)
Require Import Wellfounded.

(** ** Semantic preservation for the translation of statements *)

(** The simulation diagram for the translation of statements
  and functions is a "star" diagram of the form:
<<
           I                         I
     S1 ------- R1             S1 ------- R1
     |          |              |          |
   t |        + | t      or  t |        * | t    and |S2| < |S1|
     v          v              v          |
     S2 ------- R2             S2 ------- R2
           I                         I
>>
  where [I] is the [match_states] predicate defined below.  It includes:
- Agreement between the Cminor statement under consideration and
  the current program point in the RTL control-flow graph,
  as captured by the [tr_stmt] predicate.
- Agreement between the Cminor continuation and the RTL control-flow
  graph and call stack, as captured by the [tr_cont] predicate below.
- Agreement between Cminor environments and RTL register environments,
  as captured by [match_envs].

*)

Inductive tr_fun (tf: function) (map: mapping) (f: CminorSel.function)
                     (ngoto: labelmap) (nret: node) (rret: option reg) : Prop :=
  | tr_fun_intro: forall nentry r,
      rret = ret_reg f.(CminorSel.fn_sig) r ->
      tr_stmt tf.(fn_code) map f.(fn_body) nentry nret nil ngoto nret rret ->
      tf.(fn_stacksize) = f.(fn_stackspace) ->
      tr_fun tf map f ngoto nret rret.

Inductive tr_cont: RTL.code -> mapping ->
                   CminorSel.cont -> node -> list node -> labelmap -> node -> option reg ->
                   list RTL.stackframe -> Prop :=
  | tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
      tr_stmt c map s nd n nexits ngoto nret rret ->
      tr_cont c map k n nexits ngoto nret rret cs ->
      tr_cont c map (Kseq s k) nd nexits ngoto nret rret cs
  | tr_Kblock: forall c map k nd nexits ngoto nret rret cs,
      tr_cont c map k nd nexits ngoto nret rret cs ->
      tr_cont c map (Kblock k) nd (nd :: nexits) ngoto nret rret cs
  | tr_Kstop: forall c map ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks Kstop cs ->
      tr_cont c map Kstop nret nil ngoto nret rret cs
  | tr_Kcall: forall c map optid f sp e k ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks (Kcall optid f sp e k) cs ->
      tr_cont c map (Kcall optid f sp e k) nret nil ngoto nret rret cs

with match_stacks: CminorSel.cont -> list RTL.stackframe -> Prop :=
  | match_stacks_stop:
      match_stacks Kstop nil
  | match_stacks_call: forall optid f sp e k r tf n rs cs map nexits ngoto nret rret,
      map_wf map ->
      tr_fun tf map f ngoto nret rret ->
      match_env map e nil rs ->
      reg_map_ok map r optid ->
      tr_cont tf.(fn_code) map k n nexits ngoto nret rret cs ->
      match_stacks (Kcall optid f sp e k) (Stackframe r tf sp n rs :: cs).

Lemma match_stacks_call_cont:
  forall c map k ncont nexits ngoto nret rret cs,
  tr_cont c map k ncont nexits ngoto nret rret cs ->
  match_stacks (call_cont k) cs /\ c!nret = Some(Ireturn rret).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma tr_cont_call_cont:
  forall c map k ncont nexits ngoto nret rret cs,
  tr_cont c map k ncont nexits ngoto nret rret cs ->
  tr_cont c map (call_cont k) nret nil ngoto nret rret cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma tr_find_label:
  forall c map lbl n (ngoto: labelmap) nret rret s' k' cs,
  ngoto!lbl = Some n ->
  forall s k ns1 nd1 nexits1,
  find_label lbl s k = Some (s', k') ->
  tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
  tr_cont c map k nd1 nexits1 ngoto nret rret cs ->
  exists ns2, exists nd2, exists nexits2,
     c!n = Some(Inop ns2)
  /\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
  /\ tr_cont c map k' nd2 nexits2 ngoto nret rret cs.
Proof.
  induction s; intros until nexits1; simpl; try congruence.
  (* seq *)
  caseEq (find_label lbl s1 (Kseq s2 k)); intros.
  inv H1. inv H2. eapply IHs1; eauto. econstructor; eauto.
  inv H2. eapply IHs2; eauto.
  (* ifthenelse *)
  caseEq (find_label lbl s1 k); intros.
  inv H1. inv H2. eapply IHs1; eauto.
  inv H2. eapply IHs2; eauto.
  (* loop *)
  intros. inversion H1; subst.
  eapply IHs; eauto. econstructor; eauto. econstructor; eauto.
  (* block *)
  intros. inv H1.
  eapply IHs; eauto. econstructor; eauto.
  (* label *)
  destruct (ident_eq lbl l); intros.
  inv H0. inv H1.
  assert (n0 = n). change positive with node in H4. congruence. subst n0.
  exists ns1; exists nd1; exists nexits1; auto.
  inv H1. eapply IHs; eauto.
Qed.

Inductive MATCH_STATE:
  bool -> (nat * nat) -> Injections.Mu -> FP.t -> FP.t ->
  CminorSel_local.core * mem -> RTL_local.core * mem -> Prop :=
| match_state:
    forall mu f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret fp fp'
      (MWF: map_wf map)
      (TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)
      (TF: tr_fun tf map f ngoto nret rret)
      (TK: tr_cont tf.(fn_code) map k ncont nexits ngoto nret rret cs)
      (ME: match_env map e nil rs)
      (MEXT: Mem.extends m tm)
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block tm b)
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m tm)
      (FPMATCH: Injections.FPMatch' mu fp fp'),
      MATCH_STATE true (index_gen s k) mu fp fp'
                  (CminorSel_local.Core_State f s k sp e, m)
                  (RTL_local.Core_State cs tf sp ns rs, tm)
| match_callstate:
    forall mu b f args targs k m tm cs tf fp fp'
      (TF: transl_fundef f = OK tf)
      (MS: match_stacks k cs)
      (LD: Val.lessdef_list args targs)
      (MEXT: Mem.extends m tm)
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block tm b)
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m tm)
      (FPMATCH: Injections.FPMatch' mu fp fp'),
      MATCH_STATE b (0,0) mu fp fp'
                  (CminorSel_local.Core_Callstate f args k, m)
                  (RTL_local.Core_Callstate cs tf targs, tm)
| match_returnstate:
    forall mu v tv k m tm cs fp fp'
      (MS: match_stacks k cs)
      (LD: Val.lessdef v tv)
      (MEXT: Mem.extends m tm)
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block tm b)
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m tm)
      (FPMATCH: Injections.FPMatch' mu fp fp'),
      MATCH_STATE true (0,0) mu fp fp'
                  (CminorSel_local.Core_Returnstate v k, m)
                  (RTL_local.Core_Returnstate cs tv, tm).


Ltac resolvfp:=
  match goal with
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: Injections.FPMatch' ?mu ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; [exact H| resolvfp]
  | |- Injections.FPMatch' _ _ empfp => apply Injections.fp_match_emp'
  | H: FP.subset ?fp1 ?fp2 |- Injections.FPMatch' _ ?fp2 ?fp1 =>
    apply Injections.fp_match_subset_T' with fp2; try exact H; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp2 |- Injections.FPMatch' _ (FP.union ?fp1 _) ?fp2 =>
    apply Injections.fp_match_union_S'; auto
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
  | _ => idtac
  end.

Ltac Right := right; Ex_index; do 3 eexists; split; [|resolvfp].
Ltac FP:= match goal with |- ?P /\ _ => assert P; eresolvfp end.
Ltac Left := left; Ex_index; split; [Lt_index|eresolvfp].

Theorem TRANSF_local_ldsim:
  @local_ldsim CminorSel_IS RTL_IS sG tG sge tge.
Proof.
  eapply (@Local_ldsim CminorSel_IS RTL_IS _ _ _ _ _ index_order MATCH_STATE).
  constructor.
  (* index wf *)
  - apply wf_lex_ord; apply lt_wf.
  (* wd_mu *)
  - intros. inv H; eapply proper_mu_inject; eauto.
  (* inj ge *)
  - intros. inv H; eapply proper_mu_ge_init_inj; eauto.
  (* ge match *)
  - apply ge_match.
  (* initial call *)
  - (** TODO: this pattern is general enough... *)
    intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    (* this should be a property derived from TRANSF? *)
    (* by properties of init_core_local ? *)
    assert (HSG: sG = sge) by (inv GE_INIT; auto).
    assert (HTG: tG = tge) by (inv TGE_INIT; auto).    
    unfold init_core_local in *. simpl in *.
    unfold CminorSel_local.init_core, init_core in *.
    unfold generic_init_core in INITCORE |- * .
    rewrite HTG, symbols_preserved.
    rewrite HSG in INITCORE.
    destruct (Genv.find_symbol sge fid) eqn: FIND; try discriminate.
    destruct (Genv.find_funct_ptr sge b) eqn: FINDB; try discriminate.
    exploit function_ptr_translated; eauto. intros (tf & FINDB' & TRANSF).
    rewrite FINDB'. 
    unfold CminorSel_local.fundef_init in INITCORE.
    destruct f; try discriminate.
    assert (exists tfd, tf = Internal tfd)  as [tfd INTERNAL] by (monadInv TRANSF; eauto). subst tf.
    unfold fundef_init. 
    erewrite sig_transl_function;[|eauto].
    destruct (wd_args args (sig_args (CminorSel.funsig (Internal f)))) eqn: WDARGS; [|discriminate].
    erewrite wd_args_inject; eauto.
    eexists. split. eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists (0, 0).
    inversion INITCORE; clear INITCORE. simpl. 
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. induction args; intros args' REL G MEMREL; inv REL.
      auto. inv G. f_equal. inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. }
    subst args'.
    exploit sig_transl_function; eauto. simpl. intro SG. 
    econstructor; eauto.
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
        (generalize H3 LT; clear; intros; exfalso; apply H3 in LT; eapply Pos.lt_irrefl; eauto). }
    inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_src; auto.
    inv MEMINITINJ. inv LRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto.    
    inv MEMINITINJ; econstructor; eauto.
    simpl. intro.
    intros ? ? ? ? ? . exploit inj_inject_id. exact H. intro. inv H0.
    intro A. inv A. auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
    resolvfp.
    
  - (* tau step*)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP. simpl in STEP.
    assert (HSG: sG = sge) by (inv GE_INIT; auto);
      assert (HTG: tG = tge) by (inv TGE_INIT; auto).
    rewrite HSG in STEP. rewrite HTG. revert i mu Hfp Lfp Lcore Lm MS HSG HTG.
    induction STEP; intros until 1; inv MS.
    + (* skip seq *)
      inv TS. inv TK. intros. Left.
      econstructor; eauto.

    + (* skip block *)
      inv TS. inv TK. Left.
      econstructor; eauto. constructor. 

    + (* skip return *)
      inv TS.
      assert ((fn_code tf)!ncont = Some(Ireturn rret)
              /\ match_stacks k cs).
        inv TK; simpl in H; try contradiction; auto.
      destruct H1.
      assert (fn_stacksize tf = fn_stackspace f).
        inv TF. auto. rewrite <- H3 in *.
      edestruct Mem.free_parallel_extends as [tm' []]; eauto.
      Right.
      apply plus_one. eapply exec_Ireturn; eauto.
      FP. split. auto.
      constructor; auto; resvalid.

    + (* assign *)
      inv TS. exploit transl_expr_fp_correct; eauto.
      simpl. intros [rs' [fp' [A [B [C [D HFP]]]]]].
      (* case study on A.. *)
      inv A.
      Left. econstructor; eauto. constructor. resolvfp.
      Right.
      eapply plus_star_trans. apply plus_one. eauto. eauto. eauto. 
      FP. split; auto. econstructor; eauto. constructor.

    + (* store *)
      inv TS.
      exploit transl_exprlist_fp_correct; eauto.
      intros [rs' [fp' [A [B [C [D E]]]]]].
      exploit transl_expr_fp_correct; eauto.
      intros [rs'' [fp'' [F [G [J [K L]]]]]].
      assert (Val.lessdef_list vl rs''##rl).
      replace (rs'' ## rl) with (rs' ## rl). auto.
      apply list_map_exten. intros. apply K. auto.
      edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
      edestruct Mem.storev_extends as [tm''' []]; eauto.
      Right.
      eapply plus_right. eapply star_trans. eexact A. eexact F. reflexivity.
      eapply exec_Istore with (a := vaddr'). eauto.
      rewrite <- H6. apply eval_addressing_preserved. exact symbols_preserved.
      eauto. eauto. eauto.
      destruct vaddr; try discriminate. inv H7. simpl in *.
      FP. apply Injections.fp_match_union'; resolvfp. apply Injections.fp_match_union'; resolvfp.
      split; auto.
      econstructor; eauto; resvalid. constructor. 

    + (* call *)
      inv TS. inv H. inv H0. exploit eval_expr_det. exact H3. exact H6. intro. subst.
      (* indirect *)
      exploit transl_expr_fp_correct; eauto.
      intros [rs' [fp' [A [B [C [D X]]]]]].
      exploit transl_exprlist_fp_correct; eauto.
      intros [rs'' [fp'' [E [F [G [J Y]]]]]].
      exploit functions_translated; eauto. intros [tf' [P Q]].
      Right.
      eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
      eapply exec_Icall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
      apply sig_transl_function; auto.
      eresolvfp. FP. apply Injections.fp_match_union'; eresolvfp.
      split; auto. econstructor; eauto. econstructor; eauto.
      (* direct *)
      exploit transl_exprlist_fp_correct; eauto.
      intros [rs'' [fp'' [E [F [G [J Y]]]]]].
      exploit functions_translated; eauto. intros [tf' [P Q]].
      Right.
      eapply plus_right. eexact E.
      eapply exec_Icall; eauto. simpl. rewrite symbols_preserved. inv H. rewrite H6.
      rewrite Genv.find_funct_find_funct_ptr in P. eauto.
      apply sig_transl_function; auto. eresolvfp.
      FP. eresolvfp. rewrite FP.union_comm_eq. apply Injections.fp_match_union_S'; eresolvfp.
      split; auto. constructor; auto. econstructor; eauto.

    + (* tailcall *)
      inv TS; inv H. inv H0. exploit eval_expr_det. exact H4. exact H7. intro; subst.
      (* indirect *)
      exploit transl_expr_fp_correct; eauto.
      intros [rs' [fp' [A [B [C [D X]]]]]].
      exploit transl_exprlist_fp_correct; eauto.
      intros [rs'' [fp'' [E [F [G [J Y]]]]]].
      exploit functions_translated; eauto. intros [tf' [P Q]].
      exploit match_stacks_call_cont; eauto. intros [U V].
      assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
      edestruct Mem.free_parallel_extends as [tm''' []]; eauto.
      Right.
      eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
      eapply exec_Itailcall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
      apply sig_transl_function; auto.
      rewrite H; eauto. 
      eauto.
      rewrite H. FP. repeat apply Injections.fp_match_union'; eresolvfp.
      split; auto. constructor; auto; resvalid.
      (* direct *)
      exploit transl_exprlist_fp_correct; eauto.
      intros [rs'' [fp'' [E [F [G [J Y]]]]]].
      exploit functions_translated; eauto. intros [tf' [P Q]].
      exploit match_stacks_call_cont; eauto. intros [U V].
      assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
      edestruct Mem.free_parallel_extends as [tm''' []]; eauto.
      Right.
      eapply plus_right. eexact E.
      eapply exec_Itailcall; eauto. simpl. rewrite symbols_preserved. rewrite H7.
      rewrite Genv.find_funct_find_funct_ptr in P. eauto.
      apply sig_transl_function; auto.
      rewrite H; eauto. eauto.
      rewrite H. FP. repeat apply Injections.fp_match_union'; eresolvfp.
      rewrite FP.union_comm_eq; apply Injections.fp_match_union_S'; eresolvfp.
      split; auto. constructor; auto; resvalid.

      (* builtin 
  inv TS.
  exploit invert_eval_builtin_args; eauto. intros (vparams & P & Q).
  exploit transl_exprlist_correct; eauto.
  intros [rs' [tm' [E [F [G [J K]]]]]].
  exploit transl_eval_builtin_args; eauto.
  intros (vargs' & U & V).
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs'#r) (fun r => rs'#r)); eauto.
  intros (vargs'' & X & Y).
  assert (Z: Val.lessdef_list vl vargs'') by (eapply Val.lessdef_list_trans; eauto).
  edestruct external_call_mem_extends as [tv [tm'' [A [B [C D]]]]]; eauto.
  econstructor; split.
  left. eapply plus_right. eexact E.
  eapply exec_Ibuiltin. eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved. apply senv_preserved. eauto.
  traceEq.
  econstructor; eauto. constructor.
  eapply match_env_update_res; eauto.
       *)
      
    + (* seq *)
      inv TS.
      Left. econstructor; eauto. econstructor; eauto.

    + (* ifthenelse *)
      inv TS.
      exploit transl_condexpr_fp_correct; eauto. intros [rs' [fp' [A [B [C D]]]]].
      Right. eexact A. FP. split; auto.
      destruct b; econstructor; eauto.

    + (* loop *)
      inversion TS; subst.
      Right.
      apply plus_one. eapply exec_Inop; eauto.
      FP. split; auto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.

    + (* block *)
      inv TS.
      Left. econstructor; eauto. econstructor; eauto.

    + (* exit seq *)
      inv TS. inv TK.
      Left. econstructor; eauto. econstructor; eauto.

    + (* exit block 0 *)
      inv TS. inv TK. simpl in H0. inv H0.
      Left. econstructor; eauto. econstructor; eauto.

    + (* exit block n+1 *)
      inv TS. inv TK. simpl in H0.
      Left. econstructor; eauto. econstructor; eauto.

    + (* switch *)
      inv TS.
      exploit transl_exitexpr_fp_correct; eauto.
      intros (nd & rs' & fp' & A & B & C & D).
      inv A.
      Left. econstructor; eauto. constructor; auto. resolvfp.
      Right. eapply plus_star_trans. apply plus_one. eauto. eauto. eauto. 
      FP. split; auto. econstructor; eauto. constructor; auto.

    + (* return none *)
      inv TS.
      exploit match_stacks_call_cont; eauto. intros [U V].
      inversion TF.
      edestruct Mem.free_parallel_extends as [tm' []]; eauto.
      rewrite <- H2 in *. Right. apply plus_one. eapply exec_Ireturn; eauto. 
      FP. split; auto. constructor; auto; resvalid.

    + (* return some *)
      inv TS.
      exploit transl_expr_fp_correct; eauto.
      intros [rs' [fp' [A [B [C [D E]]]]]].
      exploit match_stacks_call_cont; eauto. intros [U V].
      inversion TF.
      edestruct Mem.free_parallel_extends as [tm'' []]; eauto.
      rewrite <-H5 in *. Right. eapply plus_right. eexact A. eapply exec_Ireturn; eauto. eauto.
      FP. apply Injections.fp_match_union'; resolvfp.
      split; auto. simpl. constructor; auto; resvalid.

    + (* label *)
      inv TS. Left. resolvfp. econstructor; eauto.

    + (* goto *)
      inv TS. inversion TF; subst.
      exploit tr_find_label; eauto. eapply tr_cont_call_cont; eauto.
      intros [ns2 [nd2 [nexits2 [A [B C]]]]].
      Right. apply plus_one. eapply exec_Inop; eauto.
      FP. split; auto. econstructor; eauto.

    + (* internal call *)
      monadInv TF. exploit transl_function_charact; eauto. intro TRF.
      inversion TRF. subst f0.
      pose (e := set_locals (fn_vars f) (set_params vargs (CminorSel.fn_params f))).
      pose (rs := init_regs targs rparams).
      assert (ME: match_env map2 e nil rs).
      unfold rs, e. eapply match_init_env_init_reg; eauto.
      assert (MWF: map_wf map2).
      assert (map_valid init_mapping s0) by apply init_mapping_valid.
      exploit (add_vars_valid (CminorSel.fn_params f)); eauto. intros [A B].
      eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.
      edestruct Mem.alloc_extends as [tm' []]; eauto; try apply Zle_refl.
      Right. apply plus_one. eapply exec_function_internal; simpl; eauto.
      FP. unfold alloc_fp. inv MEXT. rewrite mext_next. resolvfp.
      split; auto. simpl. econstructor; eauto.
      econstructor; eauto.
      inversion MS0; subst; econstructor; eauto.
      resvalid. resvalid.
      inv AGMU; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto;
        try (eapply Mem.alloc_unchanged_on; eauto; fail).

    (*
    + (* external call *)
      monadInv TF.
      edestruct external_call_mem_extends as [tvres [tm' [A [B [C D]]]]]; eauto.
      econstructor; split.
      left; apply plus_one. eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      constructor; auto.
*)
    + (* return *)
      inv MS0.
      Right. apply plus_one; constructor.
      FP. split; auto. econstructor; eauto. constructor.
      eapply match_env_update_dest; eauto.
      
  - (* at external *)
    simpl in *. unfold CminorSel_local.at_external, at_external.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MS ATEXT RC GARG.
    assert (HSG: sG = sge) by (inv GE_INIT; auto).
    assert (HTG: tG = tge) by (inv TGE_INIT; auto).
    destruct Hcore; try discriminate. destruct f0; try discriminate. destruct e; try discriminate.
    rewrite HSG in ATEXT. destruct (invert_symbol_from_string sge name) eqn:SYMBNAME; try discriminate.
    revert HSG HTG; inv ATEXT. inv MS. simpl in TF. inv TF. intros.
    erewrite match_genvs_invert_symbol_from_string_preserved; eauto.
    destruct peq; simpl in *. discriminate.
    destruct peq; simpl in *. discriminate. inv H0.
    Ex_index. eexists. split; auto. split.
    { simpl in *. unfold LDSimDefs.arg_rel. revert targs AGMU LD GARG; clear.
      induction argSrc; intros. simpl. inv LD. auto. inv LD. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto. destruct v2; auto.
      simpl in H2. eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H; eauto.
      intro. inv H0. econstructor. unfold Bset.inj_to_meminj; rewrite H. eauto. rewrite Ptrofs.add_zero; auto. }
    split.
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    split; auto.
    split.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    econstructor; eauto. apply Injections.fp_match_emp'.
    rewrite HTG. eapply match_cu_match_genv; eauto.
    inv GE_INIT; eauto. inv TGE_INIT; eauto.
    intros. inv H; auto.
    destruct peq; simpl in *. discriminate.
    destruct peq; simpl in *. discriminate. inv H0.
    destruct f1; monadInv H1; auto.

  - (* after external *)
    simpl. unfold CminorSel_local.after_external, after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    assert (HSG: sG = sge) by (inv GE_INIT; auto). assert (HTG: tG = tge) by (inv TGE_INIT; auto). revert HSG HTG.
    destruct Hcore; try discriminate. destruct f; try discriminate. destruct e; try discriminate.
    inv MS. monadInv TF. simpl in *. intros.
    assert (Hcore' = CminorSel_local.Core_Returnstate (match oresSrc with Some v => v | None => Vundef end) k).
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
    exists (Core_Returnstate cs (match oresTgt with Some v => v | None => Vundef end)).
    split.
    { destruct oresSrc, oresTgt, (sig_res sg); try contradiction; auto.
      inv RESREL; destruct t; try contradiction; simpl in *; auto. rewrite HRES. auto. }
    intros Hm' Lm' HLRELY.
    destruct HLRELY as [HRELY LRELY INV].
    subst. Ex_index. econstructor; eauto.
    { destruct oresSrc, (sig_res sg), oresTgt; simpl in *; try contradiction; auto.
      inv RESREL; auto. inv AGMU. apply proper_mu_inject_incr in H. inv H. rewrite Ptrofs.add_zero. auto. }
    inv AGMU; eapply extends_rely_extends; eauto. econstructor; eauto.
    intros ? S. apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT; auto.
    intros ? T. apply TVALID in T. unfold Mem.valid_block in *. inv LRELY. rewrite EQNEXT; auto.
    inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.    

  - (* halt *)
    simpl. unfold CminorSel_local.halted, halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES.
    destruct Hcore; try discriminate. destruct k; try discriminate.
    inv HALT. inv MS. inv MS0. exists resSrc. 
    split. 
    { f_equal. inv LD; auto. contradiction. }
    split.
    { revert AGMU GRES. clear; intros. destruct resSrc; try constructor.
      econstructor. simpl in GRES. inv AGMU.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. inv A. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      rewrite Ptrofs.add_zero; auto. }
    split.
    inv AGMU; eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto.
    split; auto.
    inv AGMU; eapply extends_reach_closed_implies_inject; eauto.
Qed.

End CORRECTNESS.

Theorem transf_local_ldsim:
  forall scu tcu,
    rtlgen.transf_program scu = OK tcu ->
    forall sge sG tge tG,
      init_genv_local CminorSel_IS scu sge sG ->
      init_genv_local RTL_IS tcu tge tG ->
      Genv.genv_next sge = Genv.genv_next tge ->
      local_ldsim sG tG sge tge.
Proof.
  intros. eapply TRANSF_local_ldsim; eauto.
  apply transf_program_match. auto.
Qed.