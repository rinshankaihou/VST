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

Require Import Coqlib Maps Postorder Integers.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep Blockset  InjRels Op_fp Footprint IS_local.
Require Import Op Registers val_casted CUAST RTL RTL_local Renumber renumber Errors LDSim_local LDSimDefs_local.
Require Import Lia. 

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.
Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

Definition match_prog (scu tcu : RTL_comp_unit) :=
  match_comp_unit_gen (fun f tf => OK (transf_fundef f) = OK tf) eq scu tcu.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_cunit. auto.
Qed.

Section PRESERVATION.


Variable scu tcu: RTL_comp_unit.
Variable sge tge: RTL.genv.

Hypothesis SGEINIT: globalenv_generic scu sge.
Hypothesis TGEINIT: globalenv_generic tcu tge.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).

Hypothesis TRANSF: match_prog scu tcu.

Lemma ge_match: ge_match_strict sge tge.
Proof. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma genv_match: Genv.match_genvs (match_globdef (fun f tf => OK (transf_fundef f) = OK tf) eq) sge tge.
Proof. eapply match_cu_match_genv; eauto. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof. destruct genv_match; eauto. Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr sge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  destruct genv_match.
  unfold fundef in *. simpl in *.
  unfold Genv.find_funct_ptr, Genv.find_def; intros.
  specialize (mge_defs b). inv mge_defs.
  rewrite <- H1 in H. discriminate.
  rewrite <- H0 in H. destruct x; inv H.
  inv H2. inv H3. eauto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct sge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  destruct v; simpl; intros; try discriminate.
  destruct Ptrofs.eq_dec; [|discriminate]. 
  apply funct_ptr_translated; auto.
Qed.

Lemma senv_preserved:
  Senv.equiv sge tge.
Proof. eapply match_cu_senv_preserved; eauto. Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. 
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function sge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol sge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.


(** Effect of an injective renaming of nodes on a CFG. *)

Section RENUMBER.

Variable f: PTree.t positive.

Hypothesis f_inj: forall x1 x2 y, f!x1 = Some y -> f!x2 = Some y -> x1 = x2.

Lemma renum_cfg_nodes:
  forall c x y i,
  c!x = Some i -> f!x = Some y -> (renum_cfg f c)!y = Some(renum_instr f i).
Proof.
  set (P := fun (c c': code) =>
              forall x y i, c!x = Some i -> f!x = Some y -> c'!y = Some(renum_instr f i)).
  intros c0. change (P c0 (renum_cfg f c0)). unfold renum_cfg.
  apply PTree_Properties.fold_rec; unfold P; intros.
  (* extensionality *)
  eapply H0; eauto. rewrite H; auto.
  (* base *)
  rewrite PTree.gempty in H; congruence.
  (* induction *)
  rewrite PTree.gsspec in H2. unfold renum_node. destruct (peq x k).
  inv H2. rewrite H3. apply PTree.gss.
  destruct f!k as [y'|] eqn:?.
  rewrite PTree.gso. eauto. red; intros; subst y'. elim n. eapply f_inj; eauto.
  eauto.
Qed.

End RENUMBER.

Definition pnum (f: function) := postorder (successors_map f) f.(fn_entrypoint).

Definition reach (f: function) (pc: node) := reachable (successors_map f) f.(fn_entrypoint) pc.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  reach f pc ->
  (transf_function f).(fn_code)!(renum_pc (pnum f) pc) = Some(renum_instr (pnum f) i).
Proof.
  intros.
  destruct (postorder_correct (successors_map f) f.(fn_entrypoint)) as [A B].
  fold (pnum f) in *.
  unfold renum_pc. destruct (pnum f)! pc as [pc'|] eqn:?.
  simpl. eapply renum_cfg_nodes; eauto.
  elim (B pc); auto. unfold successors_map. rewrite PTree.gmap1. rewrite H. simpl. congruence.
Qed.



Lemma reach_succ:
  forall f pc i s,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  reach f pc -> reach f s.
Proof.
  unfold reach; intros. econstructor; eauto.
  unfold successors_map. rewrite PTree.gmap1. rewrite H. auto.
Qed.
Definition local_block (b: block) : Prop := Ple (Genv.genv_next sge) b.
Definition stk_local (v: val) : Prop :=
  match v with
  | Vptr sp _ => local_block sp
  | _ => False
  end.

Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Ltac inv_eq:=
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; inversion H ;subst
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;subst;try contradiction;try discriminate.
Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ , B: reach _ _ |- _ ] =>
        generalize (transf_function_at _ _ _ A B); simpl renum_instr; intros
  end.
Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      reach f pc ->
      match_stackframes stk stk' ->
      regs_lessdef rs rs' ->
      stk_local (Vptr sp Ptrofs.zero) ->
      match_stackframes
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Ptrofs.zero)  (renum_pc (pnum f) pc) rs' :: stk').
Inductive match_states: core*mem -> core*mem ->Prop:=
|match_regular_state:
   forall s sp pc rs m s' rs' m' f
     (STACKS: match_stackframes s s')
     (REACH: reach f pc)
     (RLD: regs_lessdef rs rs')
     (MLD: Mem.extends m m')
     (LOCALSP: local_block sp),
     match_states (Core_State s f (Vptr sp Ptrofs.zero) pc rs, m)
                  (Core_State s' (transf_function f)(Vptr sp Ptrofs.zero) (renum_pc (pnum f)pc) rs', m')
                  
| match_callstates:
    forall s m s' m' f args args'
      (STACKS: match_stackframes s s')
      (VLD: Val.lessdef_list args args')
      (MLD: Mem.extends m m'),
      match_states (Core_Callstate s f args, m)
                   (Core_Callstate s' (transf_fundef f) args', m')
| match_returnstates:
    forall stk v m stk' m' v'
      (STACKS: match_stackframes stk stk')
      (VLD:Val.lessdef v v')
      (MLD: Mem.extends m m'),
      match_states (Core_Returnstate stk v, m)
                   (Core_Returnstate stk' v', m').

Definition MS b mu fp fp' cm cm': Prop :=
  match_states cm cm' /\
  Injections.FPMatch' mu fp fp' /\
  let (c, m) := cm in
  let (c', m') := cm' in
  (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
  (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
  (proper_mu sge tge inject_id mu) /\
  (MemClosures_local.unmapped_closed mu m m') /\
  match c with
  | RTL_local.Core_State _ _ _ _ _ => b = true
  | RTL_local.Core_Callstate _ _ _ => True
  | RTL_local.Core_Returnstate _ _ => b = true
  end.


Ltac invMS :=
  match goal with
  | H: MS _ _ _ _  ?cm1 ?cm2 |- _ =>
    destruct cm1 as [sc Hm]; destruct cm2 as [tc Lm];
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU [RCPRESV FLAG]]]]]]
  | H: MS _ _ _ _  ?cm1 ?cm2 |- _ =>
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU [RCPRESV FLAG]]]]]]
  end.

Ltac resolvfp:=
  match goal with
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; auto; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) ?fp1' => 
    eapply Injections.fp_match_union_S'; auto; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union ?fp1 _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union (FP.union ?fp1 _) _) => 
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
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union ?fp2 _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union'; resolvfp                                          
  | H: (forall b, Bset.belongsto (FP.blocks ?fp2) _ -> ~ Injections.SharedTgt ?mu _)
    |- Injections.FPMatch' _ _ ?fp2 =>
    apply Injections.fp_match_local_block; auto                                          
  | |- FP.subset ?fp ?fp => apply FP.subset_refl
  | H: fp_inject _ ?fp ?fp', H': proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp' =>
    eapply fp_inject_fp_match; inv H'; eauto
  | H: fp_inject inject_id ?fp ?fp'|- FP.subset ?fp' ?fp =>
    apply fp_inject_id_fp_subset
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

Ltac Right := do 4 eexists; [apply plus_one|resolvfp].
Ltac FP:= match goal with |- ?P /\ _ => assert P; [eresolvfp| try (split;[auto; fail|])] end.
Ltac splitMS :=
  split;
  [econstructor; eresolvfp |
   split; [eresolvfp|
           split; [try resvalid; auto |
                   split; [try resvalid; auto
                          |split; [auto|
                                   split; [try resvalid; eauto|
                                           eauto]]]]]].


Lemma TRANSF_local_ldsim:
  @local_ldsim RTL_IS RTL_IS sge tge sge tge.
Proof.
  econstructor.
  instantiate(1:= fun b (i:nat)=>MS b).
  instantiate(1:=lt).
  
  constructor.
  apply lt_wf.
  intros;invMS;eapply proper_mu_inject; eauto.
  intros;invMS;eapply proper_mu_ge_init_inj;eauto.
  apply ge_match.
  {
    intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    unfold init_core_local in *. simpl in *.
    unfold init_core in *.
    unfold generic_init_core in INITCORE |- *.
    erewrite symbols_preserved.
    inv_eq.
    erewrite funct_ptr_translated;eauto.
    unfold fundef_init in *.
    inv_eq. clear H0. 
    erewrite wd_args_inject;eauto.
    Esimpl;eauto.

    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists 0%nat. 
    (** This could be a general purposed lemma... *)
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. induction args; intros args' REL G MEMREL; inv REL.
      auto. inv G. f_equal. inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. }
    subst.
    splitMS.
    constructor.
    { clear;induction args;auto. }
    { inv MEMINITINJ; inv HRELY; inv LRELY.
      eapply inject_implies_extends;eauto.
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
    inv MEMINITINJ; econstructor; eauto. simpl. intro.
    intros ? ? ? ? ? . exploit inj_inject_id. exact H. intro. inv H0.
    intro A. inv A. auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
  }
  {
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP. simpl in STEP.
    revert i mu Hfp Lfp Lcore Lm MS.
    pose proof STEP as STEP_bk.
    induction STEP;intros;invMS; inv MS; right;exists 0%nat.
    {
      Esimpl. constructor;simpl.
      econstructor;eauto.
      eapply transf_function_at in H;eauto.
      eresolvfp.
      splitMS.
      eapply reach_succ;eauto. simpl;auto.
    }
    {
      assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
      exploit eval_operation_lessdef; eauto.
      intros [v' [EVAL' VLD]].
      exploit eval_operation_lessdef_fp; eauto.
      intros [fp' [EVALFP' FPINJ]].
      Esimpl. econstructor;simpl.
      eapply exec_Iop; eauto.
      eapply transf_function_at in H;eauto.
      erewrite <- EVAL'.
      eapply eval_operation_preserved. exact symbols_preserved.
      rewrite <- EVALFP'. apply eval_operation_fp_preserved. exact symbols_preserved.
      eresolvfp. splitMS.
      eapply reach_succ;eauto. simpl;auto.
      apply set_reg_lessdef; auto.
    }
    {
      assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
      exploit eval_addressing_lessdef; eauto.
      intros [a' [ADDR' ALD]].
      exploit Mem.loadv_extends; eauto.
      intros [v' [LOAD' VLD]].
      assert(Injections.FPMatch' mu (FP.union Hfp (FMemOpFP.loadv_fp chunk a))
                                   (FP.union Lfp (FMemOpFP.loadv_fp chunk a))).
      eresolvfp.
      Esimpl;eauto. constructor.
      
      eapply exec_Iload with (a := a'). eauto.
      eapply transf_function_at in H;eauto.
      erewrite <- ADDR'.
      apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto.
      assert (a' = a) by (destruct a; try discriminate; inv ALD; auto). subst a'.
      
      eresolvfp. splitMS.
      eapply reach_succ;eauto;simpl;auto.
      apply set_reg_lessdef; auto.
    }
    {
      assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
      exploit eval_addressing_lessdef; eauto.
      
      intros [a' [ADDR' ALD]].
      exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.
      intros [m'1 [STORE' MLD']].
      destruct a; simpl in H1; try discriminate. inv ALD. simpl in STORE'.
      Esimpl. constructor.
      eapply transf_function_at in H ;eauto.
      eapply exec_Istore. apply H.
      rewrite <- ADDR'.
      apply eval_addressing_preserved. exact symbols_preserved.
      eauto. eauto.
      eresolvfp.
      splitMS.
      eapply reach_succ;eauto. simpl;auto.
    }
    {
      
      eapply transf_function_at in H as ?;eauto.
      exploit find_function_translated;eauto.
      intro FIND'.
      Esimpl. constructor. eapply exec_Icall;eauto.
      rewrite sig_preserved;auto.
      eresolvfp.
      splitMS.
      econstructor;eauto.
      eapply reach_succ;eauto;simpl;eauto.
      eapply regs_lessdef_regs;eauto.
    }
    {
      eapply transf_function_at in H as ?;eauto.
      exploit find_function_translated;eauto.
      exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
      intro FIND'.
      Esimpl. constructor. eapply exec_Itailcall;eauto.
      rewrite sig_preserved;auto.
      rewrite stacksize_preserved;auto.

      eresolvfp.
      rewrite stacksize_preserved.
      splitMS.
      apply regs_lessdef_regs;auto.
    }
    {
      eapply transf_function_at in H as ?;eauto.
      exploit (@eval_builtin_args_lessdef _ sge (fun r => rs#r) (fun r => rs'#r)); eauto.
      intros (vargs' & P & Q).
      exploit (MemOpFP.eval_builtin_args_fp_lessdef _ sge (fun r => rs#r) (fun r => rs'#r)); eauto.
      intros EVALFP.
      exploit external_call_mem_extends; eauto.
      intros [v' [m'1 [A [B [C D]]]]].
      pose proof A as A'. apply helpers.i64ext_effects in A'. destruct A'; subst.
      Esimpl. constructor. eapply exec_Ibuiltin;eauto.
      eapply eval_builtin_args_preserved with(ge1:=sge);eauto. exact symbols_preserved.
      eapply MemOpFP.eval_builtin_args_fp_preserved. apply senv_preserved. eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      eresolvfp.
      splitMS.
      eapply reach_succ;eauto. simpl;auto.
      eapply set_res_lessdef;eauto.
      auto.
    }
    {
      eapply transf_function_at in H as ?;eauto.
      exploit eval_condition_lessdef_fp; try eassumption. apply regs_lessdef_regs; eauto.
      intros [fp' [EVALFP FPINJ]].
      Esimpl. econstructor.
      eapply exec_Icond; eauto.
      apply eval_condition_lessdef with (rs##args) m; eauto. apply regs_lessdef_regs; eauto.
      eresolvfp.
      destruct b;splitMS;eapply reach_succ;eauto; simpl;auto.
    }
    {
      (*jumptable*)
      eapply transf_function_at in H as ?;eauto.
      Esimpl. constructor. eapply exec_Ijumptable. eauto.
      specialize (RLD arg). inv RLD;try eassumption.
      rewrite H0 in H4. inv H4.
      rewrite list_nth_z_map, H1.
      simpl. eauto.
      eresolvfp.
      splitMS.
      eapply reach_succ;eauto. simpl;auto.
      eapply list_nth_z_in;eauto.
    }
    {
      eapply transf_function_at in H as ?;eauto.
      exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
      Esimpl. econstructor. eapply exec_Ireturn;eauto.
      rewrite stacksize_preserved.
      eresolvfp.
      splitMS. destruct or;auto. apply RLD.
      rewrite stacksize_preserved. eresolvfp.
    }
    {
      
      simpl.
      eapply Mem.alloc_extends in MLD as ?;eauto.
      Hsimpl.
      Esimpl. econstructor. eapply exec_function_internal.
      rewrite stacksize_preserved. eauto.
      rewrite stacksize_preserved. eauto.
      unfold MemOpFP.alloc_fp. erewrite Mem.mext_next; eauto.
      eresolvfp.
      splitMS. unfold reach. constructor.
      simpl.
      apply regs_lessdef_init_regs. auto.
      unfold local_block.
      destruct (plt stk (Genv.genv_next sge)); unfold Plt, Ple in *; [|lia].
      exfalso. apply Mem.alloc_result in H. subst.
      erewrite LDSimDefs.mu_shared_src in SVALID;[|inv AGMU;eauto].
      specialize (SVALID (Mem.nextblock m) p). unfold Mem.valid_block, Plt in SVALID.
      lia.
      unfold MemOpFP.alloc_fp. erewrite Mem.mext_next; eauto.
      eresolvfp.
      Lia.lia.
      Lia.lia.
    }
    {
      exploit external_call_mem_extends; eauto.
      intros [res' [m2' [A [B [C D]]]]].
      pose proof A as A'. apply helpers.i64ext_effects in A'; auto. destruct A'; subst.
      Esimpl. econstructor. econstructor;eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      eresolvfp. splitMS.
    }
    {
      inv STACKS.
      Esimpl. constructor.  econstructor.
      eresolvfp.
      splitMS.
      eapply set_reg_lessdef;eauto.
    }
  }
  {
    unfold at_external_local; simpl; unfold at_external; simpl.
    intros. invMS. inv MS; try discriminate.
    destruct f0; simpl; try discriminate. destruct e; try discriminate.
    destruct invert_symbol_from_string eqn:FINDID; try discriminate.
    erewrite match_genvs_invert_symbol_from_string_preserved; eauto using genv_match.
    destruct peq; simpl in *; try discriminate.
    destruct peq; simpl in *; try discriminate.
    inv H0. exists 0%nat. eexists. split; eauto. split.
    { simpl in *. unfold LDSimDefs.arg_rel.
      revert args' AGMU H2 VLD ; clear.
      (** should be extracted as a lemma ... *)
      induction argSrc; intros args' AGMU GARG LD. simpl. inv LD. auto. inv LD. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto. destruct v2; auto.
      simpl in H2. eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H; eauto.
      intro. inv H0. econstructor. unfold Bset.inj_to_meminj; rewrite H. eauto. rewrite Ptrofs.add_zero; auto. }
    split. eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    split; eresolvfp. split.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    splitMS.
    intros. inv H; auto. inv H3. destruct f1; simpl; auto. 
  }
  {
      simpl. unfold after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    destruct Hcore; try discriminate. destruct f; try discriminate. destruct e; try discriminate.
    invMS; inv MS; try discriminate.
    assert (oresSrc = oresTgt).
    { destruct oresSrc, oresTgt; try contradiction; auto. simpl in RESREL.
      inv RESREL; simpl in GRES; auto; try contradiction.
      inv AGMU. apply proper_mu_inject_incr in H. inv H. rewrite Ptrofs.add_zero. auto. }
    subst. 
    assert (Hcore' = Core_Returnstate stack (match oresTgt with Some v => v | None => Vundef end)).
    { destruct oresTgt, (sig_res sg); inv AFTEXT; auto. 
      destruct (val_has_type_func v t); inv H0. auto. } 
    rename H into AFTEXT'.
    exists (Core_Returnstate s' (match oresTgt with Some v => v | None => Vundef end)). split.
    { destruct oresTgt, (sig_res sg); try discriminate; auto.
      destruct val_has_type_func; try discriminate; auto. }
    intros Hm' Lm' [HRELY LRELY INV]. subst. exists 0%nat. splitMS.
    inv AGMU; eapply extends_rely_extends; eauto. econstructor; eauto.
    intros ? S. apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT; auto.
    intros ? T. apply TVALID in T. unfold Mem.valid_block in *. inv LRELY. rewrite EQNEXT; auto.
    inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
  }
  {
    simpl. unfold halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES. destruct Hcore, stack; try discriminate.
    invMS. inv HALT. inv MS. inv STACKS.
    exists resSrc. Esimpl;eauto.
    f_equal. inv VLD;auto. contradiction.
    {
      revert VLD GRES AGMU. clear;intros.
      destruct resSrc; try constructor. econstructor. simpl in GRES. inv AGMU.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. inv A. unfold Bset.inj_to_meminj; rewrite INJ; eauto. rewrite Ptrofs.add_zero; auto. }
    inv AGMU; eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto.
    eresolvfp. inv AGMU; eapply extends_reach_closed_implies_inject; eauto.
  }
Qed.

End PRESERVATION.