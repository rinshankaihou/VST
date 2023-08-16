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

Require Import Coqlib Integers Maps Values AST Globalenvs.
Require Import CUAST InteractionSemantics Footprint.
Require Import IS_local.
Require Import Memory Blockset Op_fp Linear Linear_local val_casted.
Require Import InjRels LDSimDefs_local LDSim_local.
Require Import Errors CleanupLabels cleanuplabels.
Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.
Definition match_cu (su tu:Linear_comp_unit):=
  match_comp_unit_gen (fun f tf => OK (transf_fundef f) = OK tf) eq su tu.
Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_cu p tp.
Proof.
  intros. eapply match_transform_partial_cunit. auto.
Qed.
Section PRESERVATION.
Variable scu tcu: Linear_comp_unit.
Variable sge tge: Linear.genv.
Hypothesis SGEINIT: globalenv_generic scu sge.
Hypothesis TGEINIT: globalenv_generic tcu tge.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).
Hypothesis TRANSF: match_cu scu tcu.
Lemma ge_match: ge_match_strict sge tge.
Proof. eapply match_cu_ge_match_strict; eauto. Qed.
Lemma genv_match: Genv.match_genvs (match_globdef (fun f tf => OK (transf_fundef f) = OK tf) eq) sge tge.
Proof. eapply match_cu_match_genv; eauto. Qed.
Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof. destruct genv_match; eauto. Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: Linear.fundef),
  Genv.find_funct_ptr sge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  destruct genv_match.  unfold transf_fundef in *.
  unfold Genv.find_funct_ptr,Genv.find_def;intros.
  destruct (Maps.PTree.get) eqn:?;inv H.
  destruct g eqn:?;inv H1.  specialize (mge_defs b). rewrite Heqo in mge_defs.
  inv mge_defs.  inv H1. inv H2. auto.
Qed.
Lemma functions_translated:
  forall (v: val) (f: Linear.fundef),
  Genv.find_funct sge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  destruct v;simpl;intros;try discriminate. destruct Ptrofs.eq_dec;inv H.
  apply funct_ptr_translated;assumption.
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
  unfold transf_function. intros. destruct (zeq (fn_stacksize f) 0); auto.
Qed.
Lemma find_function_translated:
  forall ros rs f, find_function sge ros rs = Some f ->
  find_function tge ros rs = Some (transf_fundef f).
Proof.
  intros until f; destruct ros; simpl. unfold Genv.find_funct;intros.
  destruct rs;inv H.  destruct Ptrofs.eq_dec;inv H1.
  apply funct_ptr_translated;assumption.
  intros. destruct Genv.find_symbol eqn:?;inv H.
  erewrite symbols_preserved,Heqo;eauto. apply funct_ptr_translated;assumption.
Qed.
Definition match_locset(l1 l2:locset):Prop:=
  forall loc, Val.lessdef (l1 loc)(l2 loc).
Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp rs ls0 c,
    match_locset rs ls0->
    incl c f.(fn_code) ->
    match_stackframes (Stackframe f sp rs c)
    (Stackframe (transf_function f) sp ls0
       (remove_unused_labels (labels_branched_to (fn_code f)) c)).
Lemma match_locset_refl: forall l, match_locset l l.
Proof. unfold match_locset;intros. destruct l;constructor. Qed.
Definition state:Type:=core*mem.
Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp c ls m ts ls0 m' ls2 f' ls3,
      list_forall2 match_stackframes s ts ->
      match_locset ls ls0->
      Mem.extends m m'->
      incl c f.(fn_code) ->
      match_locset ls2 ls3 ->
      match_states (Core_State s f sp c ls (mk_load_frame ls2 f'), m)
                   (Core_State ts (transf_function f) sp (remove_unused_labels (labels_branched_to f.(fn_code)) c) ls0 
                    (mk_load_frame ls3 (transf_function f')), m')
  | match_states_in:
      forall s ls m ts ls0 m' f,
      list_forall2 match_stackframes s ts ->
      match_locset ls ls0->
      Mem.extends m m'->
      match_states (Core_CallstateIn s (Internal f) ls (mk_load_frame ls f), m)
                   (Core_CallstateIn ts (transf_fundef (Internal f)) ls0 (mk_load_frame ls0 (transf_function f)), m')
  | match_states_call:
      forall s ls m ts ls0 m' fd f0 ls2 ls3,
      list_forall2 match_stackframes s ts ->
      match_locset ls ls0->
      Mem.extends m m'->
      match_locset ls2 ls3 ->
      match_states (Core_Callstate s fd ls (mk_load_frame ls2 f0), m)
                   (Core_Callstate ts (transf_fundef fd) ls0 (mk_load_frame ls3 (transf_function f0)), m')                                
  | match_states_return:
      forall s ls m ts ls0 m' f ls2 ls3,
      list_forall2 match_stackframes s ts ->
      match_locset ls ls0 ->
      Mem.extends m m' ->
      match_locset ls2 ls3 ->
      match_states (Core_Returnstate s ls (mk_load_frame ls2 f), m)
                   (Core_Returnstate ts  ls0 (mk_load_frame ls3 (transf_function f)), m').
Definition measure (st: core) : nat :=
  match st with
  | Core_State s f sp c ls m => List.length c
  | _ => O
  end.
Definition MS (_ : bool) n mu fp fp' cm cm': Prop :=
  match_states cm cm' /\
  Injections.FPMatch' mu fp fp' /\
  let (c, m) := cm in
  let (c', m') := cm' in
  (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
  (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
  (proper_mu sge tge inject_id mu) /\
  (MemClosures_local.unmapped_closed mu m m') /\
  n = measure c /\ true = true.
Ltac invMS :=
  match goal with
  | H: MS _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    destruct cm1 as [sc Hm]; destruct cm2 as [tc Lm];
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU [RCPRESV [INDEX FLAG]]]]]]]
  | H: MS _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU [RCPRESV [INDEX FLAG]]]]]]]
  end.
Lemma match_parent_locset:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  match_locset (parent_locset s) (parent_locset ts).
Proof.
  clear.
  intros. inv H. constructor.
  destruct a1, b1; auto. simpl. unfold match_locset. intros.
  inv H0. auto.
Qed.
Lemma val_lessdef_list_refl: forall s, Val.lessdef_list s s.
Proof. induction s;auto. Qed.
Lemma v_v0_inj_refl: forall mu v v0,
Val.inject (Bset.inj_to_meminj (Injections.inj mu)) v v0 ->
LDSimDefs.G_arg (Injections.SharedSrc mu) v ->
inject_incr (Bset.inj_to_meminj (Injections.inj mu)) inject_id -> v = v0.
Proof.
  intros. inv H; auto; try contradiction. eapply H1 in H2. 
  unfold inject_id in H2. inv H2. rewrite Ptrofs.add_zero; auto.
Qed.
Lemma same_val_from_matchlocset : forall mu rp rs rs1,
LDSimDefs.G_arg (Injections.SharedSrc mu) (get_result rp  rs) ->
match_locset rs rs1 ->
Some (get_result rp rs1) = Some (get_result rp rs).
Proof.
  intros.
  unfold match_locset in H0. unfold LDSimDefs.G_arg in H.
  unfold get_result. destruct rp. 
  specialize (H0 (Locations.R r)) as ?.
  inv H1; try discriminate. rewrite H4; auto.
  unfold get_result in H. rewrite <- H3 in H; try contradiction. unfold get_result in H.
  specialize (H0 (Locations.R rhi)) as ?. inv H1. 
  specialize (H0 (Locations.R rlo)) as ?. inv H1. auto.
  destruct (rs (Locations.R rhi)); simpl in *; auto.
  rewrite <-  H3 in H; try contradiction. rewrite <- H3 in H. simpl in *. contradiction.
Qed.
Lemma set_locset_lessdef:
  forall ls ls' v v' l, 
    match_locset ls ls' -> Val.lessdef v v' ->
    match_locset (Locations.Locmap.set l v ls) (Locations.Locmap.set l v' ls').
Proof.
  clear. intros. intro l0.
  unfold Locations.Locmap.set. destruct Locations.Loc.eq.
  subst. destruct l0; auto. apply Val.load_result_lessdef; auto.
  destruct Locations.Loc.diff_dec; auto.
Qed.
Lemma setpair_locset_lessdef:
  forall ls ls' v v' l, 
    match_locset ls ls' -> Val.lessdef v v' ->
    match_locset (Locations.Locmap.setpair l v ls) (Locations.Locmap.setpair l v' ls').
Proof.
  clear. intros. intro l0.
  unfold Locations.Locmap.setpair.
  destruct l. eapply set_locset_lessdef; eauto.
  eapply set_locset_lessdef; eauto. eapply set_locset_lessdef; eauto.
  eapply Val.hiword_lessdef; eauto. eapply Val.loword_lessdef; eauto.
Qed.
Lemma undef_locset_lessdef:
  forall ls ls' rl,
    match_locset ls ls' -> match_locset (LTL.undef_regs rl ls) (LTL.undef_regs rl ls').
Proof.
  clear. induction rl; intros; auto. apply IHrl in H. simpl. eapply set_locset_lessdef. auto. auto.
Qed.
Lemma call_locset_lessdef:
  forall ls ls',
    match_locset ls ls' ->
    match_locset (LTL.call_regs ls) (LTL.call_regs ls').
Proof.
  clear. intros. unfold LTL.call_regs. intro l. destruct l; auto. destruct sl; auto.
Qed.
Lemma remove_unused_labels_cons:
  forall bto i c,
  remove_unused_labels bto (i :: c) =
  match i with
  | Llabel lbl =>
      if Labelset.mem lbl bto then i :: remove_unused_labels bto c else remove_unused_labels bto c
  | _ =>
      i :: remove_unused_labels bto c
  end.
Proof.
  unfold remove_unused_labels; intros. rewrite list_fold_right_eq. auto.
Qed.
Lemma lessdef_list : forall rs ls0 args,
match_locset rs ls0 ->
Val.lessdef_list (LTL.reglist rs args) (LTL.reglist ls0 args).
Proof.
  intros. unfold match_locset in H. induction args. simpl. auto. constructor.
  apply H. auto.
Qed.
Lemma find_function_lessdef:
  forall ros ls tfd ls',
    find_function sge ros ls = Some tfd -> match_locset ls ls' ->
    find_function sge ros ls' = Some tfd.
Proof.
  clear. unfold find_function; intros. destruct ros; auto.
  unfold Genv.find_funct in *.
  specialize (H0 (Locations.R m)). inv H0; auto. rewrite <- H2 in H. discriminate.
Qed.
Lemma return_locset_lessdef:
  forall ls ls0 ls' ls0',
    match_locset ls ls' -> match_locset ls0 ls0' ->
    match_locset (LTL.return_regs ls0 ls) (LTL.return_regs ls0' ls').
Proof.
  clear. intros. intro l0. unfold LTL.return_regs. destruct l0; auto.
  destruct (Conventions1.is_callee_save r); auto.
Qed.
Lemma setres_locset_lessdef:
  forall res ls ls' vres vres',
    match_locset ls ls' ->
    Val.lessdef vres vres' ->
    match_locset (Locations.Locmap.setres res vres ls)
                   (Locations.Locmap.setres res vres' ls').
Proof.
  clear. induction res; simpl; intros; intro l; auto.
  - apply set_locset_lessdef; auto. 
  - apply IHres2. apply IHres1. auto.
    apply Val.hiword_lessdef; auto. apply Val.loword_lessdef; auto.
Qed.
Lemma match_locset0: forall s ts rs0,
list_forall2 match_stackframes s ts ->
match_locset (parent_locset0 rs0 s) (parent_locset0 rs0 ts).
Proof.
  intros. inv H. constructor.
  unfold parent_locset0. destruct a1, b1.  inv H0. auto.
Qed.

Lemma match_locset0_match_ld : forall locset_inv1 locset_inv2 s ts,
match_locset locset_inv1 locset_inv2 ->
list_forall2 match_stackframes s ts ->
match_locset (parent_locset0 locset_inv1 s) (parent_locset0 locset_inv2 ts).
Proof.
  intros.
  unfold parent_locset0. destruct s, ts. auto. inv H0. inv H0.
  destruct s, s1. inv H0. inv H4. auto.
Qed.
Definition instr_branches_to (i: instruction) (lbl: label) : Prop :=
  match i with
  | Lgoto lbl' => lbl = lbl'
  | Lcond cond args lbl' => lbl = lbl'
  | Ljumptable arg tbl => In lbl tbl
  | _ => False
  end.
Remark add_label_branched_to_incr:
  forall ls i, Labelset.Subset ls (add_label_branched_to ls i).
Proof.
  intros; red; intros; destruct i; simpl; auto.
  apply Labelset.add_2; auto. apply Labelset.add_2; auto.
  revert H; induction l; simpl. auto. intros; apply Labelset.add_2; auto.
Qed.
Remark add_label_branched_to_contains:
  forall ls i lbl, instr_branches_to i lbl -> Labelset.In lbl (add_label_branched_to ls i).
Proof.
  destruct i; simpl; intros; try contradiction.
  apply Labelset.add_1; auto. apply Labelset.add_1; auto.
  revert H. induction l; simpl; intros. contradiction.
  destruct H. apply Labelset.add_1; auto. apply Labelset.add_2; auto.
Qed.
Lemma labels_branched_to_correct:
  forall c i lbl,
  In i c -> instr_branches_to i lbl -> Labelset.In lbl (labels_branched_to c).
Proof.
  intros. assert (forall c' bto, Labelset.Subset bto (fold_left add_label_branched_to c' bto)).
  induction c'; intros; simpl; red; intros.
  auto. apply IHc'. apply add_label_branched_to_incr; auto.
  assert (forall c' bto, In i c' -> Labelset.In lbl (fold_left add_label_branched_to c' bto)).
  induction c'; simpl; intros. contradiction. destruct H2.
  subst a. apply H1. apply add_label_branched_to_contains; auto.  apply IHc'; auto.
  unfold labels_branched_to. auto.
Qed.
Lemma find_label_commut:
  forall lbl bto, Labelset.In lbl bto ->
  forall c c', find_label lbl c = Some c' ->
  find_label lbl (remove_unused_labels bto c) = Some (remove_unused_labels bto c').
Proof.
  induction c; simpl; intros. congruence.
  rewrite remove_unused_labels_cons. unfold is_label in H0. destruct a; simpl; auto.
  destruct (peq lbl l). subst l. inv H0.
  rewrite Labelset.mem_1; auto. simpl. rewrite peq_true. auto.
  destruct (Labelset.mem l bto); auto. simpl. rewrite peq_false; auto.
Qed.
Corollary find_label_translated:
  forall f i c' lbl c,
  incl (i :: c') (fn_code f) ->
  find_label lbl (fn_code f) = Some c ->
  instr_branches_to i lbl ->
  find_label lbl (fn_code (transf_function f)) =
     Some (remove_unused_labels (labels_branched_to (fn_code f)) c).
Proof.
  intros. unfold transf_function; unfold cleanup_labels; simpl.
  apply find_label_commut. eapply labels_branched_to_correct; eauto.
  apply H; auto with coqlib.
  auto.
Qed.
Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (is_label lbl a). inv H; auto with coqlib. auto with coqlib.
Qed.
Lemma find_function_temp : forall locset_inv1 locset_inv2 f' loc,
match_locset locset_inv1 locset_inv2 ->
Genv.find_funct sge (locset_inv1 loc) = Some f' ->
Genv.find_funct tge (locset_inv2 loc) = Some (transf_fundef f').
Proof.
  intros.
  assert (locset_inv1 loc = locset_inv2 loc).
  unfold match_locset in H. specialize (H loc) as ?.
  inv H1; auto. rewrite <- H3 in H0. inv H0. rewrite <- H1. eapply functions_translated; auto.
Qed.
Lemma find_function_matchlocset : forall locset_inv1 locset_inv2 locset_src locset_tgt s ts ros f',
match_locset locset_inv1 locset_inv2 ->
match_locset locset_src locset_tgt ->
list_forall2 match_stackframes s ts ->
find_function sge ros (LTL.return_regs (parent_locset0 locset_inv1 s) locset_src) =  Some f' ->
(find_function tge ros (LTL.return_regs (parent_locset0 locset_inv2 ts) locset_tgt) =
 Some (transf_fundef f')).
Proof.
  intros. destruct ros. simpl in *.
  destruct (Conventions1.is_callee_save m). simpl in *.
  unfold parent_locset0 in *. destruct ts. simpl in *.
  destruct s. simpl in *. unfold match_locset in H. eapply find_function_temp; eauto.
  destruct s. simpl in *. inv H1.
  simpl in *. destruct s0. simpl in *.
  destruct s. inv H1. destruct s. inv H1. inv H6. eapply find_function_temp; eauto.
  eapply find_function_temp; eauto.
  simpl in *. destruct (Genv.find_symbol sge i) eqn:?; try discriminate.
  assert (Genv.find_symbol tge i = Genv.find_symbol sge i). 
  eapply symbols_preserved. rewrite H3. rewrite Heqo. eapply funct_ptr_translated; auto.
Qed.
Lemma incl_less : forall a b f,
incl (a::b) f.(fn_code) -> incl b f.(fn_code).
Proof.
  clear. intros. unfold incl in *.  intros. specialize (H a0) as ?. apply H1. clear H1.
  eapply in_cns. right. auto.
Qed.
Lemma incl_rel : forall a,
incl a.(fn_code) a.(fn_code).
Proof.
  intros. unfold incl. intros. auto.
Qed.
Lemma locset_lessdef_args:
  forall ls ls' args,
    match_locset ls ls' ->
    Val.lessdef_list (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p ls) args)
                     (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p ls') args).
Proof. clear. induction args; auto. intros. constructor; auto.
       unfold Locations.Locmap.getpair. destruct a; auto.
       apply Val.longofwords_lessdef; auto. Qed.
Lemma fp_matchemp : forall mu Hfp Lfp,
 Injections.FPMatch' mu Hfp Lfp ->
 Injections.FPMatch' mu (FP.union Hfp empfp) (FP.union Lfp empfp).
Proof.
  intros. assert (FP.union Hfp empfp = Hfp) by eapply FP.fp_union_emp.
  assert (FP.union Lfp empfp = Lfp) by eapply FP.fp_union_emp.
  rewrite H0. rewrite H1. auto.
Qed.
Lemma valid_block_sm' : forall mu sm tm sm' tm',
mem_init_inj mu sm tm ->
LDefs.HLRely mu sm sm' tm tm' ->
forall b0 : block, Bset.belongsto (Injections.SharedSrc mu) b0 -> Mem.valid_block sm' b0 /\
forall b0 : block, Bset.belongsto (Injections.SharedTgt mu) b0 -> Mem.valid_block tm' b0.
Proof.
  split. intros. inv H. eapply dom_eq_src in H1. red. inv H0. inv H. rewrite EQNEXT;eauto.
  intros. inv H. eapply dom_eq_tgt in H2. red. inv H0. inv H3. rewrite EQNEXT;eauto.
Qed.

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
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x),
    H1: LDefs.Rely ?S ?m1 ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => intros ? X; unfold Mem.valid_block in *; apply H in X; inversion H1 as [EQNEXT ? ?]; rewrite EQNEXT;auto
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

Ltac Ex_index :=
  match goal with
  | |- context[Core_State ?s ?f ?sp ?pc ?rs] => exists (measure (Core_State s f sp pc rs))
  | |- context[Core_Callstate] => exists 0%nat
  | |- context[Core_Returnstate ?s ?v] => exists (measure (Core_Returnstate s v))
  end.
Ltac Right := right; do 4 eexists; split; [apply plus_one|resolvfp].
Ltac FP:= match goal with |- ?P /\ _ => assert P; [eresolvfp| try (split;[auto; fail|])] end.
Ltac Left := left; Ex_index; split; [auto|eresolvfp].
Ltac splitMS :=
  split;
  [econstructor; eresolvfp |
   split; [eresolvfp|
           split; [try resvalid; auto |
                   split; [try resvalid; auto
                          |split; [auto|
                                   split; [try resvalid; eauto|
                                           split; eauto]]]]]].
Ltac inv_eq:=
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; inversion H ;subst
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;subst;try contradiction;try discriminate.
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

Ltac resolv_ls :=
  match goal with
  | |- match_locset (Locations.Locmap.set _ _ _) (Locations.Locmap.set _ _ _) =>
    apply set_locset_lessdef; auto; resolv_ls
  | |- match_locset (LTL.undef_regs _ _) (LTL.undef_regs _ _) =>
    apply undef_locset_lessdef; auto; resolv_ls
  | |- match_locset (LTL.return_regs _ _) (LTL.return_regs _ _) =>
    apply return_locset_lessdef; auto; resolv_ls
  | |-  match_locset (LTL.call_regs _ _) (LTL.return_regs _ _) =>
    apply call_locset_lessdef; auto; resolv_ls
  | |-  match_locset (Locations.Locmap.setres _ _ _) (Locations.Locmap.setres _ _ _) =>
    apply setres_locset_lessdef; auto; resolv_ls
  | |- match_locset (Locations.Locmap.setpair _ _ _) (Locations.Locmap.setpair _ _ _) =>
    apply setpair_locset_lessdef; auto; resolv_ls                                         
  | _ => idtac
  end.
Lemma val_inject_proper_mu : forall mu l,
    proper_mu sge tge inject_id mu -> LDSimDefs.G_arg (Injections.SharedSrc mu) l->
    Val.inject (Bset.inj_to_meminj (Injections.inj mu)) l l.
Proof.
  intros. destruct l;eauto.  econstructor. inv H. unfold Bset.inj_to_meminj.  eapply Bset.inj_dom in H0; eauto. destruct H0 as [b' INJ].  exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
  intro A. rewrite INJ. inv A. eauto. rewrite Ptrofs.add_zero; auto. Qed.
Lemma match_loc_inject_list: forall mu l1 l2,
  proper_mu sge tge inject_id mu ->
  LDSimDefs.G_args (Injections.SharedSrc mu) l1 ->
  Val.lessdef_list l1 l2 ->
  Val.inject_list (Bset.inj_to_meminj (Injections.inj mu)) l1 l2.
Proof.
  intros. induction H1. constructor. constructor. inv H0. destruct v1,v2; try auto; try inv H1; try auto. eapply val_inject_proper_mu;eauto. eapply IHlessdef_list;eauto. inv H0. auto. Qed.
Lemma cleanuplabels_local_ldsim:
  @local_ldsim_properties Linear_IS Linear_IS nat lt sge tge sge tge MS.
Proof.
  econstructor;eauto.
  apply lt_wf.
  intros;invMS;inv AGMU;auto.
  intros;invMS;inv AGMU;auto.
  apply ge_match.
  { (*init*)
    intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    unfold init_core_local in *. simpl in *. unfold init_core in *.
    unfold generic_init_core in INITCORE |- *.
    erewrite symbols_preserved.
    inv_eq. erewrite funct_ptr_translated;eauto. unfold fundef_init in *.
    inv_eq. clear H0. erewrite wd_args_inject;eauto. Esimpl;eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists 0%nat. splitMS. constructor.
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. 
      induction args; intros args' REL G MEMREL; inv REL. auto. inv G. f_equal. 
      inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. } subst.  constructor.
    { inv MEMINITINJ; inv HRELY; inv LRELY.
      eapply inject_implies_extends;eauto.
      intros b0 A. unfold Mem.valid_block in A; rewrite EQNEXT, <- dom_eq_src in A. 
      eapply Bset.inj_dom in A; eauto. destruct A as [b' A]. 
      unfold Bset.inj_to_meminj. rewrite A. eauto. inv GE_INIT_INJ. 
      rewrite mu_shared_src in dom_eq_src. rewrite mu_shared_tgt in dom_eq_tgt. 
      rewrite S_EQ in dom_eq_src.
      assert (forall b, Plt b (Mem.nextblock sm0) <-> Plt b (Mem.nextblock tm0)).
      { intro. rewrite <- dom_eq_src, <- dom_eq_tgt. tauto. }
      rewrite EQNEXT, EQNEXT0.
      destruct (Pos.lt_total (Mem.nextblock sm0) (Mem.nextblock tm0)) as [LT | [EQ | LT]]; auto;
        (generalize H3 LT; clear; intros; exfalso; apply H3 in LT; eapply Pos.lt_irrefl; eauto). }
    inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. 
    apply dom_eq_src; auto. inv MEMINITINJ. inv LRELY. 
    unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto.    
    inv MEMINITINJ; econstructor; eauto. simpl. intro.
    intros ? ? ? ? ? . exploit inj_inject_id. exact H. intro. inv H0.
    intro A. inv A. auto. apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
  }
  {
    intros. simpl in *. induction H0; invMS; inv MS; try rewrite remove_unused_labels_cons.
    {
      Right. econstructor. eauto. split. eresolvfp. splitMS. resolv_ls. eapply incl_less; eauto. 
    }
    {
      Right. econstructor. eauto. split. eresolvfp. splitMS. resolv_ls. eapply incl_less; eauto. 
    }
    {
      rewrite (Op.eval_operation_preserved tge sge) in H0.
      rewrite (eval_operation_fp_preserved tge sge) in H1.
      eapply (lessdef_list rs ls0 args) in H12 as ?.
      intros. eapply Op.eval_operation_lessdef in H0 as ?; eauto. do 2 destruct H2.
      eapply eval_operation_lessdef_fp in H1; eauto. do 2 destruct H1. Right. econstructor;eauto.
      split. eresolvfp. splitMS. resolv_ls.  eapply incl_less; eauto. 
      symmetry. eapply symbols_preserved. symmetry. eapply symbols_preserved.
    }
    {
     eapply (lessdef_list rs ls0 args) in H13 as ?.
     intros. eapply Op.eval_addressing_lessdef in H0; eauto. do 2 destruct H0.
     destruct a; try discriminate. inv H2.
     eapply Mem.loadv_extends in H1; eauto. destruct H1. destruct H1. Right. econstructor;eauto. 
     erewrite Op.eval_addressing_preserved;eauto. eapply symbols_preserved. split. 
     eresolvfp. splitMS. resolv_ls. eapply incl_less;eauto. 
    }
    {
      eapply (lessdef_list rs ls0 args) in H13 as ?. intros. 
      eapply Op.eval_addressing_lessdef in H0; eauto. destruct H0. destruct H0. 
      destruct a; try discriminate. inv H2. eapply Mem.storev_extends in H1 as ?; eauto. 
      destruct H2. destruct H2. Right. econstructor;eauto. 
      erewrite Op.eval_addressing_preserved;eauto. eapply symbols_preserved. split. 
      eresolvfp. simpl in *;splitMS. resolv_ls. eapply incl_less;eauto.
    }
    {
      Right. econstructor.
      instantiate(1:=transf_fundef f'). eapply find_function_translated.
      eapply find_function_lessdef in H0 as ?; eauto. symmetry. eapply sig_preserved.
      split. eresolvfp. splitMS. constructor;eauto. constructor;eauto. eapply incl_less;eauto.
    }
    {
      eapply find_function_matchlocset in H1 as ?; eauto.
      eapply Mem.free_parallel_extends in H3 as ?; eauto. destruct H0. destruct H0.
      Right. econstructor;eauto. symmetry. eapply sig_preserved. split. eresolvfp.
      rewrite stacksize_preserved;eauto. eresolvfp. splitMS. eapply return_locset_lessdef;eauto.
      eapply match_locset0_match_ld;auto. rewrite stacksize_preserved. eresolvfp.
    }
    {
      eapply Events.eval_builtin_args_lessdef in H0 as ?; eauto. do 2 destruct H.
      eapply (Events.eval_builtin_args_preserved tge) in H.
      assert (MemOpFP.eval_builtin_args_fp tge rs sp args fp).
      eapply MemOpFP.eval_builtin_args_fp_preserved in H1; eauto. eapply symbols_preserved.
      assert (MemOpFP.eval_builtin_args_fp tge ls0 sp args fp).
      eapply MemOpFP.eval_builtin_args_fp_lessdef in H5; eauto.
      eapply Events.external_call_mem_extends in H3; eauto.
      destruct H3. destruct H3. destruct H3. destruct H7. destruct H8.
      eapply helpers.i64ext_effects in H3 as ?; eauto. destruct H11. subst.
      assert (Events.external_call ef tge x Lm Events.E0 x0 Lm).
      eapply Events.external_call_symbols_preserved in H3; eauto.
      eapply senv_preserved. Right. econstructor;eauto. split. eresolvfp. splitMS. resolv_ls.
      eapply incl_less;eauto. eapply symbols_preserved.
    }
    {
      destruct (Labelset.mem lbl (labels_branched_to (fn_code f))) eqn:?.
      Right. econstructor. split. eresolvfp. splitMS. eapply incl_less;eauto.
      left. eexists. split. eauto. splitMS. eapply incl_less;eauto.
    }
    {
      eapply find_label_incl in H0 as ?. 
      eapply find_label_translated in H0 as ?; eauto.
      Right. econstructor. eauto. split. eresolvfp. splitMS. constructor.
    }
    {
      eapply (lessdef_list rs ls0 args) in H13 as ?.
      eapply Op.eval_condition_lessdef in H0 as ?; eauto.
      eapply eval_condition_lessdef_fp in H1; eauto. destruct H1. destruct H1.
      eapply find_label_incl in H3 as ?; eauto.
      eapply find_label_translated in H3 as ?; eauto. Right. constructor;eauto. split. eresolvfp.
      splitMS. constructor.
    }
    { eapply (lessdef_list rs ls0 args) in H12 as ?.
      eapply Op.eval_condition_lessdef in H0 as ?; eauto.
      eapply eval_condition_lessdef_fp in H1; eauto. destruct H1. destruct H1.
      Right. eapply exec_Lcond_false; eauto. split. eresolvfp. splitMS. eapply incl_less;eauto.
    }
    {
      eapply find_label_incl in H2 as ?; eauto. Right. econstructor.
      unfold match_locset in H13. specialize (H13 (Locations.R arg)) as ?. inv H3;eauto.
      rewrite <- H5 in H0. inv H0. eauto. 
      eapply find_label_translated in H2 as ?; eauto. simpl. eapply list_nth_z_in; eauto.
      eauto. split. eresolvfp. splitMS. resolv_ls. 
    }
    {
      eapply Mem.free_parallel_extends in H0 as ?; eauto. destruct H. destruct H. Right. 
      econstructor;eauto. split. eresolvfp. rewrite stacksize_preserved. eresolvfp. splitMS. 
      resolv_ls. eapply match_locset0_match_ld;eauto. rewrite stacksize_preserved. eresolvfp.
    }
    {
      assert ((fn_stacksize f) <= (fn_stacksize (transf_function f)) ). simpl. Lia.lia.
      assert (0 <= 0) by Lia.lia. eapply Mem.alloc_extends in H0 as ?; eauto. destruct H2. 
      destruct H2. Right. econstructor;eauto. split. eresolvfp. 
      rewrite stacksize_preserved;eauto. 
      unfold MemOpFP.alloc_fp. inv H11. rewrite mext_next. eresolvfp. splitMS. resolv_ls.
      eapply call_locset_lessdef. auto. eapply incl_rel. rewrite stacksize_preserved.
      unfold MemOpFP.alloc_fp. inv H11. rewrite mext_next. eresolvfp.
    }
    {
      Right. econstructor. split. eresolvfp. splitMS.
    }
    {
      cut (Val.lessdef_list  (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p rs1)
            (Conventions1.loc_arguments (ef_sig ef)))
          (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p ls0)
       (Conventions1.loc_arguments (ef_sig ef)))).
     intros. eapply Events.external_call_mem_extends in H2 as ?; eauto.
     destruct H0. destruct H0. destruct H0. destruct H3. destruct H4.
     eapply helpers.i64ext_effects in H0 as ?; eauto. destruct H6. subst.
     Right. econstructor;eauto. eapply Events.external_call_symbols_preserved in H0;eauto.
     eapply senv_preserved. split. eresolvfp. splitMS. resolv_ls. eapply locset_lessdef_args;auto.
    }
    {
      inv H4. inv H1. Right. econstructor. split. eresolvfp. splitMS.
    }
  }
  {
    intros. simpl in *. unfold at_external in *. invMS. inv MS; try discriminate.
    intros. destruct fd; simpl in *; try discriminate. destruct e; simpl in *; try discriminate.
    destruct invert_symbol_from_string eqn:FINDID; try discriminate.
    erewrite match_genvs_invert_symbol_from_string_preserved; eauto using genv_match.
    destruct peq; simpl in *; try discriminate. destruct peq; simpl in *; try discriminate.
    inv H0. exists 0%nat. eexists. split;auto. split;eauto. eapply match_loc_inject_list;eauto.
    eapply locset_lessdef_args;eauto. split.
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    split; auto. split. eapply extends_reach_closed_implies_inject; inv AGMU; eauto. splitMS.
    intros. inv H. destruct f1 eqn:?; destruct f2 eqn:?; simpl; auto; try inversion H3.
    auto. inv H3. auto.
  }
  { (*after_external*)
    intros. simpl in *. unfold after_external in *. invMS. inv MS; try discriminate; auto.
    destruct fd  eqn:?; simpl in *; try discriminate.
    destruct e eqn:?; simpl in *; try discriminate.
    destruct oresSrc eqn:?; simpl in *; try discriminate.
    destruct sig_res eqn:?; simpl in *; try discriminate.
    destruct val_has_type_func eqn:?; simpl in *; try discriminate.
    inv H1. destruct oresTgt eqn:?; simpl in *; try contradiction.
    assert (v = v0). unfold LDSimDefs.res_rel in H2. 
    destruct AGMU. apply v_v0_inj_refl with mu; auto. subst. rewrite Heqb. eexists.
    split. eauto. intros. eexists. inv AGMU. splitMS. resolv_ls. 
    eapply extends_rely_extends;eauto. inv H. resvalid. inv H. resvalid. constructor;eauto. inv H.
    inv H3. eapply MemClosures_local.reach_closed_unmapped_closed; eauto. 
    destruct sig_res eqn:?; simpl in *; try discriminate.
    inv H1. destruct oresTgt eqn:?; simpl in *; try contradiction. eexists. inv AGMU.
    split;eauto. intros. eexists. splitMS. resolv_ls. 
    eapply extends_rely_extends; eauto. inv H;resvalid. inv H;resvalid. constructor;eauto.
    inv H. inv H3;eapply MemClosures_local.reach_closed_unmapped_closed; eauto. 
  }

  {(*halt*)
    intros. simpl in *. unfold halted in *. destruct Hcore eqn:?; destruct stack eqn:?;
    destruct lf eqn:?; try discriminate.
    invMS. inv H0. exists ( (get_result (Conventions1.loc_result (fn_sig f)) rs)).
    destruct Lcore eqn:?. inv MS. inv MS. inv MS. 
    inv MS. inv H5. split. simpl in *. unfold match_locset in H11.
    unfold  LDSimDefs.G_arg in H2. eapply same_val_from_matchlocset; eauto. split.
    red. eapply val_inject_proper_mu;eauto. split. inv AGMU. 
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto. split. 
    auto. unfold LDefs.Inv. destruct AGMU. eapply extends_reach_closed_implies_inject; try auto.
  }
Qed.
End PRESERVATION.
Theorem transf_local_ldsim:
  forall su tu,
    cleanuplabels.transf_program su = OK tu->
    forall sge sG tge tG,
      init_genv_local Linear_IS su sge sG-> init_genv_local Linear_IS tu tge tG->
      Genv.genv_next sge = Genv.genv_next tge-> local_ldsim sG tG sge tge.
Proof.
  intros. simpl in *. destruct H0. subst. destruct H1. subst.
  econstructor. eapply  cleanuplabels_local_ldsim; eauto. apply transf_program_match. auto.
Qed.