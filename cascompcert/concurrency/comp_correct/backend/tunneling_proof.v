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

Require Import Values AST Globalenvs CUAST InteractionSemantics Footprint IS_local LTL LTL_local LDSim_local Tunneling tunneling Errors Integers Maps Op_fp LDSimDefs_local val_casted.
Require Import Memory Blockset InjRels.
Require Import Coqlib Lia.
Require Import Injections.
Import Axioms.

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.

Definition match_cu (su tu:LTL_comp_unit):=
  match_comp_unit_gen (fun f tf => OK (tunnel_fundef f) = OK tf) eq su tu.
Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_cu p tp.
Proof.
  intros. eapply match_transform_partial_cunit. auto.
Qed.


Definition measure_edge (u: U.t) (pc s: node) (f: node -> nat) : node -> nat :=
  fun x => if peq (U.repr u s) pc then f x
           else if peq (U.repr u x) pc then (f x + f s + 1)%nat
           else f x.

Definition record_goto' (uf: U.t * (node -> nat)) (pc: node) (b: bblock) : U.t * (node -> nat) :=
  match b with
  | Lbranch s :: b' => let (u, f) := uf in (U.union u pc s, measure_edge u pc s f)
  | _ => uf
  end.

Definition branch_map_correct (c: code) (uf: U.t * (node -> nat)): Prop :=
  forall pc,
  match c!pc with
  | Some(Lbranch s :: b) =>
      U.repr (fst uf) pc = pc \/ (U.repr (fst uf) pc = U.repr (fst uf) s /\ snd uf s < snd uf pc)%nat
  | _ =>
      U.repr (fst uf) pc = pc
  end.

Lemma record_gotos'_correct:
  forall c,
  branch_map_correct c (PTree.fold record_goto' c (U.empty, fun (x: node) => O)).
Proof.
  intros.
  apply PTree_Properties.fold_rec with (P := fun c uf => branch_map_correct c uf).
(* extensionality *)
  intros. red; intros. rewrite <- H. apply H0.
(* base case *)
  red; intros; simpl. rewrite PTree.gempty. apply U.repr_empty.
(* inductive case *)
  intros m uf pc bb; intros. destruct uf as [u f].
  assert (PC: U.repr u pc = pc).
    generalize (H1 pc). rewrite H. auto.
  assert (record_goto' (u, f) pc bb = (u, f)
          \/ exists s, exists bb', bb = Lbranch s :: bb' /\ record_goto' (u, f) pc bb = (U.union u pc s, measure_edge u pc s f)).
    unfold record_goto'; simpl. destruct bb; auto. destruct i; auto. right. exists s; exists bb; auto.
  destruct H2 as [B | [s [bb' [EQ B]]]].
(* u and f are unchanged *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct (peq pc' pc). subst pc'.
  destruct bb; auto. destruct i; auto.
  apply H1.
(* b is Lbranch s, u becomes union u pc s, f becomes measure_edge u pc s f *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct (peq pc' pc). subst pc'. rewrite EQ.
(* The new instruction *)
  rewrite (U.repr_union_2 u pc s); auto. rewrite U.repr_union_3.
  unfold measure_edge. destruct (peq (U.repr u s) pc). auto. right. split. auto.
  rewrite PC. rewrite peq_true. omega.
(* An old instruction *)
  assert (U.repr u pc' = pc' -> U.repr (U.union u pc s) pc' = pc').
    intro. rewrite <- H2 at 2. apply U.repr_union_1. congruence.
  generalize (H1 pc'). simpl. destruct (m!pc'); auto. destruct b; auto. destruct i; auto.
  intros [P | [P Q]]. left; auto. right.
  split. apply U.sameclass_union_2. auto.
  unfold measure_edge. destruct (peq (U.repr u s) pc). auto.
  rewrite P. destruct (peq (U.repr u s0) pc). omega. auto.
Qed.

Definition record_gotos' (f: function) :=
  PTree.fold record_goto' f.(fn_code) (U.empty, fun (x: node) => O).

Lemma record_gotos_gotos':
  forall f, fst (record_gotos' f) = record_gotos f.
Proof.
  intros. unfold record_gotos', record_gotos.
  repeat rewrite PTree.fold_spec.
  generalize (PTree.elements (fn_code f)) (U.empty) (fun _ : node => O).
  induction l; intros; simpl.
  auto.
  unfold record_goto' at 2. unfold record_goto at 2.
  destruct (snd a). apply IHl. destruct i; apply IHl.
Qed.

Definition branch_target (f: function) (pc: node) : node :=
  U.repr (record_gotos f) pc.

Definition count_gotos (f: function) (pc: node) : nat :=
  snd (record_gotos' f) pc.

Theorem record_gotos_correct:
  forall f pc,
  match f.(fn_code)!pc with
  | Some(Lbranch s :: b) =>
       branch_target f pc = pc \/
       (branch_target f pc = branch_target f s /\ count_gotos f s < count_gotos f pc)%nat
  | _ => branch_target f pc = pc
  end.
Proof.
  intros.
  generalize (record_gotos'_correct f.(fn_code) pc). simpl.
  fold (record_gotos' f). unfold branch_map_correct, branch_target, count_gotos.
  rewrite record_gotos_gotos'. auto.
Qed.

(** * Preservation of semantics *)
Section PRESERVATION.
Variable scu tcu: LTL_comp_unit.
Variable sge tge: LTL.genv.
Hypothesis SGEINIT: globalenv_generic scu sge.
Hypothesis TGEINIT: globalenv_generic tcu tge.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).
Hypothesis TRANSF: match_cu scu tcu.

Lemma ge_match: ge_match_strict sge tge.
Proof. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma genv_match: Genv.match_genvs (match_globdef (fun f tf => OK (tunnel_fundef f) = OK tf) eq) sge tge.
Proof. eapply match_cu_match_genv; eauto. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof. destruct genv_match; eauto. Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: LTL.fundef),
  Genv.find_funct_ptr sge b = Some f ->
  Genv.find_funct_ptr tge b = Some (tunnel_fundef f).
Proof.
  destruct genv_match.
  unfold tunnel_fundef in *.
  unfold Genv.find_funct_ptr,Genv.find_def;intros.
  destruct (Maps.PTree.get) eqn:?;inv H.
  destruct g eqn:?;inv H1.
  specialize (mge_defs b). rewrite Heqo in mge_defs.
  inv mge_defs.
  inv H1. inv H2. auto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: LTL.fundef),
  Genv.find_funct sge v = Some f ->
  Genv.find_funct tge v = Some (tunnel_fundef f).
Proof.
  destruct v;simpl;intros;try discriminate.
  destruct Ptrofs.eq_dec;inv H.
  apply funct_ptr_translated;assumption.
Qed.

Lemma senv_preserved:
  Senv.equiv sge tge.
Proof. eapply match_cu_senv_preserved; eauto. Qed.


Lemma sig_preserved:
  forall f, funsig (tunnel_fundef f) = funsig f.
Proof.
  destruct f; auto.
Qed.


Lemma stacksize_preserved:
  forall f, fn_stacksize (tunnel_function f) = fn_stacksize f.
Proof.
  unfold tunnel_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs f,
  find_function sge ros rs = Some f ->
  find_function tge ros rs = Some (tunnel_fundef f).
Proof.
  intros until f; destruct ros; simpl.
  unfold Genv.find_funct;intros.
  destruct rs;inv H.
  destruct Ptrofs.eq_dec;inv H1.
  apply funct_ptr_translated;assumption.

  intros. destruct Genv.find_symbol eqn:?;inv H.
  erewrite symbols_preserved,Heqo;eauto.
  apply funct_ptr_translated;assumption.
Qed.

Definition tunneled_block (f: function) (b: bblock) :=
  tunnel_block (record_gotos f) b.

Definition tunneled_code (f: function) :=
  PTree.map1 (tunneled_block f) (fn_code f).

Definition match_locset(l1 l2:locset):Prop:=
  forall loc, Val.lessdef (l1 loc)(l2 loc).

Lemma match_locset_refl: forall l, match_locset l l.
Proof. unfold match_locset;intros. destruct l;constructor. Qed.

Lemma find_function_translated_lessdef:
  forall ros rs ls f,
    match_locset rs ls ->
    find_function sge ros rs = Some f ->
    find_function tge ros ls = Some (tunnel_fundef f).
Proof.
   unfold find_function; intros. destruct ros. destruct (H (Locations.R m)); inversion H0. apply functions_translated; auto. rewrite symbols_preserved. destruct (Genv.find_symbol sge i). apply funct_ptr_translated; auto. inversion H0.
Qed.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall f sp ls ls0 bb,
        match_locset ls ls0->
        match_stackframes
          (Stackframe f sp ls bb)
          (Stackframe (tunnel_function f) sp ls0 (tunneled_block f bb)).

Definition state:Type:=core*mem.

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls ls0 ts sigres m m',
        list_forall2 match_stackframes s ts ->
        match_locset ls ls0->
        Mem.extends m m'->
        match_states (Core_State s f sp pc ls sigres, m)
                     (Core_State ts (tunnel_function f) sp (branch_target f pc) ls0 sigres, m')
  | match_states_block:
      forall s f sp bb ls ls0 m ts sigres m',
        list_forall2 match_stackframes s ts ->
        match_locset ls ls0->
        Mem.extends m m'->
        match_states (Core_Block s f sp bb ls sigres, m)
                     (Core_Block ts (tunnel_function f) sp (tunneled_block f bb) ls0 sigres, m')
  | match_states_interm:
      forall s f sp pc bb ls ls0 m ts sigres m',
        list_forall2 match_stackframes s ts ->
        match_locset ls ls0->
        Mem.extends m m'->
        match_states (Core_Block s f sp (Lbranch pc :: bb) ls sigres, m)
                     (Core_State ts (tunnel_function f) sp (branch_target f pc) ls0 sigres, m')
  | match_states_call:
      forall s f ls ls0 m ts sigres m',
        list_forall2 match_stackframes s ts ->
        match_locset ls ls0->
        Mem.extends m m' ->
        match_states (Core_Callstate s f ls sigres, m)
                     (Core_Callstate ts (tunnel_fundef f) ls0 sigres, m')
  | match_states_return:
      forall s ls ls0 m ts sigres m',
        list_forall2 match_stackframes s ts ->
        match_locset ls ls0->
        Mem.extends m m'->
        match_states (Core_Returnstate s ls sigres, m)
                     (Core_Returnstate ts ls0 sigres, m').
Definition measure (st: core) : nat :=
  match st with
  | Core_State s f sp pc ls res => (count_gotos f pc * 2)%nat
  | Core_Block s f sp (Lbranch pc :: _) ls res=> (count_gotos f pc * 2 + 1)%nat
  | Core_Block s f sp bb ls res=> 0%nat
  | Core_Callstate s f ls res => 0%nat
  | Core_Returnstate s ls res => 0%nat
  end.

Definition MS (b:bool) n mu fp fp' cm cm': Prop :=
  match_states cm cm' /\
  Injections.FPMatch' mu fp fp' /\
  let (c, m) := cm in
  let (c', m') := cm' in
  (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
  (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
  (proper_mu sge tge inject_id mu) /\
  (MemClosures_local.unmapped_closed mu m m') /\
  n = measure c /\ b = b.

End PRESERVATION.

Lemma match_parent_locset:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  match_locset (parent_locset s) (parent_locset ts).
Proof.
  unfold match_locset; intros. induction H. auto. destruct a1; destruct b1; simpl; auto. inversion H; subst. apply (H2 loc).
Qed.

Lemma return_regs_match_locset_preserved:
  forall s ts rs ls,
    match_locset rs ls ->
    match_locset s ts ->
    match_locset (return_regs s rs) (return_regs ts ls).
Proof.
  unfold match_locset; intros. unfold return_regs. destruct loc.
  - destruct (Conventions1.is_callee_save r); auto.
  - auto.
Qed.

Lemma call_regs_match_locset_preserved:
  forall rs ls,
    match_locset rs ls ->
    match_locset (call_regs rs) (call_regs ls).
Proof.
  unfold match_locset; intros. unfold call_regs. destruct loc.
  - auto.
  - destruct sl; auto.
Qed.

Lemma val_lessdef_list_refl: forall s, Val.lessdef_list s s.
Proof. induction s;auto. Qed.

Lemma code_preserved: forall f pc, option_map (tunnel_block (record_gotos f)) ((fn_code f) ! pc) = (fn_code (tunnel_function f)) ! pc.
Proof.
  intros. unfold tunnel_function, branch_target. simpl. symmetry. apply Maps.PTree.gmap1.
Qed.

Lemma match_locset_val_lessdef_list:
  forall rs ls args, match_locset rs ls -> Val.lessdef_list (reglist rs args) (reglist ls args).
Proof.
  intros. induction args; auto. simpl. constructor; auto.
Qed.

Lemma match_locset_set_preserved:
    forall l v v' rs rs', Val.lessdef v v' -> match_locset rs rs' -> match_locset (Locations.Locmap.set l v rs) (Locations.Locmap.set l v' rs').
Proof.
  unfold match_locset; intros. unfold Locations.Locmap.set.
  destruct (Locations.Loc.eq l loc).
  - destruct l. auto. apply Val.load_result_lessdef; auto.
  - destruct (Locations.Loc.diff_dec l loc); auto.
Qed.

Lemma match_locset_setres_preserved:
    forall res vres vres' rs rs', Val.lessdef vres vres' -> match_locset rs rs' -> match_locset (Locations.Locmap.setres res vres rs) (Locations.Locmap.setres res vres' rs').
Proof.
  unfold match_locset. induction res; intros.
  - apply match_locset_set_preserved; auto.
  - auto.
  - simpl. apply IHres2. apply Val.loword_lessdef. auto.
    apply IHres1. apply Val.hiword_lessdef. auto. auto.
Qed.

Lemma match_locset_undef_preserved:
    forall l rs rs', match_locset rs rs' -> match_locset (undef_regs l rs) (undef_regs l rs').
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. apply match_locset_set_preserved. auto. auto.
Qed.

Lemma FPMatch'_loadv_fp_lessdef:
  forall a a' v m chunk (sge tge: genv) mu, Val.lessdef a a' -> Mem.loadv chunk m a = Some v -> proper_mu sge tge inject_id mu -> FPMatch' mu (FMemOpFP.loadv_fp chunk a) (FMemOpFP.loadv_fp chunk a').
Proof.
  intros. destruct H.
  - apply fp_match_id. apply H1. apply H1.
  - simpl in H0. inversion H0.
Qed.

Lemma FPMatch'_storev_fp_lessdef:
  forall a a' v m m' chunk (sge tge: genv) mu, Val.lessdef a a' -> Mem.storev chunk m a v = Some m' -> proper_mu sge tge inject_id mu -> FPMatch' mu (FMemOpFP.storev_fp chunk a) (FMemOpFP.storev_fp chunk a').
Proof.
  intros. destruct H.
  - apply fp_match_id. apply H1. apply H1.
  - simpl in H0. inversion H0.
Qed.

Lemma extends_valid_block_preserved:
  forall m m' b, Mem.extends m m' -> Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  unfold Mem.valid_block; intros. destruct H. rewrite <- mext_next. auto.
Qed.

Lemma storev_valid_block_preserved:
  forall m m' a v chunk b, Mem.storev chunk m a v = Some m' -> Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  unfold Mem.valid_block; intros. destruct a; inversion H. eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma storev_unmapped_closed_preserved:
  forall m1 m1' m2 m2' a a' v v' chunk mu (sge tge: genv),
    proper_mu sge tge inject_id mu ->
    (forall b0 : block,
        Bset.belongsto (SharedSrc mu) b0 -> Mem.valid_block m1 b0) ->
    (forall b0 : block,
        Bset.belongsto (SharedTgt mu) b0 -> Mem.valid_block m1' b0) ->
    MemClosures_local.unmapped_closed mu m1 m1' ->
    Mem.storev chunk m1 a v = Some m2 ->
    Mem.storev chunk m1' a' v' = Some m2' ->
    Val.lessdef a a' ->
    MemClosures_local.unmapped_closed mu m2 m2'.
Proof.
  intros. destruct a; inversion H3. destruct a'; inversion H4. inversion H5; subst. apply (MemClosures_local.store_val_inject_unmapped_closed_preserved mu m1 m1' chunk inject_id b0 (Ptrofs.unsigned i0) v m2 b0 0 v' m2'); auto. apply H. apply H. apply H. replace (Ptrofs.unsigned i0 + 0) with (Ptrofs.unsigned i0). auto. omega.
Qed.

Lemma free_unmapped_closed_preserved:
  forall m1 m1' m2 m2' b lo hi mu (sge tge: genv),
    proper_mu sge tge inject_id mu ->
    (forall b0 : block,
        Bset.belongsto (SharedSrc mu) b0 -> Mem.valid_block m1 b0) ->
    (forall b0 : block,
        Bset.belongsto (SharedTgt mu) b0 -> Mem.valid_block m1' b0) ->
    MemClosures_local.unmapped_closed mu m1 m1' ->
    Mem.free m1 b lo hi = Some m2 ->
    Mem.free m1' b lo hi = Some m2' ->
    MemClosures_local.unmapped_closed mu m2 m2'.
Proof.
  intros. apply (MemClosures_local.free_inject_unmapped_closed_preserved mu m1 m1' inject_id b lo hi m2 b 0 lo hi m2'); auto. apply H. apply H. apply H. omega. omega.
Qed.

Lemma list_nth_z_property:
  forall (A: Type) (l: list A) n x y (f: A -> A),
    list_nth_z l n = Some x ->
    f x = y ->
    list_nth_z (map f l) n = Some y.
Proof.
  induction l; intros. inversion H. simpl in *. destruct (zeq n 0). inversion H; subst; auto. eapply IHl; eauto.
Qed.

Lemma match_locset_map_getpair:
  forall rs ls l, match_locset rs ls -> Val.lessdef_list (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p rs) l) (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p ls) l).
Proof.
  intros. induction l; simpl; auto. constructor; auto.
  destruct a; simpl; auto. apply Val.longofwords_lessdef; auto.
Qed.

Lemma match_locset_get_result:
  forall rs ls r, match_locset rs ls -> Val.lessdef (get_result r rs) (get_result r ls).
Proof.
  intros. unfold get_result. destruct r.
  - apply H.
  - apply Val.longofwords_lessdef; apply H.
Qed.

Lemma val_lessdef_implies_val_inject:
  forall (sge tge: genv) mu v v',
    LDSimDefs.G_arg (SharedSrc mu) v->
    proper_mu sge tge inject_id mu ->
    Val.lessdef v v' ->
    Val.inject (Bset.inj_to_meminj (inj mu)) v v'.
Proof.
  intros. destruct H1; auto. destruct v; auto. econstructor. simpl in *. destruct H0. destruct proper_mu_inject. destruct (inj_dom b H) as [b' H_inj]. assert (Bset.inj_to_meminj (inj mu) b = Some (b', 0)). unfold Bset.inj_to_meminj. rewrite H_inj. auto. apply proper_mu_inject_incr in H0 as ?. inversion H1; subst. eauto. symmetry. apply Ptrofs.add_zero.
Qed.

Lemma list_lessdef_implies_list_inject:
  forall (sge tge: genv) mu l l',
    LDSimDefs.G_args (SharedSrc mu) l->
    proper_mu sge tge inject_id mu ->
    Val.lessdef_list l l' ->
    Val.inject_list (Bset.inj_to_meminj (inj mu)) l l'.
Proof.
  intros. induction H1; auto. inversion H. constructor; auto. eapply val_lessdef_implies_val_inject; eauto.
Qed.

Ltac des :=
  match goal with
    | H0: MS _ _ _ _ _ _ _ (?Hcore, ?Hm) (?Lcore, ?Lm) |-_ =>
      simpl in H0; destruct H0 as [H_match_state [H_FPmatch [H_SharedSrc [H_SharedTgt [H_mu_id [H_closure [H_measure H_true]]]]]]]; subst
    | H0: MS _ _ _ _ _ _ _ ?Hc ?Lc |-_ =>
      destruct Hc as [score sm]; destruct Lc as [tcore tm]; simpl in H0; destruct H0 as [H_match_state [H_FPmatch [H_SharedSrc [H_SharedTgt [H_mu_id [H_closure [H_measure H_true]]]]]]]; subst
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
      try (compute; eauto; fail); try omega
  | H1: Mem.free ?m1 _ _ _ = Some ?m2,
        H2: Mem.free ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try omega
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
  | |- context[Core_Block ?s ?f ?sp (Lbranch ?pc :: ?bb) ?rs ?sigres] => exists (measure (Core_Block s f sp (Lbranch pc :: bb) rs sigres))
  | |- context[Core_Callstate] => exists 0%nat
  | |- context[Core_Returnstate ?s ?v ?sigres] => eexists (*(measure (Core_Returnstate s v sigres))*)
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

Theorem transf_local_ldsim:
  forall su tu,
    transf_program su = OK tu->
    forall sge sG tge tG,
      init_genv_local LTL_IS su sge sG->
      init_genv_local LTL_IS tu tge tG->
      Genv.genv_next sge = Genv.genv_next tge->
      local_ldsim sG tG sge tge.
Proof.
  intros. simpl in *. unfold init_genv in *.
  destruct H0; subst. destruct H1; subst.
  assert (H_match: match_cu su tu) by (apply transf_program_match; auto).
  econstructor. instantiate(3:=nat).
  instantiate(2:=lt). instantiate(1:=MS sG tG).
  econstructor; intros; simpl in *; try des.
  { apply lt_wf. }
  { apply H_mu_id. }
  { apply H_mu_id. }
  { apply (ge_match su tu); auto. }
  { assert (argSrc = argTgt).
    {
      clear H7. unfold LDSimDefs.G_args, LDSimDefs.G_arg in H5.
      unfold LDSimDefs.arg_rel in H6. induction H6; auto.
      destruct v; inversion H6; inversion H5; subst;
        try (rewrite (IHinject_list H13); auto). inversion H11.
      rewrite (IHinject_list H16). apply H4 in H10.
      inversion H10; subst. rewrite Ptrofs.add_zero. auto.
    }
    subst. unfold init_core, generic_init_core, fundef_init in *.
    assert (H_symbol: Genv.find_symbol tG id = Genv.find_symbol sG id)
      by (eapply symbols_preserved; eauto) . rewrite H_symbol.
    destruct (Genv.find_symbol sG id); try discriminate.
    destruct (Genv.find_funct_ptr sG b) eqn: H_funct_ptr; try discriminate.
    eapply funct_ptr_translated in  H_funct_ptr; eauto.
    rewrite H_funct_ptr. destruct f; try discriminate. simpl in *.
    destruct (wd_args argTgt (sig_args (fn_sig f))); try discriminate.
    inversion H7; subst. clear H7. clear H_symbol. clear H_funct_ptr.
    clear H6. clear H5.
    eexists. split; eauto. intros. eexists.
    assert (H_dom_match: Genv.genv_next sG = Mem.nextblock sm) by apply H5.
    assert (H_dom_match': Genv.genv_next tG = Mem.nextblock tm) by apply H6.
    assert (H_extends: Mem.extends sm tm).
    {
      eapply inject_implies_extends; eauto. unfold Mem.valid_block.
      rewrite <- H_dom_match. destruct H0. intros.
      assert (SharedSrc mu b0). rewrite mu_shared_src. auto.
      destruct mu_inject. destruct (inj_dom b0 H9) as [b' ?].
      exists b'. exists 0. unfold Bset.inj_to_meminj. rewrite H10. auto.
      apply mem_mu_inj; auto. rewrite <- H_dom_match, <- H_dom_match'. auto.
    }
    assert (H_mem: Mem.nextblock sm = Mem.nextblock sm').
    destruct H8. destruct H8. auto.
    assert (H_mem': Mem.nextblock tm = Mem.nextblock tm').
    destruct H8. destruct H9. auto.
    split; constructor; auto.
    { constructor. }
    { apply match_locset_refl. }
    { eapply extends_rely_extends; eauto. apply H0. }
    { apply fp_match_emp'. }
    { split. unfold Mem.valid_block. rewrite <- H_mem. apply H7.
      split. unfold Mem.valid_block. rewrite <- H_mem'. apply H7.
      split. constructor; auto. apply H7. unfold sep_inject; intros.
      inversion H10; subst. apply H4 in H9 as H11. inversion H11; subst. auto.
      split. apply MemClosures_local.reach_closed_unmapped_closed.
      destruct H8. inversion H9. auto. auto. }
  }
  { inversion H4; subst.
    { destruct bb.
      {
        inv H_match_state.
        remember (record_gotos_correct f pc) as Hbranch; clear HeqHbranch.
        rewrite H0 in Hbranch. rewrite Hbranch. Right. constructor; auto.
        rewrite <- code_preserved, H0. simpl. auto.
        split. eresolvfp. splitMS.
      }
      {
        inv H_match_state. destruct i; try (right; do 4 eexists; split; [apply plus_one; constructor; remember (record_gotos_correct f pc) as Hbranch; clear HeqHbranch; rewrite H0 in Hbranch; rewrite Hbranch; rewrite <- code_preserved; rewrite H0; simpl; auto | split; [apply fp_match_union'; auto; apply fp_match_emp' | split; [constructor; auto | split; [apply fp_match_union'; auto; apply fp_match_emp' | split; auto]]]]).
        {
          destruct (peq pc (branch_target f pc)).
          {
            Right. constructor. rewrite <- code_preserved, <- e, H0.
            simpl. auto. eresolvfp. split. eresolvfp. splitMS. }
          {
            remember (record_gotos_correct f pc) as Hbranch; clear HeqHbranch.
            rewrite H0 in Hbranch.
            destruct Hbranch as [Hbranch | [H_branch_target Hcount]].
            congruence. rewrite H_branch_target. Left. simpl. omega. splitMS.
          }
        }
      }
    }
    {
      inv H_match_state.
      apply (match_locset_val_lessdef_list rs ls0 args) in H16 as H_lessdef_list.
      rewrite <- (Op.eval_operation_preserved sG tG (symbols_preserved su tu sG tG H3 H1 H2 (transf_program_match su tu H))) in H0.
      destruct (Op.eval_operation_lessdef tG sp op H_lessdef_list H17 H0) as [v' [H_op H_lessdef]].
      rewrite <- (Op_fp.eval_operation_fp_preserved sG tG (symbols_preserved su tu sG tG H3 H1 H2 (transf_program_match su tu H))) in H5.
      destruct (Op_fp.eval_operation_lessdef_fp tG sp op H_lessdef_list H17 H0 H5) as [Lfp' [H_op_fp H_lessdef_fp]].
      Right. econstructor; eauto. split. eresolvfp. splitMS.
      apply match_locset_set_preserved; auto.
      apply match_locset_undef_preserved; auto.
    }
    {
      inversion H_match_state; subst.
      apply (match_locset_val_lessdef_list rs ls0 args) in H16 as H_lessdef_list.
      rewrite <- (Op.eval_addressing_preserved sG tG (symbols_preserved su tu sG tG H3 H1 H2 (transf_program_match su tu H))) in H0.
      destruct (Op.eval_addressing_lessdef tG sp addr H_lessdef_list H0) as [a' [H_op H_lessdef]].
      destruct (Mem.loadv_extends _ _ _ _ _ _ H17 H5 H_lessdef) as [v' [H_op' H_lessdef']].
      Right. econstructor; eauto. split. eresolvfp.
      apply (FPMatch'_loadv_fp_lessdef a a' v Hm' chunk sG tG mu); auto.
      splitMS. apply match_locset_set_preserved; auto. eresolvfp.
      apply (FPMatch'_loadv_fp_lessdef a a' v Hm' chunk sG tG mu); auto.
    }
    {
      inversion H_match_state; subst. Right. econstructor; eauto.
      split. eresolvfp. splitMS. apply match_locset_set_preserved; auto.
      apply match_locset_undef_preserved; auto.
    }
    {
      inversion H_match_state; subst. Right. econstructor; eauto.
      split. eresolvfp. splitMS. apply match_locset_set_preserved; auto.
      apply match_locset_undef_preserved; auto.
    }
    {
      inversion H_match_state; subst.
      apply (match_locset_val_lessdef_list rs ls0 args) in H16 as H_lessdef_list.
      rewrite <- (Op.eval_addressing_preserved sG tG (symbols_preserved su tu sG tG H3 H1 H2 (transf_program_match su tu H))) in H0.
      destruct (Op.eval_addressing_lessdef tG sp addr H_lessdef_list H0) as [a' [H_op H_lessdef]].
      destruct (Mem.storev_extends _ _ _ _ _ _ _ _ H17 H5 H_lessdef (H16 (Locations.R src))) as [Lm' [H_op' H_extend']].
      Right. econstructor; eauto. split. eresolvfp.
      apply (FPMatch'_storev_fp_lessdef a a' (rs (Locations.R src)) Hm Hm' chunk sG tG mu); auto.
      splitMS. apply match_locset_undef_preserved; auto. eresolvfp.
      apply (FPMatch'_storev_fp_lessdef a a' (rs (Locations.R src)) Hm Hm' chunk sG tG mu); auto.
      intros. apply H_SharedSrc in H6.
      eapply storev_valid_block_preserved; eauto.
      intros. apply H_SharedTgt in H6.
      eapply storev_valid_block_preserved; eauto.
      eapply storev_unmapped_closed_preserved; eauto.
    }
    {
      inversion H_match_state; subst. Right.
      instantiate (2:= (Core_Callstate (Stackframe (tunnel_function f) sp ls0 (tunnel_block (record_gotos f) bb) :: ts) (tunnel_fundef fd) ls0 sigres)).
      econstructor; eauto.
      eapply (find_function_translated_lessdef su tu); eauto.
      apply sig_preserved. split. eresolvfp. splitMS.
      constructor; auto. constructor; auto.
    }
    { inversion H_match_state; subst.
      destruct (Mem.free_parallel_extends _ _ _ _ _ _ H17 H7) as [Lm' [H_mem H_extends]].
      Right. instantiate (2:= (Core_Callstate ts (tunnel_fundef fd) (return_regs (parent_locset ts) ls0) sigres)).
      econstructor; eauto.
      eapply (find_function_translated_lessdef su tu); eauto.
      apply return_regs_match_locset_preserved; auto.
      apply match_parent_locset; auto. apply sig_preserved. split. eresolvfp.
      rewrite stacksize_preserved. apply fp_match_id; apply H_mu_id.
      splitMS. apply return_regs_match_locset_preserved; auto.
      apply match_parent_locset; auto. eresolvfp.
      rewrite stacksize_preserved. apply fp_match_id; apply H_mu_id.
    }
    {
      inversion H_match_state; subst.
      destruct (Events.eval_builtin_args_lessdef ls0 H18 H19 H0) as [vargs' [H_vargs H_lessdef_vargs]].
      destruct (Events.external_call_mem_extends _ _ _ _ _ H7 H19 H_lessdef_vargs) as [vres' [Lm' [H_res [H_lessdef_res [H_extends H_unchanged]]]]].
      apply helpers.i64ext_effects in H_res as H_equal; auto.
      inv H_equal. Right. econstructor; eauto.
      apply (Events.eval_builtin_args_preserved tG (symbols_preserved su tu sG tG H3 H1 H2 (transf_program_match su tu H))); eauto.
      apply MemOpFP.eval_builtin_args_fp_lessdef with rs.
      eapply MemOpFP.eval_builtin_args_fp_preserved.
      apply (symbols_preserved su tu sG tG H3 H1 H2 (transf_program_match su tu H)). eauto.
      eapply Events.external_call_symbols_preserved; eauto.
      apply (senv_preserved su tu); auto. split. eresolvfp. splitMS.
      apply match_locset_setres_preserved; auto.
      apply match_locset_undef_preserved; auto.
    }
    {
      inversion H_match_state; subst.
      {
        Right. econstructor; eauto. split. eresolvfp. splitMS.
      }
      {
        left. exists (measure (Core_State s f sp pc rs sigres)). split. simpl. omega. splitMS.
      }
    }
    {
      inversion H_match_state; subst.
      apply (match_locset_val_lessdef_list rs ls0 args) in H16 as H_lessdef_list.
      destruct (eval_condition_lessdef_fp cond H_lessdef_list H17 H0 H5) as [Lfp' [H_op H_inject]].
      Right. instantiate (2:= (Core_State ts (tunnel_function f) sp (if b then (branch_target f pc1) else (branch_target f pc2)) (undef_regs (Machregs.destroyed_by_cond cond) ls0) sigres)).
      econstructor; eauto. eapply Op.eval_condition_lessdef; eauto.
      split. eresolvfp. split. destruct b; constructor; auto.
      split. eresolvfp. split; try resvalid; auto.
    }
    {
      inversion H_match_state; subst.
      assert (H_n: ls0 (Locations.R arg) = Vint n).
      destruct (H16 (Locations.R arg)); inversion H0; auto.
      assert (H_pc: list_nth_z (map (U.repr (record_gotos f)) tbl) (Int.unsigned n) = Some (branch_target f pc)).
      eapply list_nth_z_property; eauto. Right. econstructor; eauto.
      split. eresolvfp. splitMS. apply match_locset_undef_preserved; auto.
    }
    {
      inversion H_match_state; subst.
      destruct (Mem.free_parallel_extends _ _ _ _ _ _ H16 H0) as [Lm' [H_mem H_extends]].
      Right. econstructor; eauto. split. eresolvfp.
      rewrite stacksize_preserved. apply fp_match_id; apply H_mu_id.
      splitMS. apply return_regs_match_locset_preserved; auto.
      apply match_parent_locset; auto. eresolvfp.
      rewrite stacksize_preserved. apply fp_match_id; apply H_mu_id.
    }
    {
      inversion H_match_state; subst.
      assert (H_mem: exists Lm', Mem.alloc Lm 0 (fn_stacksize (tunnel_function f)) = (Lm', sp) /\ Mem.extends Hm' Lm').
      eapply Mem.alloc_extends; eauto. omega.
      assert (H_stacksize_preserved: fn_stacksize (tunnel_function f) = fn_stacksize f).
      apply stacksize_preserved. omega.
      destruct H_mem as [Lm' [H_mem H_extends]]. Right. econstructor; eauto. split. eresolvfp.
      rewrite stacksize_preserved. eapply fp_match_subset_T'.
      apply fp_match_id; apply H_mu_id. unfold MemOpFP.alloc_fp.
      replace (Mem.nextblock Lm) with (Mem.nextblock Hm).
      apply FP.subset_refl. apply H14. splitMS.
      apply match_locset_undef_preserved; auto.
      apply call_regs_match_locset_preserved; auto. eresolvfp.
      rewrite stacksize_preserved. eapply fp_match_subset_T'.
      apply fp_match_id; apply H_mu_id. unfold MemOpFP.alloc_fp.
      replace (Mem.nextblock Lm) with (Mem.nextblock Hm).
      apply FP.subset_refl. apply H14.
    }
    {
      inversion H_match_state; subst.
      apply (match_locset_map_getpair rs ls0 (Conventions1.loc_arguments (ef_sig ef))) in H14 as H_match_locset_pair.
      destruct (Events.external_call_mem_extends _ _ _ _ _ H6 H15 H_match_locset_pair) as [vres' [Lm' [H_res [H_lessdef_res [H_extends H_unchanged]]]]].
      apply helpers.i64ext_effects in H_res as H_equal; auto.
      inversion H_equal; subst. Right. econstructor; eauto.
      apply Events.external_call_symbols_preserved with sG.
      apply (senv_preserved su tu); auto. eauto. split. eresolvfp. splitMS.
      destruct (Conventions1.loc_result (ef_sig ef)); apply match_locset_set_preserved; auto.
      apply Val.loword_lessdef; auto. apply match_locset_set_preserved; auto.
      apply Val.hiword_lessdef; auto.
    }
    {
      inversion H_match_state; subst. inversion H7; inversion H6; subst. Right. econstructor; eauto. split. eresolvfp. splitMS.
    }
  }
  {
    destruct Hcore; inv H4. destruct f0; inv H7. destruct e; inv H4.
    inversion H_match_state; subst. simpl in *.
    destruct (invert_symbol_from_string sG name) eqn: E; try congruence.
    assert (H_symbol: invert_symbol_from_string tG name = Some i).
    eapply match_genvs_invert_symbol_from_string_preserved; eauto.
    eapply genv_match; eauto. intros. destruct H0.
    destruct f1; destruct f2; inversion H0; auto.
    destruct v1; destruct v2; inversion H0; auto. rewrite H_symbol.
    destruct (peq i GAST.ent_atom || peq i GAST.ext_atom); inv H7.
    eexists. exists (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p ls1) (Conventions1.loc_arguments sg)).
    simpl in *. split; auto. split. unfold LDSimDefs.arg_rel.
    eapply list_lessdef_implies_list_inject; eauto.
    apply match_locset_map_getpair; auto. destruct H_mu_id. split.
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_injection'; eauto.
    eapply extends_reach_closed_implies_inject; eauto.
    split; auto. split. eapply extends_reach_closed_implies_inject; eauto.
    split; auto. split. apply fp_match_emp'. repeat (split; auto).
  }
  {
    destruct Hcore; inv H5. destruct f; inv H7. destruct e; inv H5.
    inversion H_match_state; subst. destruct H_mu_id.
    destruct (oresSrc); destruct (sig_res sg) eqn: E; inv H7; simpl in *.
    {
      destruct oresTgt; try (inversion H6; discriminate).
      assert (H_equal: v = v0). unfold LDSimDefs.G_arg in H4.
      unfold LDSimDefs.res_rel in H6. inversion H6; subst; auto.
      apply proper_mu_inject_incr in H0 as H_inject. inversion H_inject; subst.
      rewrite Ptrofs.add_zero. auto. inversion H4.
      subst. rewrite E.
      exists (Core_Returnstate ts (Locations.Locmap.setpair (Conventions1.loc_result sg) v0 ls1) sigres).
      destruct (val_has_type_func v0 t); try discriminate.
      inversion H5; subst; clear H5. split; auto. intros. eexists.
      split; auto. econstructor; eauto.
      destruct (Conventions1.loc_result sg); apply match_locset_set_preserved; auto.
      apply match_locset_set_preserved; auto.
      eapply extends_rely_extends; eauto. split. apply fp_match_emp'.
      destruct H0. split. unfold Mem.valid_block.
      replace (Mem.nextblock Hm') with (Mem.nextblock Hm). auto.
      destruct r. auto. split. unfold Mem.valid_block.
      replace (Mem.nextblock Lm') with (Mem.nextblock Lm). auto.
      destruct r0. auto. split; auto. split; auto. split; auto.
      apply MemClosures_local.reach_closed_unmapped_closed. apply r0.
    }
    {
      rewrite E.
      exists (Core_Returnstate ts (Locations.Locmap.setpair (Conventions1.loc_result sg) Vundef ls1) sigres).
      destruct oresTgt; inversion H6; clear H6. split; auto. intros.
      eexists. split; auto. econstructor; eauto.
      destruct (Conventions1.loc_result sg); apply match_locset_set_preserved; auto.
      apply match_locset_set_preserved; auto.
      eapply extends_rely_extends; eauto. split. apply fp_match_emp'.
      destruct H0. split. unfold Mem.valid_block.
      replace (Mem.nextblock Hm') with (Mem.nextblock Hm). auto.
      destruct r. auto. split. unfold Mem.valid_block.
      replace (Mem.nextblock Lm') with (Mem.nextblock Lm). auto.
      destruct r0. auto. split; auto. split; auto. split; auto.
      apply MemClosures_local.reach_closed_unmapped_closed. apply r0.
    }
  }
  {
    destruct Hcore; inv H4. inv H_match_state.
    destruct stack; inversion H7; clear H7. inversion H9.
    remember (get_result (Conventions1.loc_result {| sig_args := nil; sig_res := sigres; sig_cc := cc_default |}) ls1) as resTgt.
    assert (H_lessdef: Val.lessdef resSrc resTgt). subst.
    apply match_locset_get_result; auto.
    assert (H_equal: resSrc = resTgt). inversion H_lessdef; auto.
    rewrite <- H0 in H6. inversion H6.
    exists resTgt. subst. simpl in *. split; auto. unfold LDSimDefs.res_rel.
    split. eapply val_lessdef_implies_val_inject; eauto. destruct H_mu_id.
    split. eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_injection'; eauto.
    eapply extends_reach_closed_implies_inject; eauto. split; auto.
    eapply extends_reach_closed_implies_inject; eauto.
  }
Qed.
