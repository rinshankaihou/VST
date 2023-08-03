Require Import EqdepFacts.
Require Import Axioms Coqlib Maps List.
Require Import Blockset Footprint GMemory MemAux InteractionSemantics
        ETrace GlobDefs NPSemantics
        Injections LDSimDefs LDSim GSimDefs.

Local Notation "'<<' i ',' c ',' sg ',' F '>>'" :=
  {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|}
    (at level 60, right associativity).

Local Notation "'[[' thdp ',' t ',' m ',' b ']]@' G " :=
  (Build_ProgConfig G thdp t m b) (at level 70, right associativity).

Local Notation "'[[' thdp ',' t ',' m ',' b ']]'" :=
  ({| thread_pool:= thdp; cur_tid:= t; gm:= m; atom_bit:= b |})
    (at level 70, right associativity).

Local Notation " GE '||-' pc1 '=<' l '|' fp '>=>>' pc2 " :=
  (@np_step GE pc1 l fp pc2) (at level 80, right associativity).

(* -------------- lemmas & tactics ----------------- *)
Lemma ocs_match_top_exists:
  forall SGE (stp: @ThreadPool.t SGE) scs c i TGE (ttp: @ThreadPool.t TGE),
    (forall i', ocs_match (ThreadPool.get_cs stp i') (ThreadPool.get_cs ttp i')) ->
    ThreadPool.get_cs stp i = Some scs ->
    CallStack.top scs = Some c ->
    exists tc, ThreadPool.get_top ttp i = Some tc.
Proof.
  intros. specialize (H i).
  inversion H; try congruence.
  inversion H4. unfold CallStack.is_emp in *. subst.
  rewrite H0 in H2. inversion H2. subst.  inversion H1.
  subst. exists c2. unfold ThreadPool.get_top. rewrite <- H3. auto.
Qed.

Lemma fp_union_emp_l:
  forall fp, FP.union FP.emp fp = fp.
Proof.
  clear; intros.
  unfold FP.union.
  destruct fp; f_equal.
Qed.
Lemma fp_union_comm:
  forall fp1 fp2 fp3,
    FP.union fp1 (FP.union fp2 fp3) =
    FP.union (FP.union fp1 fp2) fp3.
Proof.
  clear; intros.
  unfold FP.union.
  simpl. unfold Locs.union.
  f_equal;            
    do 2 (apply functional_extensionality; intro);
    rewrite orb_assoc; auto.
Qed.

Lemma star_step_plus:
  forall GE (pc: @ProgConfig GE) fp pc' fp' pc'',
    tau_star np_step pc fp pc' ->
    np_step pc' tau fp' pc'' ->
    tau_plus np_step pc (FP.union fp fp') pc''.
Proof.
  clear. induction 1.
  constructor.
  rewrite fp_union_emp_l. auto.
  intro. rewrite <- fp_union_comm.
  apply IHtau_star in H1.
  eapply tau_plus_cons; eauto.
Qed.

Lemma fp_union_emp_r:
  forall fp, FP.union fp FP.emp = fp.
Proof.
  clear; intros; unfold FP.union; destruct fp; simpl.
  unfold Locs.union. unfold Locs.emp.
  f_equal; do 2 (apply functional_extensionality; intro);
    rewrite orb_false_r; auto.
Qed.

Lemma core_step_np_step:
  forall GE i_x F c m fp c' m',
    let: Mod := GlobEnv.modules GE i_x in
    let: lang := ModSem.lang Mod in
    let: Ge := ModSem.Ge Mod in
    let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
    step lang Ge fl c m fp c' m' ->
    forall (tp: @ThreadPool.t GE) i sg b cs,
      ThreadPool.get_cs tp i = Some ((Core.Build_t i_x c sg F)::cs)  ->
      exists tp',
        np_step (Build_ProgConfig GE tp i m b) tau fp
                (Build_ProgConfig GE tp' i m' b) /\
        ThreadPool.update tp i (Core.Build_t i_x c' sg F) tp'.
Proof.
  clear; intros.
  assert (exists tp', ThreadPool.update
                   tp i
                   {| Core.i := i_x; Core.c := c'; Core.sg:= sg; Core.F := F |} tp').
  {
    assert (exists cs',
               CallStack.update
                 ({| Core.c := c; Core.sg:= sg; Core.F := F |}::cs)
                 {| Core.c := c'; Core.sg:= sg; Core.F := F |} cs').
    { eexists. econstructor; eauto.
      econstructor; eauto. }
    destruct H1 as (cs' & H_cs_upd).
    eexists; econstructor; eauto.
  }
  destruct H1 as (tp' & H_tp_upd).
  exists tp'. split. eapply Corestep; eauto.
  unfold ThreadPool.get_top. rewrite H0. simpl. eauto.
  eauto. constructor; auto. auto.
Qed.

Lemma core_plus_np_plus:
  forall GE i_x F c m fp c' m',
    let: Mod := GlobEnv.modules GE i_x in
    let: lang := ModSem.lang Mod in
    let: Ge := ModSem.Ge Mod in
    let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
    plus (step lang Ge fl) c m fp c' m' ->
    forall (tp: @ThreadPool.t GE) i sg b cs,
      ThreadPool.get_cs tp i = Some (Core.Build_t i_x c sg F :: cs) ->
      exists tp',
        tau_plus np_step (Build_ProgConfig GE tp i m b) fp
                 (Build_ProgConfig GE tp' i m' b) /\
        ThreadPool.update tp i {| Core.c:=c'; Core.sg:=sg; Core.F:=F |} tp'.
Proof.
  clear. intros GE i_x F c m fp c' m' H.
  induction H; intros.
  {
    eapply core_step_np_step in H; eauto.
    destruct H as (tp'& Hstep & Htp'). eexists; split; [econstructor|]; eauto.
  }
  {
    eapply core_step_np_step in H; eauto.
    destruct H as (tp' & Hstep & Htp'). instantiate (1:=b) in Hstep.
    inversion Htp'.
    rewrite H1 in H. inversion H. 
    edestruct (IHplus tp' i sg b cs) as [tp'' [Hplus' Htp''] ].
    subst. unfold ThreadPool.get_cs; simpl.
    rewrite PMap.gsspec. destruct peq; [|congruence].
    inversion H2. auto.
    exists tp''. split. eapply tau_plus_cons; eauto.
    inversion Htp''. subst; simpl in *; clear Hplus' IHplus H0 Hstep Htp''.
    unfold ThreadPool.get_cs in H5; simpl in H5; rewrite PMap.gsspec in H5.
    destruct peq; [|congruence]. inversion H5; subst.
    repeat (econstructor; eauto).
    f_equal.
    inversion H7. rewrite PMap.set2. subst.
    inversion H2; auto.
  }
Qed.

Lemma step_star_plus:
  forall lang Ge fl c' m' fp' c'' m'',
    InteractionSemantics.star (step lang Ge fl) c' m' fp' c'' m'' ->
    forall c m fp,
      step lang Ge fl c m fp c' m' ->
      plus (step lang Ge fl) c m (FP.union fp fp') c'' m''.
Proof.
  clear. induction 1; intros. rewrite fp_union_emp_r. constructor. auto.
  eapply plus_cons; eauto.
Qed.

Lemma tau_plus_tau_star:
  forall GE (pc: @ProgConfig GE) fp pc',
    tau_plus np_step pc fp pc' ->
    tau_star np_step pc fp pc'.
Proof.
  clear. induction 1. 
  replace fp with (FP.union fp FP.emp) by apply fp_union_emp_r.
  eapply tau_star_cons; eauto. constructor.
  eapply tau_star_cons; eauto.
Qed.

Lemma core_star_np_star:
  forall GE i_x F c m fp c' m',
    let: Mod := GlobEnv.modules GE i_x in
    let: lang := ModSem.lang Mod in
    let: Ge := ModSem.Ge Mod in
    let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
    InteractionSemantics.star (step lang Ge fl) c m fp c' m' ->
    forall (tp: @ThreadPool.t GE) i sg b cs,
      ThreadPool.get_cs tp i = Some ((Core.Build_t i_x c sg F)::cs) ->
      exists tp',
        tau_star np_step (Build_ProgConfig GE tp i m b) fp
                 (Build_ProgConfig GE tp' i m' b) /\
        (ThreadPool.update tp i (<< i_x, c', sg, F>>) tp' \/
         m = m' /\ c = c' /\ tp = tp' /\ fp = FP.emp).
Proof.
  clear. intros GE i_x F c m fp c' m' H.
  destruct H; intros.
  {
    eexists; split; [econstructor|]; eauto.
  }
  {
    eapply step_star_plus in H0; eauto.
    eapply core_plus_np_plus in H0; eauto.
    destruct H0 as [tp' [Hplus Htp'] ].
    exists tp'. split; eauto.
    apply tau_plus_tau_star. eauto.
  }
Qed.

Lemma loc_belong_bset_belong:
  forall fp b ofs,
    Locs.belongsto (FP.locs fp) b ofs ->
    Bset.belongsto (FP.blocks fp) b.
Proof.
  clear; intros. exists ofs. auto.
Qed.

Lemma bset_belong_union:
  forall fp fp' b,
    Bset.belongsto (FP.blocks fp') b ->
    Bset.belongsto (FP.blocks (FP.union fp fp')) b.
Proof.
  clear; intros.
  unfold FP.blocks, FP.union, Bset.belongsto, FP.locs in *.
  unfold Locs.union, Locs.blocks, Locs.belongsto in *; simpl.
  destruct H. exists x.
  repeat match goal with
           [ H: ?x||_=_ |- _ ] =>
           destruct x; simpl in *; repeat rewrite orb_true_r; auto
         end.
  match goal with
    [H: ?x = true |- _] => destruct x; repeat rewrite orb_true_r; auto
  end.
Qed.

Lemma loc_belong_union_block_belong:
  forall fp fp' b ofs,
    Locs.belongsto (FP.locs fp') b ofs ->
    Bset.belongsto (FP.blocks (FP.union fp fp')) b.
Proof.
  intros.
  apply bset_belong_union.
  eapply loc_belong_bset_belong; eauto.
Qed.

Lemma scs_upd_cs_match:
  forall SGE TGE (scs: @CallStack.t SGE) (tcs: @CallStack.t TGE),
    cs_match scs tcs ->
    forall c' scs',
      CallStack.update scs c' scs' ->
      cs_match scs' tcs.
Proof.
  clear. induction 1; intros.
  { inversion H1; subst; simpl in *.
    inversion H. }
  { inversion H0; subst; simpl in *.
    eapply match_cs_cons; auto. }
Qed.

Lemma stp_upd_ocs_match:
  forall SGE TGE (sthdp: @ThreadPool.t SGE) (tthdp:@ThreadPool.t TGE) i,
    ocs_match (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp i) ->
    (forall i' c' sthdp',
        ThreadPool.update sthdp i' c' sthdp' ->
        ocs_match (ThreadPool.get_cs sthdp' i) (ThreadPool.get_cs tthdp i)).
Proof.
  clear; intros SGE0 TGE0 sthdp tthdp i H i' c' sthdp' H0.
  inversion H0; subst; clear H0.
  unfold ThreadPool.get_cs in *; simpl in *.
  rewrite PMap.gsspec.
  destruct peq; [subst|auto].
  inversion H. congruence.
  rewrite H1 in H0; inversion H0; clear H0 H3. subst.
  constructor. eapply scs_upd_cs_match; eauto.
Qed.

Lemma tcs_upd_cs_match:
  forall SGE TGE (scs: @CallStack.t SGE) (tcs: @CallStack.t TGE),
    cs_match scs tcs ->
    forall c' tcs',
      CallStack.update tcs c' tcs' ->
      cs_match scs tcs'.
Proof.
  clear. induction 1; intros.
  { inversion H1; subst; simpl in *.
    inversion H0. }
  { inversion H0; subst; simpl in *.
    eapply match_cs_cons; auto. }
Qed.

Lemma ttp_upd_ocs_match:
  forall SGE TGE (sthdp: @ThreadPool.t SGE) (tthdp:@ThreadPool.t TGE) i,
    ocs_match (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp i) ->
    (forall i' c' tthdp',
        ThreadPool.update tthdp i' c' tthdp' ->
        ocs_match (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp' i)).
Proof.
  clear; intros SGE0 TGE0 sthdp tthdp i H i' c' tthdp' H0.
  inversion H0; subst; clear H0.
  unfold ThreadPool.get_cs in *; simpl in *.
  rewrite PMap.gsspec.
  destruct peq; [subst|auto].
  inversion H. congruence.
  rewrite H1 in H3; inversion H3; clear H0 H3. subst.
  constructor. eapply tcs_upd_cs_match; eauto.
Qed.

Lemma tp_push_ocs_match:
  forall SGE TGE (sthdp: @ThreadPool.t SGE) (tthdp: @ThreadPool.t TGE) i,
    ocs_match (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp i) ->
    (forall i' six sc' ssg sthdp' tix tc' tsg tthdp',
        ThreadPool.push sthdp i' six sc' ssg = Some sthdp' ->
        ThreadPool.push tthdp i' tix tc' tsg = Some tthdp' ->
        ocs_match (ThreadPool.get_cs sthdp' i) (ThreadPool.get_cs tthdp' i)).
Proof.
  clear. intros.
  unfold ThreadPool.get_cs, ThreadPool.push in *.
  repeat match goal with
         | H: match ?p with _ => _ end = Some _ |- _ =>
           destruct p eqn:?; inversion H; subst; clear H
         end.
  simpl.
  repeat rewrite PMap.gsspec; simpl. destruct peq; [|congruence].
  constructor. inversion H; subst; simpl in *. congruence.
  unfold CallStack.push. apply match_cs_cons; auto. congruence.
Qed.

Lemma tp_pop_ocs_match:
  forall SGE TGE (sthdp: @ThreadPool.t SGE) (tthdp: @ThreadPool.t TGE) i,
    ocs_match (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp i) ->
    (forall i' sthdp' tthdp',
        ThreadPool.pop sthdp i' = Some sthdp' ->
        ThreadPool.pop tthdp i' = Some tthdp' ->
        ocs_match (ThreadPool.get_cs sthdp' i) (ThreadPool.get_cs tthdp' i)).
Proof.
  clear. intros.
  unfold ThreadPool.get_cs, ThreadPool.pop in *.
  repeat match goal with
         | H: match ?p with _ => _ end = Some _ |- _ =>
           destruct p eqn:?; inversion H; subst; clear H
         end.
  simpl.
  repeat rewrite PMap.gsspec; simpl. destruct peq; [|congruence].
  constructor. inversion H; subst; simpl in *.
  unfold CallStack.pop in *.
  destruct t, t1; try congruence.
  inversion H2.
  rewrite Heqo1 in H0. inversion H0. inversion H3. subst. inversion Heqo2.
  subst. rewrite Heqo1 in H0. rewrite Heqo in H1. inversion H1; inversion H0.
  subst. inversion Heqo0; inversion Heqo2. congruence.
Qed.

Lemma stcs_upd_cs_match:
  forall SGE TGE (scs: @CallStack.t SGE) (tcs: @CallStack.t TGE),
    cs_match scs tcs ->
    forall sc' scs' tc' tcs',
      CallStack.update scs sc' scs' ->
      CallStack.update tcs tc' tcs' ->
      cs_match scs' tcs'.
Proof.
  clear. induction 1; intros.
  { inversion H1; subst; simpl in *.
    inversion H. }
  { inversion H0; inversion H1; subst; simpl in *.
    eapply match_cs_cons; auto. }
Qed.

Lemma sttp_upd_ocs_match:
  forall SGE TGE (sthdp: @ThreadPool.t SGE) (tthdp:@ThreadPool.t TGE) i,
    ocs_match (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp i) ->
    (forall si' sc' sthdp' ti' tc' tthdp',
        ThreadPool.update sthdp si' sc' sthdp' ->
        ThreadPool.update tthdp ti' tc' tthdp' ->
        ocs_match (ThreadPool.get_cs sthdp' i) (ThreadPool.get_cs tthdp' i)).
Proof.
  clear; intros.
  inversion H0; inversion H1; subst; clear H0 H1.
  unfold ThreadPool.get_cs in *; simpl in *.
  repeat rewrite PMap.gsspec.
  destruct peq; subst.
  { destruct peq; subst.
    { constructor. eapply stcs_upd_cs_match; eauto.
      inversion H; congruence. }
    { inversion H. congruence. clear H6 H7. rewrite H2 in H0; inversion H0. subst.
      constructor. eapply scs_upd_cs_match; eauto. }
  }
  { clear H2 n. destruct peq; subst.
    { inversion H. congruence. constructor.
      rewrite H6 in H1; inversion H1; clear H0 H1 H3. subst.
      eapply tcs_upd_cs_match; eauto. }
    { auto. }
  }
Qed.

Lemma thdp_upd_get_nil_false:
  forall GE (thdp: @ThreadPool.t GE) i c' thdp',
    ThreadPool.update thdp i c' thdp' ->
    ThreadPool.get_cs thdp' i = Some nil ->
    False.
Proof.
  clear; inversion 1; subst; clear H.
  unfold ThreadPool.get_cs; simpl in *.
  rewrite PMap.gsspec. destruct peq; [|congruence].
  intro C; inversion C; subst.
  inversion H1.
Qed.

Lemma thdp_upd_get:
  forall GE (thdp thdp': @ThreadPool.t GE) i c,
    ThreadPool.update thdp i c thdp' ->
    exists c0 cs,
      ThreadPool.get_cs thdp i = Some (c0 :: cs) /\
      ThreadPool.get_cs thdp' i = Some (c :: cs).
Proof.
  clear; intros GE thdp thdp' i c H.
  inversion H; inversion H1; simpl in *; subst.
  unfold ThreadPool.get_cs in *; simpl in *.
  rewrite PMap.gsspec. destruct peq; [|congruence].
  exists c0, cs0; auto.
Qed.

Ltac inv_upd:=
  repeat match goal with
         | H : ThreadPool.update _ _ _ _ |- _ =>
           inversion H; subst; simpl in *; clear H
         | H : CallStack.update _ _ _ |- _ =>
           inversion H; subst; simpl in *; clear H
         | H : Core.update _ _ _ |- _ =>
           inversion H; subst; simpl in *; clear H
         end.

Ltac solv_eq:=
  repeat
    ( match goal with
      | [H1: ?P = _, H2: ?P = _ |- _] =>
        rewrite H1 in H2; inversion H2; clear H1 H2
      | [H1: ?P = _ , H2: _ = ?P |- _] =>
        rewrite H1 in H2; inversion H2; clear H1 H2
      | [H1: _ = ?P, H2: _ = ?P |- _] =>
        rewrite <- H1 in H2; inversion H2; clear H1 H2
      end
    ); 
  try (trivial; fail)
.

Ltac norm_orb :=
  repeat
    match goal with
    | H: context[(?x || ?y) || ?z] |- _ =>
      rewrite <- orb_assoc in H
    | |- context[(?x || ?y) || ?z] =>
      rewrite <- orb_assoc
    end.
Ltac infer_orb :=
  repeat
    match goal with
    | H: orb ?x ?y = true |- _ =>
      apply orb_true_elim in H; destruct H as [H|H];
      [rewrite H in *; clear H |]
    | H: orb ?x ?y = false |- _ =>
      apply orb_false_elim in H; destruct H as [H' H''];
      rewrite H', H'' in *; clear H' H''
    end.
Ltac elim_bool :=
  match goal with
  | H: ?x = true |- context[?x] => rewrite H; clear H
  | H: ?x = false |- context[?x] => rewrite H; clear H
  end.
Ltac solv_orb_true :=
  repeat rewrite orb_true_l;
  repeat rewrite orb_true_r;
  repeat rewrite orb_true_l;
  try trivial.
Ltac solv_true_fp :=
  norm_orb; infer_orb; (try elim_bool); try (solv_orb_true).
Ltac solv_belongsto :=
  unfold FP.blocks, FP.union, Bset.belongsto, FP.locs,
  Locs.union, Locs.blocks, Locs.belongsto in *; simpl in *; solv_true_fp.

Ltac find_relatives x :=
  try
    match goal with
    | H: ThreadPool.get_cs x _ = _ |- _=>
      generalize H; clear H;
      find_relatives x 
    | H: ThreadPool.get_top x _ = _ |- _ =>
      generalize H; clear H;
      find_relatives x
    | H: context[ThreadPool.halted x _] |- _ =>
      generalize H; clear H;
      find_relatives x
    | H: context[ThreadPool.valid_tid x _] |- _ =>
      generalize H; clear H;
      find_relatives x
    | H: ThreadPool.update ?y _ ?c x |- _ =>
      generalize dependent c;
      try (generalize H; clear H);
      find_relatives y
    | H: ThreadPool.pop ?y _ = Some x |- _ =>
      generalize H; clear H;
      find_relatives y
    | H: ThreadPool.push ?y _ _ _ _ = Some x |- _ =>
      generalize H; clear H;
      find_relatives y
    end.

Ltac solv_thread' :=
  repeat
    match goal with
    | H:ThreadPool.update _ _ _ _ |- _ => inversion H; simpl in *; subst; clear H
    | H:CallStack.update _ _ _ |- _ => inversion H; simpl in *; subst; clear H
    | H:ThreadPool.halted _ _ |- _ => inversion H; simpl in *; subst; clear H
    | H:context[match (ThreadPool.content ?x) !! ?y with _ => _ end] |- _ =>
      destruct ((ThreadPool.content x) !! y) eqn:?
    end;
  unfold ThreadPool.get_top, ThreadPool.pop, ThreadPool.get_cs, ThreadPool.push,
  CallStack.pop, CallStack.top, CallStack.is_emp, CallStack.emp_cs in *; simpl in *; subst;
  repeat match goal with
           H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try (inversion H; fail)
         | H: Some _ = Some _ |- _ => inversion H; clear H; subst
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;
  solv_eq; eauto.

Ltac solv_pmap :=
  repeat
    (repeat rewrite PMap.gsspec in *;
     destruct peq; try contradiction).


Ltac decompose_ex H :=
  repeat match type of H with
         | ex (fun x => _) =>
           let x := fresh x in
           destruct H as [x H]
         end.

Ltac norm_hypos :=
  match goal with
  | H: ?P \/ ?Q |- _ => destruct H as [H|H]
  | H: _ /\ _ |- _ => destruct H as [? ?]
  end;
  subst.

Ltac solv_thread :=
  repeat match goal with
         | [H: ThreadPool.update _ _ _ _ |- _] => inversion H; simpl in *; subst; clear H
         | [H: CallStack.update _ _ _ |- _] => inversion H; simpl in *; subst; clear H
         end;
  unfold ThreadPool.get_top, ThreadPool.pop, ThreadPool.get_cs in *; simpl in *; subst;
  repeat rewrite PMap.gsspec in *;
  try (destruct peq; [|contradiction]; simpl in *; subst);
  repeat match goal with
         | H: Some _ = Some _ |- _ => inversion H; simpl in *; clear H; subst
         | H: ?P = ?Q, H1: context[?P] |- _ => rewrite H in H1
         end;
  solv_eq
.

(** should be put into ThreadPool *)
Lemma valid_tid_get_cs:
  forall GE (tp: @ThreadPool.t GE) t,
    ThreadPool.inv tp ->
    ThreadPool.valid_tid tp t <-> (exists cs, ThreadPool.get_cs tp t = Some cs).
Proof.
  clear; intros.
  inversion H. clear thdp_default.
  unfold ThreadPool.valid_tid. solv_thread'.
  split; auto.
  intros. edestruct plt; eauto.
  apply tp_finite in n. destruct H0. congruence.
Qed.

(** Lemmas, TODO: move to somewhere else *)
Lemma thrddom_eq_valid_tid:
  forall SGE TGE (sthdp:@ThreadPool.t SGE) (tthdp:@ThreadPool.t TGE),
    ThreadPool.inv sthdp ->
    ThreadPool.inv tthdp ->
    (forall t, ocs_match (ThreadPool.get_cs sthdp t) (ThreadPool.get_cs tthdp t)) ->
    (forall t, ThreadPool.valid_tid sthdp t <-> ThreadPool.valid_tid tthdp t).
Proof.
  clear; intros. specialize (H1 t).
  rewrite valid_tid_get_cs; auto. rewrite valid_tid_get_cs; auto.
  inversion H1; clear H1.
  { split; intro C; destruct C as [? C]; inversion C. }
  { split; eauto. }
Qed.
Lemma thrddom_eq_halted:
  forall SGE TGE (sthdp:@ThreadPool.t SGE) (tthdp:@ThreadPool.t TGE),
    ThreadPool.inv sthdp ->
    ThreadPool.inv tthdp ->
    (forall t, ocs_match (ThreadPool.get_cs sthdp t) (ThreadPool.get_cs tthdp t)) ->
    (forall t, ThreadPool.halted sthdp t <-> ThreadPool.halted tthdp t).
Proof.
  clear; intros. specialize (H1 t).
  split; inversion 1; eapply ThreadPool.Halted; solv_thread'.
  inversion H1; subst. inversion H5. subst. inversion H6. auto.
  inversion H1; subst. inversion H5. subst. inversion H4. auto.
Qed.
Lemma ocs_match_comm:
  forall SGE TGE (oscs: option (@CallStack.t SGE)) (otcs: option (@CallStack.t TGE)),
    ocs_match oscs otcs ->
    ocs_match otcs oscs.
Proof.
  clear; inversion 1. constructor.
  clear H1 H2 H oscs otcs.
  constructor. induction H0; solv_thread'.
  constructor; constructor.
  apply match_cs_cons. auto.
Qed.

Lemma cs_match'_comm:
  forall SGE TGE cs1 cs2,
    @cs_match' SGE TGE cs1 cs2->
    cs_match' cs2 cs1.
Proof.
  intros.
  induction H;subst;[econstructor|econstructor 2];eauto.
Qed.

Lemma ocs_match'_comm:
  forall SGE TGE ocs1 ocs2,
    @ocs_match' SGE TGE ocs1 ocs2->
    ocs_match' ocs2 ocs1.
Proof.
  induction 1;intros. constructor.
  eapply cs_match'_comm in H.
  econstructor 2;eauto.
Qed.

Lemma thrddom_eq'_comm:
  forall SGE TGE thdp thdp',
    @thrddom_eq' SGE TGE thdp thdp'->
    thrddom_eq' thdp' thdp.
Proof.
  inversion 1;subst.
  econstructor;eauto.
  intros;eapply ocs_match'_comm;eauto.
Qed.
(* ---------------------------------------------- *)