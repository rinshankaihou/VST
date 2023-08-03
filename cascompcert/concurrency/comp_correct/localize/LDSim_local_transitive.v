Require Import Coqlib Integers Streams Errors Values Globalenvs.

Require Import Blockset Footprint Memory
        Injections MemClosures_local LDSimDefs LDSimDefs_local
        InteractionSemantics IS_local.

(** reuse some lemma in Localize *)
Require Import Localize LDSim_local.

Require Import Relations Wellfounded.
Require Import Maps FiniteMaps MemInterpolant.



Section LexOrder.
  Context {T1 T2: Type}.
  Context (order1: T1 -> T1 -> Prop).
  Context (order2: T2 -> T2 -> Prop).

  Inductive lex_ord' : T1 * T2 -> T1 * T2 -> Prop :=
  | Lex_ord1: forall t1 t1' t2, order1 t1' t1 -> lex_ord' (t1', t2) (t1, t2)
  | Lex_ord2: forall t1 t1' t2 t2', order2 t2' t2 -> lex_ord' (t1', t2') (t1, t2).

  Theorem lexorder'_wf:
    well_founded order1 ->
    well_founded order2 ->
    well_founded lex_ord'.
  Proof.
    intros WF1 WF2 [x y]. generalize dependent x. 
    pattern y. apply (well_founded_ind WF2). intros y1 HACC2. 
    intro x. pattern x. apply (well_founded_ind WF1). intros x1 HACC1.
    constructor. intros [x0 y0] ORDER. inv ORDER.
    apply HACC1; auto.
    apply HACC2; auto.
  Qed.
End LexOrder.    




(** mu *)
Lemma bset_inject_preserve_finite:
  forall j (bs bs': Bset.t) (FINITE: exists bound, forall b, bs b -> Plt b bound),
    Bset.inject j bs bs' ->
    exists bound', forall b', bs' b' -> Plt b' bound'.
Proof.
  intros j bs bs' [bound FINITE] H.
  inv H. inv inj_weak.
  assert (REC: forall B, (B <= bound)%positive ->
          exists B', forall b b', (b < B \/ b >= bound)%positive -> 
                        j b = Some b' -> (b' < B')%positive).
  { intros B. pattern B. apply Pos.peano_rect; intros.
    exists 1%positive. intros. destruct H0. eapply Pos.nlt_1_r in H0. contradiction.
    eapply inj_dom', FINITE in H1. contradiction.
    assert (p <= bound)%positive by xomega.
    apply H in H1. destruct H1 as (B0 & H1).
    destruct (j p) as [p'|] eqn:?.
    exists (Pos.max B0 (Pos.succ p')). intros. destruct (peq b p). subst. rewrite Heqo in H3; inv H3. xomega.
    exploit H1; eauto. xomega. intro. xomega.
    exists B0. intros. destruct (peq b p). subst; congruence.
    exploit H1; eauto. xomega. }
  destruct (REC bound) as [bound' P]. xomega.
  exists bound'. intros. apply inj_range in H. destruct H. apply P in H. xomega. xomega.
Qed.

Record mu_compose (mu12 mu23 mu13: Mu): Prop :=
  {
    mu_finite_1: exists bound, forall b, SharedSrc mu13 b -> Plt b bound;
    mu_Shared1_equiv: SharedSrc mu12 = SharedSrc mu13;
    mu_Shared2_equiv: SharedTgt mu12 = SharedSrc mu23;
    mu_Shared3_equiv: SharedTgt mu23 = SharedTgt mu13;
    mu_inject_12: Bset.inject (inj mu12) (SharedSrc mu12) (SharedTgt mu12);
    mu_inject_23: Bset.inject (inj mu23) (SharedSrc mu23) (SharedTgt mu23);
    mu_inj_comp: forall b, inj mu13 b = match (inj mu12 b) with
                                   | Some b' => inj mu23 b'
                                   | None => None
                                   end;
    
  }.

(** TODO: move to Blockset.v *)
Lemma bset_inject_trans:
  forall bs1 bs2 bs3 j12 j23,
    Bset.inject j12 bs1 bs2 ->
    Bset.inject j23 bs2 bs3 ->
    Bset.inject (fun b => match j12 b with
                       | Some b' => j23 b'
                       | None => None
                       end)
                bs1 bs3.
Proof.
  intros. constructor.
  
  inv H; inv H0. clear inj_dom inj_dom0.
  inv inj_weak; inv inj_weak0. constructor.
  (* 1 *)
  intros. destruct (j12 b) eqn:?; inv H.
  eapply inj_dom'; eauto.
  (* 2 *)
  intros. eapply inj_range0 in H. destruct H. pose proof (inj_dom'0 _ _ H).
  eapply inj_range in H0. destruct H0. eexists. rewrite H0. eauto.
  (* 3 *)
  intros. destruct (j12 b) eqn:?; inv H.
  eapply inj_range'0; eauto.
  (* 4 *)
  intros b1 b1' b3 H H0.
  destruct (j12 b1) eqn:?; inv H. destruct (j12 b1') eqn:?; inv H0.
  specialize (inj_injective0 _ _ _ H1 H2); subst.
  eapply inj_injective; eauto.

  intros. inv H; inv H0. apply inj_dom in H1. destruct H1. rewrite H. 
  eapply inj_dom0. eapply Bset.inj_range'; eauto.
Qed.

Lemma mu_compose_bset_inject:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    Bset.inject (inj mu12) (SharedSrc mu12) (SharedTgt mu12) ->
    Bset.inject (inj mu23) (SharedSrc mu23) (SharedTgt mu23) ->
    Bset.inject (inj mu13) (SharedSrc mu13) (SharedTgt mu13).
Proof.
  intros mu12 mu23 mu13 COMP INJ12 INJ23.
  inv COMP. rewrite mu_Shared2_equiv0 in mu_inject_13.
  exploit bset_inject_trans. eexact mu_inject_13. eexact mu_inject_24.
  intros. rewrite mu_Shared1_equiv0, mu_Shared3_equiv0 in H.
  replace (inj mu13) with (fun b : block => match inj mu12 b with
                                         | Some b' => inj mu23 b'
                                         | None => None
                                         end); auto.
  apply Axioms.functional_extensionality. auto.
Qed.

Ltac tryrewrite :=
  match goal with
  | H: ?x = ?y |- context[?x] =>
    rewrite H in *; clear H
  end.

Lemma mu_compose_Shared_equiv_2:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall b, (SharedSrc mu23 b <-> SharedTgt mu12 b).
Proof.
  clear; intros.
  inv H. tryrewrite. tauto.
Qed.

Lemma mu_compose_Shared_equiv_3:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall b, (SharedTgt mu13 b <-> SharedTgt mu23 b).
Proof.
  clear; intros. inv H. tryrewrite. tauto.
Qed.

(** GE and INIT MEM *)
Lemma ge_match_mu_interpolant:
  forall F1 V1 F2 V2 F3 V3 ge1 ge2 ge3 mu13,
    @ge_match_strict F1 V1 F2 V2 ge1 ge2 ->
    @ge_match_strict F2 V2 F3 V3 ge2 ge3 ->
    ge_init_inj mu13 ge1 ge3 ->
    exists mu12 mu23,
      ge_init_inj mu12 ge1 ge2 /\
      ge_init_inj mu23 ge2 ge3 /\
      mu_compose mu12 mu23 mu13.
Proof.
  clear; intros F1 V1 F2 V2 F3 V3 ge1 ge2 ge3 mu13 GEM12 GEM23 GEINJ13.
  assert (exists j12_ident, (forall id, inj_oblock j12_ident ((Genv.genv_symb ge1) ! id) ((Genv.genv_symb ge2) ! id))
                       /\ (forall b b', j12_ident b = Some b' -> exists id, (Genv.genv_symb ge1) ! id = Some b /\
                                                                (Genv.genv_symb ge2) ! id = Some b'))
    as [j12_ident [INJSENV12 DOMRANGE12]].
  { exists (fun b => match Genv.invert_symbol ge1 b with
             | Some id => (Genv.genv_symb ge2) ! id
             | None => None
             end).
    split. intro.
    destruct ((Genv.genv_symb ge1)! id) eqn:FIND1, ((Genv.genv_symb ge2)!id) eqn:FIND2; try constructor.
    apply Genv.find_invert_symbol in FIND1. rewrite FIND1. auto.
    1-2: exfalso; erewrite genv_symb_eq in FIND1; eauto; try congruence.
    intros. destruct (Genv.invert_symbol ge1 b) eqn:FINDID; try discriminate. 
    eapply Genv.invert_find_symbol in FINDID. eauto.
  }
  assert (INJECTIVE12: Bset.inj_inject j12_ident).
  { intros b1 b2 b' J1 J2. exploit DOMRANGE12; try exact J1. intros [id1 [FIND1 FIND1']].
    exploit DOMRANGE12; try exact J2. intros [id2 [FIND2 FIND2']].
    exploit Genv.genv_vars_inj. exact FIND1'. exact FIND2'. intro; subst. congruence. }
  assert (exists j12, inject_incr (Bset.inj_to_meminj j12_ident) (Bset.inj_to_meminj j12) /\
                 Bset.inject j12 (fun b => Plt b (Genv.genv_next ge1)) (fun b => Plt b (Genv.genv_next ge2)))
    as [j12 [INJINCR12 INJECT12]].
  (** TODO: extract extension in Localize.v *)
  { inv GEM12. rewrite genv_next_eq. eapply inj_extension; eauto.
    intros. exploit DOMRANGE12; eauto. intros [id [FINDID FINDID']].
    rewrite <- genv_next_eq at 1. split; eapply Genv.genv_symb_range; eauto. }
  assert (exists j21, (forall b b', j12 b = Some b' <-> j21 b' = Some b)) as [j21 Hj21].
  { exploit finite_bset_inject_revert; eauto. simpl. eauto.
    intros [j21 [INJECT21 INJEQ]]. eauto. }
  assert (exists j23, (forall id, inj_oblock j23 ((Genv.genv_symb ge2) ! id) ((Genv.genv_symb ge3) ! id))
                 /\ Bset.inject j23 (fun b => Plt b (Genv.genv_next ge2)) (fun b => Plt b (Genv.genv_next ge3))
                 /\ (forall b, inj mu13  b = match j12 b with Some b2 => j23 b2 | None => None end))
    as [j23 [INJSENV23 [INJECT23 MUCOMP]]].
  { exists (fun b2 => match j21 b2 with Some b1 => inj mu13 b1 | None => None end).
    (** SENV *)
    split. intros. destruct ((Genv.genv_symb ge2) ! id) eqn:FIND2, ((Genv.genv_symb ge3) ! id) eqn:FIND3.
    2-3: exfalso; try erewrite genv_symb_eq in FIND2; eauto; try congruence.
    2: constructor.
    specialize (INJSENV12 id). inv INJSENV12; try congruence. rewrite FIND2 in H1; inv H1.
    eapply inject_incr_bset_inj_incr in H2; eauto. apply Hj21 in H2.
    constructor. rewrite H2. pose proof (senv_injected mu13 ge1 ge3 GEINJ13 id). inv H0; unfold Genv.find_symbol in *.
    rewrite <- H in H1; inv H1. rewrite FIND3 in H4; inv H4. auto. congruence.
    (** INJECT *)
    split. constructor. constructor; intros.
    destruct (j21 b) eqn:J21; try discriminate. apply Hj21 in J21. eapply Bset.inj_range'; inv INJECT12; eauto.
    exploit Bset.inj_range. inv GEINJ13. inv mu_inject. eauto. inv GEINJ13. rewrite mu_shared_tgt. eauto.
    intros [b1 INJ13]. exploit Bset.inj_dom'. inv GEINJ13. inv mu_inject; eauto. eauto. erewrite mu_shared_src; eauto.
    intros Hb1. eapply Bset.inj_dom in Hb1; eauto. destruct Hb1 as [b2 J12]. apply Hj21 in J12.
    exists b2. rewrite J12. auto.
    destruct (j21 b); try discriminate. inv GEINJ13. inv mu_inject. rewrite mu_shared_tgt in inj_weak.
    eapply Bset.inj_range'; eauto.
    destruct (j21 b1) eqn:J21, (j21 b2) eqn:J21'; try discriminate.
    apply Hj21 in J21. apply Hj21 in J21'. inv GEINJ13. inv mu_inject. exploit Bset.inj_injective.
    eauto. exact H. exact H0. intro; subst. congruence.
    intros b2 Hb2. eapply Bset.inj_range in Hb2; inv INJECT12; eauto. destruct Hb2 as [b1 J12].
    exploit Bset.inj_dom'; eauto. inv GEINJ13. rewrite <- mu_shared_src. intro.
    exploit Bset.inj_dom; eauto. intros [b3 J13].
    exists b3. apply Hj21 in J12. rewrite J12. auto.
    (** COMP *)
    intros b1. destruct (j12 b1) eqn:J12. apply Hj21 in J12. rewrite J12. auto.
    inv GEINJ13. destruct (plt b1 (Genv.genv_next ge1)). exfalso.
    exploit Bset.inj_dom; try exact INJECT12; eauto. intros [? ?]. congruence.
    destruct (inj mu13 b1) eqn:C; auto. eapply Bset.inj_dom' in C; inv mu_inject; eauto.
    rewrite mu_shared_src in C. contradiction. }
  exists (Build_Mu j12 (fun b => Plt b (Genv.genv_next ge1)) (fun b => Plt b (Genv.genv_next ge2))),
  (Build_Mu j23 (fun b => Plt b (Genv.genv_next ge2)) (fun b => Plt b (Genv.genv_next ge3))).
  split.
  { constructor; simpl; auto. intro id. specialize (INJSENV12 id). unfold Genv.find_symbol.
    inv INJSENV12; constructor. apply inject_incr_bset_inj_incr with j12_ident; auto. }
  split.
  { constructor; simpl; auto. }
  { constructor; simpl; auto.
    inv GEINJ13. rewrite mu_shared_src. eauto.
    erewrite mu_shared_src; eauto. erewrite mu_shared_tgt; eauto. }
Qed.

(** Here we need constraints on init_mem, which should be a property of Language...
    that says, we need any memory, with nextblock = ge.next, and initial data properly initialized,
    no matter what the content in blocks not correspond to any ident, should be a proper initial memory *)

Lemma init_mem_interpolant:
  forall L1 L3 ge1 ge3 L2 ge2 mu13,
    ge_init_inj mu13 ge1 ge3 ->
    (inject_incr (Bset.inj_to_meminj (inj mu13)) inject_id) ->
    ge_match_strict ge1 ge2 ->
    ge_match_strict ge2 ge3 ->
    exists mu12 mu23,
      mu_compose mu12 mu23 mu13 /\
      (inject_incr (Bset.inj_to_meminj (inj mu12)) inject_id) /\
      (inject_incr (Bset.inj_to_meminj (inj mu23)) inject_id) /\
      (SharedTgt mu12 = SharedTgt mu13) /\
      ge_init_inj mu12 ge1 ge2 /\
      ge_init_inj mu23 ge2 ge3 /\    
      (forall m1 m3
         (INITRC: forall m3, init_mem L3 ge3 m3 -> reach_closed m3 (fun b => Plt b (Genv.genv_next ge3))), 
          init_mem L1 ge1 m1 ->
          init_mem L2 ge2 m3 ->
          init_mem L3 ge3 m3 ->
          mem_init_inj mu13 m1 m3 ->
          mem_init_inj mu12 m1 m3 /\
          mem_init_inj mu23 m3 m3).
Proof.
  clear. intros L1 L3 ge1 ge3 L2 ge2 mu13 GEINJ13 INJID13 GEM12 GEM23.
  remember (Genv.genv_next ge1) as B.
  assert (HMU13: mu13 = Build_Mu (fun b => if plt b B then Some b else None) (fun b => Plt b B) (fun b => Plt b B)).
  { destruct mu13. inv GEINJ13. simpl in *.
    erewrite <- genv_next_eq in mu_shared_tgt; eauto.
    erewrite <- genv_next_eq in mu_shared_tgt; eauto.
    subst. f_equal.
    apply Axioms.functional_extensionality. intro b.
    destruct (inj b) eqn:INJ.
    exploit INJID13. unfold Bset.inj_to_meminj. rewrite INJ. eauto.
    intro. inv H. exploit Bset.inj_range'; eauto using Bset.inj_weak. intro. unfold Bset.belongsto in H.
    destruct plt; auto. try contradiction.
    destruct plt; auto. exploit Bset.inj_dom; eauto. intros [b' INJ']. congruence. }
  exists mu13, mu13. split.
  { (* mu compose *)
    constructor; try (subst; simpl; eauto; fail).
    inv GEINJ13; simpl in *. auto.
    inv GEINJ13; simpl in *. auto.
    intros. destruct (inj mu13 b) eqn:INJ; auto.
    exploit INJID13. unfold Bset.inj_to_meminj. rewrite INJ. eauto.
    intro A. inv A. auto. }
  split. auto. split. auto. split. auto. split.
  { (* ge_init_inj *)
    constructor. subst. simpl. eauto.
    subst. simpl. erewrite genv_next_eq; eauto.
    inv GEINJ13; eauto.
    intro. unfold Senv.find_symbol; simpl. unfold Genv.find_symbol. inv GEM12; simpl.
    rewrite <- genv_symb_eq. destruct ((Genv.genv_symb ge1)!id) eqn:A; constructor.
    apply Genv.genv_symb_range in A. destruct plt; auto. contradiction. }
  split.
  { (* ge_init_inj *)
    constructor. subst. simpl. erewrite genv_next_eq; eauto. eauto.
    subst. simpl. erewrite genv_next_eq, (genv_next_eq ge2); eauto. 
    inv GEINJ13; eauto.
    intro. unfold Senv.find_symbol; simpl. unfold Genv.find_symbol. 
    erewrite <- (genv_symb_eq ge2 ge3); auto. destruct ((Genv.genv_symb ge2)!id) eqn:A; constructor.
    apply Genv.genv_symb_range in A. erewrite <- genv_next_eq in A; eauto.
    subst. simpl. destruct plt; auto. contradiction. }
  intros m1 m3 INITRC3 INITM1 INITM2 INITM3 MEMINJ13. split. auto.
  { (* meminj33 *)
    constructor.
    1-2: inv MEMINJ13; subst; simpl in *; intro; rewrite dom_eq_tgt; tauto.
    { (* meminj *)
      assert (Bset.inj_to_meminj (inj mu13) = Mem.flat_inj (Mem.nextblock m3)).
      { apply Axioms.functional_extensionality. intro b.
        unfold Bset.inj_to_meminj, Mem.flat_inj. destruct (inj mu13 b) eqn:INJ13.
        exploit INJID13. unfold Bset.inj_to_meminj. rewrite INJ13. eauto. intro A. inv A.
        exploit Bset.inj_range'. eapply Bset.inj_weak. eapply wd_mu_init; eauto.
        eauto. erewrite dom_eq_tgt; eauto. intro. destruct plt; auto. contradiction.
        destruct plt; auto. exploit Bset.inj_dom. eapply wd_mu_init; eauto.
        erewrite mu_shared_src; eauto. do 2 (erewrite genv_next_eq; eauto).
        erewrite <- mu_shared_tgt; eauto. rewrite dom_eq_tgt; eauto.
        rewrite INJ13. intros [b' ?]. discriminate. }
      rewrite H.
      eapply Mem.neutral_inject. unfold Mem.inject_neutral. rewrite <- H.
      constructor; unfold Bset.inj_to_meminj; intros.
      { (* perm *)
        destruct (inj mu13 b1) eqn:INJ13; inv H0. simpl in *.
        destruct plt; inv INJ13. rewrite Z.add_0_r. auto.
      }
      { (* align *)
        destruct (inj mu13 b1) eqn:INJ13; inv H0. apply Z.divide_0_r.
      }
      { (* memval *)
        destruct (inj mu13 b1) eqn:INJ13; inv H0; simpl in *.
        destruct plt; inv INJ13. rewrite Z.add_0_r.
        destruct (ZMap.get ofs ((Mem.mem_contents m3) !! b2)) eqn:MEMVAL; try constructor.
        destruct v; try constructor.
        assert (Bset.belongsto (fun b => Plt b (Genv.genv_next ge1)) b).
        { do 2 (erewrite genv_next_eq; eauto). apply reachable_closure with m3; auto.
          apply Reachable with ((b2, i)::nil). econstructor; eauto. constructor.
          simpl. do 2 (erewrite genv_next_eq in p; [|eauto]). eauto. }
        econstructor.
        destruct plt; eauto. contradiction.
        rewrite Ptrofs.add_zero. auto.
      }
    }
    inv MEMINJ13; auto.
    intros b b' delta. unfold Bset.inj_to_meminj. subst; simpl. destruct plt; try discriminate.
    intro. inv H. auto.
  }
Qed.

(** ARGS *)
Lemma arg_rel_interpolant:
  forall mu12 mu23 mu13 args1 args3,
    mu_compose mu12 mu23 mu13 ->
    G_args (SharedSrc mu13) args1 ->
    arg_rel (inj mu13) args1 args3 ->
    exists args2,
      G_args (SharedSrc mu23) args2 /\
      arg_rel (inj mu12) args1 args2 /\
      arg_rel (inj mu23) args2 args3.
Proof.
  clear; intros mu12 mu23 mu13 args1.
  induction args1; intros args3 HMU GARG1 ARGREL; inv ARGREL; inv GARG1.
  eexists. split. constructor.  split; constructor.
  exploit IHargs1; eauto. intros [args2' [GARG2 [ARGREL'12 ARGREL'23]]].
  clear IHargs1 H3 H4. erewrite <-mu_Shared1_equiv in H2; eauto.
  inv H1; try (eexists; split; [| split; constructor; eauto]; econstructor; eauto; fail).
  unfold Bset.inj_to_meminj in H. destruct (inj mu13 b1) eqn:INJ; inv H.
  erewrite mu_inj_comp in INJ; eauto. destruct (inj mu12 b1) eqn:INJ12; try discriminate.
  exists (Vptr b ofs1 :: args2'). split; repeat econstructor; eauto.
  simpl. eapply Bset.inj_dom'; eauto. eapply Bset.inj_weak, mu_inject_23; eauto.
  unfold Bset.inj_to_meminj. rewrite INJ12. eauto. rewrite Ptrofs.add_zero. auto.
  unfold Bset.inj_to_meminj. rewrite INJ. auto.
Qed.

Lemma mu_compose_arg_rel_trans:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall arg1 arg2 arg3,
      arg_rel (inj mu12) arg1 arg2 ->
      arg_rel (inj mu23) arg2 arg3 ->
      arg_rel (inj mu13) arg1 arg3.
Proof.
  clear. induction arg1; intros arg2 arg3 REL12 REL23; inv REL12; inv REL23; constructor.
  inv H2; inv H3; try constructor.
  unfold Bset.inj_to_meminj in *. 
  destruct (inj mu12 b1) eqn:INJ12; inv H0. destruct (inj mu23 b2) eqn:INJ23; inv H5. eauto.
  econstructor. erewrite mu_inj_comp; eauto. rewrite INJ12, INJ23; eauto. 
  repeat rewrite Ptrofs.add_zero. auto.
  eapply IHarg1; eauto.
Qed.  

Lemma mu_compose_ores_rel_strict_interpolant:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall ores1 ores3,
      ores_rel (inj mu13) ores1 ores3 ->
      exists ores2,
        ores_rel (inj mu12) ores1 ores2 /\
        ores_rel (inj mu23) ores2 ores3.
Proof.
  intros; destruct ores1, ores3; inv H0;
    match goal with |- context[ores_rel _ ?x _] => try (exists x; split; econstructor; eauto; fail) end.
  unfold Bset.inj_to_meminj in H1. destruct (inj mu13 b1) eqn:INJ13; inv H1.
  erewrite mu_inj_comp in INJ13; eauto. destruct (inj mu12 b1) eqn:INJ12; try discriminate.
  exists (Some (Vptr b ofs1)).
  split; econstructor; unfold Bset.inj_to_meminj; try rewrite INJ12; try rewrite INJ13; eauto using Ptrofs.add_zero.
Qed.

Lemma mu_compose_res_rel_strict_trans:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall r1 r2 r3,
      res_rel (inj mu12) r1 r2 ->
      res_rel (inj mu23) r2 r3 ->
      res_rel (inj mu13) r1 r3.
Proof.
  intros. inv H0; inv H1; try constructor.
  unfold Bset.inj_to_meminj in *. destruct (inj mu12 b1) eqn:INJ12, (inj mu23 b2) eqn:INJ23; inv H2; inv H4.
  econstructor. unfold Bset.inj_to_meminj. erewrite mu_inj_comp. rewrite INJ12, INJ23. eauto. auto.
  auto using Ptrofs.add_zero.
Qed.

(** FPMatch' trans *)
Lemma mu_compose_LocMatch_trans:
    forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall ls1 ls2 ls3,
      LocMatch mu12 ls1 ls2 ->
      LocMatch mu23 ls2 ls3 ->
      LocMatch mu13 ls1 ls3.
Proof.
  intros. inv H0; inv H1. constructor; intros.
  exploit H0; eauto. erewrite mu_Shared3_equiv; eauto. intros [b2 [INJ23 SHARED2]].
  exploit H2; eauto. erewrite mu_Shared2_equiv; eauto. eapply Bset.inj_dom'; eauto. inv H. inv mu_inject_24; eauto.
  intros [b1 [INJ12 SHARED1]].
  exists b1. split; auto. unfold Bset.inject_block in *. erewrite mu_inj_comp; eauto. rewrite INJ12, INJ23. auto.
Qed.
  
Lemma mu_compose_FPMatch'_trans:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall fp1 fp2 fp3,
      FPMatch' mu12 fp1 fp2 ->
      FPMatch' mu23 fp2 fp3 ->
      FPMatch' mu13 fp1 fp3.
Proof.
  clear; intros. destruct H1 as [A B C D].
  constructor; unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes, FP.ge_frees in *;
    eapply mu_compose_LocMatch_trans; eauto; clear A B C D;
      repeat apply Injections.locs_match_union_T; inv H0; eauto;
        repeat (eapply eq_locs_match; [eapply Locs.union_sym| eapply Locs.eq_refl|apply locs_match_union_S; auto]).
Qed.

(** Inv trans *)
Lemma mu_compose_Inv_trans:
  forall mu12 mu23 mu13,
    mu_compose mu12 mu23 mu13 ->
    forall m1 m2 m3,
      LDefs.Inv mu12 m1 m2 ->
      LDefs.Inv mu23 m2 m3 ->
      LDefs.Inv mu13 m1 m3.
Proof.
  clear. intros.
  unfold LDefs.Inv in *.
  exploit Mem.inject_compose. exact H0. exact H1. clear H0 H1.
  match goal with |- Mem.inject ?j1 _ _ -> Mem.inject ?j2 _ _ => cut (j1 = j2) end.
  intros. rewrite <- H0. auto.
  unfold Bset.inj_to_meminj, compose_meminj.
  apply Axioms.functional_extensionality. intro. erewrite (mu_inj_comp _ _ mu13); eauto.
  destruct (inj mu12); auto. destruct (inj mu23); auto.
Qed.

(** RELY *)
Record HLRelyTransPre (mu12 mu23 mu13: Mu) (m1 m2 m3: Mem.mem) : Prop :=
  mkrelytranspre {
      rely_trans_mu_compose: mu_compose mu12 mu23 mu13;
    }.
        
Lemma HLRelyTransPre_mu_compose:
  forall mu12 mu23 mu13 m1 m2 m3,
    HLRelyTransPre mu12 mu23 mu13 m1 m2 m3 ->
    mu_compose mu12 mu23 mu13.
Proof. destruct 1; auto. Qed.

Lemma Inv_local_interpolant:
  forall mu12 mu23 mu13 m2 m1' m3',
    mu_compose mu12 mu23 mu13 ->
    LDefs.Inv mu13 m1' m3' ->
    reach_closed m3' (SharedTgt mu13) ->
    (forall b, SharedTgt mu12 b -> Mem.valid_block m2 b) ->
    exists m2', LDefs.Inv mu12 m1' m2' /\
           LDefs.Inv mu23 m2' m3' /\
           LDefs.Rely (SharedSrc mu23) m2 m2'.
Proof.
  intros mu12 mu23 mu13 m2 m1' m3' MUCOMP INV13 RC3 FINITE2.
  exploit mu_finite_1; eauto. intros [bound1 FINITE1].
  (** FINITE -> INJECT -> FINITE *)
  (*
  assert (exists bound2, forall b, SharedTgt mu12 b -> Plt b bound2) as (bound2 & FINITE2).
  { inv MUCOMP. inv mu_inject_13. inv inj_weak. destruct mu12; simpl in *.
    assert (FINITE: forall b', SharedTgt b' -> exists b, inj b = Some b' /\ Plt b bound1).
    { intros. apply inj_range in H. destruct H.  eexists. split. eauto. apply FINITE1.
      rewrite <- mu_Shared1_equiv0. eapply inj_dom'. eauto. }
    revert FINITE inj_injective. clear. revert inj bound1 SharedTgt. unfold block.
    intros j B T. revert T. pattern B. eapply positive_Peano_ind; clear B; intros.
    exists 1%positive. intros. exfalso. apply FINITE in H. destruct H as [b0 [H H']]. eapply Pos.nlt_1_r; eauto.
    specialize (H (fun b' => T b' /\ (forall b, j b = Some b' -> Plt b x))); simpl in H.
    exploit H. intros b' [RANGE BOUND]. apply FINITE in RANGE. destruct RANGE as [b [INJ _]]. exists b. split; auto. auto.
    intros [B' BOUND].
    destruct (j x) as [B''|] eqn:XIMG. 
    exists (Pos.max B' (Pos.succ B'')). intros. exploit FINITE. exact H0. intros [b0 [INJ BOUND']].
    destruct (peq b0 x).
    subst. rewrite XIMG in INJ. inv INJ. pose proof (Pos.le_max_r B' (Pos.succ b)).
    unfold Plt in *. apply Pos.le_succ_l; eauto.
    apply Plt_Ple_trans with B'. apply BOUND. split; auto. intros.
    exploit inj_injective. exact H1. exact INJ. intro. subst. apply Plt_succ_inv in BOUND'. destruct BOUND'; congruence.
    apply Pos.le_max_l.
    exists B'. intros. exploit FINITE. exact H0. intros [b0 [INJ BOUND']].
    destruct (peq b0 x). subst. congruence.
    apply BOUND. split; auto. intros. exploit inj_injective. exact INJ. exact H1. intros; subst.
    apply Plt_succ_inv in BOUND'. destruct BOUND'; congruence. } *)
  exploit finite_bset_inject_revert. exact FINITE2. exploit mu_inject_23; eauto. 
  erewrite <- mu_Shared2_equiv; eauto. intros [j32 [INJECT32 CONSIST23]].
  pose (Mem.nextblock m2) as bound2. 
  
  exists (update_memory (inj mu23) j32 bound2 m2 m3'). split.
  (** INV12 *)
  unfold LDefs.Inv, Bset.inj_to_meminj, update_memory.
  constructor. constructor.
  (** perm *)
  { intros until 1. destruct (inj mu12 b1) eqn:? ; inv H. pose proof Heqo as INJ12.
    eapply Bset.inj_range' in Heqo; try (eapply Bset.inj_weak; eapply mu_inject_12; eauto; fail).
    erewrite mu_Shared2_equiv in Heqo; eauto. eapply Bset.inj_dom in Heqo; try (eapply mu_inject_23; eauto).
    destruct Heqo as [b3 INJ23]. pose proof (mu_inj_comp _ _ _ MUCOMP b1) as INJ13. rewrite INJ12, INJ23 in INJ13.
    intro PERM1. exploit Mem.mi_perm; try exact PERM1.
    inv INV13; eauto. unfold Bset.inj_to_meminj. rewrite INJ13; eauto.
    rewrite Z.add_0_r. intro PERM3. unfold Mem.perm, Mem.perm_order' in *; simpl in *; intros.
    destruct ((Mem.mem_access m1') !! b1 ofs k) eqn:PERM1'; try contradiction.
    destruct ((Mem.mem_access m3') !! b3 ofs k) eqn:PERM3'; try contradiction.
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H. rewrite H0. unfold update_access_func. destruct plt.
    rewrite INJ23. rewrite PERM3'. auto.
    exfalso. eapply n. apply FINITE2. eapply Bset.inj_range' in INJ12; eauto. eapply Bset.inj_weak, mu_inject_12; eauto.
  }
  (** align *)
  { intros. destruct (inj mu12 b1); inv H. apply Z.divide_0_r. }
  (** memval *)
  { simpl. intros.
    pose proof (proj2_sig (inject_content_c (inj mu23) j32
                                            bound2 (Mem.mem_contents m2) (Mem.mem_contents m3'))).
    destruct H1. rewrite H2. destruct (inj mu12 b1) eqn:?; inv H. rewrite Z.add_0_r.
    exploit Bset.inj_range'; eauto. eapply Bset.inj_weak, mu_inject_12; eauto. intro SHARED2.
    exploit (FINITE2 b2). auto. intro BOUND. unfold inject_content. destruct plt; [|contradiction].
    exploit Bset.inj_dom. eapply mu_inject_23; eauto. erewrite <- mu_Shared2_equiv; eauto.
    intros [b3 INJ23]. rewrite INJ23.
    destruct (proj2_sig (inject_zmap_memval_c j32 (Mem.mem_contents m3') !! b3)).
    rewrite H3. unfold inject_zmap_memval.
    exploit Mem.mi_memval. inv INV13; eauto. unfold Bset.inj_to_meminj.
    erewrite mu_inj_comp; eauto. rewrite Heqo, INJ23; eauto. eauto. rewrite Z.add_0_r.
    intro MEMVAL. inv MEMVAL; simpl; constructor. inv H6; simpl; try constructor.
    unfold Bset.inj_to_meminj in H7. destruct (inj mu13 b0) eqn:INJ13'; inv H7.
    exploit mu_inj_comp; eauto. rewrite INJ13'. intro. destruct (inj mu12 b0) eqn:INJ12'; try discriminate.
    symmetry in H6. apply CONSIST23 in H6. rewrite H6. econstructor.
    rewrite INJ12'. eauto. auto. }
  (** freeblocks *)
  { intros. destruct (inj mu12 b) eqn:INJ12; auto. exfalso. 
    exploit Mem.mi_freeblocks; eauto. unfold Bset.inj_to_meminj. erewrite mu_inj_comp; eauto.
    rewrite INJ12. destruct (inj mu23 b0) eqn:INJ23. discriminate. eapply Bset.inj_range' in INJ12.
    eapply Bset.inj_dom in INJ12. rewrite INJ23 in INJ12. destruct INJ12. discriminate.
    eapply mu_inject_23; eauto. erewrite <- mu_Shared2_equiv; eauto. eapply Bset.inj_weak, mu_inject_12; eauto. }
  (** mapped blocks *)
  { intros. unfold Mem.valid_block; simpl. destruct (inj mu12 b) eqn:INJ12; inv H.
    apply Pos.max_lt_iff. right. apply FINITE2. eapply Bset.inj_range'; eauto. eapply mu_inject_12; eauto. }
  (** no overlap *)
  { unfold Mem.meminj_no_overlap. intros.
    destruct (inj mu12 b1) eqn:INJ1; inv H0.
    destruct (inj mu12 b2) eqn:INJ2; inv H1.
    left. intro. apply H. subst. eapply Bset.inj_injective; eauto. eapply mu_inject_12; eauto. }
  (** representable *)
  { intros. destruct (inj mu12 b) eqn:INJ12; inv H.
    split;[xomega|]. pose proof (Ptrofs.unsigned_range ofs). unfold Ptrofs.max_unsigned. omega. }
  (** perm inv *)
  { unfold Mem.perm, Mem.perm_order'; simpl. intros.
    destruct (inj mu12 b1) eqn:INJ12; inv H. rewrite Z.add_0_r in H0.
    exploit Bset.inj_range'; eauto. eapply Bset.inj_weak, mu_inject_12; eauto. intro SHARED2.
    exploit (FINITE2 b2). auto. intro BOUND.
    exploit Bset.inj_dom. eapply mu_inject_23; eauto. erewrite <- mu_Shared2_equiv; eauto. intros [b3 INJ23].
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H. rewrite H1 in H0. unfold update_access_func in H0.
    destruct plt; try contradiction. rewrite INJ23 in H0.
    eapply Mem.mi_perm_inv; eauto. unfold Bset.inj_to_meminj. erewrite mu_inj_comp, INJ12, INJ23; eauto.
    rewrite Z.add_0_r. auto. }

  (** INV23 *)
  split.
  unfold LDefs.Inv, Bset.inj_to_meminj, update_memory.
  constructor. constructor.
  (** perm *)
  { intros b2 b3; intros until 1. destruct (inj mu23 b2) eqn:? ; inv H. pose proof Heqo as INJ23.
    eapply Bset.inj_dom' in Heqo; try (eapply Bset.inj_weak; eapply mu_inject_23; eauto; fail).
    exploit FINITE2. erewrite mu_Shared2_equiv; eauto. intro BOUND2.
    unfold Mem.perm, Mem.perm_order'; simpl.
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H. rewrite H0. unfold update_access_func. destruct plt; try contradiction.
    rewrite INJ23, Z.add_0_r. auto. }
  (** align *)
  { intros. destruct (inj mu23 b1); inv H. apply Z.divide_0_r. }
  (** memval *)
  { simpl. intros b2 ofs b3 delta INJ23 PERM.
    pose proof (proj2_sig (inject_content_c (inj mu23) j32
                                            bound2 (Mem.mem_contents m2) (Mem.mem_contents m3'))).
    destruct H. rewrite H0. destruct (inj mu23 b2) eqn:?; inv INJ23. rewrite Z.add_0_r.
    exploit Bset.inj_dom'; eauto. eapply Bset.inj_weak, mu_inject_23; eauto. intro SHARED2.
    exploit FINITE2. erewrite mu_Shared2_equiv; eauto. intro BOUND2.
    unfold inject_content. destruct plt; try contradiction. rewrite Heqo. 
    destruct (proj2_sig (inject_zmap_memval_c j32 (Mem.mem_contents m3') !! b3)).
    rewrite H2. unfold inject_zmap_memval.
    destruct (ZMap.get ofs (Mem.mem_contents m3') !! b3); simpl; constructor.
    destruct v; simpl; try econstructor.
    destruct (j32 b) eqn:J32; [|constructor].
    apply CONSIST23 in J32. econstructor. rewrite J32. eauto. auto using Ptrofs.add_zero. }
  (** freeblocks *)
  { intros. destruct (inj mu23 b) eqn:INJ23; auto. exfalso. apply H.
    exploit FINITE2. erewrite mu_Shared2_equiv; eauto. eapply Bset.inj_dom'; eauto.
    eapply Bset.inj_weak, mu_inject_23; eauto. intro BOUND2.
    unfold Mem.valid_block. simpl. apply Pos.max_lt_iff. auto. }
  (** mapped blocks *)
  { intros b2 b3 delta INJ23. destruct (inj mu23 b2) eqn:INJ23'; inv INJ23.
    exploit Bset.inj_dom'. eapply Bset.inj_weak, mu_inject_23; eauto. eauto.
    erewrite <- mu_Shared2_equiv; eauto. intro SHARED2. exploit Bset.inj_range; eauto.
    eapply Bset.inj_weak, mu_inject_12; eauto. eauto. intros [b1 INJ12].
    eapply Mem.mi_mappedblocks; eauto. unfold Bset.inj_to_meminj. erewrite mu_inj_comp; eauto.
    rewrite INJ12, INJ23'; eauto. }
  (** no overlap *)
  { unfold Mem.meminj_no_overlap. intros.
    destruct (inj mu23 b1) eqn:INJ1; inv H0.
    destruct (inj mu23 b2) eqn:INJ2; inv H1.
    left. intro. apply H. subst. eapply Bset.inj_injective; eauto. eapply mu_inject_23; eauto. }
  (** representable *)
  { intros. destruct (inj mu23 b) eqn:INJ23; inv H.
    split;[xomega|]. pose proof (Ptrofs.unsigned_range ofs). unfold Ptrofs.max_unsigned. omega. }
  (** perm inv *)
  { unfold Mem.perm, Mem.perm_order'; simpl. intros.
    destruct (inj mu23 b1) eqn:INJ23; inv H. rewrite Z.add_0_r in H0.
    exploit Bset.inj_dom'; eauto. eapply Bset.inj_weak, mu_inject_23; eauto. intro SHARED2.
    exploit (FINITE2 b1). erewrite mu_Shared2_equiv; eauto. auto. intro BOUND.
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H. rewrite H1. unfold update_access_func. destruct plt; try contradiction.
    rewrite INJ23. auto. }
  
  (** RELY2 *)
  unfold update_memory. constructor; simpl.
  (** nextblock *)
  subst bound2. apply Pos.max_id.
  (** local unchg *)
  constructor; simpl.
  { subst bound2. rewrite Pos.max_id. auto with coqlib. }
  { unfold Mem.perm. simpl. intros.
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H1. rewrite H2. unfold update_access_func. destruct plt; try contradiction.
    destruct (inj mu23 b) eqn:INJ23; [|tauto].
    exfalso. apply H. eapply Bset.inj_dom'; eauto. eapply Bset.inj_weak, mu_inject_23; eauto. }
  { intros.
    pose proof (proj2_sig (inject_content_c (inj mu23) j32
                                            bound2 (Mem.mem_contents m2) (Mem.mem_contents m3'))).
    destruct H1. rewrite H2. unfold inject_content. destruct plt; auto.
    destruct (inj mu23 b) eqn:INJ23; auto. exfalso.
    apply H. eapply Bset.inj_dom'; eauto. eapply Bset.inj_weak, mu_inject_23; eauto. }
  (** rc *)
  constructor; simpl.
  (** reachable *)
  { intros. inv H. revert b H0. induction L; intros b REACH; inv REACH. auto.
    apply IHL in H1. clear IHL. unfold Mem.perm in H2. simpl in *. 
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H. rewrite H0 in H2. unfold update_access_func in H2.
    pose proof (proj2_sig (inject_content_c (inj mu23) j32
                                            bound2 (Mem.mem_contents m2) (Mem.mem_contents m3'))).
    destruct H3. rewrite H5 in H4. unfold inject_content in H4.
    exploit Bset.inj_dom; try exact H1. eapply mu_inject_23; eauto. intros [b'3 INJ23].
    rewrite INJ23 in H2, H4. destruct (proj2_sig (inject_zmap_memval_c j32 (Mem.mem_contents m3') !! b'3)).
    destruct plt. rewrite H7 in H4. unfold inject_zmap_memval, inject_memval in H4.
    destruct (ZMap.get z (Mem.mem_contents m3') !! b'3) eqn:CONTENT3; inv H4.
    destruct v; inv H9. destruct (j32 b0) eqn:J32; inv H8. apply CONSIST23 in J32.
    eapply Bset.inj_dom'. eapply Bset.inj_weak, mu_inject_23; eauto. eauto.
    exfalso. apply n0. apply FINITE2. erewrite mu_Shared2_equiv; eauto. }
  (** no undef *)
  { intros until z. unfold Mem.perm.
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H as [_ H]. rewrite H. unfold update_access_func.
    pose proof (proj2_sig (inject_content_c (inj mu23) j32
                                            bound2 (Mem.mem_contents m2) (Mem.mem_contents m3'))).
    destruct H0 as [_ H0]. rewrite H0. unfold inject_content. 
    intros SHARED2. exploit Bset.inj_dom. eapply mu_inject_23; eauto. eauto. intros [b3 INJ23].
    exploit Bset.inj_range'. eapply Bset.inj_weak, mu_inject_23; eauto. eauto. intros SHARED3.
    destruct plt.
    rewrite INJ23. destruct (proj2_sig (inject_zmap_memval_c j32 (Mem.mem_contents m3') !! b3)) as [_ H1].
    rewrite H1. unfold inject_zmap_memval, inject_memval.
    intros PERM3 UNDEF. destruct (ZMap.get z (Mem.mem_contents m3') !! b3) eqn:CONTENT3; try discriminate.
    exploit no_undef. exact RC3. erewrite <- mu_Shared3_equiv; eauto. eauto. auto. auto.
    exfalso. apply n, FINITE2. erewrite mu_Shared2_equiv; eauto. }
  (** no vundef *)
  { intros until n. unfold Mem.perm.
    pose proof (proj2_sig (update_access_c (inj mu23) bound2 (Mem.mem_access m2) (Mem.mem_access m3'))).
    destruct H as [_ H]. rewrite H. unfold update_access_func.
    pose proof (proj2_sig (inject_content_c (inj mu23) j32
                                            bound2 (Mem.mem_contents m2) (Mem.mem_contents m3'))).
    destruct H0 as [_ H0]. rewrite H0. unfold inject_content. 
    intros SHARED2. exploit Bset.inj_dom. eapply mu_inject_23; eauto. eauto. intros [b3 INJ23].
    exploit Bset.inj_range'. eapply Bset.inj_weak, mu_inject_23; eauto. eauto. intros SHARED3.
    destruct plt.
    rewrite INJ23. destruct (proj2_sig (inject_zmap_memval_c j32 (Mem.mem_contents m3') !! b3)) as [_ H1].
    rewrite H1. unfold inject_zmap_memval, inject_memval.
    intros PERM3 UNDEF. destruct (ZMap.get z (Mem.mem_contents m3') !! b3) eqn:CONTENT3; try discriminate.
    inv UNDEF. destruct v; inv H3.
    exploit no_vundef. exact RC3. erewrite <- mu_Shared3_equiv; eauto. eauto. eauto. auto.
    destruct (j32 b0) eqn:SHARED0; inv H4.
    exploit reachable_closure. exact RC3. instantiate (1:=b0). 
    econstructor. instantiate (1:= (b3, i)::nil). econstructor.
    constructor. eapply Bset.inj_range'; eauto.  erewrite <- mu_Shared3_equiv; eauto.
    eapply Bset.inj_weak, mu_inject_23; eauto. eauto. eauto. intro SHARED0'.
    eapply Bset.inj_range in SHARED0'; eauto. destruct SHARED0'. rewrite CONSIST23 in H2.
    rewrite H2 in SHARED0. discriminate.
    erewrite <- mu_Shared3_equiv; eauto. eapply mu_inject_23; eauto.
    exfalso. apply n0, FINITE2. erewrite mu_Shared2_equiv; eauto. }
Qed.

Lemma HLRely_local_interpolant:
  forall mu12 mu23 m1 m1' m2 m3 m3' mu13,
    HLRelyTransPre mu12 mu23 mu13 m1 m2 m3 ->
    LDefs.HLRely mu13 m1 m1' m3 m3' ->
    (forall b, SharedTgt mu12 b -> Mem.valid_block m2 b) ->
    exists m2', LDefs.HLRely mu12 m1 m1' m2 m2' /\
           LDefs.HLRely mu23 m2 m2' m3 m3'.
Proof.
  intros mu12 mu23 m1 m1' m2 m3 m3' mu13 PRE HLRELY13 SHARED2.
  destruct HLRELY13 as [RELY1 RELY3 INV13]. 
  exploit Inv_local_interpolant; eauto. eapply HLRelyTransPre_mu_compose; eauto.
  inv RELY3. auto.
  intros (m2' & INV12 & IN23 & RELY2). exists m2'.
  split.
  econstructor; eauto.
  eapply bset_eq_Rely_local; eauto. 
  erewrite <- mu_Shared1_equiv; [|eapply HLRelyTransPre_mu_compose; eauto]. tauto.
  eapply bset_eq_Rely_local; eauto.
  erewrite <- mu_Shared2_equiv; [|eapply HLRelyTransPre_mu_compose; eauto]. tauto.
  econstructor; eauto.
  eapply bset_eq_Rely_local; eauto.
  erewrite <- mu_Shared3_equiv; [|eapply HLRelyTransPre_mu_compose; eauto]. tauto.
Qed.

(** one step sim to plus step sim *)
Lemma plus_concat:
  forall C M (step: C -> M -> FP.t -> C -> M -> Prop) c m fp c' m' fp' c'' m'',
    plus step c m fp c' m' ->
    plus step c' m' fp' c'' m'' ->
    plus step c m (FP.union fp fp') c'' m''.
Proof.
  clear. intros C M step c m fp c' m' fp' c'' m'' H H0.
  generalize dependent fp'. generalize c'' m''. clear c'' m''.
  induction H; intros. eapply plus_cons; eauto. 
  rewrite <- FP.fp_union_assoc. eapply plus_cons; eauto.
Qed.

Lemma match_tau_step_plus:
  forall L1 L2 I order G1 G2 (R12: bool -> I -> Mu -> FP.t -> FP.t -> core L1 * mem -> core L2 * mem -> Prop),
    (forall i mu fp1 fp2 c1 m1 c2 m2,
        R12 true i mu fp1 fp2 (c1, m1) (c2, m2) ->
        forall c1' m1' fp1',
          step_local L1 G1 c1 m1 fp1' c1' m1' ->
          (exists i', order i' i /\ R12 true i' mu (FP.union fp1 fp1') fp2 (c1', m1') (c2, m2))
          \/
          (exists i' fp2' c2' m2',
              plus (step_local L2 G2) c2 m2 fp2' c2' m2' /\
              FPMatch' mu (FP.union fp1 fp1') (FP.union fp2 fp2') /\
              R12 true i' mu (FP.union fp1 fp1') (FP.union fp2 fp2') (c1', m1') (c2', m2')))
    ->
    (forall i mu fp1 fp2 c1 m1 c2 m2,
        R12 true i mu fp1 fp2 (c1, m1) (c2, m2) ->
        forall c1' m1' fp1',
          plus (step_local L1 G1) c1 m1 fp1' c1' m1' ->
          (exists i', clos_trans _ order i' i /\ R12 true i' mu (FP.union fp1 fp1') fp2 (c1', m1') (c2, m2))
          \/
          (exists i' fp2' c2' m2',
              plus (step_local L2 G2) c2 m2 fp2' c2' m2' /\
              FPMatch' mu (FP.union fp1 fp1') (FP.union fp2 fp2') /\
              R12 true i' mu (FP.union fp1 fp1') (FP.union fp2 fp2') (c1', m1') (c2', m2'))).
Proof.
  clear. intros L1 L2 I order G1 G2 R12 SIM i mu fp1 fp2 c1 m1 c2 m2 MATCH c1' m1' fp1' PLUS.
  generalize i mu fp1 fp2 c2 m2 MATCH. clear i mu fp1 fp2 c2 m2 MATCH.
  induction PLUS.
  (* step one *)
  intros. eapply SIM in MATCH; eauto. destruct MATCH; auto.
  left. destruct H0 as [i' [ORDER MATCH]]. exists i'. apply (t_step _ order) in ORDER. auto.
  (* induction *)
  intros i mu fp1 fp2 c2 m2 MATCH.
  exploit SIM; eauto. intros [(i' & ORDER & MATCH')|(i' & fp2' & c2' & m2' & PLUS2 & FPMATCH & MATCH')].
  (* 0 ++ (0\/+) *)
  eapply IHPLUS in MATCH'.
  destruct MATCH' as [(i'' & ORDER' & MATCH'')|(i'' & fp2' & c2' & m2' & PLUS2 & FPMATCH & MATCH')].
  (* 0 ++ 0 *)
  left. exists i''. split; auto. eapply t_trans; eauto. apply t_step; auto. rewrite FP.fp_union_assoc. auto.
  (* 0 ++ + *)
  right. exists i'', fp2', c2', m2'. rewrite FP.fp_union_assoc; auto.
  (* + ++ (0\/+) *)
  eapply IHPLUS in MATCH'.
  destruct MATCH' as [(i'' & ORDER' & MATCH'')|(i'' & fp2'' & c2'' & m2'' & PLUS2' & FPMATCH' & MATCH')].
  right. exists i'', fp2', c2', m2'. rewrite FP.fp_union_assoc.
  split; auto. split. apply fp_match_union_S'; auto. auto.
  right. exists i'', (FP.union fp2' fp2''), c2'', m2''. repeat rewrite FP.fp_union_assoc. split; auto.
  eapply plus_concat; eauto.
Qed.
  

Section TRANSITIVITY.

Variable (L1 L2 L3: sem_local).

Lemma arg_rel_G_args:
  forall j S1 S2,
    Bset.inject j S1 S2 ->
    forall args1 args2,
      arg_rel j args1 args2 ->
      G_args S1 args1 -> G_args S2 args2.
Proof.
  clear. induction args1; intros; inv H0; inv H1; constructor; auto.
  inv H4; auto. simpl. eapply Bset.inj_range'; eauto using Bset.inj_weak.
  unfold Bset.inj_to_meminj in H0. instantiate (1:= b1). destruct (j b1); inv H0; auto.
  inversion H3.
  apply IHargs1; auto.
Qed.

Lemma local_ldsim_transitive:
  forall G1 G2 G3 ge1 ge2 ge3
    (INITRC3: forall m3, init_mem L3 ge3 m3 -> reach_closed m3 (fun b => Plt b (Genv.genv_next ge3)))
    (INITMEMCOMPAT2: forall m3, init_mem L3 ge3 m3 -> init_mem L2 ge2 m3),
    @local_ldsim L1 L2 G1 G2 ge1 ge2 ->
    @local_ldsim L2 L3 G2 G3 ge2 ge3 ->
    @local_ldsim L1 L3 G1 G3 ge1 ge3.
Proof.
  intros G1 G2 G3 ge1 ge2 ge3 INITRC3 INITMEMCOMPAT2 SIM12 SIM23.
  destruct SIM12. rename H into SIM12.
  rename I into I12. rename I_order into order12. rename match_state into R12.
  destruct SIM23. rename H into SIM23.
  rename I into I23. rename I_order into order23. rename match_state into R23.

  remember (lex_ord' order12 (clos_trans _ order23)) as order13.
  remember (fun (beta:bool) (i: I12 * I23) mu13 fp1 fp3 (s1: core L1 * mem) (s3: core L3 * mem) =>
              let (i12, i23) := i in
              let (c1, m1) := s1 in
              let (c3, m3) := s3 in
              if beta
              then
                (exists mu12 mu23 fp2 c2 m2,
                    R12 beta i12 mu12 fp1 fp2 (c1, m1) (c2, m2) /\
                    R23 beta i23 mu23 fp2 fp3 (c2, m2) (c3, m3) /\
                    mu_compose mu12 mu23 mu13)
              else (exists mu12 mu23 c2 m2,
                       R12 beta i12 mu12 fp1 FP.emp (c1, m1) (c2, m2) /\
                       R23 beta i23 mu23 FP.emp fp3 (c2, m2) (c3, m3) /\
                       mu_compose mu12 mu23 mu13 /\
                       (forall b, SharedTgt mu12 b -> Mem.valid_block m2 b ))
           ) as R13.
  
  eapply (Local_ldsim G1 G3 ge1 ge3 _ order13 R13).
  constructor.
  
  (* order wf *)
  subst. apply lexorder'_wf; try eapply wf_clos_trans; eapply index_wf; eauto.
  
  (* mu wd*)
  intros beta [i12 i23] mu13 fp1 fp3 [c1 m1] [c3 m3] MATCH13. destruct beta.
  subst R13. destruct MATCH13 as (mu12 & mu23 & fp2 & c2 & m2 & MATCH12 & MATCH23 & COMPATMU).
  eapply mu_compose_bset_inject; eauto.
  eapply wd_mu. eapply SIM12. eapply MATCH12.  
  eapply wd_mu. eapply SIM23. eapply MATCH23.
  subst R13. destruct MATCH13 as (mu12 & mu23 & c2 & m2 & MATCH12 & MATCH23 & COMPATMU & SHARED2).
  eapply mu_compose_bset_inject; eauto.
  eapply wd_mu. eapply SIM12. eapply MATCH12.  
  eapply wd_mu. eapply SIM23. eapply MATCH23.

  (* ge init inj *)
  intros. rewrite HeqR13 in H.
  assert (exists mu12 mu23, ge_init_inj mu12 ge1 ge2 /\ ge_init_inj mu23 ge2 ge3 /\ mu_compose mu12 mu23 mu)
    as [mu12 [mu23 [GEINJ12 [GEINJ23 MUCOMP]]]].
  { destruct i, Hc, Lc, b.
    destruct H as (mu12 & mu23 & ? & ? & ? & MATCH12 & MATCH23 & MUCOMP).
    exists mu12, mu23. split; [|split; auto]; eapply match_mu_ge; eauto.
    destruct H as (mu12 & mu23 & ? & ? & MATCH12 & MATCH23 & MUCOMP & _).
    exists mu12, mu23. split; [|split; auto]; eapply match_mu_ge; eauto. }
  constructor.
  erewrite <-mu_Shared1_equiv; eauto. eapply mu_shared_src; eauto.
  erewrite <-mu_Shared3_equiv; eauto. eapply mu_shared_tgt; eauto.
  eapply mu_compose_bset_inject; eauto; inv MUCOMP; eauto.
  intro. eapply senv_injected in GEINJ12. eapply senv_injected in GEINJ23.
  instantiate (1:=id) in GEINJ12. instantiate (1:=id) in GEINJ23.
  unfold Senv.find_symbol in *. simpl in *.
  inv GEINJ23; inv GEINJ12; try constructor; try congruence.
  erewrite mu_inj_comp; eauto. rewrite H6. rewrite <- H0 in H5. inv H5. auto.
  
  (* ge match *)
  simpl in *. eapply match_genv in SIM12. eapply match_genv in SIM23.
  revert SIM12 SIM23; clear. intros. inv SIM12. inv SIM23.
  constructor.
  intro. rewrite genv_public_eq. auto.
  intro. rewrite genv_symb_eq. auto.
  intros. assert ((Genv.genv_symb ge2) ! id = Some b'). rewrite genv_symb_eq0. auto.
  specialize (genv_defs_match id b b' H H1).
  specialize (genv_defs_match0 id b' b' H1 H0).
  inv genv_defs_match; inv genv_defs_match0; try congruence; constructor.
  inv H4; inv H7; try congruence. constructor. constructor. rewrite <- H3 in H5. inv H5.
  inv H8; inv H4. simpl. constructor.
  congruence.
  
  (* init trans *)
  intros mu13 id args1 args3 c1 GEREL13 INJID13 GARG1 ARGREL13 INITCORE1.
  exploit (init_mem_interpolant _ _ ge1 ge3).
  eauto. eauto. eauto. eapply match_genv; eauto. eapply match_genv; eauto.
  intros (mu12 & mu23 & MUCOMP & INJID12 & INJID23 & SHAREDEQ23 & GEREL12 & GEREL23 & INITMEM).
  exploit arg_rel_interpolant; eauto. intros (args2 & GARG2 & ARGREL12 & ARGREL23).
  exploit (@match_init L1 L2); try exact SIM12; eauto. 
  erewrite mu_Shared1_equiv; eauto. intros (c2 & INITCORE2 & MATCH12).
  exploit (@match_init L2 L3); try exact SIM23; eauto. intros (c3 & INITCORE3 & MATCH23).
  exists c3. split; [auto|].
  intros m1 m3 INITMEM1 INITMEM3 MEMINIT13.
  exploit INITMEM; eauto. intros [MEMINIT12 MEMINIT23].
  exploit INITMEMCOMPAT2. eauto. intro INITMEM2.
  specialize (MATCH12 _ _ INITMEM1 INITMEM2 MEMINIT12).
  specialize (MATCH23 _ _ INITMEM2 INITMEM3 MEMINIT23).
  intros m1' m3' RELY13.
  exploit (HLRely_local_interpolant mu12 mu23 m1 m1' m3 m3 m3'); eauto.
  econstructor; eauto.
  intros. eapply dom_eq_tgt; eauto.
  erewrite mu_Shared3_equiv, <- SHAREDEQ23. auto. eauto.
  intros (m2' & RELY12 & RELY23).
  destruct (MATCH12 _ _ RELY12) as (i12 & MATCH12').
  destruct (MATCH23 _ _ RELY23) as (i23 & MATCH23').
  exists (i12, i23). subst R13. exists mu12, mu23, FP.emp, c2, m2'. auto.
  
  (* tau step *)
  intros [i12 i23] mu13 fp1 fp3 c1 m1 c3 m3 fp1' c1' m1' MATCH13 STEP1.
  subst R13. destruct MATCH13 as (mu12 & mu23 & fp2 & c2 & m2 & MATCH12 & MATCH23 & MUCOMP).
  exploit (@match_tau_step L1 L2); try exact SIM12; eauto.
  intros [(i12' & ORDER12 & MATCH12') | (i12' & fp2' & c2' & m2' & PLUS2 & FPMATCH12 & MATCH12')].
  (*   0 , 0 *)
  left. exists (i12', i23). split. subst order13. constructor. auto.
  exists mu12, mu23, fp2, c2, m2. auto.
  (*   + , (0\/+) *)
  exploit (match_tau_step_plus L2 L3); eauto. intros.
  eapply (@match_tau_step L2 L3); eauto.
  intros [(i23' & ORDER23 & MATCH23')|(i23' & fp3' & c3' & m3' & PLUS3 & FPMATCH23 & MATCH23')].
  (*   + , 0 *)
  left. exists (i12', i23'). split. subst order13. econstructor; eauto.
  exists mu12, mu23, (FP.union fp2 fp2'), c2', m2'. split; auto.
  (*   + , + *)
  right. exists (i12', i23'), fp3', c3', m3'. split; auto. split.
  eapply mu_compose_FPMatch'_trans; eauto.
  exists mu12, mu23, (FP.union fp2 fp2'), c2', m2'. split; auto.
  
  (* at ext *)
  intros [i12 i23] mu13 fp1 fp3 c1 m1 c3 m3 f sg arg1 MATCH13 ATEXT1 RC1 GARG1.
  subst R13. destruct MATCH13 as (mu12 & mu23 & fp2 & c2 & m2 & MATCH12 & MATCH23 & MUCOMP).
  pose proof (mu_Shared1_equiv _ _ _ MUCOMP); eauto.
  exploit (@match_at_external L1 L2); eauto.
  eapply bset_eq_reach_closed_local; eauto. intro; rewrite H; tauto.
  eapply bset_eq_G_args; eauto. intro; rewrite H; tauto.
  intros (i12' & arg2 & ATEXT2 & ARGREL12 & RC2 & FPMATCH12 & INV12 & MATCH12').
  pose proof (mu_Shared2_equiv _ _ _ MUCOMP); eauto.  
  exploit (@match_at_external L2 L3); eauto.
  eapply bset_eq_reach_closed_local; eauto.
  rewrite H0; tauto.
  rewrite <- H0.
  eapply arg_rel_G_args; eauto. inv MUCOMP. rewrite <- mu_Shared1_equiv0. auto.
  intros (i23' & arg3 & ATEXT3 & ARGREL23 & RC3 & FPMATCH23 & INV23 & MATCH23').
  exists (i12', i23'), arg3. split; auto.
  split. eapply mu_compose_arg_rel_trans; eauto.
  split. pose proof (mu_Shared3_equiv _ _ _ MUCOMP).
  eapply bset_eq_reach_closed_local; eauto. rewrite H1; tauto.
  split. eapply mu_compose_FPMatch'_trans; eauto.
  split. eapply mu_compose_Inv_trans; eauto.
  exists mu12, mu23, c2, m2. repeat (split; auto).
  intros. eapply Bset.inj_range in H1. destruct H1 as [b0 INJ12].
  eapply Mem.mi_mappedblocks; eauto. unfold Bset.inj_to_meminj. rewrite INJ12. eauto.
  eapply Bset.inj_weak, mu_inject_12; eauto.

  (* aft ext *)
  intros [i12 i23] mu13 c1 m1 c3 m3 ores1 c1' ores3 MATCH13 GRES1 AFTEXT1 RESREL13.
  subst R13. destruct MATCH13 as (mu12 & mu23 & c2 & m2 & MATCH12 & MATCH23 & MUCOMP & SHARED2).
  exploit mu_compose_ores_rel_strict_interpolant; eauto. intros (ores2 & RESREL12 & RESREL23).
  exploit (@match_after_external L1 L2). exact SIM12. eauto.
  instantiate (1:= ores1). unfold G_oarg in *. destruct ores1; auto.
  erewrite mu_Shared1_equiv; eauto. eauto. eauto.
  intros (c2' & AFTEXT2 & RELY12).
  exploit (@match_after_external L2 L3). exact SIM23. eauto.
  instantiate (1:= ores2). unfold ores_rel in RESREL12.
  destruct ores1; destruct ores2; try contradiction; auto. simpl.
  erewrite <- mu_Shared2_equiv; eauto. inv RESREL12; auto; try contradiction. simpl.
  inv MUCOMP. eapply Bset.inj_range'; eauto using Bset.inj_weak. instantiate (1:= b1).
  unfold Bset.inj_to_meminj in H. destruct (inj mu12 b1); inv H; auto.
  eauto. eauto.
  intros (c3' & AFTEXT3 & RELY23).
  exists c3'. split. auto.
  intros m1' m3' RELY13. exploit HLRely_local_interpolant; eauto.
  (** TODO: find out the preconditions of RELY interpolant 
      seems to be finite (Shared* mu) and mu_compose and inv12 & inv23
   *)
  econstructor; eauto.
  intros (m2' & RELY12' & RELY23').
  apply RELY12 in RELY12'. apply RELY23 in RELY23'.
  destruct RELY12' as (i12' & MATCH12'). destruct RELY23' as (i23' & MATCH23').
  exists (i12', i23'), mu12, mu23, FP.emp, c2', m2'. auto.


  (* halt *)
  intros [i12 i23] mu13 fp1 fp3 c1 m1 c3 m3 res1 MATCH13 HALT1 RC1 GARG1.
  subst R13. destruct MATCH13 as (mu12 & mu23 & fp2 & c2 & m2 & MATCH13 & MATCH23 & MUCOMP).
  pose proof (mu_Shared1_equiv _ _ _ MUCOMP).
  pose proof (mu_Shared2_equiv _ _ _ MUCOMP).
  pose proof (mu_Shared3_equiv _ _ _ MUCOMP).
  exploit (@match_halt L1 L2); eauto.
  eapply bset_eq_reach_closed_local; eauto. generalize H; clear; intros. rewrite H; tauto.
  eapply bset_eq_G_arg; eauto. generalize H; clear; intros. rewrite H; tauto.
  intros (res2 & HALT2 & RESREL12 & RC2 & FPMATCH12 & INV12).
  exploit (@match_halt L2 L3); eauto.
  eapply bset_eq_reach_closed_local; eauto. rewrite H0. tauto.
  erewrite <- mu_Shared2_equiv; eauto. inv RESREL12; auto; try contradiction. simpl.
  inv MUCOMP. eapply Bset.inj_range'; eauto using Bset.inj_weak. instantiate (1:= b1).
  unfold Bset.inj_to_meminj in H2. destruct (inj mu12 b1); inv H2; auto.
  intros (res3 & HALT3 & RELREL23 & RC3 & FPMATCH23 & INV23).
  exists res3. split. auto. 
  split. eapply mu_compose_res_rel_strict_trans; eauto.
  split. eapply bset_eq_reach_closed_local; eauto. rewrite H1. tauto.
  split. eapply mu_compose_FPMatch'_trans; eauto.
  eapply mu_compose_Inv_trans; eauto.
Qed.
  

Theorem ldsim_local_transitive:
  forall cu1 cu2 cu3
    (INIT_REL12:
       forall G1 ge1,
         init_genv_local L1 cu1 ge1 G1 ->
         exists G2 ge2, init_genv_local L2 cu2 ge2 G2 /\ Genv.genv_next ge2 = Genv.genv_next ge1)
    (INITRC3:
       forall G3 ge3 m3, init_genv_local L3 cu3 ge3 G3 -> init_mem L3 ge3 m3 ->
                    reach_closed m3 (fun b => Plt b (Genv.genv_next ge3)))
    (INITMEMCOMPAT32:
       forall G2 ge2 G3 ge3 m3,
         init_genv_local L2 cu2 ge2 G2 ->
         init_genv_local L3 cu3 ge3 G3 ->
         Genv.genv_next ge2 = Genv.genv_next ge3 ->
         init_mem L3 ge3 m3 ->
         init_mem L2 ge2 m3),
    @ldsim_local L1 L2 cu1 cu2 ->
    @ldsim_local L2 L3 cu2 cu3 ->
    @ldsim_local L1 L3 cu1 cu3.
Proof.
  intros cu1 cu2 cu3 ? ? ? SIM12 SIM23.
  intros G1 ge1 G3 ge3 GENV1 GENV3 GENVDOMEQ.
  assert (exists G2 ge2, init_genv_local L2 cu2 ge2 G2 /\ Genv.genv_next ge2 = Genv.genv_next ge1)
    as (G2 & ge2 & GENV2 & GENVDOMEQ') by eauto.
  specialize (SIM12 _ _ _ _ GENV1 GENV2). rewrite GENVDOMEQ' in SIM12. specialize (SIM12 eq_refl).
  specialize (SIM23 _ _ _ _ GENV2 GENV3). rewrite GENVDOMEQ' in SIM23. specialize (SIM23 GENVDOMEQ).
  eapply local_ldsim_transitive; eauto.
  intro. eapply INITMEMCOMPAT32; eauto. congruence.
Qed.

End TRANSITIVITY.



