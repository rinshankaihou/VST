Require Import Coqlib.
Require Import Maps Errors Values Globalenvs.
Require Import Blockset Memory Footprint
        IS_local Injections MemClosures_local.

Require Import LDSimDefs.

Module LDefs.
  (** For local LDSim, we need to define counter part for:
      - [HfpG], [LfpG]: FPMatch
      - [HG], [LG]: reach_closed, rc & FPMatch & Inv
      - [HLRely]: [Inv] & 
   *)

Definition Inv mu sm tm : Prop := Mem.inject (Bset.inj_to_meminj (inj mu)) sm tm.

(** LG mu fpSrc sm fpTgt tm *)
(** [FPMatch mu fpSrc fpTgt] /\ 
    [reach_closed tm (SharedTgt mu)] /\
    [Inv mu sm tm] *)

Definition unchg_local (B:Bset.t) (m m' : mem) : Prop :=
  Mem.unchanged_on (fun (b: block) (_ : Z) => ~ Bset.belongsto B b) m m'.

Inductive Rely Shared m m' : Prop :=
  RELY: forall (EQNEXT: Mem.nextblock m' = Mem.nextblock m),
    unchg_local Shared m m' ->
    reach_closed m' Shared ->
    Rely Shared m m'.

Lemma Rely_trans:
  forall Shared m1 m2 m3,
    Rely Shared m1 m2 ->
    Rely Shared m2 m3 ->
    Rely Shared m1 m3.
Proof.
  intros.
  inversion H; inversion H0.
  constructor; auto. congruence.
  unfold unchg_local in *.
  eapply Mem.unchanged_on_trans; eauto.
Qed.
    
Inductive HLRely mu sm sm' tm tm' : Prop :=
  HLR: Rely (SharedSrc mu) sm sm' ->
       Rely (SharedTgt mu) tm tm' ->
       Inv mu sm' tm' ->
       HLRely mu sm sm' tm tm'.

Lemma HLRely_trans:
  forall mu sm1 sm2 sm3 tm1 tm2 tm3,
    HLRely mu sm1 sm2 tm1 tm2 ->
    HLRely mu sm2 sm3 tm2 tm3 ->    
    HLRely mu sm1 sm3 tm1 tm3.
Proof.
  intros.
  inversion H; inversion H0.
  constructor; auto.
  eapply Rely_trans; eauto.
  eapply Rely_trans; eauto.
Qed.

End LDefs.

Lemma bset_eq_Rely_local:
  forall bs m m' bs',
    LDefs.Rely bs m m' ->
    (forall b, bs b <-> bs' b) ->
    LDefs.Rely bs' m m'.
Proof.
  intros.
  inv H. constructor. auto.
  inv H1. constructor; eauto. intros. rewrite <- H0 in H. eauto. intros. rewrite <- H0 in H. eauto.
  rewrite bset_eq_reach_closed_local; eauto. intro. rewrite H0. tauto.
Qed.



(** LEMMAS about Mem.extends *)
Lemma inject_implies_extends:
  forall j m m'
    (DOMTOTAL: forall b, Mem.valid_block m b -> exists b' ofs', j b = Some (b', ofs')),
    Mem.inject j m m' ->
    inject_incr j inject_id ->
    Mem.nextblock m = Mem.nextblock m' ->
    Mem.extends m m'.
Proof.
  clear. intros. inv H.
  constructor; auto.
  { generalize DOMTOTAL mi_inj H0; clear; intros. inv mi_inj.
    constructor; intros.
    { exploit Mem.perm_valid_block; eauto. intro.
      apply DOMTOTAL in H2. destruct H2 as (? & ? & A). inv H. 
      eapply mi_perm; eauto. rewrite A. apply H0 in A. inv A; auto. }
    { inv H. apply Z.divide_0_r. }
    { apply memval_inject_incr with j; auto.
      eapply mi_memval; eauto. inv H. 
      exploit Mem.perm_valid_block. eapply H1. intro.
      apply DOMTOTAL in H. destruct H as (? & ? & A).
      rewrite A. apply H0 in A; inv A; auto. }
  }
  intros. rewrite (Zplus_0_r_reverse ofs) in H. eapply mi_perm_inv; eauto.
  exploit Mem.perm_valid_block; eauto. intro. unfold Mem.valid_block in H2; rewrite <- H1 in H2.
  apply DOMTOTAL in H2. destruct H2 as (? & ? & A). rewrite A.
  apply H0 in A; inv A; auto.
Qed.

Lemma extends_rely_extends:
  forall mu m1 m1' m2 m2',
    Mem.extends m1 m1' ->
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (Injections.inj mu)) inject_id ->
    LDefs.HLRely mu m1 m2 m1' m2' ->
    Mem.extends m2 m2'.
Proof.
  clear. intros.
  inv H2. inv H3. inv H4.
  assert (Mem.nextblock m2 = Mem.nextblock m1) by auto.
  assert (Mem.nextblock m2' = Mem.nextblock m1') by auto.
  inv H. constructor.
  congruence. 
  { clear mext_perm_inv; inv mext_inj.
    eapply Mem.mi_inj in H5. inv H5.
    constructor; intros.
    { inv H. destruct (Injections.inj mu b2) eqn:DOM.
      eapply mi_perm0; eauto.
      unfold Bset.inj_to_meminj. rewrite DOM. f_equal. f_equal.
      exploit H1. unfold Bset.inj_to_meminj. rewrite DOM. eauto. intros. inv H; auto.

      erewrite <- Mem.unchanged_on_perm; eauto.
      eapply mi_perm; eauto. reflexivity.
      erewrite Mem.unchanged_on_perm; eauto.
      simpl. intro. eapply Bset.inj_dom in H; eauto. destruct H; congruence.
      unfold Mem.valid_block. rewrite <- H4. eapply Mem.perm_valid_block; eauto.
      simpl. intro. eapply Bset.inj_range in H; [|inv H0;eauto]. destruct H.
      exploit H1. unfold Bset.inj_to_meminj. rewrite H. eauto. intro. inv H9. congruence.
      unfold Mem.valid_block. rewrite <-mext_next, <- H4. eapply Mem.perm_valid_block; eauto. }
    { inv H. apply Z.divide_0_r. }
    { destruct (Bset.inj_to_meminj (Injections.inj mu) b1) as [[b1' ofs']|] eqn:DOM .
      eapply memval_inject_incr; eauto. eapply mi_memval0.
      rewrite DOM. apply H1 in DOM. inv DOM. inv H. auto. auto.
      assert (~ Injections.SharedTgt mu b2).
      { intro. eapply Bset.inj_range in H9; [|inv H0;eauto]. destruct H9.
        inv H. exploit H1. unfold Bset.inj_to_meminj. rewrite H9; eauto. intro. inv H.
        unfold Bset.inj_to_meminj in DOM. rewrite H9 in DOM. discriminate. }
      assert (~ Injections.SharedSrc mu b1).
      { intro. eapply Bset.inj_dom in H10; eauto. destruct H10.
        unfold Bset.inj_to_meminj in DOM; rewrite H10 in DOM. discriminate. }
      inv H. 
      erewrite Mem.unchanged_on_contents; eauto.
      erewrite (Mem.unchanged_on_contents _ m1' m2'); eauto.
      eapply mi_memval. reflexivity.
      rewrite Mem.unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite <- H4. eapply Mem.perm_valid_block; eauto.
      eapply mi_perm. reflexivity. erewrite  Mem.unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite <- H4. eapply Mem.perm_valid_block; eauto.
      erewrite  Mem.unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite <- H4. eapply Mem.perm_valid_block; eauto. }
  }
  { intros. exploit Mem.perm_valid_block; eauto. unfold Mem.valid_block; intro.
    destruct (Bset.inj_to_meminj (Injections.inj mu) b) as [[b' ofs']|] eqn:DOM.
    inv H5. eapply mi_perm_inv; eauto. apply H1 in DOM. inv DOM. rewrite Z.add_0_r; auto.
    assert (~ Injections.SharedTgt mu b).
    { intro. eapply Bset.inj_range in H10; [|inv H0;eauto]. destruct H10.
      exploit H1. unfold Bset.inj_to_meminj. rewrite H10; eauto. intro. inv H11.
      unfold Bset.inj_to_meminj in DOM. rewrite H10 in DOM. discriminate. }
    assert (~ Injections.SharedSrc mu b).
    { intro. eapply Bset.inj_dom in H11; eauto. destruct H11.
      unfold Bset.inj_to_meminj in DOM; rewrite H11 in DOM. discriminate. }
    assert (Mem.valid_block m1 b).
    { apply Mem.perm_valid_block in H. unfold Mem.valid_block in *. congruence. }
    repeat erewrite <- (Mem.unchanged_on_perm _ m1 m2); eauto.
    eapply mext_perm_inv. erewrite Mem.unchanged_on_perm; eauto.
    unfold Mem.valid_block in *; congruence.
  }
Qed.

Lemma extends_reach_closed_implies_inject:
  forall mu m m'
    (VALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
    (VALID': forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b),
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (Injections.inj mu)) inject_id ->
    reach_closed m (Injections.SharedSrc mu) ->
    Mem.extends m m' ->
    Mem.inject (Bset.inj_to_meminj (Injections.inj mu)) m m'.
Proof.
  clear. intros mu m m' VALID VALID' BINJ INCR RC EXT.
  constructor.
  { apply Mem.mext_inj in EXT; inv EXT. constructor; intros.
    apply INCR in H. eauto. apply INCR in H. eauto. 
    pose proof H. apply INCR in H. eauto. eapply mi_memval in H; eauto.
    inv H; try constructor. inv H4; try constructor. inv H.
    destruct (Injections.inj mu b1) eqn:INJ; unfold Bset.inj_to_meminj in H1; rewrite INJ in H1; inv H1.
    econstructor; eauto.
    inv RC. exploit (reachable_closure b3).
    econstructor. instantiate (1:= (b1, ofs1)::nil). econstructor; eauto. constructor; auto.
    eapply Bset.inj_dom'; eauto. inv BINJ; eauto. intro.
    eapply Bset.inj_dom in H; eauto. destruct H.
    exploit INCR. unfold Bset.inj_to_meminj. rewrite H; eauto. 
    intro. unfold Bset.inj_to_meminj. inv H1. rewrite H. eauto. }
  { intros. destruct (Injections.inj mu b) eqn:INJ.
    exfalso. eapply Bset.inj_dom' in INJ; eauto. inv BINJ; eauto.
    unfold Bset.inj_to_meminj. rewrite INJ; auto. }
  { intros. apply VALID'. unfold Bset.inj_to_meminj in H. destruct (Injections.inj mu b) eqn:INJ; inv H.
    eapply Bset.inj_range'; eauto. inv BINJ; eauto. }
  { unfold Mem.meminj_no_overlap. intros. apply INCR in H0. apply INCR in H1. inv H0; inv H1. auto. }
  { intros. apply INCR in H; inv H. split. Lia.lia.
    pose proof (Integers.Ptrofs.unsigned_range ofs). unfold Integers.Ptrofs.max_unsigned. Lia.lia. }
  { inv EXT. intros. apply INCR in H. inv H. rewrite Z.add_0_r in H0. eauto. }
Qed.

Lemma locs_match_id:
  forall mu ls,
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (Injections.inj mu)) inject_id ->
    Injections.LocMatch mu ls ls.
Proof.
  clear. intros. constructor; intros.
  exists b. split; auto. eapply Bset.inj_range in H1; [|inv H;eauto].
  destruct H1. exploit H0. unfold Bset.inj_to_meminj. rewrite H1. eauto.
  intro. inv H3. auto.
Qed.

Lemma fp_match_id:
  forall mu fp,
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (Injections.inj mu)) inject_id ->
    Injections.FPMatch' mu fp fp.
Proof.
  clear. intros. destruct fp.
  constructor; unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes;
    repeat apply Injections.locs_match_union_S; simpl; apply locs_match_id; auto.
Qed.