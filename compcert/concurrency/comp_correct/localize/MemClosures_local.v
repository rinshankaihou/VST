(* This file is adapted from [reach.v] of Compositional CompCert.
   Modifications explained in comments. *)

Require Import Coqlib Maps Integers Values Memdata.
Require Import Blockset Memory Injections InjRels.

Import Mem.


(** * Memory Closures *)

(** This file defines closures on memory *)

Local Notation "a # b" := (PMap.get b a) (at level 1).

Inductive reach' (m: mem) (B: Bset.t) : list (block * ptrofs) -> block -> Prop :=
| reach_nil: forall b, Bset.belongsto B b -> reach' m B nil b
| reach_cons: forall b L b' z ofs q n,
    reach' m B L b' ->
    perm m b' z Cur Readable ->
    ZMap.get z (mem_contents m)!!b' = Fragment (Vptr b ofs) q n->
    reach' m B ((b',ofs)::L) b.

Inductive reachable : mem -> Bset.t -> block -> Prop :=
  Reachable : forall m bs b L,
    reach' m bs L b -> reachable m bs b.

(** MODIFICATION:
    strengthen [reach_closed], requiring memory contains no Vundef / Undef values within block set of interest *)
Record reach_closed (m: mem) (B: Bset.t) : Prop :=
  {
    reachable_closure: forall b, reachable m B b -> Bset.belongsto B b;
    no_undef: forall b z,
        Bset.belongsto B b ->
        perm m b z Cur Readable ->
        (~ ZMap.get z (mem_contents m) !! b = Undef);
    no_vundef: forall b z q n,
        Bset.belongsto B b ->
        perm m b z Cur Readable ->
        (~ ZMap.get z (mem_contents m) !! b = Fragment Vundef q n);
  }.

Lemma reach_closed_belongsto:
  forall m B b,
    reach_closed m B ->
    reachable m B b ->
    Bset.belongsto B b.
Proof.
  intros. inv H. inv H0. apply reachable_closure0.
  econstructor; eauto.
Qed.

Lemma bset_eq_reach'_local:
  forall bs1 bs2,
    (forall b, bs1 b <-> bs2 b) ->
    forall m L b, reach' m bs1 L b <-> reach' m bs2 L b.
Proof.
  intros bs1 bs2 EQ m.
  induction L.
  - split; intro H; inversion H;
      constructor; unfold Bset.belongsto in *;
        apply EQ; auto.
  - split; intros H; inversion H; subst; simpl in *.
    econstructor; eauto. apply IHL. auto.
    econstructor; eauto. apply IHL. auto.
Qed.

Lemma bset_eq_reachable_local:
  forall bs1 bs2 m,
    (forall b, bs1 b <-> bs2 b) ->
    (forall b, reachable m bs1 b <-> reachable m bs2 b).
Proof.
  clear. intros.
  split; intros.
  - inversion H0. subst.
    rewrite bset_eq_reach'_local in H1; eauto.
    econstructor; eauto.
  - inversion H0. subst.
    rewrite bset_eq_reach'_local in H1; eauto.
    econstructor; eauto. firstorder.
Qed.


Lemma bset_eq_reach_closed_local:
  forall bs1 bs2 m,
    (forall b, bs1 b <-> bs2 b) ->
    reach_closed m bs1 <-> reach_closed m bs2.
Proof.
  clear. intros.
  split; intros.
  - inversion H0. constructor.
    intros. erewrite bset_eq_reachable_local in H1; eauto.
    eapply H. eapply reachable_closure0. eauto. split; intro; apply H; auto.
    intros. rewrite <- H in H1. eauto.
    intros. rewrite <- H in H1. eauto.
  - inversion H0. 
    constructor.
    intros. erewrite bset_eq_reachable_local in H1; eauto. rewrite H. apply reachable_closure0. auto.
    intros. rewrite H in H1. eauto.
    intros. rewrite H in H1. eauto.
Qed.

(** TODO: move to LDSimDefs_local? *)
(* invariants to Guarantee *)
Lemma sep_inject_rc_inject:
  forall mu j m m',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (inj mu)) j ->
    sep_inject (Bset.inj_to_meminj (inj mu)) j ->
    inject j m m' ->
    reach_closed m (SharedSrc mu) ->
    inject (Bset.inj_to_meminj (inj mu)) m m'.
Proof.
  intros mu j m m' INJECT INCR SEPINJ MEMINJ RC.
  constructor.
  * constructor.
    ** intros. eapply mi_perm. inv MEMINJ; eauto. eapply INCR; eauto. auto.
    ** intros. eapply mi_align. inv MEMINJ; eauto. eapply INCR; eauto. eauto.
    ** intros. exploit mi_memval. inv MEMINJ; eauto. eapply INCR; eauto. eauto.
       intro MEMVALINJ. inv MEMVALINJ; try constructor.
       inv H3; try constructor.
       simpl. econstructor; eauto.
       exploit reachable_closure; eauto. econstructor. instantiate (2:=(b1,ofs1)::nil).
       econstructor. constructor. eapply Bset.inj_dom'.
       inv INJECT; eauto. unfold Bset.inj_to_meminj in H. destruct (inj mu b1); inv H; eauto.
       eauto.
       eauto.
       intro. exploit Bset.inj_dom; eauto. intros [b' INJ].
       unfold Bset.inj_to_meminj in *. destruct (inj mu b0) eqn:?; inv INJ.
       exploit INCR. rewrite Heqo; eauto. intro. rewrite H4 in H5; inv H5; auto.
  * intros. unfold Bset.inj_to_meminj; destruct (inj mu b) eqn:INJ; auto.
    exfalso. eapply mi_freeblocks in H; eauto.
    exploit INCR. unfold Bset.inj_to_meminj; rewrite INJ; eauto. congruence.
  * inv MEMINJ. eauto. 
  * inv MEMINJ. unfold meminj_no_overlap in *; intros; eauto.
  * inv MEMINJ. eauto.
  * inv MEMINJ. eauto.
Qed.

(* Rely to invatiants *)
Lemma sep_inject_rely_inject:
  forall mu j m1 m1' m2 m2',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (inj mu)) j ->
    sep_inject (Bset.inj_to_meminj (inj mu)) j ->
    inject j m1 m1' ->
    unchanged_on (fun b _ => ~ SharedSrc mu b) m1 m2 ->
    reach_closed m2 (SharedSrc mu) ->
    unchanged_on (fun b _ => ~ SharedTgt mu b) m1' m2' ->
    reach_closed m2' (SharedTgt mu) ->
    inject (Bset.inj_to_meminj (inj mu)) m2 m2' ->
    inject j m2 m2'.
Proof.
  intros mu j m1 m1' m2 m2' INJECT INCR SEPINJ MEMINJ UNCHG RC UNCHG' RC' MEMINJ'.
  constructor.
  * constructor.
    ** intros. destruct (inj mu b1) eqn:INJ.
       (* Shared *)
       exploit INCR. unfold Bset.inj_to_meminj. rewrite INJ. eauto. intro. rewrite H in H1; inv H1.
       eapply mi_perm. inv MEMINJ'; eauto. unfold Bset.inj_to_meminj. rewrite INJ. auto. auto.
       (* Local *)
       erewrite <- unchanged_on_perm in H0 |- *; eauto. eapply mi_perm; eauto. inv MEMINJ; auto.
       simpl. intro. eapply Bset.inj_dom in H1; eauto. destruct H1. congruence.
       unfold valid_block. destruct (plt b1 (nextblock m1)); auto. eapply mi_freeblocks in n; eauto. congruence.
       simpl. intro. eapply Bset.inj_range in H1; [|inv INJECT; eauto]. destruct H1.
       eapply SEPINJ in H. unfold Bset.inj_to_meminj in H. rewrite INJ in H; discriminate.
       unfold Bset.inj_to_meminj. rewrite H1; eauto.
       eapply mi_mappedblocks; eauto.
    ** intros. destruct (inj mu b1) eqn:INJ.
       (* Shared *)
       exploit INCR. unfold Bset.inj_to_meminj. rewrite INJ. eauto. intro. rewrite H in H1; inv H1.
       eapply mi_align. inv MEMINJ'; eauto. unfold Bset.inj_to_meminj. rewrite INJ. auto. eauto.
       (* Local *)
       eapply mi_align. inv MEMINJ; eauto. eauto. instantiate (1:= p). instantiate (1:= ofs).
       intros z RANGE. erewrite unchanged_on_perm; eauto.
       simpl. intro. eapply Bset.inj_dom in H1; eauto. destruct H1. congruence.
       unfold valid_block. destruct (plt b1 (nextblock m1)); auto. eapply mi_freeblocks in n; eauto. congruence.
    ** intros. destruct (inj mu b1) eqn:INJ.
       (* Shared *)
       exploit INCR. unfold Bset.inj_to_meminj. rewrite INJ. eauto. intro. rewrite H in H1; inv H1.
       exploit mi_memval. inv MEMINJ'; eauto. unfold Bset.inj_to_meminj. rewrite INJ. eauto. eauto. intro MEMVALINJ.
       inv MEMVALINJ; try constructor.
       eapply val_inject_incr; eauto.
       (* Local *)
       exploit mi_memval. inv MEMINJ; eauto. eauto. rewrite unchanged_on_perm; eauto.
       simpl. intro C. eapply Bset.inj_dom in C; eauto. destruct C. congruence.
       unfold valid_block. destruct (plt b1 (nextblock m1)); auto. eapply mi_freeblocks in n; eauto. congruence.
       assert (~ SharedTgt mu b2).
       { intro C. eapply Bset.inj_range in C; [|inv INJECT; eauto]. destruct C.
         eapply SEPINJ in H. unfold Bset.inj_to_meminj in H. rewrite INJ in H. congruence. 
         unfold Bset.inj_to_meminj. rewrite H1. eauto. }
       assert (~ SharedSrc mu b1).
       { intro C. eapply Bset.inj_dom in C; eauto. destruct C; congruence. }
       erewrite <- unchanged_on_perm in H0; eauto.
       intro. erewrite (unchanged_on_contents _ m1 m2), (unchanged_on_contents _ m1' m2'); eauto.
       eapply mi_perm. inv MEMINJ; eauto. eauto. auto.
       unfold valid_block. destruct (plt b1 (nextblock m1)); auto. eapply mi_freeblocks in n; eauto. congruence.
  * intros. unfold valid_block in H. destruct (plt b (nextblock m1)); [|eapply mi_freeblocks; eauto].
    eapply (Plt_Ple_trans _ _ (nextblock m2)) in p;
      [contradiction|eapply (unchanged_on_nextblock _ m1 m2); eauto].
  * intros. eapply Plt_Ple_trans with (nextblock m1'). eapply mi_mappedblocks; eauto.
    eapply unchanged_on_nextblock; eauto.
  * inv MEMINJ. unfold meminj_no_overlap in *.
    intros.
    destruct (inj mu b1) eqn:INJ1; destruct (inj mu b2) eqn:INJ2;
      repeat match goal with
             | H: j ?b = Some _, H': inj mu ?b = Some _ |- _ =>
               exploit INCR; try (unfold Bset.inj_to_meminj; rewrite H'; eauto);
                 intro TMP; rewrite H in TMP; inv TMP; clear H
             | H: inj mu ?b = None |- _ =>
               assert (~ SharedSrc mu b) by (intro C; eapply Bset.inj_dom in C; eauto; destruct C; congruence);
                 clear H
             end.
    left. intro. subst. exploit Bset.inj_injective. inv INJECT; eauto. exact INJ1. exact INJ2. auto.
    left. intro. subst. exploit SEPINJ; eauto; unfold Bset.inj_to_meminj. rewrite INJ1; eauto.
    destruct (inj mu b2) eqn:INJ2';[|discriminate]. intro C; inv C. 
    exploit Bset.inj_injective. inv INJECT; eauto. exact INJ1. exact INJ2'. auto.
    left. intro. subst. exploit SEPINJ; eauto; unfold Bset.inj_to_meminj. rewrite INJ2; eauto.
    destruct (inj mu b1) eqn:INJ1';[|discriminate]. intro C; inv C. 
    exploit Bset.inj_injective. inv INJECT; eauto. exact INJ2. exact INJ1'. auto.
    assert (valid_block m1 b1).
    { destruct (plt b1 (nextblock m1)); auto. eapply mi_freeblocks0 in n. congruence. }
    assert (valid_block m1 b2).
    { destruct (plt b2 (nextblock m1)); auto. eapply mi_freeblocks0 in n. congruence. }
    assert (perm m1 b1 ofs1 Max Nonempty) by (erewrite unchanged_on_perm; eauto).
    assert (perm m1 b2 ofs2 Max Nonempty) by (erewrite unchanged_on_perm; eauto). 
    eapply mi_no_overlap0; eauto.
  * intros. destruct (inj mu b) eqn:INJ.
    (* Shared *)
    exploit INCR. unfold Bset.inj_to_meminj; rewrite INJ; eauto. intro. rewrite H in H1; inv H1.
    exploit mi_representable; eauto. unfold Bset.inj_to_meminj. rewrite INJ; eauto.
    (* Local *)
    assert (~ SharedSrc mu b).
    { intro C. eapply Bset.inj_dom in C; [|eauto]. destruct C. congruence. }
    assert (valid_block m1 b).
    { unfold valid_block. destruct (plt b (nextblock m1)); auto. eapply mi_freeblocks in n; eauto. congruence. }
    do 2 erewrite <- (unchanged_on_perm _ m1 m2) in H0; eauto.
    exploit mi_representable; try exact MEMINJ; eauto.
  * intros. destruct (inj mu b1) eqn:INJ.
    (* Shared *)
    exploit INCR. unfold Bset.inj_to_meminj; rewrite INJ; eauto. intro. rewrite H in H1; inv H1.
    exploit mi_perm_inv; eauto. unfold Bset.inj_to_meminj. rewrite INJ; eauto.
    (* Local *)
    assert (~ SharedSrc mu b1).
    { intro C. eapply Bset.inj_dom in C; [|eauto]. destruct C. congruence. }
    assert (valid_block m1 b1).
    { unfold valid_block. destruct (plt b1 (nextblock m1)); auto. eapply mi_freeblocks in n; eauto. congruence. }
    erewrite <- (unchanged_on_perm _ m1 m2); eauto.
    erewrite <- (unchanged_on_perm _ m1 m2); eauto.
    exploit mi_perm_inv; try exact MEMINJ; eauto.
    erewrite unchanged_on_perm; eauto.
    intro C. eapply Bset.inj_range in C; [|inv INJECT; eauto]. destruct C.
    eapply SEPINJ in H. unfold Bset.inj_to_meminj in H. rewrite INJ in H. congruence. 
    unfold Bset.inj_to_meminj. rewrite H3. eauto.
    unfold valid_block. eapply mi_mappedblocks; eauto.
Qed.
    
    
Lemma unchanged_on_reach_closed:
  forall m B m',
    reach_closed m B ->
    Mem.unchanged_on (fun b _ => B b) m m' ->
    (forall b, Bset.belongsto B b -> Mem.valid_block m b) ->
    reach_closed m' B.
Proof.
  intros. 
  constructor; intros. 
  * destruct H as [CLOSED _ _]. apply CLOSED. inv H2. apply Reachable with L. revert L b H. induction L.
    intros. constructor; inv H; auto.
    intros. inv H. destruct H0 as [NEXT PERM CONTENT].
    rewrite <- PERM in H5;[|apply CLOSED; auto|].
    rewrite CONTENT in H7; auto.
    econstructor; eauto.
    apply CLOSED. econstructor. eauto.
    econstructor; eauto.
    apply H1. apply CLOSED. econstructor; eauto.
  * erewrite <- unchanged_on_perm in H3; eauto.
    erewrite unchanged_on_contents; eauto. inv H; eauto.
  * erewrite <- unchanged_on_perm in H3; eauto.
    erewrite unchanged_on_contents; eauto. inv H; eauto.
Qed.

Lemma unchanged_on_reach_closed_inverse:
  forall m B m',
    reach_closed m' B ->
    Mem.unchanged_on (fun b _ => B b) m m' ->
    (forall b, Bset.belongsto B b -> Mem.valid_block m b) ->
    reach_closed m B.
Proof.
  intros. 
  constructor; intros. 
  * destruct H as [CLOSED _ _]. apply CLOSED. inv H2. apply Reachable with L. revert L b H. induction L.
    intros. constructor; inv H; auto.
    intros. inv H. destruct H0 as [NEXT PERM CONTENT].
    pose proof H5 as READABLE.
    rewrite PERM in H5;[|apply CLOSED; auto|].
    rewrite <- CONTENT in H7; auto.
    econstructor; eauto.
    apply CLOSED. econstructor. eauto.
    econstructor; eauto.
    apply H1. apply CLOSED. econstructor; eauto.
  * pose proof H3 as READABLE. erewrite unchanged_on_perm in H3; eauto.
    erewrite <- unchanged_on_contents; eauto. inv H; eauto.
  * pose proof H3 as READABLE. erewrite unchanged_on_perm in H3; eauto.
    erewrite <- unchanged_on_contents; eauto. inv H; eauto.
Qed.

(** An invariant for RC preservation *)
Record unmapped_closed (mu: Mu) (m m': mem) : Prop :=
  {
    unmapped_closure:
      forall b' z b0 ofs0 q n,
        Bset.belongsto (SharedTgt mu) b' ->
        (* unmapped *)
        (forall b, (inj mu) b = Some b' -> ~ perm m b z Cur Readable) ->
        perm m' b' z Cur Readable ->
        ZMap.get z (mem_contents m') !! b' = Fragment (Vptr b0 ofs0) q n ->
        Bset.belongsto (SharedTgt mu) b0;
    unmapped_no_undef:
      forall b' z,
        Bset.belongsto (SharedTgt mu) b' ->
        (* unmapped *)
        (forall b, (inj mu) b = Some b' -> ~ perm m b z Cur Readable) ->
        perm m' b' z Cur Readable ->
        ZMap.get z (mem_contents m') !! b' <> Undef;
    unmapped_no_vundef:
      forall b' z q n,
        Bset.belongsto (SharedTgt mu) b' ->
        (* unmapped *)
        (forall b, (inj mu) b = Some b' -> ~ perm m b z Cur Readable) ->
        perm m' b' z Cur Readable ->
        ZMap.get z (mem_contents m') !! b' <> Fragment Vundef q n;
  }.

Lemma reach_closed_unmapped_closed:
  forall mu m m',
    reach_closed m' (SharedTgt mu) ->
    unmapped_closed mu m m'.
Proof.
  intros. constructor; inv H; auto.
  intros. eapply reachable_closure0. econstructor. instantiate(1:=(b', ofs0)::nil). econstructor; eauto. constructor; auto.
Qed.

Lemma inject_shared_src_valid:
  forall mu j m m',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (inj mu)) j ->
    inject j m m' ->
    (forall b, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m b).
Proof.
  intros. exploit Bset.inj_dom; eauto. intros [b' INJ].
  exploit H0. unfold Bset.inj_to_meminj; rewrite INJ; eauto. intro INJ'.
  destruct (plt b (nextblock m)); auto.
  eapply mi_freeblocks in n; eauto. congruence.
Qed.
  
Lemma inject_shared_tgt_valid:
  forall mu j m m',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (inj mu)) j ->
    inject j m m' ->
    (forall b, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m' b).
Proof.
  intros. exploit Bset.inj_range; eauto. inv H; eauto. intros [b0 INJ].
  exploit H0. unfold Bset.inj_to_meminj; rewrite INJ; eauto. intro INJ'.
  eapply mi_mappedblocks; eauto.
Qed.


Lemma unmapped_closed_reach_closed_preserved_by_extends:
  forall mu m m',
    inject_incr (Bset.inj_to_meminj (inj mu)) inject_id ->
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    (forall b, Bset.belongsto (SharedSrc mu) b -> valid_block m b) ->
    (forall b, Bset.belongsto (SharedTgt mu) b -> valid_block m' b) ->    
    extends m m' ->
    unmapped_closed mu m m' ->
    reach_closed m (SharedSrc mu) ->
    reach_closed m' (SharedTgt mu).
Proof.
  intros.
  assert (EQS: forall b, SharedSrc mu b <-> SharedTgt mu b).
  { intro. inv H0. split; intro SHARED.
    eapply inj_dom in SHARED. destruct SHARED as [b' A]. exploit H. unfold Bset.inj_to_meminj; rewrite A; eauto.
    intro. inv H0. eapply Bset.inj_range'; eauto.
    eapply Bset.inj_range in SHARED; eauto. destruct SHARED as [b' A]. exploit H. unfold Bset.inj_to_meminj; rewrite A; eauto.
    intro. inv H0. eapply Bset.inj_dom'; eauto. }
  constructor.
  * intros. inv H6. revert L b H7. induction L; intros.
    inv H7. auto.
    inv H7. apply IHL in H9. clear IHL.
    exploit Bset.inj_range; eauto. inv H0; eauto. intros (b'0 & INJ).
    destruct (perm_dec m b'0 z Cur Readable).
    (* mapped *)
    ** exploit mi_memval. inv H3; eauto. eapply H. unfold Bset.inj_to_meminj; rewrite INJ. eauto. eauto.
    rewrite Z.add_0_r, H12. intro INJVAL; inv INJVAL. inv H8. inv H14.
    exploit H. unfold Bset.inj_to_meminj. rewrite INJ. eauto. intro A; inv A.
    eapply EQS. eapply reachable_closure; eauto.
    apply Reachable with ((b', ofs1)::nil).
    econstructor; eauto with mem. constructor. apply EQS. auto.
    exfalso. eapply no_vundef; eauto with mem. eapply Bset.inj_dom'; eauto. inv H0; eauto.
    exfalso. eapply no_undef; eauto with mem. eapply Bset.inj_dom'; eauto. inv H0; eauto.
    (* unmapped *)
    ** eapply unmapped_closure; eauto.
    intros. exploit Bset.inj_injective. inv H0; eauto. exact INJ. exact H6. intro EQ; subst; eauto.
  * intros. 
    exploit Bset.inj_range; eauto. inv H0; eauto. intros (b0 & INJ).
    destruct (perm_dec m b0 z Cur Readable).
    exploit mi_memval. inv H3; eauto. eapply H. unfold Bset.inj_to_meminj; rewrite INJ. eauto. eauto.
    rewrite Z.add_0_r. intro INJVAL; inv INJVAL; try discriminate. 
    exfalso. eapply no_undef; eauto. eapply Bset.inj_dom'; eauto. inv H0; eauto.
    eapply unmapped_no_undef; eauto.
    intros. exploit Bset.inj_injective. inv H0; eauto. exact INJ. exact H8. intro EQ; subst; auto.
  * intros. 
    exploit Bset.inj_range; eauto. inv H0; eauto. intros (b0 & INJ).
    destruct (perm_dec m b0 z Cur Readable).
    exploit mi_memval. inv H3; eauto. eapply H. unfold Bset.inj_to_meminj; rewrite INJ. eauto. eauto.
    rewrite Z.add_0_r. intro INJVAL; inv INJVAL; try discriminate. 
    inv H10; try discriminate. exfalso. eapply no_vundef; eauto. eapply Bset.inj_dom'; eauto. inv H0; eauto.
    exfalso. eapply no_undef; eauto. eapply Bset.inj_dom'; eauto. inv H0; eauto.
    eapply unmapped_no_vundef; eauto.
    intros. exploit Bset.inj_injective. inv H0; eauto. exact INJ. exact H8. intro EQ; subst; auto.
Qed.


Lemma unmapped_closed_reach_closed_preserved_by_injection:
  forall mu m m',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    (forall b, Bset.belongsto (SharedSrc mu) b -> valid_block m b) ->
    (forall b, Bset.belongsto (SharedTgt mu) b -> valid_block m' b) ->    
    inject (Bset.inj_to_meminj (inj mu)) m m' ->
    unmapped_closed mu m m' ->
    reach_closed m (SharedSrc mu) ->
    reach_closed m' (SharedTgt mu).
Proof.
  intros. constructor.
  * intros. inv H5. revert L b H6. induction L; intros.
    inv H6; auto.
    inv H6. apply IHL in H8. clear IHL.
    exploit Bset.inj_range; eauto. inv H; eauto. intros (b'0 & INJ).
    destruct (perm_dec m b'0 z Cur Readable).
    exploit mi_memval. inv H2; eauto. unfold Bset.inj_to_meminj; rewrite INJ. eauto. eauto.
    rewrite Z.add_0_r, H11. intro INJVAL; inv INJVAL. inv H7.
    unfold Bset.inj_to_meminj in H13. destruct (inj mu b1) eqn:INJ'; [|discriminate]. inv H13.
    eapply Bset.inj_range'; eauto. inv H; eauto.
    exfalso. eapply no_vundef; eauto. eapply Bset.inj_dom'; eauto. inv H; eauto.
    exfalso. eapply no_undef; eauto. eapply Bset.inj_dom'; eauto. inv H; eauto.
    eapply unmapped_closure; eauto.
    intros. exploit Bset.inj_injective. inv H; eauto. exact INJ. exact H5. intro EQ; subst; auto.
  * intros. 
    exploit Bset.inj_range; eauto. inv H; eauto. intros (b0 & INJ).
    destruct (perm_dec m b0 z Cur Readable).
    exploit mi_memval. inv H2; eauto. unfold Bset.inj_to_meminj; rewrite INJ. eauto. eauto.
    rewrite Z.add_0_r. intro INJVAL; inv INJVAL; try discriminate. 
    exfalso. eapply no_undef; eauto. eapply Bset.inj_dom'; eauto. inv H; eauto.
    eapply unmapped_no_undef; eauto.
    intros. exploit Bset.inj_injective. inv H; eauto. exact INJ. exact H7. intro EQ; subst; auto.
  * intros. 
    exploit Bset.inj_range; eauto. inv H; eauto. intros (b0 & INJ).
    destruct (perm_dec m b0 z Cur Readable).
    exploit mi_memval. inv H2; eauto. unfold Bset.inj_to_meminj; rewrite INJ. eauto. eauto.
    rewrite Z.add_0_r. intro INJVAL; inv INJVAL; try discriminate. 
    inv H9; try discriminate. exfalso. eapply no_vundef; eauto. eapply Bset.inj_dom'; eauto. inv H; eauto.
    exfalso. eapply no_undef; eauto. eapply Bset.inj_dom'; eauto. inv H; eauto.
    eapply unmapped_no_vundef; eauto.
    intros. exploit Bset.inj_injective. inv H; eauto. exact INJ. exact H7. intro EQ; subst; auto.
Qed.

Lemma unmapped_closed_reach_closed_preserved_by_injection':
  forall mu m m',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    inject (Bset.inj_to_meminj (inj mu)) m m' ->
    unmapped_closed mu m m' ->
    reach_closed m (SharedSrc mu) ->
    reach_closed m' (SharedTgt mu).
Proof.
  intros; eapply unmapped_closed_reach_closed_preserved_by_injection; eauto.
  eapply inject_shared_src_valid; eauto.
  eapply inject_shared_tgt_valid; eauto.
Qed.

Lemma unmapped_closed_reach_closed_preserved_by_injection'':
  forall mu j m m',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (inj mu)) j ->
    sep_inject (Bset.inj_to_meminj (inj mu)) j ->
    inject j m m' ->
    unmapped_closed mu m m' ->
    reach_closed m (SharedSrc mu) ->
    reach_closed m' (SharedTgt mu).
Proof.
  intros; eapply unmapped_closed_reach_closed_preserved_by_injection'; eauto.
  eapply sep_inject_rc_inject; eauto.
Qed.

Lemma unchanged_on_unmapped_closed_preserved:
  forall mu m1 m1' m2 m2',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    (forall b, Bset.belongsto (SharedSrc mu) b -> valid_block m1 b) ->
    (forall b, Bset.belongsto (SharedTgt mu) b -> valid_block m1' b) ->    
    unmapped_closed mu m1 m1' ->
    unchanged_on (fun b _ => SharedSrc mu b) m1 m2 ->
    unchanged_on (fun b _ => SharedTgt mu b) m1' m2' ->
    unmapped_closed mu m2 m2'.
Proof.
  intros. constructor; intros.
  * eapply unmapped_closure; eauto. intros. intro. eapply H6; eauto.
    erewrite unchanged_on_perm in H10; eauto.
    eapply Bset.inj_dom'; eauto. inv H; eauto.
    eapply H0. eapply Bset.inj_dom'; eauto. inv H; eauto.
    erewrite unchanged_on_perm; eauto.
    erewrite <- unchanged_on_contents; eauto. erewrite unchanged_on_perm; eauto.
  * erewrite unchanged_on_contents; eauto.
    eapply unmapped_no_undef; eauto. intros. intro. eapply H6; eauto.
    erewrite unchanged_on_perm in H9; eauto.
    eapply Bset.inj_dom'; eauto. inv H; eauto.
    eapply H0. eapply Bset.inj_dom'; eauto. inv H; eauto.
    erewrite unchanged_on_perm; eauto.
    erewrite unchanged_on_perm; eauto.    
  * erewrite unchanged_on_contents; eauto.
    eapply unmapped_no_vundef; eauto. intros. intro. eapply H6; eauto.
    erewrite unchanged_on_perm in H9; eauto.
    eapply Bset.inj_dom'; eauto. inv H; eauto.
    eapply H0. eapply Bset.inj_dom'; eauto. inv H; eauto.
    erewrite unchanged_on_perm; eauto.
    erewrite unchanged_on_perm; eauto.
Qed.
  
Lemma unchanged_on_reach_closed_preserved:
  forall mu m1 m1' m2 m2',
    (forall b, Bset.belongsto (SharedSrc mu) b -> valid_block m1 b) ->
    (forall b, Bset.belongsto (SharedTgt mu) b -> valid_block m1' b) ->    
    (reach_closed m1 (SharedSrc mu) -> reach_closed m1' (SharedTgt mu)) ->
    unchanged_on (fun b _ => SharedSrc mu b) m1 m2 ->
    unchanged_on (fun b _ => SharedTgt mu b) m1' m2' ->
    (reach_closed m2 (SharedSrc mu) -> reach_closed m2' (SharedTgt mu)).
Proof.
  intros. eapply unchanged_on_reach_closed; eauto.
  apply H1. eapply unchanged_on_reach_closed_inverse; eauto.
Qed.

Lemma store_val_inject_unmapped_closed_preserved:
  forall mu m1 m1' chunk j b ofs v m2 b' delta v' m2',
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    (forall b, Bset.belongsto (SharedSrc mu) b -> valid_block m1 b) ->
    (forall b, Bset.belongsto (SharedTgt mu) b -> valid_block m1' b) ->
    inject_incr (Bset.inj_to_meminj (inj mu)) j ->
    sep_inject (Bset.inj_to_meminj (inj mu)) j ->
    unmapped_closed mu m1 m1' ->
(*    inject (Bset.inj_to_meminj (inj mu)) m1 m1' -> *)
    store chunk m1 b ofs v = Some m2 ->
    j b = Some (b', delta) ->
    store chunk m1' b' (ofs + delta) v' = Some m2' ->
    unmapped_closed mu m2 m2'.
Proof.
  intros mu m1 m1' chunk j b ofs v m2 b' delta v' m2'
         INJECT SHAREDVALID SHAREDVALID' INCR SEPINJ RCINV STORE INJPTR STORE'.
  assert (MAPPED: forall z, ofs <= z < ofs + size_chunk chunk -> perm m2 b z Cur Readable).
  { intros. eapply perm_store_1; eauto. exploit store_valid_access_3; try exact STORE. 
    unfold valid_access. intros [RANGEPERM _]. apply perm_implies with Writable; auto using Mem.perm_cur_max. constructor. }
  constructor. 
  * intros. erewrite store_mem_contents in H2; eauto.
    destruct (eq_block b' b'0).
    subst. rewrite PMap.gss in H2. 
    destruct (zlt z (ofs + delta)). rewrite setN_outside in H2; auto.
    eapply unmapped_closure; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
    destruct (zlt z (ofs + delta + size_chunk chunk)).
    exploit Bset.inj_range; try exact H. inv INJECT; eauto. intros [b1 INJ1].
    exploit SEPINJ. unfold Bset.inj_to_meminj. rewrite INJ1. eauto. eauto. unfold Bset.inj_to_meminj; intro C.
    destruct (inj mu b) eqn:INJ2; inv C. exploit Bset.inj_injective. inv INJECT; eauto. exact INJ1. exact INJ2. intro; subst.
    exfalso. eapply H0; eauto. apply MAPPED. split; Lia.lia.
    rewrite setN_outside in H2; [|rewrite encode_val_length, <- size_chunk_conv; auto].
    eapply unmapped_closure; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
    rewrite PMap.gso in H2; auto.
    eapply unmapped_closure; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
  * intros. erewrite store_mem_contents; eauto.
    destruct (eq_block b' b'0).
    subst. rewrite PMap.gss.
    destruct (zlt z (ofs + delta)). rewrite setN_outside; auto.
    eapply unmapped_no_undef; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
    destruct (zlt z (ofs + delta + size_chunk chunk)).
    exploit Bset.inj_range; try exact H. inv INJECT; eauto. intros [b1 INJ1].
    exploit SEPINJ. unfold Bset.inj_to_meminj. rewrite INJ1. eauto. eauto. unfold Bset.inj_to_meminj; intro C.
    destruct (inj mu b) eqn:INJ2; inv C. exploit Bset.inj_injective. inv INJECT; eauto. exact INJ1. exact INJ2. intro; subst.
    exfalso. eapply H0; eauto. apply MAPPED. split; Lia.lia.
    rewrite setN_outside; [|rewrite encode_val_length, <- size_chunk_conv; auto].
    eapply unmapped_no_undef; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
    rewrite PMap.gso; auto.
    eapply unmapped_no_undef; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
  * intros. erewrite store_mem_contents; eauto.
    destruct (eq_block b' b'0).
    subst. rewrite PMap.gss.
    destruct (zlt z (ofs + delta)). rewrite setN_outside; auto.
    eapply unmapped_no_vundef; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
    destruct (zlt z (ofs + delta + size_chunk chunk)).
    exploit Bset.inj_range; try exact H. inv INJECT; eauto. intros [b1 INJ1].
    exploit SEPINJ. unfold Bset.inj_to_meminj. rewrite INJ1. eauto. eauto. unfold Bset.inj_to_meminj; intro C.
    destruct (inj mu b) eqn:INJ2; inv C. exploit Bset.inj_injective. inv INJECT; eauto. exact INJ1. exact INJ2. intro; subst.
    exfalso. eapply H0; eauto. apply MAPPED. split; Lia.lia.
    rewrite setN_outside; [|rewrite encode_val_length, <- size_chunk_conv; auto].
    eapply unmapped_no_vundef; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
    rewrite PMap.gso; auto.
    eapply unmapped_no_vundef; eauto. intros. intro; eapply H0; eauto. eapply perm_store_1; eauto. eapply perm_store_2; eauto.
Qed.

Lemma free_inject_unmapped_closed_preserved:
  forall mu m1 m1' j b lo hi m2 b' delta lo' hi' m2',
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    (forall b0 : block, Bset.belongsto (Injections.SharedSrc mu) b0 -> Mem.valid_block m1 b0) ->
    (forall b0 : block, Bset.belongsto (Injections.SharedTgt mu) b0 -> Mem.valid_block m1' b0) ->
    inject_incr (Bset.inj_to_meminj (Injections.inj mu)) j ->
    sep_inject (Bset.inj_to_meminj (Injections.inj mu)) j ->
    unmapped_closed mu m1 m1' ->
    Mem.free m1 b lo hi = Some m2 ->
    j b = Some (b', delta) ->
    lo' <= (lo + delta) ->
    (hi + delta) <= hi' ->
    Mem.free m1' b' lo' hi' = Some m2' ->
    unmapped_closed mu m2 m2'.
Proof.
  intros mu m1 m1' j b lo hi m2 b' delta lo' hi' m2'
         INJECT SHAREDVALID SHAREDVALID' INCR SEPINJ RCINV FREE INJPTR HLO HHI FREE'.
  exploit free_unchanged_on. eauto.
  instantiate (1:= fun b z => ~ (b = b' /\ lo' <= z < hi')); simpl. intros. intro. apply H0. split; auto.
  intro UNCHG'.
  (** unmapped are less *)
  assert (forall b' z,
             Bset.belongsto (SharedTgt mu) b' ->
             (forall b, inj mu b = Some b' -> ~ perm m2 b z Cur Readable) ->
             perm m2' b' z Cur Readable ->
             (forall b, inj mu b = Some b' -> ~ perm m1 b z Cur Readable)).
  { intros. intro. eapply H0. eauto.
    exploit perm_free_3; eauto. intro.
    eapply perm_free_1; eauto.
    destruct (eq_block b0 b); auto. subst. right.
    destruct (zlt z lo); auto. destruct (zle hi z); [Lia.lia|]. exfalso.
    exploit INCR. unfold Bset.inj_to_meminj. rewrite H2. eauto. intro A. rewrite INJPTR in A; inv A.
    eapply perm_free_2; eauto.  Lia.lia. }
  constructor. 
  * intros. exploit perm_free_3; eauto. intro. 
    erewrite unchanged_on_contents in H3.
    eapply unmapped_closure; try eassumption.
    eapply H; eauto. eauto. 
    simpl. intro. destruct H5. subst. eapply perm_free_2; eauto. auto. 
  * intros. exploit perm_free_3; eauto. intro.
    erewrite unchanged_on_contents; eauto.
    eapply unmapped_no_undef; eauto.
    simpl. intro. destruct H4. subst. eapply perm_free_2; eauto.
  * intros. exploit perm_free_3; eauto. intro.
    erewrite unchanged_on_contents; eauto.
    eapply unmapped_no_vundef; eauto.
    simpl. intro. destruct H4. subst. eapply perm_free_2; eauto.
Qed.

