Require Import Globalenvs.
Require Import Blockset Footprint.

(** * The triple [Mu] for recording shared memory locations *)
(** 
- [inj] : the injection function relating source and target shared blocks 
- [SharedSrc] : shared memory blocks of source program state 
- [SharedTgt] : shared memory blocks of target program state 
  *)

Record Mu: Type :=
  {
    inj: Bset.inj;
    SharedSrc: Bset.t;
    SharedTgt: Bset.t;
  }.

(** Consistency relation between locations.
    It is basically a subset relation modulo [Mu] *)
Inductive LocMatch (mu: Mu) (lsSrc lsTgt: Locs.t) : Prop :=
| Loc_Match :
    (forall b ofs,
        Bset.belongsto (SharedTgt mu) b ->
        Locs.belongsto lsTgt b ofs ->
        (exists bSrc,
            Bset.inject_block (inj mu) bSrc b /\
            Locs.belongsto lsSrc bSrc ofs))
    ->
    LocMatch mu lsSrc lsTgt.

(** Target footprint matches with source, 
    each component of target footprint [fpTgt] subsets of 
    the corresponding component of source footprint [fpSrc] *)
Record FPMatch (mu: Mu) (fpSrc fpTgt: FP.t) : Prop :=
  {
    cmp_match: LocMatch mu (FP.cmps fpSrc) (FP.cmps fpTgt);
    read_match: LocMatch mu (FP.reads fpSrc) (FP.reads fpTgt);
    write_match: LocMatch mu (FP.writes fpSrc) (FP.writes fpTgt);
    free_match: LocMatch mu (FP.frees fpSrc) (FP.frees fpTgt);
  }.

(** A generalized definition that is weaker, 
    such that it is possible to degrade a shared memory write to read *)
Record FPMatch' (mu: Mu) (fpSrc fpTgt: FP.t) : Prop :=
  {
    cmp_match': LocMatch mu (FP.ge_cmps fpSrc) (FP.cmps fpTgt);
    read_match': LocMatch mu (FP.ge_reads fpSrc) (FP.reads fpTgt);
    write_match': LocMatch mu (FP.ge_writes fpSrc) (FP.writes fpTgt);
    free_match': LocMatch mu (FP.ge_frees fpSrc) (FP.frees fpTgt);
  }.

Lemma eq_locs_match:
  forall mu ls1 ls2 ls1' ls2',
    Locs.eq ls1 ls1' ->
    Locs.eq ls2 ls2' ->
    LocMatch mu ls1 ls2 ->
    LocMatch mu ls1' ls2'.
Proof.
  intros.
  inversion H1.
  constructor. intros.
  rewrite Locs.belongsto_eq in H, H0.
  specialize (H2 b ofs H3).
  erewrite <- H0 in H4. clear H0.
  specialize (H2 H4). 
  destruct H2 as (b'&Hinj&Hbelong).
  exists b'. split; auto.
  rewrite <- H; auto.
Qed.

Lemma locs_match_union:
  forall mu sls sls' tls tls',
    LocMatch mu sls tls ->
    LocMatch mu sls' tls' ->
    LocMatch mu (Locs.union sls sls') (Locs.union tls tls').
Proof.
  intros.
  inversion H; inversion H0.
  constructor; intros.
  unfold Locs.belongsto, Locs.union in *.
  apply Bool.orb_true_elim in H4; destruct H4.
  apply (H1 _ _ H3) in e. destruct e as (b'&H'&H'').
  exists b'. split; auto. rewrite H''; auto.
  apply (H2 _ _ H3) in e. destruct e as (b'&H'&H'').
  exists b'. split; auto. rewrite H''. apply Bool.orb_true_r.
Qed.

Lemma locs_match_union_S:
  forall mu sls tls sls',
    LocMatch mu sls tls ->
    LocMatch mu (Locs.union sls sls') tls.
Proof.
  intros.
  inversion H. constructor; intros.
  destruct (H0 b ofs H1 H2) as (b'&Hinj&Hbelong).
  exists b'. split; auto.
  unfold Locs.belongsto, Locs.union in *. rewrite Hbelong; auto.
Qed.

Lemma locs_match_union_T:
  forall mu sls tls tls',
    LocMatch mu sls tls ->
    LocMatch mu sls tls' ->
    LocMatch mu sls (Locs.union tls tls').
Proof.
  intros.
  inversion H; inversion H0. constructor; intros.
  unfold Locs.belongsto, Locs.union in *.
  apply Bool.orb_true_elim in H4; destruct H4.
  apply (H1 _ _ H3) in e. destruct e as (b'&H'&H''). exists b'. split; auto.
  apply (H2 _ _ H3) in e. destruct e as (b'&H'&H''). exists b'. split; auto.
Qed.

Lemma locs_match_subset_S:
  forall mu sls tls sls',
    LocMatch mu sls tls ->
    Locs.subset sls sls' ->
    LocMatch mu sls' tls.
Proof.
  intros.
  inversion H. constructor; intros.
  apply (H1 _ _ H2) in H3. destruct H3 as (b'&H'&H''). exists b'. split; auto.
Qed.

Lemma locs_match_subset_T:
  forall mu sls tls tls',
    LocMatch mu sls tls ->
    Locs.subset tls' tls ->
    LocMatch mu sls tls'.
Proof.
  intros. inversion H. constructor; intros.
  apply H1; auto.
Qed.

Lemma eq_fp_match:
  forall mu fp1 fp2 fp1' fp2',
    FP.eq fp1 fp1' ->
    FP.eq fp2 fp2' ->
    FPMatch mu fp1 fp2 ->
    FPMatch mu fp1' fp2'.
Proof.
  intros.
  inversion H; inversion H0; inversion H1.
  constructor; try (eapply eq_locs_match; eauto).
Qed.

Lemma eq_fp_match':
  forall mu fp1 fp2 fp1' fp2',
    FP.eq fp1 fp1' ->
    FP.eq fp2 fp2' ->
    FPMatch' mu fp1 fp2 ->
    FPMatch' mu fp1' fp2'.
Proof.
  intros. inversion H0; inversion H1. constructor.
  eapply eq_locs_match; try (eapply FP.eq_fp_eq_ge_cmps; eauto); eauto.
  eapply eq_locs_match; try (eapply FP.eq_fp_eq_ge_reads; eauto); eauto.
  eapply eq_locs_match; try (eapply FP.eq_fp_eq_ge_writes; eauto); eauto.
  eapply eq_locs_match; try (eapply FP.eq_fp_eq_ge_frees; eauto); eauto.
Qed.
  
Lemma fp_match_union:
  forall mu sfp sfp' tfp tfp',
    FPMatch mu sfp tfp ->
    FPMatch mu sfp' tfp' ->
    FPMatch mu (FP.union sfp sfp') (FP.union tfp tfp').
Proof.
  intros.
  inversion H; inversion H0.
  unfold FP.union in *.
  constructor; intros; simpl in *; apply locs_match_union; auto.
Qed.

Lemma fp_match_union':
  forall mu sfp sfp' tfp tfp',
    FPMatch' mu sfp tfp ->
    FPMatch' mu sfp' tfp' ->
    FPMatch' mu (FP.union sfp sfp') (FP.union tfp tfp').
Proof.
  intros. inversion H; inversion H0.
  constructor; intros; simpl in *.
  rewrite FP.union_ge_cmps_comm; apply locs_match_union; auto.
  rewrite FP.union_ge_reads_comm; apply locs_match_union; auto.
  rewrite FP.union_ge_writes_comm; apply locs_match_union; auto.
  apply locs_match_union; auto.
Qed.

Lemma fp_match_union_S:
  forall mu sfp tfp sfp',
    FPMatch mu sfp tfp ->
    FPMatch mu (FP.union sfp sfp') tfp.
Proof.
  intros. inversion H. unfold FP.union.
  constructor; intros; simpl in *; apply locs_match_union_S; auto.
Qed.

Lemma fp_match_union_S':
  forall mu sfp tfp sfp',
    FPMatch' mu sfp tfp ->
    FPMatch' mu (FP.union sfp sfp') tfp.
Proof.
  intros. inversion H. constructor; intros; simpl in *.
  rewrite FP.union_ge_cmps_comm; apply locs_match_union_S; auto.
  rewrite FP.union_ge_reads_comm; apply locs_match_union_S; auto.
  rewrite FP.union_ge_writes_comm; apply locs_match_union_S; auto.
  apply locs_match_union_S; auto.
Qed.

Lemma fp_match_union_T:
  forall mu sfp tfp tfp',
    FPMatch mu sfp tfp ->
    FPMatch mu sfp tfp' ->
    FPMatch mu sfp (FP.union tfp tfp').
Proof.
  intros. inversion H; inversion H0. unfold FP.union.
  constructor; intros; simpl in *; apply locs_match_union_T; auto.
Qed.

Lemma fp_match_union_T':
  forall mu sfp tfp tfp',
    FPMatch' mu sfp tfp ->
    FPMatch' mu sfp tfp' ->
    FPMatch' mu sfp (FP.union tfp tfp').
Proof.
  intros. inversion H; inversion H0.
  constructor; intros; simpl in *; apply locs_match_union_T; auto.
Qed.

Lemma fp_match_subset_S:
  forall mu sfp tfp sfp',
    FPMatch mu sfp tfp ->
    FP.subset sfp sfp' ->
    FPMatch mu sfp' tfp.
Proof.
  intros.
  inversion H; inversion H0.
  constructor; intros; eapply locs_match_subset_S; eauto.
Qed.

Lemma fp_match_subset_S':
  forall mu sfp tfp sfp',
    FPMatch' mu sfp tfp ->
    FP.subset sfp sfp' ->
    FPMatch' mu sfp' tfp.
Proof.
  intros. inversion H; inversion H0.
  constructor; intros; simpl in *; eapply locs_match_subset_S; eauto.
  eapply FP.subset_ge_cmps_subset; eauto.
  eapply FP.subset_ge_reads_subset; eauto.
  eapply FP.subset_ge_writes_subset; eauto.
Qed.

Lemma fp_match_subset_T:
  forall mu sfp tfp tfp',
    FPMatch mu sfp tfp ->
    FP.subset tfp' tfp ->
    FPMatch mu sfp tfp'.
Proof.
  intros.
  inversion H; inversion H0.
  constructor; intros; eapply locs_match_subset_T; eauto.
Qed.

Lemma fp_match_subset_T':
  forall mu sfp tfp tfp',
    FPMatch' mu sfp tfp ->
    FP.subset tfp' tfp ->
    FPMatch' mu sfp tfp'.
Proof.
  intros.
  inversion H; inversion H0.
  constructor; intros; eapply locs_match_subset_T; eauto.
Qed.

Lemma fp_match_emp':
  forall mu fp,
    FPMatch' mu fp FP.emp.
Proof.
  clear; intros. constructor; constructor; intros b ofs _ C; inversion C.
Qed.

Lemma fp_match_local_block:
  forall mu fp' fp, 
    (forall b, Bset.belongsto (FP.blocks fp') b -> ~ SharedTgt mu b) ->
    FPMatch' mu fp fp'.
Proof.
  clear. intros.
  constructor;
    constructor; intros; exfalso; eapply H; eauto;
      unfold FP.blocks, FP.locs, Bset.belongsto, Locs.blocks; Locs.unfolds; eexists; red_boolean_true.
Qed.



