Require Import Coqlib Maps Errors Values Globalenvs.
Require Import List Streams.
Require Import Blockset GMemory Footprint MemAux
        InteractionSemantics Injections MemClosures.



(** * Footprint Matching and Rely/Guarantee Conditions in Local Simulations *)

(** This file defines the footprint matching relations and 
    rely/guarantee conditions used in module local simulations. 
    (Draft Fig. 11) *)

(** [fpG]: footprint subset of shared memory blocks union local freelist *)
Definition fpG (fl: freelist) (Shared: Bset.t) (fp: FP.t) : Prop :=
  (forall b, Bset.belongsto (FP.blocks fp) b ->
             Bset.belongsto Shared b \/
             exists n, Str_nth n fl = b).

(** [LfpG]: target footprint [fpG] and footprints matched by [FPMatch] *)
Inductive LfpG' (fl: freelist) (mu: Mu) (fpSrc fpTgt: FP.t) : Prop :=
  LFPG':  FPMatch' mu fpSrc fpTgt ->
         fpG fl (SharedTgt mu) fpTgt ->
         LfpG' fl mu fpSrc fpTgt.

(** [HfpG]: source footprint [fpG] *)
Inductive HfpG (fl: freelist) (mu: Mu) (fpSrc : FP.t) : Prop :=
  HFPG: fpG fl (SharedSrc mu) fpSrc -> HfpG fl mu fpSrc.

(** The guarantee condition : footprint subset of shared memory blocks and resulting memory is reach-closed *)
Inductive Guarantee (fl: freelist) (Shared: Bset.t) (fp: FP.t) (gm': gmem) : Prop :=
  GUARANTEE: fpG fl Shared fp ->
             reach_closed gm' Shared ->
             Guarantee fl Shared fp gm'.

(** The Inv in paper Fig. 8 is instantiated as memory injection of CompCert *)
Definition Inv mu sgm tgm : Prop := GMem.inject (Bset.inj_to_meminj (inj mu)) sgm tgm.

(** HG in paper Fig. 8, source memory action satisfies [Guarantee] *) 
Inductive HG fl mu fpSrc sgm' : Prop :=
  HGuarantee: Guarantee fl (SharedSrc mu) fpSrc sgm' -> HG fl mu fpSrc sgm'.

(** LG in paper Fig. 8, target memory action satisfies [Guarantee],
    and footprint are matched by [mu],
    and resulting memory states are related by [Inv]. *)
Inductive LG' fl mu fpSrc sgm' fpTgt tgm' : Prop :=
  LGuarantee': Guarantee fl (SharedTgt mu) fpTgt tgm' ->
              FPMatch' mu fpSrc fpTgt ->
              Inv mu sgm' tgm' ->
              LG' fl mu fpSrc sgm' fpTgt tgm'.

(** constraints on argument: 
    arguments of external calls cannot be [Vundef] or 
    pointers of memory location outside of shared memory *)
Definition G_arg (S: Bset.t) (arg: val) : Prop :=
  match arg with
  | Vundef => False
  | Vptr b _ => Bset.belongsto S b
  | _ => True
  end.

Definition G_oarg (S: Bset.t) (oarg: option val) : Prop :=
  match oarg with
  | Some arg => G_arg S arg
  | Noen => True
  end.

Definition G_args (S: Bset.t) (args: list val) : Prop:=
  Forall (G_arg S) args.

(** source and target arguments and return values 
    should be related by value-injection of CompCert *)
Definition arg_rel (phi: Bset.inj) : list val -> list val -> Prop :=
  Val.inject_list (Bset.inj_to_meminj phi).

Definition res_rel (phi: Bset.inj) : val -> val -> Prop :=
  Val.inject (Bset.inj_to_meminj phi).

Definition ores_rel (phi: Bset.inj) : option val -> option val -> Prop :=
  fun or1 or2 =>
    match or1, or2 with
    | Some res1, Some res2 => res_rel phi res1 res2
    | None, None => True
    | _, _ => False
    end.

(** The R condition in paper Fig. 8 *)
(** The enviconment step should make sure:
    - memory domain is enlarged
    - module local freelist is not changed
    - the resulting memory state is still reach-closed *)
Inductive Rely fl Shared gm gm' : Prop :=
  RELY: GMem.forward gm gm' ->
        unchg_freelist fl gm gm' ->
        reach_closed gm' Shared ->
        Rely fl Shared gm gm'.

(** The Rely condition in paper Fig. 8 *)
(** The [HLRely] requires source and target environment steps
    satisfying [Rely] condition, and the resulting memory states satisfies [Inv] *)
Inductive HLRely flSrc flTgt mu sgm sgm' tgm tgm' : Prop :=
  HLR: Rely flSrc (SharedSrc mu) sgm sgm' ->
       Rely flTgt (SharedTgt mu) tgm tgm' ->
       Inv mu sgm' tgm' ->
       HLRely flSrc flTgt mu sgm sgm' tgm tgm'.




(** obsoleted definitions *)
Inductive LfpG (fl: freelist) (mu: Mu) (fpSrc fpTgt: FP.t) : Prop :=
  LFPG:  FPMatch mu fpSrc fpTgt ->
         fpG fl (SharedTgt mu) fpTgt ->
         LfpG fl mu fpSrc fpTgt.

Inductive LG fl mu fpSrc sgm' fpTgt tgm' : Prop :=
  LGuarantee: Guarantee fl (SharedTgt mu) fpTgt tgm' ->
              FPMatch mu fpSrc fpTgt ->
              Inv mu sgm' tgm' ->
              LG fl mu fpSrc sgm' fpTgt tgm'.



Lemma fpG_eq: forall fl S fp fp',
    fpG fl S fp ->
    FP.eq fp fp' ->
    fpG fl S fp'.
Proof.
  unfold fpG, FP.blocks, FP.locs; intros.
  apply H. clear H. inversion H0.
  unfold Bset.belongsto, Locs.blocks, Locs.belongsto, Locs.union, Locs.eq in *.
  destruct H1. exists x.
  repeat (match goal with [H:forall b ofs, _|-_]=> specialize (H b x); rewrite H end).
  auto.
Qed.
  
Lemma fpG_emp: forall fl S,
    fpG fl S FP.emp.
Proof.
  unfold fpG; intros. exfalso. destruct H. eauto with locs.
Qed.

Lemma fpG_union: forall fl S fp1 fp2,
    fpG fl S fp1 ->
    fpG fl S fp2 ->
    fpG fl S (FP.union fp1 fp2).
Proof.
  intros. intros b H1. apply FP.union_belongsto in H1. destruct H1; auto.
Qed.

Lemma fpG_subset: forall fl S fp1 fp2,
    fpG fl S fp1 ->
    FP.subset fp2 fp1 ->
    fpG fl S fp2.
Proof.
  intros. intros b H1. apply H. eapply FP.belongsto_subset; eauto.
Qed.

(*
Lemma LfpG_union_S:
  forall fl mu fpS fpT fpS',
    LfpG fl mu fpS fpT ->
    LfpG fl mu (FP.union fpS fpS') fpT.
Proof.
  intros. inversion H.
  constructor; auto.
  eapply fp_match_union_S; eauto.
Qed.
 *)

Lemma LfpG'_union_S:
  forall fl mu fpS fpT fpS',
    LfpG' fl mu fpS fpT ->
    LfpG' fl mu (FP.union fpS fpS') fpT.
Proof.
  intros. inversion H.
  constructor; auto.
  eapply fp_match_union_S'; eauto.
Qed.

(*
Lemma LfpG_union_T:
  forall fl mu fpS fpT fpT',
    LfpG fl mu fpS fpT ->
    LfpG fl mu fpS fpT' ->
    LfpG fl mu fpS (FP.union fpT fpT').
Proof.
  intros. inversion H; inversion H0.
  constructor. apply fp_match_union_T; auto.
  apply fpG_union; auto.
Qed.
 *)

Lemma LfpG'_union_T:
  forall fl mu fpS fpT fpT',
    LfpG' fl mu fpS fpT ->
    LfpG' fl mu fpS fpT' ->
    LfpG' fl mu fpS (FP.union fpT fpT').
Proof.
  intros. inversion H; inversion H0.
  constructor. apply fp_match_union_T'; auto.
  apply fpG_union; auto.
Qed.

(*
Lemma LfpG_union:
  forall fl mu fpS fpT fpS' fpT',
    LfpG fl mu fpS fpT ->
    LfpG fl mu fpS' fpT' ->
    LfpG fl mu (FP.union fpS fpS') (FP.union fpT fpT').
Proof.
  intros. inversion H; inversion H0.
  constructor; auto.
  apply fp_match_union; eauto.
  apply fpG_union; auto.
Qed.
 *)

Lemma LfpG'_union:
  forall fl mu fpS fpT fpS' fpT',
    LfpG' fl mu fpS fpT ->
    LfpG' fl mu fpS' fpT' ->
    LfpG' fl mu (FP.union fpS fpS') (FP.union fpT fpT').
Proof.
  intros. inversion H; inversion H0.
  constructor; auto.
  apply fp_match_union'; eauto.
  apply fpG_union; auto.
Qed.

(*
Lemma LfpG_subset_S:
  forall fl mu fpS fpT fpS',
    LfpG fl mu fpS fpT ->
    FP.subset fpS fpS' ->
    LfpG fl mu fpS' fpT.
Proof.
  intros. inversion H. constructor; auto.
  eapply fp_match_subset_S; eauto.
Qed.
 *)

Lemma LfpG'_subset_S:
  forall fl mu fpS fpT fpS',
    LfpG' fl mu fpS fpT ->
    FP.subset fpS fpS' ->
    LfpG' fl mu fpS' fpT.
Proof.
  intros. inversion H. constructor; auto.
  eapply fp_match_subset_S'; eauto.
Qed.

(*
Lemma LfpG_subset_T:
  forall fl mu fpS fpT fpT',
    LfpG fl mu fpS fpT ->
    FP.subset fpT' fpT ->
    LfpG fl mu fpS fpT'.
Proof.
  intros. inversion H. constructor; auto.
  eapply fp_match_subset_T; eauto.
  eapply fpG_subset; eauto.
Qed.
 *)

Lemma LfpG'_subset_T:
  forall fl mu fpS fpT fpT',
    LfpG' fl mu fpS fpT ->
    FP.subset fpT' fpT ->
    LfpG' fl mu fpS fpT'.
Proof.
  intros. inversion H. constructor; auto.
  eapply fp_match_subset_T'; eauto.
  eapply fpG_subset; eauto.
Qed.


(** In order to deal with arguments in external calls 
    (like no stack pointer leakage etc.),
    we need a stricted version of value injection, 
    i.e. Vundef could not be inject to a stack pointer.
    For convenience here I further restrict Vundef only able to 
    inject to Vundef
 *)

Lemma Rely_trans:
  forall fl Shared gm1 gm2 gm3,
    Rely fl Shared gm1 gm2 ->
    Rely fl Shared gm2 gm3 ->
    Rely fl Shared gm1 gm3.
Proof.
  intros.
  inversion H; inversion H0.
  constructor; auto.
  eapply GMem.forward_trans; eauto.
  eapply unchg_freelist_trans; eauto.
Qed.
    
    
Lemma HLRely_trans:
  forall flSrc flTgt mu sgm1 sgm2 sgm3 tgm1 tgm2 tgm3,
    HLRely flSrc flTgt mu sgm1 sgm2 tgm1 tgm2 ->
    HLRely flSrc flTgt mu sgm2 sgm3 tgm2 tgm3 ->    
    HLRely flSrc flTgt mu sgm1 sgm3 tgm1 tgm3.
Proof.
  intros.
  inversion H; inversion H0.
  constructor; auto.
  eapply Rely_trans; eauto.
  eapply Rely_trans; eauto.
Qed.


(* key lemma for footprint preservation *)
Lemma fp_match_ge_cmps_match:
  forall mu fpS fpT,
    FPMatch' mu fpS fpT ->
    LocMatch mu (FP.ge_cmps fpS) (FP.ge_cmps fpT).
Proof.
  intros. destruct H. FP.unfolds_thrshd.
  repeat apply locs_match_union_T; eapply locs_match_subset_S; eauto;
    Locs.unfolds; intros; red_boolean_true.
Qed.

Lemma fp_match_ge_reads_match:
  forall mu fpS fpT,
    FPMatch' mu fpS fpT ->
    LocMatch mu (FP.ge_reads fpS) (FP.ge_reads fpT).
Proof.
  intros. destruct H. FP.unfolds_thrshd.
  repeat apply locs_match_union_T; eapply locs_match_subset_S; eauto;
    clear; Locs.unfolds; intros; red_boolean_true.
Qed.

Lemma fp_match_ge_writes_match:
  forall mu fpS fpT,
    FPMatch' mu fpS fpT ->
    LocMatch mu (FP.ge_writes fpS) (FP.ge_writes fpT).
Proof.
  intros. destruct H. FP.unfolds_thrshd.
  repeat apply locs_match_union_T; eapply locs_match_subset_S; eauto;
    clear; Locs.unfolds; intros; red_boolean_true.
Qed.

Lemma fp_match_ge_frees_match:
  forall mu fpS fpT,
    FPMatch' mu fpS fpT ->
    LocMatch mu (FP.ge_frees fpS) (FP.ge_frees fpT).
Proof.
  intros. destruct H. FP.unfolds_thrshd.
  repeat apply locs_match_union_T; eapply locs_match_subset_S; eauto;
    clear; Locs.unfolds; intros; red_boolean_true.
Qed.
  
Lemma locs_smile_preservation_via_locmatch:
  forall mu ls1 ls2 lt1 lt2,
    Bset.inj_inject (inj mu) ->
    LocMatch mu ls1 lt1 ->
    LocMatch mu ls2 lt2 ->
    Locs.smile ls1 ls2 ->
    Bset.subset (Locs.blocks (Locs.intersect lt1 lt2)) (SharedTgt mu) ->
    Locs.smile lt1 lt2.
Proof.
  intros. destruct H0, H1.
  unfold Bset.inject_block, Bset.belongsto, Bset.subset, Locs.blocks in *. Locs.unfolds.
  intros. destruct (lt1 b ofs) eqn:Hlt1, (lt2 b ofs) eqn:Hlt2; auto.
  assert (SharedTgt mu b).
  { apply H3. exists ofs. rewrite Hlt1, Hlt2. auto. }
  specialize (H0 b ofs H4 Hlt1). specialize (H1 b ofs H4 Hlt2).
  clear H3 H4 Hlt1 Hlt2. destruct H0 as (b1 & INJ1 & Hls1), H1 as (b2 & INJ2 & Hls2).
  specialize (H _ _ _ INJ1 INJ2). subst.
  specialize (H2 b2 ofs). rewrite Hls1, Hls2 in *. inversion H2.
Qed.

Lemma fpG_disj_fl_intersect:
  forall fp1 fp2 S fl1 fl2,
    disj fl1 fl2 ->
    fpG fl1 S fp1 ->
    fpG fl2 S fp2 ->
    Bset.subset (Locs.blocks (Locs.intersect (FP.locs fp1) (FP.locs fp2))) S.
Proof.
  unfold fpG, Bset.belongsto, Bset.subset, FP.blocks, FP.locs, Locs.blocks in *.
  Locs.unfolds. intros. destruct H2 as [ofs H2].
  exploit (H0 b). exists ofs. red_boolean_true. clear H0.
  exploit (H1 b). exists ofs. red_boolean_true. clear H1 H2.
  intros. destruct H0; [auto|destruct H1]; auto.
  destruct H0, H1. destruct H. specialize (H x0 x). rewrite <- H0 in H1.
  congruence.
Qed.

Theorem smile_preserv_via_LfpG:
  forall fpS1 fpS2,
    FP.smile' fpS1 fpS2 ->
    forall mu fl1 fpT1 fl2 fpT2,
      Bset.inj_inject (inj mu) ->
      disj fl1 fl2 ->
      LfpG' fl1 mu fpS1 fpT1 ->
      LfpG' fl2 mu fpS2 fpT2 ->
      FP.smile' fpT1 fpT2.
Proof.  
  intros. destruct H2 as [FPM1 fpG1]. destruct H3 as [FPM2 fpG2]. destruct H.
  pose proof (fpG_disj_fl_intersect _ _ _ _ _ H1 fpG1 fpG2). clear H1 fpG1 fpG2 fl1 fl2.
  constructor. 
  clear smile'_rw. destruct smile'_cf as [c1f2 c2f1].
  split; [clear c2f1|clear c1f2].
  apply fp_match_ge_cmps_match in FPM1.
  apply fp_match_ge_frees_match in FPM2.
  eapply locs_smile_preservation_via_locmatch; eauto.
  generalize H; clear. intros. unfold Bset.subset, Locs.blocks, FP.locs in *.
  FP.unfolds_thrshd. intros. apply H. clear H. Locs.unfolds. destruct H0. exists x. red_boolean_true.
  apply fp_match_ge_cmps_match in FPM2.
  apply fp_match_ge_frees_match in FPM1.
  eapply locs_smile_preservation_via_locmatch; eauto.
  generalize H; clear. intros. unfold Bset.subset, Locs.blocks, FP.locs in *.
  FP.unfolds_thrshd. intros. apply H. clear H. Locs.unfolds. destruct H0. exists x. red_boolean_true.
  clear smile'_cf. destruct smile'_rw as [r1w2 r2w1].
  split; [clear r2w1|clear r1w2].
  apply fp_match_ge_reads_match in FPM1.
  apply fp_match_ge_writes_match in FPM2.
  eapply locs_smile_preservation_via_locmatch; eauto.
  generalize H; clear. intros. unfold Bset.subset, Locs.blocks, FP.locs in *.
  FP.unfolds_thrshd. intros. apply H. clear H. Locs.unfolds. destruct H0. exists x. red_boolean_true.
  apply fp_match_ge_reads_match in FPM2.
  apply fp_match_ge_writes_match in FPM1.
  eapply locs_smile_preservation_via_locmatch; eauto.
  generalize H; clear. intros. unfold Bset.subset, Locs.blocks, FP.locs in *.
  FP.unfolds_thrshd. intros. apply H. clear H. Locs.unfolds. destruct H0. exists x. red_boolean_true.
Qed.




Lemma bset_eq_G_arg:
  forall bs1 bs2 arg,
    (forall b, bs1 b <-> bs2 b) ->
    G_arg bs1 arg <-> G_arg bs2 arg.
Proof.
  intros; unfold G_arg. destruct arg; auto; tauto.
Qed.

Lemma bset_eq_G_args:
  forall bs1 bs2 args,
    (forall b, bs1 b <-> bs2 b) -> G_args bs1 args <-> G_args bs2 args.
Proof.
  clear. intros.
  unfold G_args. induction args. split; auto.
  split; intro.
  inversion H0. subst. constructor.
  destruct a; auto. unfold G_arg in *. rewrite <- H. auto.
  rewrite <- IHargs. auto.
  inversion H0. subst. constructor.
  destruct a; auto. unfold G_arg in *. rewrite H. auto.
  rewrite IHargs. auto.
Qed.

Lemma bset_eq_fpG:
  forall fl fp bs1 bs2,
    (forall b, bs1 b <-> bs2 b) ->
    fpG fl bs1 fp <-> fpG fl bs2 fp.
Proof.
  clear; intros.
  unfold fpG, Bset.belongsto in *.
  split; intros; [rewrite <- H | rewrite H]; auto.
Qed.


(** * Relating ges *)
(** every ident in target prog corresponds to the same ident in source prog,
    and the datas (fun/globdef) bounded are related *)

Inductive gvar_match {V1 V2: Type}: AST.globvar V1 -> AST.globvar V2 -> Prop :=
| gvar_match_intro: forall v1 v2 initdata fro fvo,
    gvar_match (AST.mkglobvar v1 initdata fro fvo) (AST.mkglobvar v2 initdata fro fvo).

Lemma gvar_match_trans:
  forall V1 V2 V3 gv1 gv2 gv3,
    @gvar_match V1 V2 gv1 gv2 ->
    @gvar_match V2 V3 gv2 gv3 ->
    gvar_match gv1 gv3.
Proof.
  intros. inv H; inv H0. constructor.
Qed.

Inductive globdef_match {F1 V1 F2 V2: Type}:
  AST.globdef F1 V1 ->  AST.globdef F2 V2 -> Prop :=
| Gfun_match:
    forall f1 f2, globdef_match (AST.Gfun f1) (AST.Gfun f2)
| Gvar_match:
    forall gv1 gv2, gvar_match gv1 gv2 -> globdef_match (AST.Gvar gv1) (AST.Gvar gv2).

Lemma globdef_match_trans:
  forall F1 V1 F2 V2 F3 V3 gd1 gd2 gd3,
    @globdef_match F1 V1 F2 V2 gd1 gd2 ->
    @globdef_match F2 V2 F3 V3 gd2 gd3 ->
    globdef_match gd1 gd3.
Proof.
  intros. inv H; inv H0; constructor. 
  eapply gvar_match_trans; eauto.
Qed.
      
Record ge_match {F1 V1 F2 V2: Type}
       (sge:Genv.t F1 V1)
       (tge:Genv.t F2 V2) : Prop :=
  {
    genv_public_eq: forall id, In id (Genv.genv_public sge) <-> In id (Genv.genv_public tge);
    genv_symb_eq_dom: forall id, PTree.get id (Genv.genv_symb sge) = None <->
                            PTree.get id (Genv.genv_symb tge) = None;
    genv_defs_match: forall id b b', PTree.get id (Genv.genv_symb sge) = Some b ->
                                PTree.get id (Genv.genv_symb tge) = Some b' ->
                                option_rel (globdef_match)
                                           (PTree.get b (Genv.genv_defs sge))
                                           (PTree.get b' (Genv.genv_defs tge));
    genv_next_eq: Genv.genv_next sge = Genv.genv_next tge;
  }.

Lemma ge_match_trans:
  forall F1 V1 F2 V2 F3 V3
    (ge1: Genv.t F1 V1)
    (ge2: Genv.t F2 V2)
    (ge3: Genv.t F3 V3),
    ge_match ge1 ge2 ->
    ge_match ge2 ge3 ->
    ge_match ge1 ge3.
Proof.
  constructor; intros.
  erewrite genv_public_eq; eauto. apply (genv_public_eq _ _ H0).
  erewrite genv_symb_eq_dom; eauto. apply (genv_symb_eq_dom _ _ H0).
  destruct ((Genv.genv_symb ge2) ! id) eqn:H3.
  exploit (genv_defs_match ge1 ge2 H id); eauto. 
  exploit (genv_defs_match ge2 ge3 H0 id); eauto. intros.
  inv H4.
  rewrite <- H7 in *. inv H5. constructor.
  rewrite <- H6 in *. inv H5. constructor.
  eapply globdef_match_trans; eauto.
  erewrite genv_symb_eq_dom in H3; eauto. rewrite H2 in H3; inv H3.
  erewrite genv_next_eq. eapply (genv_next_eq _ _ H0). auto.
Qed.


(** * Relating mu and ges *)
(** should be moved to another file, or find corresponding definition in CompCert? *)
Inductive inj_oblock : Bset.inj -> option block -> option block -> Prop :=
  | Inj_block:
      forall bj b b',
        bj b = Some b' ->
        inj_oblock bj (Some b) (Some b')
  | Inj_none:
      forall bj, inj_oblock bj None None.
      
  
Record ge_init_inj {F1 V1 F2 V2: Type}
       (mu: Mu)
       (sge: Genv.t F1 V1)
       (tge: Genv.t F2 V2) : Prop :=
  {
    mu_shared_src:
      SharedSrc mu = fun b => Plt b (Genv.genv_next sge);
    mu_shared_tgt:
      SharedTgt mu = fun b => Plt b (Genv.genv_next tge);
    mu_inject:
      Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu);
    senv_injected:
      forall id, inj_oblock (inj mu) (Senv.find_symbol sge id) (Senv.find_symbol tge id)
  }.

Lemma ge_init_inj_SharedSrc:
  forall F1 V1 F2 V2 mu sge tge,
    @ge_init_inj F1 V1 F2 V2 mu sge tge ->
    (SharedSrc mu) = fun b => Plt b (Genv.genv_next sge).
Proof. inversion 1; auto. Qed.

Lemma ge_init_inj_SharedTgt:
  forall F1 V1 F2 V2  mu sge tge,
    @ge_init_inj F1 V1 F2 V2 mu sge tge ->
    (SharedTgt mu) = fun b => Plt b (Genv.genv_next tge).
Proof. inversion 1; auto. Qed.

Lemma inj_id_arg_eq:
  forall mu argSrc argTgt,
    inject_incr (Bset.inj_to_meminj (inj mu)) inject_id ->
    G_args (SharedSrc mu) argSrc ->
    arg_rel (inj mu) argSrc argTgt ->
    argSrc = argTgt.
Proof.
  intros until 1. revert argSrc argTgt. induction argSrc; intros; inv H1; inv H0; auto.
  f_equal. inv H4; auto. apply H in H0. inv H0. rewrite Integers.Ptrofs.add_zero. auto. inv H3.
  apply IHargSrc; auto.
Qed.