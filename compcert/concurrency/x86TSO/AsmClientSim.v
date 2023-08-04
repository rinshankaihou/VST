Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.

Require Import CUAST.

Require Import Footprint GMemory FMemory TSOMem FMemOpFP.
Require Import GlobDefs GAST ETrace LDSimDefs.

Require Import ASM_local AsmLang AsmTSO TSOGlobSem.
Require Import InteractionSemantics.
Require Import RGRels ClientSim SCSemLemmas TSOSemLemmas TSOMemLemmas.

Local Notation footprint := FP.t.

Lemma strip_fl_eq_fmem_eq:
  forall fm fm',
    strip fm = strip fm' ->
    Mem.freelist fm = Mem.freelist fm' ->
    fm = fm'.
Proof.
  clear. intros. destruct fm, fm'; simpl in *.
  unfold strip in H. simpl in *. inv H.
  assert (nextblockid = nextblockid0).
  { revert valid_wd valid_wd0. clear. intros.
    destruct (Nat.eq_dec nextblockid nextblockid0); auto.
    apply Nat.lt_gt_cases in n. destruct n.
    exploit (valid_wd nextblockid); eauto.
    exploit (valid_wd0 nextblockid); eauto.
    intros. apply H0 in H. apply H1 in H. omega.
    exploit (valid_wd nextblockid0); eauto.
    exploit (valid_wd0 nextblockid0); eauto.
    intros. apply H1 in H. apply H0 in H. omega. }
  subst nextblockid. f_equal; auto using proof_irr.
Qed.

Lemma helpers_i64ext_sem_det:
  forall ef vargs vres vres',
    helpers.i64ext_sem ef vargs vres ->
    helpers.i64ext_sem ef vargs vres' ->
    vres = vres'.
Proof.
  clear. intros.
  eapply helpers.i64ext_extcall in H. eapply helpers.i64ext_extcall in H0.
  destruct H, H0.
  specialize (H1 (Genv.empty_genv fundef unit nil) Memory.Mem.empty).
  specialize (H2 (Genv.empty_genv fundef unit nil) Memory.Mem.empty).
  exploit external_call_determ. exact H1. exact H2. clear. intuition.
Qed.
          
Lemma tupdate_update_same:
  forall t bufs,
    tupdate t (bufs t) bufs = bufs.
Proof.
  intros; apply functional_extensionality; intro; unfold tupdate; destruct peq; subst; auto.
Qed.

Lemma tupdate_update_get_same:
  forall t bufs buf,
    tupdate t buf bufs t = buf.
Proof.
  intros. unfold tupdate. destruct peq; auto; contradiction.
Qed.

Lemma tupdate_update2:
  forall t buf buf' bufs,
    tupdate t buf (tupdate t buf' bufs) = tupdate t buf bufs.
Proof.
  clear. intros. apply functional_extensionality.
  intro. unfold tupdate. destruct peq; auto.
Qed.

Lemma emp_not_conflictc:
  forall t bufs, ~ conflictc t FP.emp bufs.
Proof.
  intros. intro. inv H. inv H2; Locs.unfolds; destruct H as (b & ofs & H); red_boolean_true.
Qed.

Lemma conflictc_ext:
  forall fp bufs bufs' t,
    conflictc t fp bufs ->
    (forall t', t' <> t -> bufs t' = bufs' t') ->
    conflictc t fp bufs'.
Proof.
  clear. intros.
  inv H. rewrite H0 in H2; auto. econstructor; eauto.
Qed.

Lemma conflictc_union:
  forall fp1 fp2 bufs t,
    conflictc t (FP.union fp1 fp2) bufs ->
    conflictc t fp1 bufs \/ conflictc t fp2 bufs.
Proof.
  clear. intros. inv H. unfold conflict_bi in H2.
  apply FP.conflict_sym, FPLemmas.fpconflict_union in H2.
  destruct H2 as [H2|H2]; [left|right]; apply FP.conflict_sym in H2;
    repeat (econstructor; eauto).
Qed.

Lemma conflictc_union':
  forall fp1 fp2 bufs t,
    conflictc t fp1 bufs \/ conflictc t fp2 bufs ->
    conflictc t (FP.union fp1 fp2) bufs.
Proof.
  clear. intros. destruct H; inv H; econstructor; eauto.
  eapply USimDRF.conflict_union; eauto.
  rewrite FP.union_comm_eq. eapply USimDRF.conflict_union; eauto.
Qed.

Lemma store_args_fp_in_stk:
  forall stk tys,
    exists locs,
      loadframe.store_args_fp stk tys = FP.Build_t Locs.emp Locs.emp locs Locs.emp /\
      (forall b ofs, Locs.belongsto locs b ofs -> b = stk).
Proof.
  intros. unfold loadframe.store_args_fp. generalize 0. induction tys.
  intros. exists Locs.emp. split; auto. intros. inv H.
  intro. simpl. specialize (IHtys (z + typesize a)). 
  destruct IHtys as (locs0 & Hfp0 & Hstk0). rewrite Hfp0.
  unfold loadframe.store_stack_fp. simpl. unfold store_fp. simpl.
  unfold FP.union. simpl. rewrite Locs.emp_union_locs.
  destruct a; eexists; split; eauto; intros;
    apply belongsto_union in H; destruct H; eauto;
      try apply range_locset_loc in H; try tauto.
    apply belongsto_union in H; destruct H; eauto;
      try apply range_locset_loc in H; try tauto.
Qed.

Lemma conflict_store_args_conflict_alloc:
  forall t stk tys bufs lo hi,
    conflictc t (loadframe.store_args_fp stk tys) bufs ->
    conflictc t (tsoalloc_fp stk lo hi) bufs.
Proof.
  clear. intros t stk tys bufs.
  unfold tsoalloc_fp, uncheck_alloc_fp. intros _ _.
  destruct (store_args_fp_in_stk stk tys) as [locs [Hfp Hstk]].
  rewrite Hfp. clear Hfp tys.
  intros. inv H. 
  inv H2; Locs.unfolds; destruct H as (b & ofs & H); 
    unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes, FP.ge_frees in *; simpl in *; Locs.unfolds;
      try rewrite andb_false_r in H; try discriminate.

  rewrite orb_false_r in H. red_boolean_true. apply Hstk in H. subst b.
  econstructor; eauto. eapply FP.conflict_ff; simpl. Locs.unfolds.
  exists stk, ofs. destruct peq; try contradiction; rewrite H2; auto.

  red_boolean_true. apply Hstk in H2. subst b.
  econstructor; eauto. eapply FP.conflict_rf; simpl. Locs.unfolds.
  exists stk, ofs. destruct peq; try contradiction; rewrite H; auto.

  red_boolean_true. apply Hstk in H. subst b.
  econstructor; eauto. eapply FP.conflict_wf; simpl. Locs.unfolds.
  exists stk, ofs. destruct peq; try contradiction; rewrite H2; auto.
Qed.

Lemma conflict_store_conflict_alloc:
  forall chunk stk ofs lo hi bufs t,
    conflictc t (store_fp chunk stk ofs) bufs ->
    conflictc t (tsoalloc_fp stk lo hi) bufs.
Proof.
  clear. intros. inv H. econstructor. eauto. eauto.
  unfold store_fp, tsoalloc_fp, uncheck_alloc_fp in *.
  apply FP.conflict'_conflict_equiv in H2.
  inv H2; simpl in *; unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes, FP.ge_frees in *;
    simpl in *; Locs.unfolds.
  destruct H as (b & ofs' & H). eapply FP.conflict'_conflict_equiv.
  red_boolean_true; econstructor; exists b, ofs';
    unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes, FP.ge_frees in *; simpl; Locs.unfolds; simpl;
      try (rewrite H; simpl; auto; fail).
  apply range_locset_loc in H3. destruct H3. subst b. destruct peq; try contradiction; simpl.
  rewrite H. auto.
  rewrite H. simpl. destruct peq; subst; auto with bool.
  rewrite H2. simpl. destruct peq; simpl; auto with bool.
  rewrite H. simpl. destruct peq; simpl; auto 10 with bool.
  destruct H as (b & ofs' & H). eapply FP.conflict'_conflict_equiv.
  red_boolean_true; econstructor; exists b, ofs';
    unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes, FP.ge_frees in *; simpl; Locs.unfolds; simpl;
      try (rewrite H3; destruct peq; auto 10 with bool; fail).
  apply range_locset_loc in H2. destruct H2. subst b.
  destruct peq; try contradiction; simpl. rewrite H3. auto 10 with bool.
  apply range_locset_loc in H2. destruct H2. subst b.
  destruct peq; try contradiction; simpl. rewrite H3. auto 10 with bool.
  apply range_locset_loc in H3. destruct H3. subst b.
  destruct peq; try contradiction; simpl. rewrite H. auto 10 with bool.
  apply range_locset_loc in H3. destruct H3. subst b.
  destruct peq; try contradiction; simpl. rewrite H2. auto 10 with bool.
  apply range_locset_loc in H3. destruct H3. subst b.
  destruct peq; try contradiction; simpl. rewrite H2. auto 10 with bool.
  rewrite H. destruct peq; auto 10 with bool.
  rewrite H2. destruct peq; auto 10 with bool.
  rewrite H2. destruct peq; auto 10 with bool.
Qed.

Lemma Pallocframe_succeed_link_ra_inrange:
  forall ge f sz ofs_ra ofs_link rs m rs' m',
    exec_instr ge f (Pallocframe sz ofs_ra ofs_link) rs m = AsmLang.Next rs' m' ->
    (Ptrofs.unsigned ofs_ra + size_chunk Mptr <= sz /\ (align_chunk Mptr | Ptrofs.unsigned ofs_ra)) /\
    (Ptrofs.unsigned ofs_link + size_chunk Mptr <= sz /\ (align_chunk Mptr | Ptrofs.unsigned ofs_link)).
Proof.
  simpl. intros.
  destruct (Mem.alloc m 0 sz) as [m1 stk] eqn:Halloc.
  destruct Mem.store eqn:Hstore1; [|discriminate].
  destruct (Mem.store Mptr m0 _ _ _) eqn:Hstore2; [|discriminate]. clear H.
  exploit Mem.store_access. exact Hstore1. intro Haccess2.
  split.
  { clear Hstore1. apply Mem.store_valid_access_3 in Hstore2.
    rewrite Ptrofs.add_zero_l in Hstore2. destruct Hstore2. split; auto.
    specialize (H (Ptrofs.unsigned ofs_ra + size_chunk Mptr - 1)).
    pose proof (Mem.perm_alloc_inv _ _ _ _ _ Halloc
                                   stk (Ptrofs.unsigned ofs_ra + size_chunk Mptr - 1)
                                   Memperm.Cur Memperm.Writable).
    exploit H. clear. unfold size_chunk, Mptr. destruct Archi.ptr64; omega.
    clear H. intro H. unfold Mem.perm in *. rewrite Haccess2 in *. apply H1 in H. clear H1.
    destruct eq_block; try contradiction. omega. }
  { clear Hstore2 Haccess2. apply Mem.store_valid_access_3 in Hstore1.
    rewrite Ptrofs.add_zero_l in Hstore1. destruct Hstore1. split; auto.
    specialize (H (Ptrofs.unsigned ofs_link + size_chunk Mptr - 1)).
    pose proof (Mem.perm_alloc_inv _ _ _ _ _ Halloc
                                   stk (Ptrofs.unsigned ofs_link + size_chunk Mptr - 1)
                                   Memperm.Cur Memperm.Writable).
    exploit H. clear. unfold size_chunk, Mptr. destruct Archi.ptr64; omega.
    clear H. intro H. apply H1 in H. clear H1. destruct eq_block; try contradiction. omega. }
Qed.

Lemma eq_on_loc_trans:
  forall b ofs m1 m2 m3,
    eq_on_loc b ofs m1 m2 ->
    eq_on_loc b ofs m2 m3 ->
    eq_on_loc b ofs m1 m3.
Proof.
  intros. inv H; inv H0. constructor.
  rewrite eq_loc_validity; auto.
  intro. rewrite eq_loc_perm. auto.
  congruence.
Qed.

Lemma Gc_trans:
  forall t sm1 tm1 sm2 tm2 sm3 tm3,
    Gc t sm1 tm1 sm2 tm2 ->
    Gc t sm2 tm2 sm3 tm3 ->
    Gc t sm1 tm1 sm3 tm3.
Proof.
  unfold Gc. intros.
  split. intuition.
  split. intuition.
  split. intuition. apply H4, H3. auto. apply H3, H4. auto.
  split. intuition. eapply eq_on_loc_trans. eauto. apply H6. apply H3. auto.
  split. intuition. congruence.
  split. intuition.
  { destruct H9 as (bis1 & Hinsert1 & Hclient1).
    destruct H10 as (bis2 & Hinsert2 & Hclient2).
    exists (bis1 ++ bis2). split. rewrite Hinsert2, Hinsert1.
    unfold tupdate. apply functional_extensionality. intro.
    destruct peq; subst; auto.
    destruct peq. rewrite app_assoc; auto. contradiction.
    intros. inv H9. apply in_app in H11. destruct H11; [eapply Hclient1|eapply Hclient2]; eauto.
    econstructor; eauto.
    econstructor; eauto.
    apply H3. auto. }
  eapply GMem.forward_trans; intuition; eauto.
Qed.

Lemma Gc_refl:
  forall t sm tm,
    Ic sm tm ->
    Gc t sm tm sm tm.
Proof.
  repeat (split; auto). exists nil. split.
  rewrite app_nil_r. unfold tupdate. apply functional_extensionality. intro; destruct peq; subst; auto.
  intros. inv H0. inv H1.
Qed.

Lemma eq_validity_eq_nextblock:
  forall fl m m' fm fm',
    (forall b n, MemAux.get_block fl n = b -> In b (GMem.validblocks m) <-> In b (GMem.validblocks m')) ->
    embed m fl fm ->
    embed m' fl fm' ->
    Mem.nextblock fm = Mem.nextblock fm'.
Proof.
  clear. intros.
  inv H0; inv H1.
  pose proof (Mem.valid_wd fm). pose proof (Mem.valid_wd fm').
  unfold Mem.nextblock. rewrite H0 in *. clear H0.
  f_equal. revert H H1 H2. simpl.
  generalize (Mem.nextblockid fm) (Mem.nextblockid fm') (Mem.freelist fm) (Mem.validblocks fm) (Mem.validblocks fm').
  intros N1 N2 fl vl1 vl2 H1 H2 H3.
  destruct (Nat.eq_dec N1 N2); auto. apply Nat.lt_gt_cases in n. destruct n; exfalso.
  specialize (H3 N1 (MemAux.get_block fl N1) eq_refl).
  specialize (H2 N1 (MemAux.get_block fl N1) eq_refl).
  specialize (H1 (MemAux.get_block fl N1) N1 eq_refl).
  apply H3, H1, H2 in H. omega.
  specialize (H3 N2 (MemAux.get_block fl N2) eq_refl).
  specialize (H2 N2 (MemAux.get_block fl N2) eq_refl).
  specialize (H1 (MemAux.get_block fl N2) N2 eq_refl).
  apply H2, H1, H3 in H. omega.
Qed.

Lemma rel_vb_nextblock_eq:
  forall m bufs tm fl t,
    rel_tm_gm_vb (strip m) (mktsomem bufs (strip tm)) fl t ->
    (forall t', bufs t' = nil) ->
    Mem.freelist m = Mem.freelist tm ->
    Mem.freelist m = fl ->
    Mem.nextblock m = Mem.nextblock tm.
Proof.
  clear. intros. subst fl.
  unfold rel_tm_gm_vb in H. simpl in H. rewrite H0 in H. simpl in H.
  assert (forall n, In (MemAux.get_block (Mem.freelist m) n) (Mem.validblocks m)
               <-> In (MemAux.get_block (Mem.freelist tm) n) (Mem.validblocks tm)).
  { intro. specialize (H n). erewrite <- H; eauto. simpl. rewrite H1. tauto. }
  clear H.
  assert (forall n, n < Mem.nextblockid m <-> n < Mem.nextblockid tm)%nat.
  { intro. erewrite <- Mem.valid_wd; eauto. erewrite <- Mem.valid_wd; eauto. }
  clear H2.
  unfold Mem.nextblock. f_equal; auto. revert H. 
  generalize (Mem.nextblockid m) (Mem.nextblockid tm). clear.
  intros n1 n2 Heq. destruct (Nat.eq_dec n1 n2); auto.
  apply (Nat.lt_gt_cases n1 n2) in n.
  destruct n as [n|n]; [specialize (Heq n1)|specialize (Heq n2)]; omega.
Qed.
          
(** Refinement on Mem Ops *)
Record meminv (t: tid) (fl: MemAux.freelist) (sgm: gmem) (bufs: buffers) (tgm: gmem) : Prop :=
  {
    meminv_Ic: Ic sgm (mktsomem bufs tgm);
    meminv_sep: sep_obj_client_block sgm;
    meminv_rel_vb: rel_tm_gm_vb sgm (mktsomem bufs tgm) fl t;
    meminv_alloc_local: tm_alloc_not_fl (mktsomem bufs tgm) fl t;
  }.

(** Res type is for recording returning values:
      - [alloc] : new block 
      - [load] : loaded value 
      - [store] : unit
      - [free] : unit
      - [valid_block] : true/false
 *)

Definition fmemop {Res: Type}: Type := mem -> FP.t -> Res -> mem -> Prop.
Definition tsofmemop {Res: Type}: Type := tsofmem -> FP.t -> Res -> tsofmem -> Prop.

Definition memops_refine {Res: Type} (opSrc: @fmemop Res) (opTgt: @tsofmemop Res) : Prop :=
  forall t fl sgm bufs tgm sfm tfm,
    meminv t fl sgm bufs tgm ->
    embed sgm fl sfm ->
    embed tgm fl tfm ->
    let tbfm := mktsofmem (bufs t) tfm in
    forall tfp tres tbfm',
      opTgt tbfm tfp tres tbfm' ->
      (* case 1: matched step? *)
      (exists sfp sres sfm',
          opSrc sfm sfp sres sfm' /\
          let sgm' := strip sfm' in
          let tgm' := strip (fmemory tbfm') in
          let buf' := tbuffer tbfm' in
          let bufs' := tupdate t buf' bufs in
          (* subcase 1: fp, res, result state matched *)
          ((~ conflictc t tfp bufs) /\
           fpmatchc sfp tfp /\
           sres = tres /\
           meminv t fl sgm' bufs' tgm' /\
           Gc t sgm (mktsomem bufs tgm) sgm' (mktsomem bufs' tgm'))
          \/
          (* subcase 2: fp conflict *)
          (conflictc t tfp bufs /\
           fpmatchc sfp tfp))
      \/
      (forall sfp sres sfm', ~ opSrc sfm sfp sres sfm').


Local Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Local Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Local Ltac ex_match:=
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?Hx; try discriminate
         end;try congruence.
Local Ltac ex_match2:=
  repeat match goal with
         | H: context[match ?x with _ => _ end]  |- _ => destruct x eqn:?Hx; try discriminate
         | H: _ |- context[match ?x with _ => _ end ] => destruct x eqn:?Hx;try discriminate
         end;try congruence;try contradiction.
Local Ltac ex_match3:=
  match goal with
    H: ?x = ?y |- context [?x] => rewrite H
  end.

    
Lemma meminv_fl_embed_nextblockeq:
  forall m m' t fl bfs,
    meminv t fl m bfs m'->
    forall m2 fm1 fm2,
      embed m fl fm1 ->
      apply_buffer (bfs t) m' = Some m2 ->
      embed m2 fl fm2 ->
      fm1.(Mem.nextblockid) = fm2.(Mem.nextblockid).
Proof.
  intros.
  inv H0;inv H2;  inv H.
  unfold rel_tm_gm_vb in meminv_rel_vb0.
  assert(forall n b, MemAux.get_block (Mem.freelist fm1) n = b ->
                In b (GMem.validblocks (strip fm2))<-> In b (GMem.validblocks (strip fm1))).
  intros;eauto.
  revert H H0;clear;intros.
  destruct fm1,fm2;simpl in *.
  destruct (Nat.lt_total nextblockid nextblockid0);subst;auto.
  {
    assert(exists b,MemAux.get_block freelist nextblockid = b). eauto.
    Hsimpl.
    exploit valid_wd;eauto.
    exploit valid_wd0;eauto.
    exploit H;eauto.
    intros.
    rewrite<- H3,H2,H4 in H1.
    omega.
  }
  {
    destruct H1;auto.
    assert(exists b,MemAux.get_block freelist nextblockid0 = b). eauto.
    Hsimpl.
    exploit valid_wd;eauto.
    exploit valid_wd0;eauto.
    exploit H;eauto.
    intros.
    rewrite <- H4,<- H2, H3 in H0.
    omega.
  }
Qed.

Lemma inbuffer_split:
  forall bf1 bf2 b ofs,
    in_buffer (bf1++bf2) b ofs ->
    in_buffer bf1 b ofs \/ in_buffer bf2 b ofs.
Proof.
  intros.
  inv H.
  apply in_app_or in H0 as [|];[left|right];econstructor;eauto.
Qed.

Lemma strip_fold:
  forall fm,
    {|
      GMem.mem_contents := Mem.mem_contents fm;
      GMem.mem_access := Mem.mem_access fm;
      GMem.validblocks := Mem.validblocks fm;
      GMem.access_max := Mem.access_max fm;
      GMem.invalid_noaccess := Mem.invalid_noaccess fm;
      GMem.contents_default := Mem.contents_default fm |} = strip fm.
Proof.
  eauto.
Qed.
Lemma unbuffer_forward:
  forall tm,
    buf_alloc_invalid tm ->
    buf_alloc_norep tm ->
    forall t tm' ,
      unbuffer tm t = Some tm'->
      GMem.forward (memory tm)(memory tm').
Proof.
  unfold unbuffer.
  intros. ex_match2. inv H1. simpl.
  constructor.
  {
    destruct b;simpl in Hx0;unfold alloc,free,store in Hx0;ex_match2;inv Hx0;unfold GMem.valid_block;simpl;auto.
  }
  {
    intros.
    destruct b;simpl in Hx0;unfold alloc,free,store in Hx0;ex_match2;inv Hx0;unfold GMem.valid_block;simpl in *;auto.
    2 :rewrite PMap.gsspec in H2; ex_match2.
    rewrite PMap.gsspec in H2. ex_match2. subst.
    exfalso. eapply H;eauto.
    erewrite Hx. left;eauto.
  }
Qed.
Lemma apply_buffer_forward:
   forall tm,
    buf_alloc_invalid tm ->
    buf_alloc_norep tm ->
    forall t bf ls tm',
      tso_buffers tm t = bf++ls->
      apply_buffer bf (memory tm) = Some tm' ->
      GMem.forward (memory tm) tm'.
Proof.
  intros until bf.
  revert tm H H0 t.
  induction bf;intros.
  simpl in H2. inv H2;auto. apply GMem.forward_refl.
  simpl in H2. unfold optbind in H2. ex_match2.
  assert(exists tm1 ,unbuffer tm t = Some tm1 /\ memory tm1 = g).
  unfold unbuffer. rewrite H1. simpl. rewrite Hx. eauto.
  Hsimpl.
  exploit unbuffer_forward;eauto.
  simpl;intro.
  eapply GMem.forward_trans;eauto.
  exploit Ic_buf_alloc_invalid_norep_stable;eauto. intros[].
  assert(tso_buffers x t = bf++ls).
  unfold unbuffer in H3. ex_match2. inv H3.  simpl in *.
  unfold tupdate. ex_match2.
  eapply IHbf;eauto.
  congruence.
Qed.


Lemma tsoalloc_thread_local_norep:
  forall tm  lo hi tm' b,
    tsoalloc tm lo hi (tm',b) ->
    forall b' lo hi,
      In (BufferedAlloc b' lo hi) (tbuffer tm) ->
      b' <> b.
Proof.
  intros.
  inv H.
  simpl in *.
  eapply In_nth_error in H0. Hsimpl.
  eapply nth_error_split in H.
  Hsimpl. subst.
  eapply TSOMemLemmas.apply_buffer_split in H6. Hsimpl.
  apply apply_buffer_split_2 in H0. Hsimpl.

  assert(In b' (GMem.validblocks x2)).
  inv H0;simpl in *. left;auto.
  eapply apply_buffer_in_validblocks_stable in H2;eauto.
  inv H7. intro;subst. contradict H2.
  unfold strip;simpl.
  apply next_block_not_in_validblock.
Qed.
Lemma alloc_refine:
  forall lo hi,
    let opSrc := fun sfm fp stk sfm' =>
                   Mem.alloc sfm lo hi = (sfm', stk) /\ fp = alloc_fp sfm lo hi in
    let opTgt := fun tbfm fp stk tbfm' =>
                   tsoalloc tbfm lo hi (tbfm', stk) /\ fp = tsoalloc_fp stk lo hi in
    @memops_refine block opSrc opTgt.
Proof.
  unfold memops_refine;intros.
  left.
  Local Transparent Mem.alloc.
  assert(exists sfm' sres,  (Mem.alloc sfm lo hi = (sfm', sres))).
  unfold Mem.alloc.
  Esimpl;eauto.
  Hsimpl;subst.
  Esimpl;eauto.
  rename H3 into R0.
  assert(BLOCKEQ: (Mem.nextblock sfm = tres)).
  { inv H2.
    inv H1.
    exploit meminv_fl_embed_nextblockeq;eauto.
    intro. unfold Mem.nextblock.
    inv H0. inv H10. congruence. }
  assert(BLOCKEQ2: tres = x0).
  unfold Mem.alloc in R0;inv R0;auto. subst x0.
  assert(FPMATCHC:fpmatchc (alloc_fp sfm lo hi)  (tsoalloc_fp tres lo hi)).
  { unfold alloc_fp,tsoalloc_fp;subst; apply FP.subset_refl.  }
  rename x into sfm'.
  assert(conflictc t  (tsoalloc_fp tres lo hi) bufs \/ ~conflictc t  (tsoalloc_fp tres lo hi) bufs).
  apply Classical_Prop.classic.
  destruct H3;[right|left].
  Esimpl;eauto.
  assert(R:forall t' ofs, in_buffer (bufs t')(Mem.nextblock sfm) ofs -> t' = t).
  {
    subst.
    revert H3;clear;intros.
    destruct (peq t' t);auto.
    inv H.
    contradict H3. econstructor;eauto.
    unfold conflict_bi,tsoalloc_fp,uncheck_alloc_fp.
    inv H1.
    + apply FP.conflict_ff;simpl. Locs.unfolds.
      exists (Mem.nextblock sfm),0. ex_match2;auto.
    + apply FP.conflict_ff;simpl;Locs.unfolds.
      exists (Mem.nextblock sfm),ofs;ex_match2;auto.
      simpl. unfold range_locset;ex_match2.
      rewrite <- add_minus_eq. destruct zle,zlt;auto;omega.
    + apply FP.conflict_wf;simpl;Locs.unfolds;simpl.
      exists (Mem.nextblock sfm),ofs. unfold range_locset.
      ex_match2. destruct zle,zlt;auto;omega.
  }
  assert(UBS1:unbuffer_safe
    {|
    tso_buffers := tupdate t (tbuffer tbfm') bufs;
    memory := strip (fmemory tbfm') |}).
  {
     apply meminv_Ic in H. 
     apply Ic_ub_safe in H.
     inv H2. 
     inv H1. inv H0. simpl.
     eapply unbuffer_safe_append_preserve with(bi:= (BufferedAlloc (Mem.nextblock fm') lo hi))(t:=t) in H.
     unfold tsoupd in H;simpl in *;auto.
     simpl in *.
     assert(exists gm'',alloc gm' (Mem.nextblock fm') lo hi = Some gm'').
     unfold alloc;eauto.
     Hsimpl.
     exists x. erewrite TSOAuxDefs.apply_buffer_app_eq;eauto. simpl. eauto.

     unfold inv_bi;intros.
     apply fpsmile_nfconflict. apply FP.smile_conflict_compat;intro;contradict H3.
     econstructor;eauto. simpl in H4.
     unfold conflict_bi,tsoalloc_fp. congruence.
   }
  assert(IC1:
    Ic (strip sfm')
    {|
    tso_buffers := tupdate t (tbuffer tbfm') bufs;
    memory := strip (fmemory tbfm') |}).
  {
    unfold strip;simpl.
    econstructor;simpl.
    rewrite !strip_fold.
    auto.
    {
      apply meminv_Ic in H.
      inversion H as [_ ? _].
      inv H2. inv H0.
      simpl in *.
      intros.

      unfold tupdate in H4,H5;ex_match2;subst.
      {
        apply inbuffer_split in H5 as [|].
        {
          eapply Ic_no_conflict_bi. 3:exact H4. 3:exact H5. eauto.
          assert(b <> Mem.nextblock sfm). intro. subst.
          eapply R in H4;eauto.
          intro;contradict H2.
          unfold Mem.alloc in R0;inv R0.
          inv H7;econstructor;simpl;auto; rewrite PMap.gso;auto.
        }
        {
          inv H5. inv H6. inv H7.
          rewrite H10 in H4. apply R in H4. contradiction.
          inv H5.
        }
      }
      {
        apply inbuffer_split in H4 as [|].
        {
          eapply Ic_no_conflict_bi. 3:exact H4. 3:exact H5. eauto.
          assert(b <> Mem.nextblock sfm). intro. subst.
          eapply R in H5;eauto.
          intro;contradict H2.
          unfold Mem.alloc in R0;inv R0.
          inv H7;econstructor;simpl;auto; rewrite PMap.gso;auto.
        }
        {
          inv H4. inv H6. inv H7.
          rewrite H10 in H5. apply R in H5. contradiction.
          inv H4.
        }
      }
      {
        assert(b <> Mem.nextblock sfm). intro;subst.
        eapply R in H4. apply R in H5. congruence.
        eapply Ic_no_conflict_bi in H4;try apply H5;eauto.
        intro;contradict H2. inv H7.
        unfold Mem.alloc in R0;inv R0.
        econstructor;simpl;rewrite PMap.gso;auto.
      }
    }
    {
      apply meminv_Ic in H.
      inversion H as [_ _ ?].
      erewrite strip_fold.
      intros.
      inv H2. inv H1. inv H0. simpl in *.
      unfold tupdate in H4. ex_match2. subst.
      Focus 2.
      {
        assert(t <> t0). auto.
        specialize (H6 t H0) as ?. rewrite TSOMemLemmas.tupdate_b_get in H2.
        assert(b <> Mem.nextblock fm').
        intro;contradict H2. Hsimpl.
        econstructor. eapply in_or_app. right. simpl. left;eauto.
        subst. econstructor.
        rewrite H13 in H7.
        assert(~obj_mem (strip sfm) b ofs).
        intro;contradict H5. unfold Mem.alloc in R0;inv R0.
        inv H8;econstructor;simpl;rewrite PMap.gso;auto.
        exploit Ic_mem_eq . exact H4. eauto. 
        intros. intro.
        eapply H6 in H9. contradict H9.
        unfold tupdate. ex_match2;auto. 
        inv H10;econstructor. apply in_or_app. left;eauto. auto.
        intro.
        eapply eq_on_loc_trans;eauto.
        revert R0 H7;clear. unfold Mem.alloc;inversion 1;subst.
        econstructor;FMemLemmas.gmem_unfolds.
        constructor;auto. intros[];congruence.
        rewrite PMap.gso;eauto.
        rewrite PMap.gso;auto.
      }
      Unfocus.
      apply TSOMemLemmas.apply_buffer_split in H4;Hsimpl.
      rewrite H0 in *. inv H12.
      destruct (peq b (Mem.nextblock fm')).
      {
        subst.
        simpl in H2. unfold optbind in H2;ex_match. inv H2.
        unfold Mem.alloc in R0;inv R0.
        econstructor;FMemLemmas.gmem_unfolds.
        {
          split;intro. left;congruence.
          left. congruence.
        }
        {
          intros.
          rewrite !PMap.gss,H13,PMap.gss. auto.
        }
        {
          rewrite PMap.gss,H13,PMap.gss;auto.
        }
      }
      {
        assert(~obj_mem (strip sfm) b ofs).
        unfold Mem.alloc in R0;inv R0.
        intros [];contradict H5;split;simpl in *;rewrite PMap.gso;try congruence.
        eapply Ic_mem_eq in H0;eauto.
        erewrite strip_fold in *.
        revert H2 R0 H0 H1 H13 n;clear;intros.
        simpl in H2;unfold optbind in H2;ex_match;inv H2.
        unfold Mem.alloc in R0;inv R0;inv H0;econstructor;FMemLemmas.gmem_unfolds.
        {
          split;intro;auto;
            try solve[destruct H;[left; congruence|right; apply eq_loc_validity;auto]].
        }
        {
          intros.
          rewrite !PMap.gso;try congruence. eauto.
        }
        {
          rewrite !PMap.gso;try congruence. eauto.
        }
        intros. apply H6 in H7 as ?.
        unfold tupdate in H8;ex_match2.
      }
    }
    {
      unfold buf_alloc_invalid,GMem.valid_block;simpl.
      intros. inv H2;simpl in *. inv H1.
      unfold tupdate in H4. destruct peq;subst.
      {
        apply in_app_or in H4 as [|].
        {
          inv H. inv meminv_Ic0. eapply Ic_buf_alloc_invalid;eauto.
        }
        {
          destruct H1;inv H1.
          inv H0. inv H12.
          assert(~ In (Mem.nextblock fm')(Mem.validblocks fm')).
          apply next_block_not_in_validblock.
          intro;contradict H2.
          inv H. inv meminv_Ic0. simpl in *.
          eapply apply_buffer_forward in Ic_buf_alloc_invalid;eauto.
          Focus 2. simpl. erewrite List.app_nil_r;eauto.
          simpl in *. eapply Ic_buf_alloc_invalid;eauto.
        }
      }
      {
        inv H. inv meminv_Ic0.
        eapply Ic_buf_alloc_invalid;eauto.
      }
    }
    {
      rewrite strip_fold. inv H1.
      inversion H2;subst.
      inversion H as [[_ _ _ _ ?] _ _ _].
      eapply alloc_norep_preserve;eauto.
      intros.
      destruct (peq t t0).
      subst.
      pose proof tsoalloc_thread_local_norep _ _ _ _ _ H2 _ _ _ H1. congruence.
      simpl in *.
      intro;subst.
      contradict H3. econstructor;eauto.
      unfold conflict_bi. simpl.
      unfold tsoalloc_fp,uncheck_alloc_fp.
      apply FP.conflict_ff. Locs.unfolds;simpl.
      rewrite H9. exists (Mem.nextblock sfm),0. ex_match2;auto.
    }
  }

  Esimpl;eauto.
  {
    econstructor;eauto.
    {
      unfold sep_obj_client_block.
      intros.
      
      destruct (peq b (tres)).
      {
        subst.
        unfold Mem.alloc in R0;inv R0;unfold strip in *;simpl in *.
        inv H4. simpl in *. rewrite PMap.gss in *.
        ex_match2.
      }
      {
        eapply alloc_obj_mem_unchg in H4 as ?;eauto.
        eapply alloc_clt_mem_unchg in H5 as ?;eauto.
        inv H0.
        inv H. eapply meminv_sep0;eauto.
      }
    }
    {
      unfold rel_tm_gm_vb;simpl;intros.
      unfold tupdate in H5;ex_match2.
      inv H2. simpl in *. apply TSOMemLemmas.apply_buffer_split in H5. Hsimpl.
      rewrite H11 in H2;inv H2.
      simpl in H4;unfold optbind in H4;ex_match. inv H4;simpl.
      inv H0. inv H1.
      unfold Mem.alloc in R0;inv R0;simpl.
      inv H13. unfold GMem.validblocks,strip.
      inv H. unfold rel_tm_gm_vb in meminv_rel_vb0.
      exploit meminv_rel_vb0. 
      2: simpl; eauto. eauto.
      intro.
      
      split;try solve[intros[];[ left; congruence| right; eapply H;eauto]].
    }
    {
      inv H. 
      unfold tm_alloc_not_fl in *.
      simpl.
      intros.
      unfold tupdate in H4;ex_match2.
      eapply meminv_alloc_local0 in H4;eauto.
    }
  }
  {
    unfold Gc;simpl.
    Esimpl;eauto.
    inv H;auto.
    {
      intros. inv H0. split;intro;eapply alloc_obj_mem_unchg in R0;apply R0;eauto.
    }
    {
      intros. inv H0.
      assert(b<> (Mem.nextblock sfm)).
      intro;subst.
      eapply alloc_obj_mem_unchg in R0 as R2;try apply R2 in H4;eauto.
      inv H4. unfold Mem.alloc in R0;inv R0. unfold strip in *;simpl in *.
      rewrite PMap.gss in *. congruence.

      unfold Mem.alloc in R0;inv R0;econstructor;FMemLemmas.gmem_unfolds.
      {
        split;intro;try congruence. right;auto. destruct H5;congruence.
      }
      {
        rewrite PMap.gso;auto.
      }
      rewrite PMap.gso;auto.
    }
    {
      inv H1. inv H2. auto.
    }
    {
      instantiate(1:=BufferedAlloc tres lo hi :: nil).
      inv H2. simpl. auto.
    }
    {
      intros. inv H4. destruct H5.
      Focus 2. inv H4.
      intro. eapply alloc_obj_mem_unchg in R0 as ?;eauto.
      inv H0.
      eapply H7 in H5.
      inv H6. inv H5.
      unfold Mem.alloc in R0;inv R0. simpl in *.

      rewrite PMap.gss in *. congruence.
    }
    {
      eapply FMemLemmas.alloc_forward;eauto.
    }
  }
Qed.
Local Opaque Mem.alloc.

Lemma store_refine:
  forall chunk b ofs v,
    let opSrc := fun sfm fp res sfm' =>
                   Mem.store chunk sfm b ofs v = Some sfm' /\ fp = store_fp chunk b ofs in
    let opTgt := fun tbfm fp res tbfm' =>
                   tsostore chunk tbfm b ofs v = Some tbfm' /\ fp = store_fp chunk b ofs in
    @memops_refine unit opSrc opTgt.
Proof.
  Local Transparent Mem.store.
  intros.
  unfold memops_refine. intros.
  assert( (forall sfp sres sfm', ~ opSrc sfm sfp sres sfm') \/  ~(forall sfp sres sfm', ~ opSrc sfm sfp sres sfm')).
  apply Classical_Prop.classic.
  destruct H3;auto.
  do 3 apply Classical_Pred_Type.not_all_ex_not in H3 as [].
  apply Classical_Prop.NNPP in H3.
  left.
  assert(TRANS: opSrc sfm x tres x1).
  inv H3. econstructor;eauto.
  clear H3. rename TRANS into H3.
  exists x,tres,x1. split;auto.
  assert(fpmatchc x tfp).
  {
    unfold opTgt,opSrc in *. Hsimpl;subst.
    apply FP.subset_refl.
  }
  assert( conflictc t tfp bufs \/ ~conflictc t tfp bufs).
  apply Classical_Prop.classic.
  destruct H5;[right|left];auto.
  unfold opTgt,opSrc in *. Hsimpl;subst. simpl.
  assert(R:forall ofs0,  ofs <= ofs0 < ofs + size_chunk chunk ->  forall t' : tid, t' <> t -> ~ in_buffer (bufs t') b ofs0).
  {
    unfold tsostore in H2. inv H2.
    unfold Mem.store in *.
    ex_match2. inv H3.
    intros.
    intro. contradict H5. inv H6.
    econstructor;eauto.
    revert H7 H2;clear;intros.
    unfold conflict_bi,store_fp.
    pose proof size_chunk_pos chunk.
    inv H7;simpl;unfold uncheck_alloc_fp,free_fp,store_fp.
    apply FP.conflict_wf. Locs.unfolds;simpl.
    exists b,ofs. unfold range_locset;ex_match2;auto.
    destruct zle,zlt;auto;omega.
    apply FP.conflict_wf. Locs.unfolds;simpl.
    exists b,ofs0. unfold range_locset;ex_match2;auto. rewrite <- add_minus_eq.
    destruct zle,zlt,zle,zlt;auto;try omega. simpl.
    apply FP.conflict_ww. Locs.unfolds;simpl.
    exists b,ofs0. unfold range_locset;ex_match2;auto.
    destruct zle,zlt,zle,zlt;auto;omega.
  }
  enough(Gc t sgm {| tso_buffers := bufs; memory := tgm |} (strip x1)
    {|
    tso_buffers := tupdate t (tbuffer tbfm') bufs;
    memory := strip (fmemory tbfm') |}).
  Esimpl;eauto.
  {
    econstructor.
    unfold Gc in H6;Hsimpl;auto.
    {
      unfold sep_obj_client_block;intros.
      inv H. exploit meminv_sep0.
      instantiate(2:=b0). instantiate(1:=ofs1).
      unfold Mem.store in H3;ex_match;inv H3;destruct H7;unfold strip in *;simpl in *.
      inv H0. econstructor;eauto.
      
      instantiate(1:=ofs2).
      unfold Mem.store in H3;ex_match;inv H3;destruct H8;unfold strip in *;simpl in *.
      inv H0. econstructor;eauto.
      auto.
    }
    {
      unfold rel_tm_gm_vb.
      simpl.
      intros.
      unfold Mem.store in H3;ex_match;inv H3.
      simpl.
      unfold tupdate in H8;ex_match2.
      unfold tsostore in H2;inv H2. simpl in *.
      apply TSOMemLemmas.apply_buffer_split in H8;Hsimpl.
      inv H.
      exploit meminv_rel_vb0. eauto. simpl. inv H1. eauto.
      instantiate(1:=n). intro.

      inv H0. unfold strip in H;simpl in H.
      simpl in H3. unfold optbind in H3;ex_match.
      inv H3. unfold store in Hx1;ex_match;inv Hx1. simpl. tauto.
    }
    {
      inv H.
      unfold tm_alloc_not_fl in *. simpl in *.
      intros. unfold tupdate in H7;ex_match2.
      eapply meminv_alloc_local0;eauto.
    }
  }
  unfold Gc.
  assert( forall (b0 : block) (ofs0 : Z), obj_mem sgm b0 ofs0 <-> obj_mem (strip x1) b0 ofs0).
  {
    intros. inv H0.
    unfold Mem.store in H3;ex_match;inv H3.
    split;intros[];unfold strip;constructor;simpl;auto.
  }
  assert( forall (b0 : block) (ofs0 : Z),
            obj_mem sgm b0 ofs0 -> eq_on_loc b0 ofs0 sgm (strip x1)).
  {
    intros. inv H0.
    unfold Mem.store in H3;ex_match;inv H3.
    unfold strip;simpl.
    econstructor;FMemLemmas.gmem_unfolds;try tauto.
    inv H7;simpl in *.
    rewrite PMap.gsspec. ex_match2;subst.
    rewrite Mem.setN_other;auto.
    intros.
    intro;subst.
    inversion v0.
    rewrite encode_val_length,<-size_chunk_conv in H7.
    specialize (H8 ofs0 H7).
    unfold Mem.perm in H8. rewrite H3 in H8. inv H8.
  }
  assert(R2:  forall (b0 : block) (ofs0 : Z),
            in_buffer (BufferedStore chunk b ofs v :: nil) b0 ofs0 -> ~ obj_mem sgm b0 ofs0).
  {
    intros. 
    intro. inv H9.
    inv H8. inv H9. 2:inv H8.
    inv H12. unfold Mem.store in H3. ex_match. inversion v0.
    inv H0. unfold strip in H11;simpl in H11. specialize (H8 _ H17).
    unfold Mem.perm in H8.
    rewrite H11 in H8;inv H8.
  }
  Esimpl;eauto.
  inv H;auto.
  {
    constructor;simpl.
    {
      inv H. inv meminv_Ic0.
      simpl in *.
      unfold tsostore in H2;inv H2. simpl in *.
      eapply unbuffer_safe_append_preserve with(bi:=BufferedStore chunk b ofs v)(t:=t) in Ic_ub_safe;eauto. simpl in Ic_ub_safe.
      unfold tsoupd in Ic_ub_safe. simpl in Ic_ub_safe.
      inv H1;auto.
      simpl.
      {
        eapply unbuffer_safe_apply_buffer with(t:=t) in Ic_ub_safe.
        Hsimpl.
        unfold TSOAuxDefs.buffer_safe.
        erewrite TSOAuxDefs.apply_buffer_app_eq;eauto.
        assert(forall ofs0,  ofs <= ofs0 < ofs + size_chunk chunk-> eq_on_loc b ofs0 sgm x).
        intros. assert(~obj_mem sgm b ofs0).
        eapply R2. econstructor. left;eauto.
        econstructor;eauto.
        eapply Ic_mem_eq;eauto.
        simpl. unfold optbind. ex_match2;eauto. inv H0;inv H1.
        revert H2 H3 Hx;clear;unfold Mem.store,store;intros;ex_match2.
        clear Hx Hx1 Hx0 H3.  contradict n.
        inv v0;split;auto.
        unfold range_perm ;intros.
        specialize (H _ H1).
        specialize (H2 _ H1).
        inversion H2 as [_ ? _].
        unfold Mem.perm in H. clear H2.
        unfold strip in *;simpl in *.
        rewrite eq_loc_perm in H.
        unfold Mem.perm_order' in *.
        exploit GMem.access_max.
        instantiate(2:=x). instantiate(2:=b). instantiate(1:=ofs0).
        unfold Memperm.perm_order'';intro. ex_match2.
        inv H;inv H2;constructor.
      }
      {
        unfold inv_bi.
        compute[tso_buffers].
        intros.
        apply fpsmile_nfconflict. apply FP.smile_conflict_compat.
        intro. contradict H5.
        econstructor;eauto.
      }
    }
    {
      intros.
      assert(~obj_mem sgm b0 ofs0).
      intro;contradict H9.
      eapply H6;eauto.
      inversion H as [? _ _ _].
      inversion meminv_Ic0 as [_ ? _ ].
      unfold tupdate in H10,H11;ex_match2;subst.
      {
        unfold tsostore in H2;inv H2;simpl in *.
        inv H11.
        apply in_app_or in H2.
        destruct H2.
        {
          exploit Ic_no_conflict_bi;eauto. econstructor;eauto.
        }
        simpl in H2. destruct H2;try contradiction. subst.
        inv H13.
        exploit R;eauto.
      }
      {
        unfold tsostore in H2;inv H2;simpl in *.
        inv H10.
        apply in_app_or in H2.
        destruct H2.
        {
          exploit Ic_no_conflict_bi;eauto. econstructor;eauto.
        }
        simpl in H2. destruct H2;try contradiction. subst.
        inv H13.
        exploit R;eauto.
      }
      {
        simpl in *.
        eapply Ic_no_conflict_bi in H8;eauto.
      }
    }
    {
      inversion H as [? _ _ _].
      inversion meminv_Ic0 as [_ _ ?  ].
      simpl in *.
      intros.
      assert(~obj_mem sgm b0 ofs0).
      intro;contradict H9;eapply H6;eauto.
      unfold tsostore in H2;inv H2. simpl in *.
      unfold tupdate in H8;ex_match2.
      {
        apply TSOMemLemmas.apply_buffer_split in H8;Hsimpl.
        inv H1. inv H0.
        exploit Ic_mem_eq;eauto.
        intros. intro. apply H10 in H0 as ?. contradict H13.
        inv H12. econstructor;eauto.
        unfold tupdate. ex_match2.
        revert H3 H8;clear;simpl;intros.
        unfold optbind in H8;ex_match. inv H8.
        unfold Mem.store,store in *. ex_match.
        inv Hx. inv H3.
        unfold strip;simpl.
        inv H.
        econstructor;FMemLemmas.gmem_unfolds; auto.
        rewrite !PMap.gsspec;ex_match2.
        destruct (range_locset b ofs (size_chunk chunk) b ofs0) eqn:?.
        {
          unfold range_locset in Heqb1. ex_match2.
          destruct zle,zlt;inv Heqb1.
          erewrite FMemLemmas.setN_geteq2;eauto.
          rewrite encode_val_length,<- size_chunk_conv. auto.
        }
        {
          unfold range_locset in Heqb1. ex_match2.
          assert( forall r : Z, ofs <= r < ofs + Z.of_nat (length (encode_val chunk v)) -> r <> ofs0).  rewrite encode_val_length,<- size_chunk_conv. 
          intros. intro;subst. destruct zle,zlt;auto;omega.
          erewrite !Mem.setN_other;eauto.
          congruence.
        }
      }
      {
        inv H0;inv H1.
        exploit Ic_mem_eq;eauto.
        intros. 
        apply H10 in H1 as ?. unfold tupdate in H2. ex_match2.
        intro;contradict H2.
        inv H12;econstructor;eauto. apply in_or_app;auto.

        intro. eapply eq_on_loc_trans;eauto.
        assert(t<>t0). auto.
        specialize (H10 t H2).
        assert(~  in_buffer_item ( BufferedStore chunk b ofs v) b0 ofs0).
        intro;contradict H10. econstructor;eauto.
        unfold tupdate;ex_match2. apply in_or_app. right;auto. left;auto.
        revert H12 H3;clear;unfold Mem.store;intros. ex_match;inv H3.
        econstructor;simpl;FMemLemmas.gmem_unfolds;auto.
        tauto.
        destruct (range_locset b ofs (size_chunk chunk) b0 ofs0) eqn:?.
        {
          unfold range_locset in Heqb1. ex_match2.
          contradict H12.
          subst. econstructor.
          destruct zle,zlt;auto;inv Heqb1.
        }
        {
          unfold range_locset in Heqb1.
          rewrite PMap.gsspec.
          ex_match2;subst.
          erewrite !Mem.setN_other;eauto.
          rewrite encode_val_length,<-size_chunk_conv.
          intros. intro;subst. destruct zle,zlt;auto;omega.
        }
      }
    }
    {
      inversion H as [[ _ _ _ ? _ ] _ _ _ ].
      unfold tsostore in H2;inv H2;simpl. inv H1;auto.
      unfold buf_alloc_invalid,tupdate;simpl;intros;ex_match2;eauto.
      apply in_app_or in H1 as [|];eauto.
      destruct H1;try discriminate. inv H1.
    }
    {
      inversion H as [[ _ _ _ _ ? ] _ _ _ ].
      unfold tsostore in H2;inv H2;simpl. inv H1;auto.
      eapply alloc_norep_preserve;eauto.
    }
  }
  simpl. unfold tsostore in H2;inv H2;auto. inv H1;auto.
  simpl. unfold tsostore in H2;inv H2;simpl;eauto.
  eapply FMemLemmas.store_forward;eauto.
Qed.
Local Opaque Mem.store.

Lemma free_refine:
  forall b lo hi,
    let opSrc := fun sfm fp res sfm' =>
                   Mem.free sfm b lo hi = Some sfm' /\ fp = free_fp b lo hi in
    let opTgt := fun tbfm fp res tbfm' =>
                   tsofree tbfm b lo hi = Some tbfm' /\ fp = free_fp b lo hi in
    @memops_refine unit opSrc opTgt.
Proof.
  Local Transparent Mem.free.
  intros.
  unfold memops_refine. intros.
  assert( (forall sfp sres sfm', ~ opSrc sfm sfp sres sfm') \/  ~(forall sfp sres sfm', ~ opSrc sfm sfp sres sfm')).
  apply Classical_Prop.classic.
  destruct H3;auto.
  do 3 apply Classical_Pred_Type.not_all_ex_not in H3 as [].
  apply Classical_Prop.NNPP in H3.
  left.
  assert(TRANS: opSrc sfm x tres x1).
  inv H3. econstructor;eauto.
  clear H3. rename TRANS into H3.
  exists x,tres,x1. split;auto.
  assert(fpmatchc x tfp).
  {
    unfold opTgt,opSrc in *. Hsimpl;subst.
    apply FP.subset_refl.
  }
  assert( conflictc t tfp bufs \/ ~conflictc t tfp bufs).
  apply Classical_Prop.classic.
  destruct H5;[right|left];auto.
  unfold opTgt,opSrc in *. Hsimpl;subst. simpl.
  assert(R:forall ofs0,  lo <= ofs0 < hi ->  forall t' : tid, t' <> t -> ~ in_buffer (bufs t') b ofs0).
  {
    unfold tsofree in H2. inv H2.
    unfold Mem.free in *.
    ex_match2. inv H3.
    intros.
    intro. contradict H5. inv H6.
    econstructor;eauto.
    revert H7 H2;clear;intros.
    unfold conflict_bi,store_fp.
    inv H7;simpl;unfold uncheck_alloc_fp,free_fp,store_fp.
    apply FP.conflict_ff. Locs.unfolds;simpl.
    exists b,ofs0. unfold range_locset;ex_match2;auto.
    destruct zle,zlt;auto;omega.
    apply FP.conflict_ff. Locs.unfolds;simpl.
    exists b,ofs0. unfold range_locset;ex_match2;auto. rewrite <- add_minus_eq.
    destruct zle,zlt,zle,zlt;auto;try omega. simpl.
    apply FP.conflict_wf. Locs.unfolds;simpl.
    exists b,ofs0. unfold range_locset;ex_match2;auto.
    destruct zle,zlt,zle,zlt;auto;omega.
  }
  enough(Gc t sgm {| tso_buffers := bufs; memory := tgm |} (strip x1)
    {|
    tso_buffers := tupdate t (tbuffer tbfm') bufs;
    memory := strip (fmemory tbfm') |}).
  Esimpl;eauto.
  {
    unfold Gc in H6. Hsimpl;auto. simpl in *.
    econstructor;eauto.
    {
      unfold sep_obj_client_block.
      intros.
      apply H8 in H14 as ?.
      assert(client_mem sgm b0 ofs2).
      {
        inv H0.
        unfold Mem.free in H3;ex_match2. inv H3.
        unfold Mem.unchecked_free,strip in H15;destruct H15;simpl in *.
        rewrite PMap.gsspec in *.
        destruct (peq b0 b) eqn:?;ex_match2;subst;split;auto.
      }
      inv H. eapply meminv_sep0;eauto.
    }
    {
      unfold rel_tm_gm_vb;simpl.
      intros. unfold tsofree in H2;inv H2. simpl in *.
      
      inversion H as [? _ ?  _].
      inversion meminv_Ic0 as [? _ _].
      simpl in *.
      eapply TSOMemLemmas.unbuffer_safe_apply_buffer with(t:=t) in Ic_ub_safe.
      Hsimpl.
      unfold tupdate in H2,H15;ex_match2.
      apply TSOMemLemmas.apply_buffer_split in H15. Hsimpl.
      rewrite H2 in H10;inv H10.

      simpl in H14. unfold optbind in H14;ex_match. inv H14.
      unfold rel_tm_gm_vb in meminv_rel_vb0.
      exploit meminv_rel_vb0;eauto. instantiate(1:=n).
      revert Hx0 H3. inv H0;inv H1.
      clear. unfold free,Mem.free,unchecked_free;intros;ex_match2.
      inv Hx0. inv H3. simpl.
      tauto.
    }
    {
      inversion H as [_ _ _ ?].
      unfold tm_alloc_not_fl in *. simpl in *.
      intros.
      unfold tupdate in H15;ex_match2.
      eauto.
    }
  }
  {
    unfold Gc.
    assert( forall (b0 : block) (ofs0 : Z), obj_mem sgm b0 ofs0 <-> obj_mem (strip x1) b0 ofs0).
    {
      intros. inv H0.
      eapply free_obj_mem_unchg in H3;eauto.
    }
    assert( forall (b0 : block) (ofs0 : Z),
              obj_mem sgm b0 ofs0 -> eq_on_loc b0 ofs0 sgm (strip x1)).
    {
      intros. inv H0.
      unfold Mem.free in H3;ex_match;inv H3.
      unfold strip;simpl.
      econstructor;FMemLemmas.gmem_unfolds;try tauto.
      inv H7;simpl in *.
      rewrite PMap.gsspec. ex_match2;subst.
      exfalso.
      clear H6.
      exploit r. instantiate(1:=ofs0).
      destruct zle,zlt;auto;inv Hx1.
      unfold Mem.perm. rewrite H3. inversion 1.
    }
    assert(R2:  forall (b0 : block) (ofs0 : Z),
              in_buffer (BufferedFree b lo hi  :: nil) b0 ofs0 -> ~ obj_mem sgm b0 ofs0).
    {
      intros. 
      intro. inv H9.
      inv H8. inv H9. 2:inv H8.
      inv H12. unfold Mem.free in H3. ex_match.  inv H3. 
      inv H0. unfold strip in H11;simpl in H11. specialize (r _ H16) as ?.
      unfold Mem.perm in H0.
      rewrite H11 in H0;inv H0.
    }
    Esimpl;eauto.
    inv H;auto.
    {
      constructor;simpl .
      {
        inv H. inv meminv_Ic0.
        simpl in *.
        unfold tsofree in H2;inv H2. simpl in *.
        eapply unbuffer_safe_append_preserve with(bi:=BufferedFree b lo hi)(t:=t) in Ic_ub_safe;eauto. simpl in Ic_ub_safe.
        unfold tsoupd in Ic_ub_safe. simpl in Ic_ub_safe.
        inv H1;auto.
        simpl.
        {
          eapply TSOMemLemmas.unbuffer_safe_apply_buffer with(t:=t) in Ic_ub_safe.
          Hsimpl.
          unfold TSOAuxDefs.buffer_safe.
          erewrite TSOAuxDefs.apply_buffer_app_eq;eauto.
          assert(forall ofs0,  lo <= ofs0 < hi-> eq_on_loc b ofs0 sgm x).
          intros. assert(~obj_mem sgm b ofs0).
          eapply R2. econstructor. left;eauto.
          econstructor;eauto.
          eapply Ic_mem_eq;eauto.
          simpl. unfold optbind. ex_match2;eauto. inv H0;inv H1.
          revert H2 H3 Hx;clear;unfold Mem.free,free;intros;ex_match2.
          clear Hx Hx1 Hx0 H3.  contradict n.
          unfold range_perm ;intros.
          specialize (r _ H).
          specialize (H2 _ H).
          inversion H2 as [_ ? _].
          unfold Mem.perm in r. clear H2.
          unfold strip in *;simpl in *.
          rewrite eq_loc_perm in r.
          unfold Mem.perm_order' in *.
          exploit GMem.access_max.
          instantiate(2:=x). instantiate(2:=b). instantiate(1:=ofs).
          unfold Memperm.perm_order'';intro. ex_match2.
          inv r;inv H0;constructor.
        }
        {
          unfold inv_bi.
          compute[tso_buffers].
          intros.
          apply fpsmile_nfconflict. apply FP.smile_conflict_compat.
          intro. contradict H5.
          econstructor;eauto.
        }
      }
      {
        intros.
        assert(~obj_mem sgm b0 ofs).
        intro;contradict H9.
        eapply H6;eauto.
        inversion H as [? _ _ _].
        inversion meminv_Ic0 as [_ ? _ ].
        unfold tupdate in H10,H11;ex_match2;subst.
        {
          unfold tsofree in H2;inv H2;simpl in *.
          inv H11.
          apply in_app_or in H2.
          destruct H2.
          {
            exploit Ic_no_conflict_bi;eauto. econstructor;eauto.
          }
          simpl in H2. destruct H2;try contradiction. subst.
          inv H13.
          exploit R;eauto.
        }
        {
          unfold tsofree in H2;inv H2;simpl in *.
          inv H10.
          apply in_app_or in H2.
          destruct H2.
          {
            exploit Ic_no_conflict_bi;eauto. econstructor;eauto.
          }
          simpl in H2. destruct H2;try contradiction. subst.
          inv H13.
          exploit R;eauto.
        }
        {
          simpl in *.
          eapply Ic_no_conflict_bi in H8;eauto.
        }
      }
      {
        inversion H as [? _ _ _].
        inversion meminv_Ic0 as [_ _ ?  ].
        simpl in *.
        intros.
        assert(~obj_mem sgm b0 ofs).
        intro;contradict H9;eapply H6;eauto.
        unfold tsofree in H2;inv H2. simpl in *.
        unfold tupdate in H8;ex_match2.
        {
          apply TSOMemLemmas.apply_buffer_split in H8;Hsimpl.
          inv H1. inv H0.
          exploit Ic_mem_eq;eauto.
          intros. intro. apply H10 in H0 as ?. contradict H13.
          inv H12. econstructor;eauto.
          unfold tupdate. ex_match2.
          revert H3 H8;clear;simpl;intros.
          unfold optbind in H8;ex_match. inv H8.
          unfold Mem.free,free in *. ex_match.
          inv Hx. inv H3.
          unfold strip;simpl.
          inv H.
          econstructor;FMemLemmas.gmem_unfolds; auto.
          rewrite !PMap.gsspec;ex_match2;subst;auto.
        }
        {
          inv H0;inv H1.
          exploit Ic_mem_eq;eauto.
          intros. 
          apply H10 in H1 as ?. unfold tupdate in H2. ex_match2.
          intro;contradict H2.
          inv H12;econstructor;eauto. apply in_or_app;auto.

          intro. eapply eq_on_loc_trans;eauto.
          assert(t<>t0). auto.
          specialize (H10 t H2).
          assert(~  in_buffer_item ( BufferedFree b lo hi) b0 ofs).
          intro;contradict H10. econstructor;eauto.
          unfold tupdate;ex_match2. apply in_or_app. right;auto. left;auto.
          revert H12 H3;clear;unfold Mem.free;intros. ex_match;inv H3.
          econstructor;simpl;FMemLemmas.gmem_unfolds;auto.
          tauto.
          destruct (range_locset b lo (hi-lo) b0 ofs) eqn:?.
          {
            unfold range_locset in Heqb1. ex_match2.
            contradict H12.
            subst. econstructor. rewrite <- add_minus_eq in Heqb1.
            destruct zle,zlt;auto;inv Heqb1.
          }
          {
            unfold range_locset in Heqb1.
            rewrite PMap.gsspec.
            ex_match2;subst.
            rewrite <- add_minus_eq in Heqb1. congruence.
          }
        }
      }
      {
        inversion H as [[ _ _ _ ? _ ] _ _ _ ].
        unfold tsofree in H2;inv H2;simpl. inv H1;auto.
        unfold buf_alloc_invalid,tupdate;simpl;intros;ex_match2;eauto.
        apply in_app_or in H1 as [|];eauto.
        destruct H1;try discriminate. inv H1.
      }
      {
        inversion H as [[ _ _ _ _ ? ] _ _ _ ].
        unfold tsofree in H2;inv H2;simpl. inv H1;auto.
        eapply alloc_norep_preserve;eauto.
      }
    }
    simpl. unfold tsofree in H2;inv H2;auto. simpl. inv H1;auto.
    simpl. unfold tsofree in H2;inv H2;auto.
    eapply FMemLemmas.free_forward;eauto.
  }
Qed.
Local Opaque Mem.free.

Lemma load_refine:
  forall chunk b ofs,
    let opSrc := fun sfm fp v sfm' =>
                   sfm = sfm' /\ Mem.load chunk sfm b ofs = Some v /\ fp = load_fp chunk b ofs in
    let opTgt := fun tbfm fp v tbfm' =>
                   tbfm = tbfm' /\ tsoload chunk tbfm b ofs = Some v /\ fp = load_fp chunk b ofs in
    @memops_refine val opSrc opTgt.
Proof.
  Local Transparent Mem.load.

  intros.
  unfold memops_refine. intros.
  assert( (forall (sfp : footprint) (sres : val) (sfm' : mem), ~ opSrc sfm sfp sres sfm') \/  ~(forall (sfp : footprint) (sres : val) (sfm' : mem), ~ opSrc sfm sfp sres sfm')).
  apply Classical_Prop.classic.
  destruct H3;auto.
  do 3 apply Classical_Pred_Type.not_all_ex_not in H3 as [].
  apply Classical_Prop.NNPP in H3.
  left.
  exists x,x0,x1. split;auto.
  assert(fpmatchc x tfp).
  {
    unfold opTgt,opSrc in *. Hsimpl;subst.
    apply FP.subset_refl.
  }
  assert( conflictc t tfp bufs \/ ~conflictc t tfp bufs).
  apply Classical_Prop.classic.
  destruct H5;[right|left];auto.
  unfold opTgt,opSrc in *. Hsimpl;subst. simpl.
  assert(R:forall ofs0,  ofs <= ofs0 < ofs + size_chunk chunk ->  forall t' : tid, t' <> t -> ~ in_buffer (bufs t') b ofs0).
  {
    unfold tsoload in H8. ex_match2.
    unfold Mem.load,load in *.
    ex_match2. inv H8;inv H6.
    f_equal.
    inv H. inv meminv_Ic0.
    intros. simpl.
    intro. contradict H5. inv H3.
    econstructor;eauto.
    revert H6 H;clear;intros.
    unfold conflict_bi,load_fp.
    pose proof size_chunk_pos chunk.
    inv H6;simpl;unfold uncheck_alloc_fp,free_fp,store_fp.
    apply FP.conflict_rf. Locs.unfolds;simpl.
    exists b,ofs. unfold range_locset;ex_match2;auto.
    destruct zle,zlt;auto;omega.
    apply FP.conflict_rf. Locs.unfolds;simpl.
    exists b,ofs0. unfold range_locset;ex_match2;auto. rewrite <- add_minus_eq.
    destruct zle,zlt,zle,zlt;auto;try omega. simpl.
    apply FP.conflict_rw. Locs.unfolds;simpl.
    exists b,ofs0. unfold range_locset;ex_match2;auto.
    destruct zle,zlt,zle,zlt;auto;omega.
  }
  assert(x0 = tres).
  {
    unfold tsoload in H8. ex_match2.
    unfold Mem.load,load in *.
    ex_match2. inv H8;inv H6.
    f_equal.
    inv H. inv meminv_Ic0.

    apply FMemLemmas.get_eq_getN_eq.
    intros. rewrite <-size_chunk_conv in H.
    
    exploit Ic_mem_eq.
    simpl. inv H1;eauto.
    {
      instantiate(1:=ofs0). instantiate(1:=b).
      intros[]. inversion v. specialize (H6 ofs0 H).
      inv H0. unfold strip in H3;simpl in H3. unfold Mem.perm in H6.
      rewrite H3 in H6. inv H6.
    }
    {
      simpl;eauto.
    }
    intro.
    inv H2. inv H0;auto.
  }
  do 3 (split;auto).
  assert(Gc  t sgm {| tso_buffers := bufs; memory := tgm |} (strip x1)
             {| tso_buffers := tupdate t (bufs t) bufs; memory := strip tfm |}).
  {
    unfold Gc.
    Esimpl.
    inv H;auto.
    rewrite TSOMemLemmas.tupdate_same_eq;auto. inv H;inv H0;inv H1;auto.
    inv H0;tauto.
    inv H0. intros. inv H1. econstructor;FMemLemmas.gmem_unfolds;try tauto;auto.
    inv H1;auto.
    simpl. instantiate(1:=nil). rewrite app_nil_r;auto.
    intros. inv H3. inv H7.
    inv H0. apply GMem.forward_refl.
  }
  split;auto.
  inv H0;inv H1.
  rewrite TSOMemLemmas.tupdate_same_eq;auto.
Qed.

Local Opaque Mem.load.
Lemma meminv_client_loc_forward:
  forall sfm tfm bufs t b ofs tgm',
    let fl := Mem.freelist sfm in
    let sm := strip sfm in
    let tm := strip tfm in
    Mem.freelist sfm = Mem.freelist tfm ->
    meminv t fl sm bufs tm ->
    client_mem sm b ofs ->
    apply_buffer (bufs t) tm = Some tgm' ->
    GMem.valid_block tgm' b ->
    GMem.perm sm b ofs Memperm.Cur Memperm.Nonempty ->
    GMem.perm tgm' b ofs Memperm.Cur Memperm.Nonempty.
Proof.
  intros.
  assert((exists t, in_buffer (bufs t) b ofs) \/ ~ (exists t, in_buffer (bufs t) b ofs)).
  apply Classical_Prop.classic.
  destruct H5.
  {
    Hsimpl.
    destruct (peq x t).
    {
      subst.
      inv H0. inv meminv_Ic0 ;simpl in*.
      exploit Ic_mem_eq;eauto.
      intros[].
      unfold GMem.perm in *. erewrite <- eq_loc_perm. eauto.
    }
    {
      inversion H0 as [[? ? ? ? ? ] ? _ _]; simpl in *.
      apply TSOMemLemmas.unbuffer_safe_apply_buffer with(t:=x) in Ic_ub_safe.
      Hsimpl.
      exploit Ic_mem_eq;eauto.
      intros[].
      assert(GMem.perm x0 b ofs Memperm.Cur Memperm.Nonempty).
      unfold GMem.perm in *;erewrite <- eq_loc_perm;eauto.
      exploit apply_buffer_forward;eauto. simpl. rewrite app_nil_r. eauto.
      simpl. intros[].
      Lemma apply_buffer_item_validity_preserve:
        forall m bi b m',
          apply_buffer_item bi m = Some m'->
          GMem.valid_block m b ->
          GMem.valid_block m' b.
      Proof.
        unfold GMem.valid_block; intros.
        destruct bi;simpl in H;unfold alloc,free,store in H;ex_match2;inv H;simpl;auto.
      Qed.
      assert(GMem.valid_block tm b).
      {
        assert(~ in_buffer (bufs t) b ofs). eauto.
        revert H8 H2 H3.  clear.
        generalize dependent (bufs t).
        generalize dependent tm. clear tfm t bufs.
        intros. revert b ofs tm tgm' H8 H2 H3.
        induction b0;intros;simpl in *.
        inv H2. auto.
        unfold optbind in H2;ex_match. 
        exploit IHb0;eauto. instantiate(1:=ofs). intros[];contradict H8. econstructor;eauto. right;auto.
        intro.
        clear H3 H2. destruct a;simpl in Hx;unfold alloc,free,store in Hx;ex_match;inv Hx;auto. unfold GMem.valid_block in H. simpl in *. destruct H;auto.
        subst. contradict H8. econstructor;eauto. left. eauto. econstructor;eauto.
      }
      {
        eapply alloc_forward in H8 as ?;eauto.
        assert(~ in_buffer (bufs t) b ofs). eauto.
        revert H10 H8 H2 H9. clear.
        generalize dependent (bufs t).
        generalize dependent tm. clear tfm t bufs.
        intros. revert b ofs tm tgm' H8 H2 H9 H10.
        induction b0;intros;simpl in *.
        inv H2. auto.
        unfold optbind in H2;ex_match.
        assert(GMem.valid_block g b). eapply apply_buffer_item_validity_preserve;eauto.
        exploit IHb0;eauto.
        {
          destruct a;simpl in Hx;unfold store,free,alloc in Hx;ex_match;inv Hx;simpl in *;auto.
          rewrite PMap.gsspec. ex_match2;auto. constructor.
          contradict H10. econstructor;eauto. left;eauto. subst. econstructor;eauto.

          rewrite PMap.gsspec. ex_match2;auto.
          contradict H10. econstructor;eauto. left;eauto. subst;econstructor;eauto.
          destruct zle,zlt;auto;inv Hx1;omega.
        }
        intros[];contradict H10. econstructor;eauto. right;auto.
      }
    }
  }
  {
    inv H0. inv meminv_Ic0. simpl in *.
    exploit Ic_mem_eq;eauto.
    intros[].
    unfold GMem.perm in *. erewrite <-eq_loc_perm;eauto.
  }
Qed.
Lemma tso_valid_pointer_matchc:
  forall tfm sm bufs t  b ofs,
    meminv t (Mem.freelist sm)(strip sm) bufs (strip tfm) ->
    Mem.freelist sm = Mem.freelist tfm->
    Mem.valid_pointer sm b ofs = true ->
    forall tgm',
      apply_buffer (bufs t)(strip tfm) = Some tgm'->
      GMem.valid_block tgm' b ->
      tso_valid_pointer {|tbuffer:=bufs t;fmemory := tfm|} b ofs = true.
Proof.
  unfold Mem.weak_valid_pointer,TSOAuxDefs.tso_weak_valid_pointer,Mem.valid_pointer,tso_valid_pointer;intros.
  inversion H as [[? _ _ _ _] _ _ _].
  eapply unbuffer_safe_apply_buffer with(t:=t) in Ic_ub_safe. Hsimpl.
  rewrite H4.
  destruct Mem.perm_dec,perm_dec;inv H1;auto.
  contradict n. eapply meminv_client_loc_forward;eauto.
  enough((GMem.mem_access (strip sm)) !! b ofs Memperm.Cur <> None).
  destruct (strip sm);split;auto. simpl in *. intro.
  specialize (access_max b ofs) as ?.
  rewrite H5 in H6. simpl in H6. ex_match2.
  unfold Mem.perm in p. unfold strip;simpl;intro.
  rewrite H1 in p;inv p.

  rewrite H2 in H4;inv H4;auto.
Qed.
Lemma tso_weak_valid_pointer_matchc:
  forall tfm sm bufs t  b ofs,
    meminv t (Mem.freelist sm)(strip sm) bufs (strip tfm) ->
    Mem.freelist sm = Mem.freelist tfm->
    Mem.weak_valid_pointer sm b ofs = true ->
    forall tgm',
      apply_buffer (bufs t)(strip tfm) = Some tgm'->
      GMem.valid_block tgm' b ->
      TSOAuxDefs.tso_weak_valid_pointer {|tbuffer:=bufs t;fmemory := tfm|} b ofs = true.
Proof.
  unfold Mem.weak_valid_pointer,TSOAuxDefs.tso_weak_valid_pointer.
  intros.
  apply orb_true_iff in H1 as [].
  erewrite tso_valid_pointer_matchc;eauto.
  erewrite tso_valid_pointer_matchc with(ofs :=ofs -1 );eauto with bool.
Qed.  
Lemma tso_weak_valid_pointer_fp_matchc:
  forall tfm sm bufs t  b ofs,
    meminv t (Mem.freelist sm)(strip sm) bufs (strip tfm) ->
    Mem.freelist sm = Mem.freelist tfm->
    TSOAuxDefs.tso_weak_valid_pointer {|tbuffer:=bufs t;fmemory := tfm|} b ofs = true ->
    Mem.weak_valid_pointer sm b ofs = true ->
    FP.subset (tso_weak_valid_pointer_fp {|tbuffer:=bufs t;fmemory := tfm|} b ofs)(weak_valid_pointer_fp sm b ofs).
Proof.
  intros.
  inversion H as [[? _ _ _ _] _ _ _].
  eapply unbuffer_safe_apply_buffer with(t:=t) in Ic_ub_safe;eauto.
  Hsimpl.
  unfold tso_weak_valid_pointer_fp,weak_valid_pointer_fp,valid_pointer_fp,Mem.valid_pointer;simpl.
  rewrite H3.
  ex_match2;try apply FP.subset_refl;constructor;try apply Locs.subset_refl;simpl;try apply FMemLemmas.range_locset_expend1_subset.
  destruct perm_dec,Mem.perm_dec ;inv Hx;inv Hx0.
  contradict n.
  eapply meminv_client_loc_forward;try exact H;eauto.
  enough((GMem.mem_access (strip sm)) !! b ofs Memperm.Cur <> None).
  destruct (strip sm);split;auto. simpl in *. intro.
  specialize (access_max b ofs) as ?.
  rewrite H5 in H6. simpl in H6. ex_match2.
  unfold Mem.perm in p. unfold strip;simpl;intro.
  rewrite H4 in p;inv p.
  
  unfold TSOAuxDefs.tso_weak_valid_pointer,tso_valid_pointer in H1. ex_match2. inv H3.
  apply orb_true_iff in H1 as [|];destruct perm_dec;try discriminate;eapply Memperm_validblock;eauto.
Qed.
Lemma meminv_compare_ints_fp_subset:
  forall sfm tfm bufs t v1 v2,
    let fl := Mem.freelist sfm in
    let sm := strip sfm in
    let tm := strip tfm in
    Mem.freelist sfm = Mem.freelist tfm ->
    meminv t fl sm bufs tm ->
    check_compare_ints v1 v2 sfm = true ->
    check_compare_ints_TSO v1 v2 (mktsofmem (bufs t) tfm) = true ->
    FP.subset (compare_ints_TSO_fp v1 v2 (mktsofmem (bufs t) tfm))
              (compare_ints_fp v1 v2 sfm).
Proof.
  clear. unfold check_compare_ints,check_compare_ints_TSO. intros.
  ex_match2.
  clear H1 H2.
  unfold compare_ints_fp,compare_ints_TSO_fp.
  apply FP.subset_parallel_union.
  {
    unfold tso_cmpu_bool_fp_total,Cop_fp.cmpu_bool_fp_total,Val.cmpu_bool in *;ex_match2;subst;try apply FP.subset_refl;compute["&&"] in *.
    eapply tso_weak_valid_pointer_fp_matchc;eauto.
    eapply tso_weak_valid_pointer_fp_matchc;eauto.
    ex_match2; eapply FP.subset_parallel_union;
      eapply tso_weak_valid_pointer_fp_matchc;eauto.
  }
  {
    unfold tso_cmpu_bool_fp_total,Cop_fp.cmpu_bool_fp_total,Val.cmpu_bool in *;ex_match2;subst;try apply FP.subset_parallel_union;try apply FP.subset_refl;compute["&&"] in *;try solve [eapply tso_weak_valid_pointer_fp_matchc;eauto].
    ex_match2;eapply tso_weak_valid_pointer_fp_matchc;eauto.
    ex_match2;eapply tso_weak_valid_pointer_fp_matchc;eauto.
  }
Qed.
Lemma meminv_compare_ints_not_conflict_eq:
  forall sfm tfm bufs t v1 v2 rs,
    let fl := Mem.freelist sfm in
    let sm := strip sfm in
    let tm := strip tfm in
    Mem.freelist sfm = Mem.freelist tfm ->
    meminv t fl sm bufs tm ->
    check_compare_ints v1 v2 sfm = true ->
    check_compare_ints_TSO v1 v2 (mktsofmem (bufs t) tfm) = true ->
    ~ conflictc t (compare_ints_TSO_fp v1 v2 (mktsofmem (bufs t) tfm)) bufs ->
    compare_ints v1 v2 rs sfm = compare_ints_TSO v1 v2 rs (mktsofmem (bufs t) tfm).
Proof.
  unfold compare_ints,compare_ints_TSO,check_compare_ints,check_compare_ints_TSO;intros.
  f_equal. f_equal. f_equal. f_equal.
  2: f_equal.
  {
    unfold Val.cmpu,Val.cmpu_bool in *.
    ex_match2;auto.
  }
  {
    unfold Val.cmpu,Val.cmpu_bool in *.
    ex_match2;auto.
  }
Qed.
Lemma meminv_extcall_arg:
  forall t fl sm tm sfm tfm rs a fp v,
    meminv t fl sm (tso_buffers tm) (memory tm) ->
    embed sm fl sfm ->
    embed (memory tm) fl tfm ->  
    extcall_arg_fp rs a fp ->
    extcall_arg rs {| tbuffer := tso_buffers tm t; fmemory := tfm |} a v ->
    (exists v',
        AsmLang.extcall_arg rs sfm a v' /\
        ((~ conflictc t fp (tso_buffers tm) /\ v' = v)
         \/ conflictc t fp (tso_buffers tm)))
    \/
    (forall v', ~ AsmLang.extcall_arg rs sfm a v').
Proof.
  intros. inv H3; inv H2.
  { left. eexists. split. repeat econstructor.
    left. split; auto using emp_not_conflictc. }
  { destruct Val.offset_ptr eqn:Haddr; try discriminate. simpl in H5.
    exploit load_refine; eauto.
    intros [(fp' & v' & _ & (_ & Hload & Hfp) & [(Hdrf & Hmatch & Hv & _) |Hrace]) |Habort];
      [left|left|right]; subst.
    eexists. split. econstructor. econstructor. eauto. rewrite Haddr. eauto.
    left. split; auto.
    eexists. split. econstructor. econstructor. eauto. rewrite Haddr. eauto.
    right. simpl. tauto.
    intros. intro C. inv C. rewrite Haddr in H7. eapply Habort. eauto. }
Qed.
  
Lemma meminv_extcall_arg_pair:
forall t fl sm tm sfm tfm rs a fp v,
    meminv t fl sm (tso_buffers tm) (memory tm) ->
    embed sm fl sfm ->
    embed (memory tm) fl tfm ->  
    extcall_arg_pair_fp rs a fp ->
    extcall_arg_pair rs {| tbuffer := tso_buffers tm t; fmemory := tfm |} a v ->
    (exists v',
        AsmLang.extcall_arg_pair rs sfm a v' /\
        ((~ conflictc t fp (tso_buffers tm) /\ v' = v)
         \/ conflictc t fp (tso_buffers tm)))
    \/
    (forall v', ~ AsmLang.extcall_arg_pair rs sfm a v').
Proof.
  intros. inv H3; inv H2.
  { exploit meminv_extcall_arg; eauto. intros [(v' & Harg & Hfp) | Habort]; [left|right].
    eexists. split; eauto. econstructor; eauto.
    intros. intro C. inv C. eapply Habort. eauto. }
  { eapply meminv_extcall_arg in H4; eauto.
    eapply meminv_extcall_arg in H5; eauto.
    destruct H4 as [(vhi' & Hhi & Hfp1) | Habort]; [|right; intros; intro C; inv C; eapply Habort; eauto].
    destruct H5 as [(vlo' & Hlo & Hfp2) | Habort]; [|right; intros; intro C; inv C; eapply Habort; eauto].
    left. eexists. split. econstructor; eauto.
    destruct Hfp1 as [[Hfp1 Hhi']|Hrace];[|right; eapply conflictc_union'; eauto].
    destruct Hfp2 as [[Hfp2 Hlo']|Hrace];[|right; eapply conflictc_union'; eauto].
    subst. left. split; auto. intro. eapply conflictc_union in H2; destruct H2; eauto. }
Qed.  

Lemma meminv_extcall_arguments:
  forall t fl sm tm sfm tfm rs sig args fp,
    meminv t fl sm (tso_buffers tm) (memory tm) ->
    embed sm fl sfm ->
    embed (memory tm) fl tfm ->
    extcall_arguments rs (mktsofmem (tso_buffers tm t) tfm) sig args ->
    extcall_arguments_fp rs sig fp ->
    (exists args',
        AsmLang.extcall_arguments rs sfm sig args' /\
        ((~ conflictc t fp (tso_buffers tm) /\ args' = args)
         \/ conflictc t fp (tso_buffers tm)))
    \/
    (forall args', ~ AsmLang.extcall_arguments rs sfm sig args').
Proof.
  clear. unfold extcall_arguments, extcall_arguments_fp, AsmLang.extcall_arguments.
  intros until sig. generalize (Conventions1.loc_arguments sig). clear.
  intros. revert fp H3. induction H2; intros fp Hfp; inv Hfp.
  left. eexists. split. econstructor. left; split; auto using emp_not_conflictc.
  exploit meminv_extcall_arg_pair; eauto. intros [(v' & Harg & A) | Habort]; [|right].
  exploit IHlist_forall2; eauto. intros [(args' & Hargs & B) | Habort]; [left|right].
  eexists. split. econstructor; eauto.
  destruct A as [[Hdrf Hv']|Hrace]; [|right].
  destruct B as [[Hdrf' Hargs']|Hrace']; [left|right].
  split; subst; auto. intro. apply conflictc_union in H4. destruct H4; eauto.
  eapply conflictc_union'; eauto. eapply conflictc_union'; eauto.
  intros; intro C; inv C; eapply Habort; eauto.
  intros. intro C; inv C; eapply Habort; eauto.
Qed.

Lemma store_args_refine:
  forall stk args tys,
    let opSrc := fun sfm fp (x:unit) sfm' =>
                   loadframe.store_args_fmem sfm stk args tys = Some sfm' /\
                   fp = loadframe.store_args_fp stk tys in
    let opTgt := fun tbfm fp (x:unit) tbfm' =>
                   store_args_fmem tbfm stk args tys = Some tbfm' /\
                   fp = loadframe.store_args_fp stk tys in
    memops_refine opSrc opTgt.
Proof.
  unfold loadframe.store_args_fmem, store_args_fmem,loadframe.store_args_fp.
  generalize 0. intros until tys. revert z args.
  induction tys; intros; unfold memops_refine; intros.
  { left. destruct H2. destruct args; simpl in *; inv H2. simpl.
    do 3 eexists. split. eauto. left. split. auto using emp_not_conflictc.
    split. apply FP.subset_refl. split. eauto.
    rewrite tupdate_update_same.
    inv H0; inv H1. split; auto. eapply Gc_refl. destruct H; auto. }
  { destruct H2. subst.
    remember (loadframe.store_args_rec_fp stk z (a :: tys)) as FP.
    destruct args; [inv H2|].
    destruct a; simpl in H2 |- *; unfold loadframe.store_stack_fmem; simpl.
    { match goal with
      | |- context[Mem.store ?chunk _ ?stk ?ofs ?v] =>
        exploit (store_refine chunk stk ofs v); eauto; try split; simpl; unfold tsostore; eauto;
          instantiate (1:=tt)
      end.
      intros [(sfp1 & _ & sfm1 & (Hstore1 & Hfp1) &
               [(Hdrf1 & Hfpmatch1 & _ & Hmeminv1 & HGc1)
               |[Hconflict Hfpmatch1]])
             |Habort].
      rewrite Hstore1.
      exploit IHtys; try exact Hmeminv1; try rewrite tupdate_update_get_same in *;
        simpl; eauto; simpl.
      econstructor; eauto. erewrite Mem.store_freelist; eauto. inv H0; auto.
      econstructor; eauto. inv H1; auto.
      intros [(sfp2 & _ & sfm2 & (Hstore2 & Hfp2) &
               [(Hdrf2 & Hfpmatch2 & _ & Hmeminv2 & HGc2)
               |[Hconflict Hfpmatch2]])
             |Habort].
      left. rewrite Hstore2. do 3 eexists. split. eauto.
      left. split. subst FP. simpl. intro C. apply conflictc_union in C; destruct C; eauto.
      eapply Hdrf2. eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction.
      split. apply FP.subset_refl.
      split. eauto.
      rewrite tupdate_update2 in *. split. auto. eapply Gc_trans; eauto.

      left. do 3 eexists. split. eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. right. eapply conflictc_ext; eauto.
      intros. unfold tupdate. destruct peq; auto; contradiction.

      right. intros. intros [C1 C2]. eapply Habort; eauto.

      rewrite Hstore1. destruct loadframe.store_args_rec_fmem; [left|right; intros; intros [C _]; inv C].
      do 3 eexists. split; eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. left. auto.

      right. intros. intros [C1 C2]. destruct Mem.store; try discriminate. eapply Habort; eauto.
    }
    { match goal with
      | |- context[Mem.store ?chunk _ ?stk ?ofs ?v] =>
        exploit (store_refine chunk stk ofs v); eauto; try split; simpl; unfold tsostore; eauto;
          instantiate (1:=tt)
      end.
      intros [(sfp1 & _ & sfm1 & (Hstore1 & Hfp1) &
               [(Hdrf1 & Hfpmatch1 & _ & Hmeminv1 & HGc1)
               |[Hconflict Hfpmatch1]])
             |Habort].
      rewrite Hstore1.
      exploit IHtys; try exact Hmeminv1; try rewrite tupdate_update_get_same in *;
        simpl; eauto; simpl.
      econstructor; eauto. erewrite Mem.store_freelist; eauto. inv H0; auto.
      econstructor; eauto. inv H1; auto.
      intros [(sfp2 & _ & sfm2 & (Hstore2 & Hfp2) &
               [(Hdrf2 & Hfpmatch2 & _ & Hmeminv2 & HGc2)
               |[Hconflict Hfpmatch2]])
             |Habort].
      left. rewrite Hstore2. do 3 eexists. split. eauto.
      left. split. subst FP. simpl. intro C. apply conflictc_union in C; destruct C; eauto.
      eapply Hdrf2. eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction.
      split. apply FP.subset_refl.
      split. eauto.
      rewrite tupdate_update2 in *. split. auto. eapply Gc_trans; eauto.

      left. do 3 eexists. split. eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. right. eapply conflictc_ext; eauto.
      intros. unfold tupdate. destruct peq; auto; contradiction.

      right. intros. intros [C1 C2]. eapply Habort; eauto.

      rewrite Hstore1. destruct loadframe.store_args_rec_fmem; [left|right; intros; intros [C _]; inv C].
      do 3 eexists. split; eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. left. auto.

      right. intros. intros [C1 C2]. destruct Mem.store; try discriminate. eapply Habort; eauto.
    }
    { destruct v; try discriminate.
      match goal with
      | |- context[Mem.store ?chunk _ ?stk ?ofs (Vint (Int64.hiword i))] =>
        exploit (store_refine chunk stk ofs (Vint (Int64.hiword i))); eauto; try split; simpl; unfold tsostore; eauto;
          instantiate (1:=tt)
      end.
      intros [(sfp1 & _ & sfm1 & (Hstore1 & Hfp1) &
               [(Hdrf1 & Hfpmatch1 & _ & Hmeminv1 & HGc1)
               |[Hconflict1 Hfpmatch1]])
             |Habort]; try rewrite Hstore1; [| | right].
      match goal with
      | |- context[Mem.store ?chunk _ ?stk ?ofs (Vint (Int64.loword i))] =>
        exploit (store_refine chunk stk ofs (Vint (Int64.loword i))); eauto; try split; simpl; unfold tsostore; eauto
      end.
      erewrite Mem.store_freelist; eauto. inv H0. auto. inv H1; auto.
      intros [(sfp2 & _ & sfm2 & (Hstore2 & Hfp2) &
               [(Hdrf2 & Hfpmatch2 & _ & Hmeminv2 & HGc2)
               |[Hconflict2 Hfpmatch2]])
             |Habort]; try rewrite Hstore2; [| | right].
      
      exploit IHtys; try exact Hmeminv2; try rewrite tupdate_update_get_same in *;
        simpl; eauto; simpl.
      econstructor; eauto. erewrite Mem.store_freelist; eauto. inv H0; auto. eapply Mem.store_freelist; eauto.
      econstructor; eauto. inv H1; auto.
      revert H2. unfold buffer_insert. simpl. rewrite tupdate_update_get_same. eauto.
      intros [(sfp3 & _ & sfm3 & (Hstore3 & Hfp3) &
               [(Hdrf3 & Hfpmatch3 & _ & Hmeminv3 & HGc3)
               |[Hconflict3 Hfpmatch3]])
             |Habort].
      left. rewrite Hstore3. do 3 eexists. split. eauto.
      left. split.
      { subst FP. simpl. unfold loadframe.store_stack_fp. simpl. intro C.
        apply conflictc_union in C. destruct C as [C|C]. apply conflictc_union in C. destruct C as [C|C].
        eapply Hdrf2. eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction.
        eapply Hdrf1. auto.
        eapply Hdrf3. eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction. }
      split. apply FP.subset_refl.
      split. eauto.
      repeat rewrite tupdate_update2 in *. split; auto.
      eapply Gc_trans. eauto. eapply Gc_trans. eauto. eauto.
      { left. do 3 eexists. split. eauto. right. split;[|apply FP.subset_refl].
        subst FP. simpl. apply conflictc_union'. right. eapply conflictc_ext; eauto.
        intros. unfold tupdate. destruct peq; auto; contradiction. }
      { right. intros. intros [C1 C2]. eapply Habort; eauto. }
      { destruct loadframe.store_args_rec_fmem; [left|right; intros; intros [C _]; inv C].
        do 3 eexists. split; eauto. right. split;[|apply FP.subset_refl].
        subst FP. simpl. apply conflictc_union'. left. apply conflictc_union'. left.
        eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction. }
      { revert Habort; clear; intros. intros [C1 C2]. destruct Mem.store; try discriminate. eapply Habort; eauto. }
      { destruct (Mem.store _ _ _ _ (Vint (Int64.loword i))); [|right;intros; intros [C _]; inv C].
        destruct loadframe.store_args_rec_fmem; [left|right; intros; intros [C _]; inv C].
        do 3 eexists. split; eauto. right. split;[|apply FP.subset_refl].
        subst FP. simpl. apply conflictc_union'. left. apply conflictc_union'. auto. }
      { revert Habort; clear; intros. intros [C1 C2]. destruct Mem.store; try discriminate. eapply Habort; eauto. }
    }
    { match goal with
      | |- context[Mem.store ?chunk _ ?stk ?ofs ?v] =>
        exploit (store_refine chunk stk ofs v); eauto; try split; simpl; unfold tsostore; eauto;
          instantiate (1:=tt)
      end.
      intros [(sfp1 & _ & sfm1 & (Hstore1 & Hfp1) &
               [(Hdrf1 & Hfpmatch1 & _ & Hmeminv1 & HGc1)
               |[Hconflict Hfpmatch1]])
             |Habort].
      rewrite Hstore1.
      exploit IHtys; try exact Hmeminv1; try rewrite tupdate_update_get_same in *;
        simpl; eauto; simpl.
      econstructor; eauto. erewrite Mem.store_freelist; eauto. inv H0; auto.
      econstructor; eauto. inv H1; auto.
      intros [(sfp2 & _ & sfm2 & (Hstore2 & Hfp2) &
               [(Hdrf2 & Hfpmatch2 & _ & Hmeminv2 & HGc2)
               |[Hconflict Hfpmatch2]])
             |Habort].
      left. rewrite Hstore2. do 3 eexists. split. eauto.
      left. split. subst FP. simpl. intro C. apply conflictc_union in C; destruct C; eauto.
      eapply Hdrf2. eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction.
      split. apply FP.subset_refl.
      split. eauto.
      rewrite tupdate_update2 in *. split. auto. eapply Gc_trans; eauto.

      left. do 3 eexists. split. eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. right. eapply conflictc_ext; eauto.
      intros. unfold tupdate. destruct peq; auto; contradiction.

      right. intros. intros [C1 C2]. eapply Habort; eauto.

      rewrite Hstore1. destruct loadframe.store_args_rec_fmem; [left|right; intros; intros [C _]; inv C].
      do 3 eexists. split; eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. left. auto.

      right. intros. intros [C1 C2]. destruct Mem.store; try discriminate. eapply Habort; eauto.
    }
    { match goal with
      | |- context[Mem.store ?chunk _ ?stk ?ofs ?v] =>
        exploit (store_refine chunk stk ofs v); eauto; try split; simpl; unfold tsostore; eauto;
          instantiate (1:=tt)
      end.
      intros [(sfp1 & _ & sfm1 & (Hstore1 & Hfp1) &
               [(Hdrf1 & Hfpmatch1 & _ & Hmeminv1 & HGc1)
               |[Hconflict Hfpmatch1]])
             |Habort].
      rewrite Hstore1.
      exploit IHtys; try exact Hmeminv1; try rewrite tupdate_update_get_same in *;
        simpl; eauto; simpl.
      econstructor; eauto. erewrite Mem.store_freelist; eauto. inv H0; auto.
      econstructor; eauto. inv H1; auto.
      intros [(sfp2 & _ & sfm2 & (Hstore2 & Hfp2) &
               [(Hdrf2 & Hfpmatch2 & _ & Hmeminv2 & HGc2)
               |[Hconflict Hfpmatch2]])
             |Habort].
      left. rewrite Hstore2. do 3 eexists. split. eauto.
      left. split. subst FP. simpl. intro C. apply conflictc_union in C; destruct C; eauto.
      eapply Hdrf2. eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction.
      split. apply FP.subset_refl.
      split. eauto.
      rewrite tupdate_update2 in *. split. auto. eapply Gc_trans; eauto.

      left. do 3 eexists. split. eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. right. eapply conflictc_ext; eauto.
      intros. unfold tupdate. destruct peq; auto; contradiction.

      right. intros. intros [C1 C2]. eapply Habort; eauto.

      rewrite Hstore1. destruct loadframe.store_args_rec_fmem; [left|right; intros; intros [C _]; inv C].
      do 3 eexists. split; eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. left. auto.

      right. intros. intros [C1 C2]. destruct Mem.store; try discriminate. eapply Habort; eauto.
    }
    { match goal with
      | |- context[Mem.store ?chunk _ ?stk ?ofs ?v] =>
        exploit (store_refine chunk stk ofs v); eauto; try split; simpl; unfold tsostore; eauto;
          instantiate (1:=tt)
      end.
      intros [(sfp1 & _ & sfm1 & (Hstore1 & Hfp1) &
               [(Hdrf1 & Hfpmatch1 & _ & Hmeminv1 & HGc1)
               |[Hconflict Hfpmatch1]])
             |Habort].
      rewrite Hstore1.
      exploit IHtys; try exact Hmeminv1; try rewrite tupdate_update_get_same in *;
        simpl; eauto; simpl.
      econstructor; eauto. erewrite Mem.store_freelist; eauto. inv H0; auto.
      econstructor; eauto. inv H1; auto.
      intros [(sfp2 & _ & sfm2 & (Hstore2 & Hfp2) &
               [(Hdrf2 & Hfpmatch2 & _ & Hmeminv2 & HGc2)
               |[Hconflict Hfpmatch2]])
             |Habort].
      left. rewrite Hstore2. do 3 eexists. split. eauto.
      left. split. subst FP. simpl. intro C. apply conflictc_union in C; destruct C; eauto.
      eapply Hdrf2. eapply conflictc_ext; eauto. intros. unfold tupdate. destruct peq; auto; contradiction.
      split. apply FP.subset_refl.
      split. eauto.
      rewrite tupdate_update2 in *. split. auto. eapply Gc_trans; eauto.

      left. do 3 eexists. split. eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. right. eapply conflictc_ext; eauto.
      intros. unfold tupdate. destruct peq; auto; contradiction.

      right. intros. intros [C1 C2]. eapply Habort; eauto.

      rewrite Hstore1. destruct loadframe.store_args_rec_fmem; [left|right; intros; intros [C _]; inv C].
      do 3 eexists. split; eauto. right. split;[|apply FP.subset_refl].
      subst FP. simpl. apply conflictc_union'. left. auto.

      right. intros. intros [C1 C2]. destruct Mem.store; try discriminate. eapply Habort; eauto.
    }
    Unshelve. all: constructor.
  }
Qed.

Lemma meminv_initialize:
  forall t fl sm bufs tm sfm tfm args tys z bm1 stk tsofm',
    meminv t fl sm bufs tm ->
    embed sm fl sfm ->
    embed tm fl tfm ->
    loadframe.args_len_rec args tys = Some z ->
    tsoalloc (mktsofmem (bufs t) tfm) 0 (4 * z) (bm1, stk) ->
    store_args_fmem bm1 stk args tys = Some tsofm' ->
    let bufs' := (tupdate t (tbuffer tsofm') bufs) in
    let tm' := (strip (fmemory tsofm')) in
    (exists sfm1 sfm',
        Mem.alloc sfm 0 (4 * z) = (sfm1, stk) /\
        loadframe.store_args_fmem sfm1 stk args tys = Some sfm' /\
        (Gc t sm (mktsomem bufs tm) (strip sfm') (mktsomem bufs' tm') /\
         meminv t fl (strip sfm') bufs' tm'
         \/
         conflictc t (tsoalloc_fp stk 0 (4 * z)) bufs)
    )
    \/
    loadframe.store_args_fmem (fst (Mem.alloc sfm 0 (4 * z))) stk args tys = None.
Proof.
  intros. remember (mktsomem bufs tm) as TM.
  destruct (Mem.alloc sfm 0 (4 * z)) as [sfm1 stk'] eqn:Halloc.
  assert (stk' = stk) as Hstk.
  { clear H4. inv H3. apply Mem.alloc_result in Halloc. subst stk'.
    inv H11. 
    assert (forall n, In (MemAux.get_block fl n) (Mem.validblocks fm') <->
                 In (MemAux.get_block fl n) (Mem.validblocks sfm)).
    { intros. inv H0; inv H1. eapply meminv_rel_vb in H9; eauto. simpl in H9. eauto. }
    eapply eq_validity_eq_nextblock; eauto. instantiate (1:= (strip fm')).
    intros. subst b. inv H0; inv H1. simpl. specialize (H4 n). tauto.
    inv H0; inv H1. rewrite <- H0, <- H3. econstructor; eauto. }
  subst stk'.
  destruct (Classical_Prop.classic (conflictc t (tsoalloc_fp stk 0 (4 * z)) (tso_buffers TM)))
    as [|Hnotconflict].
  { destruct (loadframe.store_args_fmem sfm1 stk args tys) eqn:A; [left|right; auto].
    do 2 eexists. split; eauto. split; eauto. subst TM. simpl in *. auto. }
  assert (~ conflictc t (loadframe.store_args_fp stk tys) (tso_buffers TM)).
  { intro C. apply Hnotconflict. eapply conflict_store_args_conflict_alloc. eauto. }
  exploit alloc_refine; eauto.
  intros [(fp1 & stk' & sfm1' & (Halloc' & Hfp) & [Hmatch|[Hconflict _]]) | Habort];
    [|exfalso; apply Hnotconflict; subst TM; simpl; auto| exfalso; eapply Habort; eauto].
  subst fp1. destruct Hmatch as (_ & _ & _ & Hmeminv1 & HGc1). rewrite Halloc in Halloc'; inv Halloc'.
  exploit store_args_refine. exact Hmeminv1.
  (* embed after alloc... *)
  { econstructor; eauto. erewrite Mem.alloc_freelist; eauto. inv H0; auto. }
  { instantiate (1:= (fmemory bm1)). inv H3. simpl in *.
    econstructor; eauto. inv H1; auto. }
  unfold tupdate. destruct peq; try contradiction. clear e.
  replace bm1 with (mktsofmem (tbuffer bm1) (fmemory bm1)) in H4 by (destruct bm1; auto). eauto.
  instantiate (1:=tt).
  intros [(sfp2 & _ & sfm' & (Hstoreargs & Hsfp2) & [(_ & _ & _ & Hmeminv' & HGc' )| [Hconflict _]])|Habort];
    [left|left|right].
  
  exists sfm1', sfm'. split. auto. split. eauto. left.
  subst bufs'. rewrite tupdate_update2 in *. split. eapply Gc_trans; eauto. auto.
  
  exfalso. eapply H5. simpl. eapply conflictc_ext. eauto.
  intros. unfold tupdate. destruct peq; auto. contradiction.

  simpl. destruct loadframe.store_args_fmem; auto. exfalso. eapply Habort; eauto. constructor.
Qed.

Lemma store_args_succeed_tso:
  forall args tys z m stk m' tfm,
    loadframe.args_len_rec args tys = Some z ->
    loadframe.store_args_fmem m stk args tys = Some m' ->
    exists tfm',
      store_args_fmem (buffer_insert {| tbuffer := nil; fmemory := tfm |}
                                     (BufferedAlloc (Mem.nextblock tfm) 0 (4 * z)))
                      (Mem.nextblock tfm) args tys = Some tfm'
      /\ exists m'', apply_buffer (tbuffer tfm') (strip (fmemory tfm')) = Some m''.
Proof.
  unfold store_args_fmem. intros.
  generalize (Mem.nextblock tfm). intro b.
  remember (buffer_insert {| tbuffer := nil; fmemory := tfm |} (BufferedAlloc b 0 (4 * z)))
    as tbfm.
  assert (exists z0, z0 = 0) as [z0 Hz0] by eauto.
  assert (exists buf',
             store_args_rec_fmem tbfm (Vptr b Ptrofs.zero) 0 args tys
             = Some (mktsofmem (tbuffer tbfm ++ buf') (fmemory tbfm))
             /\ (forall bi, In bi buf' ->
                      exists chunk ofs v,
                        bi = BufferedStore chunk b ofs v
                        /\ z0 <= ofs
                        /\ ofs + size_chunk chunk <= 4 * z
                        /\ (align_chunk chunk | ofs))).
  { clear Heqtbfm. clear tfm.
    replace (4 * z) with (0 + (4 * z)) by omega.
    revert H0. unfold loadframe.store_args_fmem.
    cut (4 | 0). remember 0 as z'. cut (z' >= 0). rewrite Heqz' in Hz0. clear Heqz'.
    generalize z'. revert args z tbfm m m' H. subst z0.
    induction tys.
    { unfold loadframe.args_len_rec. intros. simpl in *.
      destruct args; inv H. simpl. exists nil. rewrite app_nil_r.
      split. destruct tbfm; auto. intros. inv H. }
    { intros. destruct args as [|v args]; [inv H|]. simpl in H.
      destruct val_casted.val_has_type_func; [|inv H]. 
      destruct loadframe.args_len_rec eqn:A; inv H.
      specialize (IHtys args z0).
      remember (4 * (Locations.typesize a + z0)) as OFS.
      simpl. simpl in H2. unfold loadframe.store_stack_fmem in H2.
      destruct a; simpl in H2.
      { (* int *)
        destruct Mem.store eqn:Hstore; try discriminate.
        apply Mem.store_valid_access_3 in Hstore. destruct Hstore as [_ Halign].
        match goal with | |- context[store_args_rec_fmem ?tm _ _ _ _] => specialize (IHtys tm) end.
        exploit (Z.divide_add_r). exact H1. eapply Z.divide_refl. intro Halign0.
        assert (z'0 + 4 >= 0) as Hge0 by omega.
        specialize (IHtys _ _ A _ Hge0 Halign0 H2). destruct IHtys as (buf_tail & Hstoreargs & Hbuf_tail).
        simpl in Hstoreargs. simpl. rewrite Hstoreargs. eexists. split. simpl. rewrite app_assoc. eauto.
        intros. destruct H. subst bi. do 3 eexists. split. eauto.
        rewrite Ptrofs.add_zero_l in *. split. destruct (Ptrofs.unsigned_range (Ptrofs.repr z'0)); auto.
        split; auto. simpl. rewrite Ptrofs.unsigned_repr_eq.
        apply Z.add_le_mono. eapply Z.mod_le. omega. pose proof Ptrofs.modulus_pos; omega.
        subst OFS. apply loadframe.args_len_rec_non_neg in A. replace (Locations.typesize Tint) with 1 by auto. omega.
        
        simpl in H. eapply Hbuf_tail in H.
        subst OFS. replace (Locations.typesize Tint) with 1 by auto. rewrite <- Zred_factor2.
        rewrite Z.add_assoc. auto. }
      { (* float64 *)
        destruct Mem.store eqn:Hstore; try discriminate.
        apply Mem.store_valid_access_3 in Hstore. destruct Hstore as [_ Halign].
        match goal with | |- context[store_args_rec_fmem ?tm _ _ _ _] => specialize (IHtys tm) end.
        exploit (Z.divide_add_r). exact H1. eapply Z.divide_factor_l. intro Halign0.
        instantiate (1:=2) in Halign0. replace (4 * 2) with 8 in Halign0 by omega.
        assert (z'0 + 8 >= 0) as Hge0 by omega.
        specialize (IHtys _ _ A _ Hge0 Halign0 H2). destruct IHtys as (buf_tail & Hstoreargs & Hbuf_tail).
        simpl in Hstoreargs. simpl. rewrite Hstoreargs. eexists. split. simpl. rewrite app_assoc. eauto.
        intros. destruct H. subst bi. do 3 eexists. split. eauto.
        rewrite Ptrofs.add_zero_l in *. split. destruct (Ptrofs.unsigned_range (Ptrofs.repr z'0)); auto.
        split; auto. simpl. rewrite Ptrofs.unsigned_repr_eq.
        apply Z.add_le_mono. eapply Z.mod_le. omega. pose proof Ptrofs.modulus_pos; omega.
        subst OFS. apply loadframe.args_len_rec_non_neg in A. replace (Locations.typesize Tfloat) with 2 by auto. omega.
        
        simpl in H. eapply Hbuf_tail in H.
        subst OFS. replace (Locations.typesize Tfloat) with 2 by auto. rewrite <- Zred_factor4.
        rewrite Z.add_assoc. auto. }
      { (* long *)
        destruct v; try discriminate.
        destruct Mem.store eqn:Hstore1; try discriminate.
        destruct (Mem.store _ _ _ _ (Vint (Int64.loword i))) eqn:Hstore2; try discriminate.
        apply Mem.store_valid_access_3 in Hstore1. destruct Hstore1 as [_ Halign1].
        apply Mem.store_valid_access_3 in Hstore2. destruct Hstore2 as [_ Halign2].
        match goal with | |- context[store_args_rec_fmem ?tm _ _ _ _] => specialize (IHtys tm) end.
        exploit (Z.divide_add_r). exact H1. eapply Z.divide_factor_l. intro Halign0.
        instantiate (1:=2) in Halign0. replace (4 * 2) with 8 in Halign0 by omega.
        assert (z'0 + 8 >= 0) as Hge0 by omega.
        specialize (IHtys _ _ A _ Hge0 Halign0 H2). destruct IHtys as (buf_tail & Hstoreargs & Hbuf_tail).
        simpl in Hstoreargs. simpl. rewrite Hstoreargs. eexists. split. simpl.
        repeat rewrite <- app_assoc. eauto.
        intros. simpl in H. destruct H as [H|[H|H]].
        
        subst bi. do 3 eexists. split. eauto. rewrite Ptrofs.add_zero_l in *.
        split. destruct (Ptrofs.unsigned_range (Ptrofs.repr (z'0 + 4))); auto.
        split; auto. simpl. rewrite Ptrofs.unsigned_repr_eq.
        subst OFS. replace (Locations.typesize Tlong) with 2 by auto.
        rewrite <- Zred_factor4, Z.add_assoc. replace (4 * 2) with (4 + 4) by omega.
        rewrite <- Z.add_assoc. rewrite <-(Z.add_assoc 4 4 (4*z0)). rewrite Z.add_assoc.
        apply Z.add_le_mono. eapply Z.mod_le. omega. pose proof Ptrofs.modulus_pos; omega.
        apply loadframe.args_len_rec_non_neg in A. omega.

        subst bi. do 3 eexists. split. eauto. rewrite Ptrofs.add_zero_l in *.
        split. destruct (Ptrofs.unsigned_range (Ptrofs.repr z'0 )); auto.
        split; auto. simpl. rewrite Ptrofs.unsigned_repr_eq.
        subst OFS. replace (Locations.typesize Tlong) with 2 by auto.
        apply Z.add_le_mono. eapply Z.mod_le. omega. pose proof Ptrofs.modulus_pos; omega.
        rewrite <- Zred_factor4. apply loadframe.args_len_rec_non_neg in A. omega.
        
        simpl in H. eapply Hbuf_tail in H.
        subst OFS. replace (Locations.typesize Tlong) with 2 by auto. rewrite <- Zred_factor4.
        rewrite Z.add_assoc. auto.
      }
      { (* float32 *)
        destruct Mem.store eqn:Hstore; try discriminate.
        apply Mem.store_valid_access_3 in Hstore. destruct Hstore as [_ Halign].
        match goal with | |- context[store_args_rec_fmem ?tm _ _ _ _] => specialize (IHtys tm) end.
        exploit (Z.divide_add_r). exact H1. eapply Z.divide_refl. intro Halign0.
        assert (z'0 + 4 >= 0) as Hge0 by omega.
        specialize (IHtys _ _ A _ Hge0 Halign0 H2). destruct IHtys as (buf_tail & Hstoreargs & Hbuf_tail).
        simpl in Hstoreargs. simpl. rewrite Hstoreargs. eexists. split. simpl. rewrite app_assoc. eauto.
        intros. destruct H. subst bi. do 3 eexists. split. eauto.
        rewrite Ptrofs.add_zero_l in *. split. destruct (Ptrofs.unsigned_range (Ptrofs.repr z'0)); auto.
        split; auto. simpl. rewrite Ptrofs.unsigned_repr_eq.
        apply Z.add_le_mono. eapply Z.mod_le. omega. pose proof Ptrofs.modulus_pos; omega.
        subst OFS. apply loadframe.args_len_rec_non_neg in A. replace (Locations.typesize Tsingle) with 1 by auto. omega.
        
        simpl in H. eapply Hbuf_tail in H.
        subst OFS. replace (Locations.typesize Tsingle) with 1 by auto. rewrite <- Zred_factor2.
        rewrite Z.add_assoc. auto. }
      { (* any32 *)
        destruct Mem.store eqn:Hstore; try discriminate.
        apply Mem.store_valid_access_3 in Hstore. destruct Hstore as [_ Halign].
        match goal with | |- context[store_args_rec_fmem ?tm _ _ _ _] => specialize (IHtys tm) end.
        exploit (Z.divide_add_r). exact H1. eapply Z.divide_refl. intro Halign0.
        assert (z'0 + 4 >= 0) as Hge0 by omega.
        specialize (IHtys _ _ A _ Hge0 Halign0 H2). destruct IHtys as (buf_tail & Hstoreargs & Hbuf_tail).
        simpl in Hstoreargs. simpl. rewrite Hstoreargs. eexists. split. simpl. rewrite app_assoc. eauto.
        intros. destruct H. subst bi. do 3 eexists. split. eauto.
        rewrite Ptrofs.add_zero_l in *. split. destruct (Ptrofs.unsigned_range (Ptrofs.repr z'0)); auto.
        split; auto. simpl. rewrite Ptrofs.unsigned_repr_eq.
        apply Z.add_le_mono. eapply Z.mod_le. omega. pose proof Ptrofs.modulus_pos; omega.
        subst OFS. apply loadframe.args_len_rec_non_neg in A. replace (Locations.typesize Tany32) with 1 by auto. omega.
        
        simpl in H. eapply Hbuf_tail in H.
        subst OFS. replace (Locations.typesize Tany32) with 1 by auto. rewrite <- Zred_factor2.
        rewrite Z.add_assoc. auto. }
      { (* any64 *)
        destruct Mem.store eqn:Hstore; try discriminate.
        apply Mem.store_valid_access_3 in Hstore. destruct Hstore as [_ Halign].
        match goal with | |- context[store_args_rec_fmem ?tm _ _ _ _] => specialize (IHtys tm) end.
        exploit (Z.divide_add_r). exact H1. eapply Z.divide_factor_l. intro Halign0.
        instantiate (1:=2) in Halign0. replace (4 * 2) with 8 in Halign0 by omega.
        assert (z'0 + 8 >= 0) as Hge0 by omega.
        specialize (IHtys _ _ A _ Hge0 Halign0 H2). destruct IHtys as (buf_tail & Hstoreargs & Hbuf_tail).
        simpl in Hstoreargs. simpl. rewrite Hstoreargs. eexists. split. simpl. rewrite app_assoc. eauto.
        intros. destruct H. subst bi. do 3 eexists. split. eauto.
        rewrite Ptrofs.add_zero_l in *. split. destruct (Ptrofs.unsigned_range (Ptrofs.repr z'0)); auto.
        split; auto. simpl. rewrite Ptrofs.unsigned_repr_eq.
        apply Z.add_le_mono. eapply Z.mod_le. omega. pose proof Ptrofs.modulus_pos; omega.
        subst OFS. apply loadframe.args_len_rec_non_neg in A. replace (Locations.typesize Tany64) with 2 by auto. omega.
        
        simpl in H. eapply Hbuf_tail in H.
        subst OFS. replace (Locations.typesize Tany64) with 2 by auto. rewrite <- Zred_factor4.
        rewrite Z.add_assoc. auto. }
    }
    subst. omega.
    apply Z.divide_0_r.
  }
  destruct H1 as (buf & Hstore & Hbuf). rewrite Hstore. eexists. split. eauto.
  clear Hstore. simpl. subst tbfm. simpl.
  match goal with
  | |- context[apply_buffer _ ?m] =>
    remember m as M
  end.
  assert (range_perm M b 0 (4 * z) Memperm.Max Memperm.Writable).
  { subst M. clear. intros ofs Hofs. simpl. rewrite PMap.gss.
    destruct zle; try omega. simpl in *.
    destruct zlt; try omega. simpl. constructor. }
  subst z0. revert H1 Hbuf. clear. revert M. generalize (4 * z). clear. intros Bound.
  induction buf; intros.
  { simpl. eauto. }
  { simpl. exploit Hbuf. left. eauto. intros (chunk & ofs & v & Hbi & Hlo & Hhi & Halign).
    subst a. simpl. unfold store.
    destruct valid_access_dec. simpl. eapply IHbuf.
    intros ofs' Hofs'. simpl. eauto.
    intros. eapply Hbuf. right. auto.
    exfalso. apply n. clear n. split; auto.
    intros ofs' Hofs'. eapply H1. omega. }
Qed.

Lemma meminv_load_refine':
  forall sm tm fl sfm bufs t chunk b ofs v,
    embed sm fl sfm ->
    (forall t', bufs t' = nil) ->
    meminv t fl sm bufs tm ->
    Mem.load chunk sfm b ofs = Some v ->
    load chunk tm b ofs = Some v.
Proof.
  clear. intros. pose proof H2 as Hload. apply Mem.load_valid_access in H2.
  simpl. unfold load.
  destruct valid_access_dec; simpl; eauto.
  f_equal.
  { Local Transparent Mem.load.
    unfold Mem.load in Hload. destruct Mem.valid_access_dec; try contradiction.
    inv Hload. f_equal. eapply Mem.getN_exten.
    intros. clear v1. destruct H2 as [Hperm _]. rewrite <- size_chunk_conv in H3.
    eapply Hperm in H3. revert H3 H0 H1. inv H; simpl; clear. intros.
    exploit Mem.perm_cur_max. eauto. intro.
    replace (Mem.mem_contents sfm) with (GMem.mem_contents (strip sfm)) by auto.
    symmetry. eapply eq_loc_content. eapply Ic_mem_eq. destruct H1. eauto.
    simpl. rewrite H0. simpl. auto.
    intro. destruct H2. unfold Mem.perm in *. simpl in *. rewrite H4 in H3. inv H3.
    intros. simpl. rewrite H0. intro C. inv C. inv H4.
    Unshelve. auto.
    Local Opaque Mem.load.
  }
  exfalso. apply n. clear n.
  apply meminv_Ic in H1. destruct H2. split; auto.
  intros ofs' Hofs'. specialize (H2 ofs' Hofs'). exploit Mem.perm_cur_max. eauto.
  intro A. unfold Mem.perm in *.
  cut ((Mem.mem_access sfm) !! b ofs' Memperm.Max = (GMem.mem_access tm) !! b ofs' Memperm.Max).
  intro B; rewrite <- B. auto.
  eapply Ic_mem_eq in H1; simpl.
  eapply eq_loc_perm in H1. rewrite <- H1. inv H. auto.
  rewrite H0. simpl. auto.
  unfold obj_mem. inv H. simpl. unfold Mem.perm_order' in *.
  destruct ((Mem.mem_access sfm) !! b ofs' Memperm.Cur); try contradiction.
  destruct ((Mem.mem_access sfm) !! b ofs' Memperm.Max); try contradiction.
  intros [C1 C2]. congruence.
  intros. rewrite H0. intro. inv H5. inv H6.
  Unshelve. exact 1%positive.
Qed.

Lemma meminv_store_refine':
  forall sm tm fl sfm tfm bufs t chunk b ofs v sfm',
    embed sm fl sfm ->
    embed tm fl tfm ->
    (forall t', bufs t' = nil) ->
    meminv t fl sm bufs tm ->
    Mem.store chunk sfm b ofs v = Some sfm' ->
    exists buf, tsostore chunk (mktsofmem (bufs t) tfm) b ofs v = Some (mktsofmem buf tfm) /\
           exists tm', apply_buffer buf tm = Some tm'.
Proof.
  clear. intros. eapply Mem.store_valid_access_3 in H3.
  simpl. unfold tsostore. unfold buffer_insert. simpl. rewrite H1. simpl.
  eexists. split; eauto.
  unfold apply_buffer. simpl. unfold store.
  destruct valid_access_dec; simpl; eauto.
  exfalso. apply n. clear n.
  apply meminv_Ic in H2. destruct H3. split; auto. intros ofs' Hofs'.
  specialize (H3 ofs' Hofs'). exploit Mem.perm_cur_max. eauto. intro A. unfold Mem.perm in *.
  cut ((Mem.mem_access sfm) !! b ofs' Memperm.Max = (GMem.mem_access tm) !! b ofs' Memperm.Max).
  intro B; rewrite <- B. auto.
  eapply Ic_mem_eq in H2; simpl.
  eapply eq_loc_perm in H2. rewrite <- H2. inv H. auto.
  rewrite H1. simpl. auto.
  unfold obj_mem. inv H. simpl. unfold Mem.perm_order' in *.
  destruct ((Mem.mem_access sfm) !! b ofs' Memperm.Cur); try contradiction.
  destruct ((Mem.mem_access sfm) !! b ofs' Memperm.Max); try contradiction.
  intros [C1 C2]. congruence.
  intros. rewrite H1. intro. inv H6. inv H7.
  Unshelve. exact 1%positive.
Qed.

Lemma Val_and_result:
  forall v1 v2,
    Val.and v1 v2 = Vundef \/ exists n, Val.and v1 v2 = Vint n.
Proof.
  clear. destruct v1; simpl; eauto. destruct v2; simpl; eauto.
Qed.

Lemma meminv_free_refine':
  forall sm bufs tm t fl sfm b lo hi sfm',
    embed sm fl sfm ->
    meminv t fl sm bufs tm ->
    (forall t', bufs t' = nil) ->
    Mem.free sfm b lo hi = Some sfm' ->
    exists tm', apply_buffer (BufferedFree b lo hi :: nil) tm = Some tm'.
Proof.
  clear. intros. apply Mem.free_range_perm in H2.
  simpl. unfold free.
  destruct range_perm_dec; simpl; eauto.
  exfalso. apply n. clear n.
  apply meminv_Ic in H0. intros ofs Hofs.
  specialize (H2 ofs Hofs). exploit Mem.perm_cur_max. eauto. intro A. unfold Mem.perm in *.
  cut ((Mem.mem_access sfm) !! b ofs Memperm.Max = (GMem.mem_access tm) !! b ofs Memperm.Max).
  intro B; rewrite <- B. auto.
  eapply Ic_mem_eq in H0; simpl.
  eapply eq_loc_perm in H0. rewrite <- H0. inv H. auto.
  rewrite H1. simpl. auto.
  unfold obj_mem. inv H. simpl. unfold Mem.perm_order' in *.
  destruct ((Mem.mem_access sfm) !! b ofs Memperm.Cur); try contradiction.
  destruct ((Mem.mem_access sfm) !! b ofs Memperm.Max); try contradiction.
  intros [C1 C2]. congruence.
  intros. rewrite H1. intro. inv H4. inv H5.
  Unshelve. exact 1%positive.
Qed.

Lemma meminv_extcall_arg':
  forall t fl sm tm sfm tfm rs a arg,
    meminv t fl sm (tso_buffers tm) (memory tm) ->
    embed sm fl sfm ->
    embed (memory tm) fl tfm ->
    (forall t', (tso_buffers tm) t' = nil) ->
    AsmLang.extcall_arg rs sfm a arg ->
    extcall_arg rs (mktsofmem (tso_buffers tm t) tfm) a arg.
Proof.
  intros. inv H3. econstructor.
  destruct Val.offset_ptr eqn:Haddr; try discriminate. simpl in H5.
  econstructor. eauto. rewrite Haddr. simpl. rewrite H2. simpl.
  inv H1; inv H0. eapply meminv_load_refine'; eauto.
  econstructor. eauto. eauto. rewrite H4. eauto.
Qed.

Lemma meminv_extcall_arg_pair':
  forall t fl sm tm sfm tfm rs l arg,
    meminv t fl sm (tso_buffers tm) (memory tm) ->
    embed sm fl sfm ->
    embed (memory tm) fl tfm ->
    (forall t', (tso_buffers tm) t' = nil) ->
    AsmLang.extcall_arg_pair rs sfm l arg ->
    extcall_arg_pair rs (mktsofmem (tso_buffers tm t) tfm) l arg.
Proof.
  intros. inv H3; econstructor; eauto using meminv_extcall_arg'.
Qed.

Lemma meminv_extcall_arguments':
  forall t fl sm tm sfm tfm rs sig args,
    meminv t fl sm (tso_buffers tm) (memory tm) ->
    embed sm fl sfm ->
    embed (memory tm) fl tfm ->
    (forall t', (tso_buffers tm) t' = nil) ->
    AsmLang.extcall_arguments rs sfm sig args ->
    extcall_arguments rs (mktsofmem (tso_buffers tm t) tfm) sig args.
Proof.
  intros until sig. unfold AsmLang.extcall_arguments, extcall_arguments.
  generalize (Conventions1.loc_arguments sig). clear. intros.
  induction H3; econstructor; eauto using meminv_extcall_arg_pair'.
Qed.

Lemma meminv_valid_pointer_refine':
  forall sm bufs tm t fl sfm tfm b ofs,
    embed sm fl sfm ->
    embed tm fl tfm ->
    meminv t fl sm bufs tm ->
    (forall t', bufs t' = nil) ->
    Mem.valid_pointer sfm b ofs = true ->
    tso_valid_pointer (mktsofmem (bufs t) tfm) b ofs = true.
Proof.
  unfold Mem.valid_pointer, tso_valid_pointer. intros.
  destruct Mem.perm_dec; inv H3.
  rewrite H2. simpl. destruct perm_dec; auto.
  exfalso. apply n. unfold Mem.perm in p.
  exploit Mem.perm_cur_max. eauto. intro p'.
  assert (~ obj_mem sm b ofs).
  { intro. destruct H3. inv H. simpl in *. rewrite H4 in p. inv p. }
  eapply Ic_mem_eq in H3. erewrite <- eq_loc_perm; eauto. inv H. auto.
  destruct H1. eauto.
  simpl. rewrite H2. simpl. inv H0. auto.
  intros. simpl. rewrite H2. intro. inv H5. inv H6.
  Unshelve. auto.
Qed.

Lemma meminv_cmpu_bool_Some_refine':
  forall sm bufs tm t fl sfm tfm c v1 v2 b,
    embed sm fl sfm ->
    embed tm fl tfm ->
    meminv t fl sm bufs tm ->
    (forall t', bufs t' = nil) ->
    Val.cmpu_bool (Mem.valid_pointer sfm) c v1 v2 = Some b ->
    exists b', Val.cmpu_bool (tso_valid_pointer (mktsofmem (bufs t) tfm)) c v1 v2 = Some b'.
Proof.
  intros. unfold Val.cmpu_bool in *.
  repeat match goal with
         | H: _ || _ = true |- _ => apply orb_true_iff in H; destruct H
         | H: match ?x && ?y with _ => _ end = Some _ |- _ =>
           destruct x eqn:?Hx; simpl in H; try discriminate
         | H: match ?x || ?y with _ => _ end = Some _ |- _ =>
           destruct x eqn:?Hx; simpl in H; try discriminate
         | H: match ?x with _ => _ end = Some _ |- _ =>
           destruct x eqn:?Hx; simpl in H; try discriminate
         end; eauto.
  all:
    repeat match goal with
           | H: Mem.valid_pointer _ ?b ?ofs = true |- context[tso_valid_pointer _ ?b ?ofs] =>
             erewrite (meminv_valid_pointer_refine' _ _ _ _ _ _ _ b ofs); try exact H; try exact H1; try eassumption
           end;
    try (repeat rewrite orb_true_r; simpl; eauto; fail).
Qed.

Section MatchStateSim.

  Variable (cu : Asm_comp_unit).
  Hypothesis (HNODUPGD: nodup_gd_ident (cu_defs cu) = true).
  Hypothesis (HNODUPEF: (nodup_ef (cu_defs cu)) = true).
  Variable (sge : Genv.t fundef unit).
  Variable (tge : Genv.t fundef unit).
  Hypothesis (HSINITGE : init_genv AsmLang cu sge sge).
  Hypothesis (HTINITGE : AsmTSO.init_genv cu tge).
  Hypothesis (HGEMATCH : genv_match _ _ sge tge).

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
  Proof. intro s. exploit genv_symb_eq; eauto. Qed.

  Lemma find_def_find_symbol:
    forall b gd, Genv.find_def sge b = Some gd -> exists s, Genv.find_symbol sge s = Some b.
  Proof.
    intros. inv HSINITGE. inv H1.
    exploit H7. eauto. intros (b0 & Hb0).
    exploit H8. eauto. intros Hgd.
    unfold Genv.find_def in H. rewrite H in Hgd.
    exploit nodup_gd_ident_exists; try exact Hgd. auto.
    intros (id & Hid). specialize (H5 id). unfold Genv.find_symbol in *.
    unfold cu_to_prog in Hid. rewrite Hid in H5. inv H5. rewrite Hb0 in H12. inv H12. eauto.
  Qed.

  Lemma find_def_find_symbol':
    forall b gd, Genv.find_def tge b = Some gd -> exists s, Genv.find_symbol tge s = Some b.
  Proof.
    intros. inv HTINITGE.
    exploit H5. eauto. intros (b0 & Hb0).
    exploit H6. eauto. intros Hgd.
    unfold Genv.find_def in H. rewrite H in Hgd.
    exploit nodup_gd_ident_exists; try exact Hgd. auto.
    intros (id & Hid). specialize (H3 id). unfold Genv.find_symbol in *.
    unfold cu_to_prog in Hid. rewrite Hid in H3. inv H3. rewrite Hb0 in H11. inv H11. eauto.
  Qed.

  Lemma find_def_eq:
    forall b, Genv.find_def sge b = Genv.find_def tge b.
  Proof.
    unfold Genv.find_def. intro b.
    destruct ((Genv.genv_defs sge) ! b) eqn:A.
    exploit find_def_find_symbol. eauto. intros [s Hs].
    exploit genv_symb_eq. eauto. unfold Genv.find_symbol in Hs. rewrite Hs. intro Hs'.
    symmetry in Hs'. destruct HSINITGE as [_ HSINITGE'].
    inv HSINITGE'. inv HTINITGE. fold (cu_to_prog cu) in *.
    unfold Genv.find_symbol in *.
    specialize (H2 s). specialize (H10 s). rewrite Hs in H2. rewrite Hs' in H10.
    inv H2. inv H10.
    exploit H5. eauto. exploit H13. eauto.
    rewrite <- H2 in H15. inv H15. intros C D. rewrite C in D. congruence.
    destruct ((Genv.genv_defs tge) ! b) eqn:B; auto.
    exploit find_def_find_symbol'. eauto. intros [s Hs].
    exploit genv_symb_eq. eauto. unfold Genv.find_symbol in Hs. rewrite Hs.
    intro C. exploit genv_defs_match; eauto. rewrite A, B. inversion 1.
  Qed.
    
  Lemma senv_preserved:
    Senv.equiv sge tge.	
  Proof.
    split.
    apply symbols_preserved.
    
    split.
    intro. unfold Senv.public_symbol. simpl. unfold Genv.public_symbol.
    rewrite symbols_preserved. destruct Genv.find_symbol; auto.
    destruct in_dec; destruct in_dec; auto; exfalso.
    erewrite <- genv_public_eq in i; eauto.
    erewrite genv_public_eq in i; eauto.

    unfold Senv.block_is_volatile; simpl. unfold Genv.block_is_volatile, Genv.find_var_info.
    intro. rewrite find_def_eq. auto. 
  Qed.    
  
  Lemma function_ptr_eq:
    forall b, Genv.find_funct_ptr sge b = Genv.find_funct_ptr tge b.
  Proof.
    unfold Genv.find_funct_ptr. intro. rewrite find_def_eq. auto.
  Qed.

  Lemma symbol_address_eq:
    forall id ofs,
      Genv.symbol_address tge id ofs = Genv.symbol_address sge id ofs.
  Proof.
    unfold Genv.symbol_address. intros; rewrite symbols_preserved; auto.
  Qed.

  Lemma eval_addrmode32_eq:
    forall a rs,
      eval_addrmode32 tge a rs = eval_addrmode32 sge a rs.
  Proof.
    intros. unfold eval_addrmode32. 
    destruct a, base; repeat f_equal; destruct const; auto.
    all: destruct p; auto using symbol_address_eq.
  Qed.

  Lemma eval_addrmode64_eq:
    forall a rs,
      eval_addrmode64 tge a rs = eval_addrmode64 sge a rs.
  Proof.
    intros. unfold eval_addrmode64.
    destruct a, base; repeat f_equal; destruct const; auto.
    all: destruct p; auto using symbol_address_eq.
  Qed.

  Lemma eval_addrmode_eq:
    forall a rs,
      eval_addrmode tge a rs = eval_addrmode sge a rs.
  Proof.
    intros; unfold eval_addrmode; destruct Archi.ptr64;
      auto using eval_addrmode32_eq, eval_addrmode64_eq.
  Qed.

  Lemma senv_symbol_address_eq:
    forall id ofs, Senv.symbol_address sge id ofs = Senv.symbol_address tge id ofs.
  Proof.
    unfold Senv.symbol_address, Senv.find_symbol; simpl. intros. rewrite symbols_preserved. auto.
  Qed.

  Lemma eval_builtin_arg_fp_eq:
    forall (rs: Asm.preg -> val) sp arg fp,
      MemOpFP.eval_builtin_arg_fp sge rs sp arg fp <->
      MemOpFP.eval_builtin_arg_fp tge rs sp arg fp.
  Proof.
    intros. split; intro A; induction A; try constructor.
    rewrite senv_symbol_address_eq. econstructor.
    subst fp. econstructor; eauto.
    rewrite <- senv_symbol_address_eq. econstructor.
    subst fp. econstructor; eauto.
  Qed.
  
  Lemma genv_match_eval_builtin_args_fp:
    forall (rs: Asm.preg -> val) sp args fp,
      MemOpFP.eval_builtin_args_fp sge rs sp args fp <->
      MemOpFP.eval_builtin_args_fp tge rs sp args fp.
  Proof.
    intros until args. induction args.
    intros. split; intro A; inv A; constructor.
    intro.
    split; intro A; inv A; econstructor;
      try eapply IHargs; try eapply eval_builtin_arg_fp_eq; eauto.
  Qed.    

  Lemma meminv_eval_builtin_arg:
    forall t sm bufs tm fl sfm tfm (rs: Asm.preg -> val) sp arg v fp,
      meminv t fl sm bufs tm ->
      embed sm fl sfm ->
      embed tm fl tfm ->
      eval_builtin_arg tge rs sp (mktsofmem (bufs t) tfm) arg v ->
      MemOpFP.eval_builtin_arg_fp tge rs sp arg fp ->
      (exists v', AsmLang.eval_builtin_arg sge rs sp sfm arg v' /\
             ((~ conflictc t fp bufs /\ v' = v)
              \/ conflictc t fp bufs))
      \/
      (forall v', ~ AsmLang.eval_builtin_arg sge rs sp sfm arg v').
  Proof.
    intros until 4. revert fp.
    induction H2; intros fp Hfp;
      try (left; eexists; split; [econstructor; eauto|left; split; auto; inv Hfp; apply emp_not_conflictc]; fail).
    { destruct (Val.offset_ptr sp ofs) eqn:Haddr; try discriminate. simpl in H2.
      exploit load_refine. eauto. eauto. eauto. split; eauto.
      intros [(sfp & v' & _ & (_ & Hload & Hsfp) & [(Hdrf & Hmatch & Hv' & _ & _) | (Hrace & Hmatch)])|Habort];
        [left|left|right].
      subst. exists v. split. econstructor. rewrite Haddr. eauto. left. split; auto. inv Hfp. rewrite Haddr. auto.
      exists v'. split. econstructor. rewrite Haddr. eauto. right. inv Hfp. rewrite Haddr. auto.
      intros. intro C. inv C. eapply Habort. split. eauto. split. rewrite Haddr in H6. eauto. eauto. }
    { destruct (Senv.symbol_address tge id ofs) eqn:Haddr; try discriminate. simpl in H2.
      rewrite <- senv_symbol_address_eq in Haddr.
      exploit load_refine. eauto. eauto. eauto. split; eauto.
      intros [(sfp & v' & _ & (_ & Hload & Hsfp) & [(Hdrf & Hmatch & Hv' & _ & _) | (Hrace & Hmatch)])|Habort];
        [left|left|right].
      subst. exists v. split. econstructor. rewrite Haddr. eauto. left. split; auto. inv Hfp.
      rewrite <- senv_symbol_address_eq, Haddr. auto.
      exists v'. split. econstructor. rewrite Haddr. eauto. right. inv Hfp.
      rewrite <- senv_symbol_address_eq, Haddr. auto.
      intros. intro C. inv C. eapply Habort. split. eauto. split. rewrite Haddr in H7. eauto. eauto. }    
    { left. eexists. split. econstructor. inv Hfp. left. rewrite senv_symbol_address_eq. split; auto.
      apply emp_not_conflictc. }
    { inv Hfp. eapply IHeval_builtin_arg1 in H4. eapply IHeval_builtin_arg2 in H5.
      destruct H4 as [Heval1|Habort]; [|right; intros; intro C; inv C; eapply Habort; eauto].
      destruct H5 as [Heval2|Habort]; [|right; intros; intro C; inv C; eapply Habort; eauto].
      destruct Heval1 as (v1' & Heval1 & Hfp1). destruct Heval2 as (v2' & Heval2 & Hfp2).
      left. eexists. split. econstructor; eauto.
      destruct Hfp1 as [[Hdrf1 Hv1']|Hrace1]; [|right]. destruct Hfp2 as [[Hdrf2 Hv2']|Hrace2]; [left|right].
      subst.  split; auto. intro C. eapply conflictc_union in C. destruct C; eauto.
      eapply conflictc_union'; eauto. eapply conflictc_union'; eauto. }
  Qed.
  
  Lemma meminv_eval_builtin_args:
    forall t sm bufs tm fl sfm tfm (rs: Asm.preg -> val) sp args vargs fp,
      meminv t fl sm bufs tm ->
      embed sm fl sfm ->
      embed tm fl tfm ->
      eval_builtin_args tge rs sp (mktsofmem (bufs t) tfm) args vargs ->
      MemOpFP.eval_builtin_args_fp tge rs sp args fp ->
      (exists vargs', AsmLang.eval_builtin_args sge rs sp sfm args vargs' /\
                 ((~ conflictc t fp bufs /\ vargs = vargs')
                  \/ conflictc t fp bufs))
      \/
      (forall vargs', ~ AsmLang.eval_builtin_args sge rs sp sfm args vargs').
  Proof.
    intros. revert fp H3. induction H2; intros fp Hfp; inv Hfp. 
    left. eexists. split. econstructor. left; split; auto using emp_not_conflictc.
    exploit meminv_eval_builtin_arg; eauto.
    intros [Heval|Habort]; [|right; intros; intro C; inv C; eapply Habort; eauto].
    exploit IHlist_forall2; eauto.
    intros [Heval'|Habort]; [|right; intros; intro C; inv C; eapply Habort; eauto].
    destruct Heval as (v' & Heval & Hfp). destruct Heval' as (args' & Heval' & Hfp').
    left. eexists. split. econstructor; eauto.
    destruct Hfp as [[Hdrf Hv']|Hrace]; [|right]. destruct Hfp' as [[Hdrf' Hargs']|Hrace']; [|right].
    left. subst. split; auto. intro C. eapply conflictc_union in C. destruct C; eauto.
    eapply conflictc_union'; eauto. eapply conflictc_union'; eauto. 
  Qed.

  Lemma meminv_eval_builtin_arg':
    forall t sm bufs tm fl sfm tfm (rs: Asm.preg -> val) sp arg v,
      meminv t fl sm bufs tm ->
      (forall t', bufs t' = nil) ->
      embed sm fl sfm ->
      embed tm fl tfm ->
      AsmLang.eval_builtin_arg sge rs sp sfm arg v ->
      eval_builtin_arg tge rs sp (mktsofmem (bufs t) tfm) arg v.
  Proof.
    intros. induction H3; try (econstructor; eauto; fail).
    { destruct Val.offset_ptr eqn:Haddr; try discriminate.
      exploit meminv_load_refine'; try exact H; eauto. intros Hload.
      econstructor; eauto. rewrite Haddr. simpl. rewrite H0. simpl. inv H2. eauto. }
    { rewrite senv_symbol_address_eq in H3. destruct Senv.symbol_address eqn:Haddr; try discriminate.
      exploit meminv_load_refine'; try exact H; eauto. intros Hload.
      econstructor; eauto. rewrite Haddr. simpl. rewrite H0. simpl. inv H2. eauto. }
    { rewrite senv_symbol_address_eq. econstructor. }
  Qed.
    
  Lemma meminv_eval_builtin_args':
    forall t sm bufs tm fl sfm tfm (rs: Asm.preg -> val) sp args vargs,
      meminv t fl sm bufs tm ->
      (forall t', bufs t' = nil) ->
      embed sm fl sfm ->
      embed tm fl tfm ->
      AsmLang.eval_builtin_args sge rs sp sfm args vargs ->
      eval_builtin_args tge rs sp (mktsofmem (bufs t) tfm) args vargs.
  Proof.
    intros. induction H3. econstructor.
    exploit meminv_eval_builtin_arg'; eauto. intros Heval. 
    econstructor; eauto.
  Qed.
            
  Lemma invert_symbol_from_string_eq:
    forall name, invert_symbol_from_string tge name = invert_symbol_from_string sge name.
  Proof.
    intros name.
    unfold invert_symbol_from_string.
    unfold invert_block_from_string.
    unfold Genv.invert_symbol.
    repeat rewrite PTree.fold_spec.
    exploit PTree.elements_extensional. exact find_def_eq. intro A.
    simpl in *. unfold fundef in *. rewrite A.
    destruct fold_left; auto.
    repeat rewrite PTree.fold_spec.
    exploit PTree.elements_extensional. exact symbols_preserved. intro B.
    simpl in *. unfold fundef in *. unfold block in B. rewrite B. auto.
  Qed.
  
  Ltac simpl_hypos:=
  match goal with
  | [H1: ?x = _, H2: ?x = _ |- _] => rewrite H1 in H2; inv H2; simpl in *; simpl_hypos
  | [H1: context[Genv.find_funct_ptr sge _], H2: context[Genv.find_funct_ptr tge _] |- _ ]
    => rewrite function_ptr_eq in H1; simpl in *; simpl_hypos
  | _ => idtac
  end.

  
  Record match_state (t: tid) (scm: core AsmLang * gmem) (tcm: core AsmLang * tsomem) : Prop :=
    {
      match_sep_obj_clt: sep_obj_client_block (snd scm);
      match_core: fst scm = fst tcm;
      match_mem: Ic (snd scm) (snd tcm);
    }.

  Local Hint Resolve FP.subset_refl FP.subset_emp.
  
  Lemma meminv_exec_instr_eq:
    forall t sfm bufs (tfm: Mem.mem) f i rs rs' tsofm' tfp,
      let fl := Mem.freelist sfm in
      let sgm := strip sfm in
      let tgm := mktsomem bufs (strip tfm) in
      Mem.freelist sfm = Mem.freelist tfm ->
      meminv t fl sgm bufs (strip tfm) ->
      exec_instr_TSO tge f i rs (mktsofmem (bufs t) tfm) = Next rs' tsofm' ->
      exec_instr_TSO_fp tge f i rs (mktsofmem (bufs t) tfm) = tfp ->
      (* case 1: can execute *)
      (exists srs' sfp sfm',
          exec_instr sge f i rs sfm = AsmLang.Next srs' sfm' /\
          exec_instr_fp sge f i rs sfm = sfp /\
          (* subcase 1: fp not conflict with other threads' buffers *)
          ((~ conflictc t tfp bufs) /\
           srs' = rs' /\
           fpmatchc sfp tfp /\
           meminv t fl (strip sfm') (tupdate t (tbuffer tsofm') bufs) (strip (fmemory tsofm')) /\
           Gc t sgm tgm
              (strip sfm') (mktsomem (tupdate t (tbuffer tsofm') bufs) (strip (fmemory tsofm')))
           \/
           (* subcase 2: fp conflicts with other threads' buffers *)
           (conflictc t tfp bufs /\
            fpmatchc sfp tfp)
          )
      )
      \/
      exec_instr sge f i rs sfm = AsmLang.Stuck.
  Proof.
    intros t sfm bufs tfm f i rs rs' tsofm' tfp fl sgm tgm Hfreelist Hmeminv HexecTSO Htfp.
    destruct i; eauto; simpl in HexecTSO, Htfp; try discriminate. 
    (* trivial cases: *)
    all:
      simpl; unfold goto_label, tso_goto_label in *; simpl in HexecTSO; simpl;
      repeat match goal with
             | H : match ?a with _ => _ end = Next _ _ |- _ =>
               destruct a eqn:?Ha; try discriminate
             end.
    all:
      match goal with
      | H: Next _ _ = Next _ _ |- _ => simpl; inv HexecTSO
      | _ => idtac
      end;
      match goal with
      | |- context[AsmLang.Next ?srs' ?sfm' = AsmLang.Next _ _] =>
        left; eexists srs', FP.emp, sfm'; split; auto; split; auto; left
      | _ => idtac
      end.
    all:
      match goal with
      | |- ~ conflictc _ _ _ /\ _ =>
        simpl;
          repeat rewrite tupdate_update_same;
          repeat rewrite symbol_address_eq;
          repeat rewrite eval_addrmode32_eq;
          repeat rewrite eval_addrmode64_eq; 
          split; auto using emp_not_conflictc;
            split; auto;
              split; try apply FP.subset_emp; auto;
                split; auto;
                  destruct Hmeminv; auto using Gc_refl
      | _ => idtac
      end.
    
    (* exec_load *)
    (* unfold exec_load to mem load *)
    all:
      match goal with
      | H: exec_load_TSO _ _ _ _ _ _ = _ |- _ =>
        simpl; unfold exec_load_TSO in H; unfold exec_load_fp in *; unfold exec_load, exec_load_fp;
          destruct tsoloadv eqn:Hload; inv HexecTSO;
            unfold tsoloadv, Mem.loadv in *;
            rewrite <- eval_addrmode_eq; destruct eval_addrmode; try discriminate
      | _ => idtac
      end.
    (* construct SC load and eliminate abort case *)
    all:
      match goal with
      | H: tsoload _ _ _ _ = Some _ |- _ =>
        exploit load_refine; try exact Hmeminv; eauto;
          [subst fl sgm; rewrite Hfreelist; econstructor; eauto| econstructor; eauto | ];
          intros [Hstep|Habort]; [left|right; destruct Mem.load; [exfalso; eapply Habort|]; eauto]
      | _ => idtac
      end.
    (* done *)
    all:
      try
        (destruct Hstep as (sfp & sres & sfm' & (Hsfm' & Hload' & Hsfp) & [Hstep|Hrace]);
         rewrite Hload'; simpl; do 3 eexists; repeat (split; eauto);
         left; destruct Hstep as (Hconflict & Hfpmatch & Hres & Hmeminv' & HGc); subst; repeat (split; auto);
         fail).

    (* exec_store *)
    (* unfold exec_store to mem store *)
    all: 
      match goal with
      | H: exec_store_TSO _ _ _ _ _ _ _ = _ |- _ =>
        simpl; unfold exec_store_TSO, exec_store_fp, exec_store, exec_store_fp in *;
          destruct tsostorev eqn:Hstore; inv H;
            unfold tsostorev, Mem.storev in *;
            try rewrite <- eval_addrmode_eq; destruct eval_addrmode; try discriminate
      | _ => idtac
      end.
    (* construct SC store and eliminate abort case *)
    all:
      match goal with
      | H: tsostore _ _ _ _ _ = Some _ |- _ =>
        exploit store_refine; try exact Hmeminv; eauto;
          [subst fl sgm; rewrite Hfreelist; econstructor; eauto| econstructor; eauto | ];
          intros [Hstep|Habort]; [left|right; destruct Mem.store; [exfalso; eapply Habort|]; eauto using tt]
      | _ => idtac
      end.
    all:
      match goal with
      | H: tsostore _ _ _ _ _ = Some _ |- _ =>
        instantiate (1:=tt) in Hstep;
          destruct Hstep as (sfp & sres & sfm' & (Hstore' & Hsfp) & [Hstep|Hrace]); subst;
            rewrite Hstore'; simpl; do 3 eexists; repeat (split; eauto);
              left; destruct Hstep as (Hconflict & A & Hres & Hmeminv' & HGc); repeat (split; auto)
      | _ => idtac
      end.

    (* compare_ints *)
    { destruct (check_compare_ints) eqn: Hcheck; [left|right; auto].
      do 3 eexists. split. eauto. split. eauto.
      match goal with
      | |- context[conflictc ?a ?b ?c] =>
        destruct (Classical_Prop.classic (conflictc a b c)); [right; split; auto|left; simpl]
      end.
      eapply meminv_compare_ints_fp_subset; eauto.
      rewrite tupdate_update_same.
      split. auto. exploit meminv_compare_ints_not_conflict_eq; eauto.
      intros Hres. rewrite Hres. 
      split; auto. split; auto.
      eapply meminv_compare_ints_fp_subset; eauto. split. auto.
      subst sgm tgm. eapply Gc_refl. destruct Hmeminv; auto. }
    
    (* compare_longs *)
    { left. do 3 eexists. split; eauto. split; eauto. simpl.
      match goal with
      | |-context[conflictc ?a ?b ?c] => destruct (Classical_Prop.classic (conflictc a b c)); [right; split; auto|left]
      end.
      unfold compare_longs_fp, compare_longs_TSO_fp.
      unfold Cop_fp.cmplu_bool_fp_total, tso_cmplu_bool_fp_total.
      destruct Archi.ptr64 eqn:C; inv C; simpl. apply FP.subset_refl.
      split. auto. split. 
      unfold compare_longs_TSO, compare_longs, Val.cmplu, Val.cmplu_bool.
      destruct Archi.ptr64 eqn:C; inv C; simpl; auto.
      split.
      unfold compare_longs_fp, compare_longs_TSO_fp.
      unfold Cop_fp.cmplu_bool_fp_total, tso_cmplu_bool_fp_total.
      destruct Archi.ptr64 eqn:C; inv C; simpl; apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.
    }

    { destruct (check_compare_ints) eqn: Hcheck; [left|right; auto].
      do 3 eexists. split. eauto. split. eauto.
      match goal with
      | |- context[conflictc ?a ?b ?c] =>
        destruct (Classical_Prop.classic (conflictc a b c)); [right; split; auto|left; simpl]
      end.
      eapply meminv_compare_ints_fp_subset; eauto.
      rewrite tupdate_update_same.
      split. auto. exploit meminv_compare_ints_not_conflict_eq; eauto.
      intros Hres. rewrite Hres. 
      split; auto. split; auto.
      eapply meminv_compare_ints_fp_subset; eauto. split. auto.
      subst sgm tgm. eapply Gc_refl. destruct Hmeminv; auto. }
    
    { left. do 3 eexists. split; eauto. split; eauto. simpl.
      match goal with
      | |-context[conflictc ?a ?b ?c] => destruct (Classical_Prop.classic (conflictc a b c)); [right; split; auto|left]
      end.
      unfold compare_longs_fp, compare_longs_TSO_fp.
      unfold Cop_fp.cmplu_bool_fp_total, tso_cmplu_bool_fp_total.
      destruct Archi.ptr64 eqn:C; inv C; simpl. apply FP.subset_refl.
      split. auto. split. 
      unfold compare_longs_TSO, compare_longs, Val.cmplu, Val.cmplu_bool.
      destruct Archi.ptr64 eqn:C; inv C; simpl; auto.
      split.
      unfold compare_longs_fp, compare_longs_TSO_fp.
      unfold Cop_fp.cmplu_bool_fp_total, tso_cmplu_bool_fp_total.
      destruct Archi.ptr64 eqn:C; inv C; simpl; auto. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.
    }

    (* compare zero *)
    { assert (Val.and (rs (Asm.IR r1)) (rs (Asm.IR r2)) = Vundef \/
              exists n, Val.and (rs (Asm.IR r1)) (rs (Asm.IR r2)) = Vint n) as [HVundef|[n HInt]].
      { destruct (rs (Asm.IR r1)), (rs (Asm.IR r2)); simpl; auto. right. eauto. }
      rewrite HVundef. unfold compare_ints_TSO_fp, compare_ints_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_ints, compare_ints_TSO, Val.cmpu; simpl; auto.
      split; auto. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.

      rewrite HInt. unfold compare_ints_TSO_fp, compare_ints_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_ints, compare_ints_TSO, Val.cmpu; simpl; auto.
      split; auto. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.
    }
    { assert (Val.andl (rs (Asm.IR r1)) (rs (Asm.IR r2)) = Vundef \/
              exists n, Val.andl (rs (Asm.IR r1)) (rs (Asm.IR r2)) = Vlong n) as [HVundef|[n HInt]].
      { destruct (rs (Asm.IR r1)), (rs (Asm.IR r2)); simpl; auto. right. eauto. }
      rewrite HVundef. unfold compare_longs_TSO_fp, compare_longs_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_longs, compare_longs_TSO, Val.cmpu; simpl; auto.
      split. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.

      rewrite HInt. unfold compare_longs_TSO_fp, compare_longs_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_longs, compare_longs_TSO, Val.cmpu; simpl; auto.
      split. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.
    }
    { assert (Val.and (rs (Asm.IR r1)) (Vint n) = Vundef \/
              exists n', Val.and (rs (Asm.IR r1)) (Vint n) = Vint n') as [HVundef|[n' HInt]].
      { destruct (rs (Asm.IR r1)); simpl; auto. right. eauto. }
      rewrite HVundef. unfold compare_ints_TSO_fp, compare_ints_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_ints, compare_ints_TSO, Val.cmpu; simpl; auto.
      split. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.

      rewrite HInt. unfold compare_ints_TSO_fp, compare_ints_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_ints, compare_ints_TSO, Val.cmpu; simpl; auto.
      split. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.
    }
    { assert (Val.andl (rs (Asm.IR r1)) (Vlong n) = Vundef \/
              exists n', Val.andl (rs (Asm.IR r1)) (Vlong n) = Vlong n') as [HVundef|[n' HInt]].
      { destruct (rs (Asm.IR r1)); simpl; auto. right. eauto. }
      rewrite HVundef. unfold compare_longs_TSO_fp, compare_longs_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_longs, compare_longs_TSO, Val.cmpu; simpl; auto.
      split. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.

      rewrite HInt. unfold compare_longs_TSO_fp, compare_longs_fp. simpl. rewrite FP.fp_union_emp.
      left. do 3 eexists. split; eauto. split; eauto. left; split; auto using emp_not_conflictc.
      split. unfold compare_longs, compare_longs_TSO, Val.cmpu; simpl; auto.
      split. apply FP.subset_refl.
      subst sgm tgm. rewrite tupdate_update_same. split. auto. destruct Hmeminv. auto using Gc_refl.
    }

    (* free *)
    (* construct load ra *)
    exploit load_refine.
    eauto. subst sgm fl. constructor; eauto. subst fl. econstructor. rewrite <- Hfreelist. eauto. eauto.
    split. eauto. split. simpl in Ha. eauto. eauto.
    intros [Hload1 | Habort]; [|right].
    destruct Hload1 as (sfp1 & v' & sfm' & (Hsfm' & Hload1 & Hsfp1) & Hloadmatch1); subst sfp1 sfm'.
    rewrite Hload1.
    (* construct load link *)
    exploit load_refine.
    eauto. subst sgm fl. constructor; eauto. subst fl. econstructor. rewrite <- Hfreelist. eauto. eauto.
    split. eauto. split. simpl in Ha0. eauto. eauto.
    intros [Hload2 | Habort]; [|right].
    destruct Hload2 as (sfp2 & v0' & sfm' & (Hsfm' & Hload2 & Hsfp2) & Hloadmatch2); subst sfp2 sfm'.
    rewrite Hload2.
    (* construct free *)
    exploit free_refine.
    eauto. subst sgm fl. constructor; eauto. subst fl. econstructor. rewrite <- Hfreelist. eauto. eauto.
    split; eauto. unfold tsofree. eauto.
    intros [Hfree | Habort]; [|right].
    destruct Hfree as (sfp3 & sres & sfm' & (Hfree & Hsfp3) & Hfreematch); subst sfp3.
    rewrite Hfree.

    left.
    simpl in *. clear Hload1 Hload2 Hfree Ha Ha0. instantiate (1:=tt) in Hfreematch.
    do 3 eexists. split. eauto. split. eauto.
    (* race load1 ? *)
    destruct Hloadmatch1 as [Hloadmatch1 | Hrace1]; [|right].
    destruct Hloadmatch1 as (Hdrf1 & _ & Hv' & _ & _).
    (* race load2 ? *)
    destruct Hloadmatch2 as [Hloadmatch2 | Hrace2]; [|right].
    destruct Hloadmatch2 as (Hdrf2 & _ & Hv0' & _ & _).
    (* race free ? *)
    destruct Hfreematch as [(Hdrf3 & _ & Hres & Hmeminv' & HGc') | Hrace3]; [|right].
    
    left. split. intro.
    eapply conflictc_union in H. destruct H; eauto.
    eapply conflictc_union in H. destruct H; eauto.
    split. subst. auto.
    split. apply FP.subset_refl.
    split; auto.

    split; [| apply FP.subset_refl]. apply conflictc_union'. tauto.
    split; [| apply FP.subset_refl]. apply conflictc_union'. left. apply conflictc_union'. tauto.
    split; [| apply FP.subset_refl]. apply conflictc_union'. left. apply conflictc_union'. tauto.

    destruct Mem.free; auto; exfalso. eapply Habort; econstructor; eauto.
    destruct (Mem.load Mptr sfm b (Ptrofs.unsigned (Ptrofs.add i ofs_link))); auto.
    exfalso. eapply Habort. split; eauto.
    destruct (Mem.load Mptr sfm b (Ptrofs.unsigned (Ptrofs.add i ofs_ra))); auto.
    exfalso. eapply Habort. split; eauto.
  Qed.
    
  Lemma meminv_exec_instr_eq':
    forall f i rs sm bufs tm t fl sfm rs' sfm' tfm,
      embed sm fl sfm ->
      embed tm fl tfm ->
      meminv t fl sm bufs tm ->
      (forall t', bufs t' = nil) ->
      exec_instr sge f i rs sfm = AsmLang.Next rs' sfm' ->
      not_alloc_instr i ->
      exists rs'' b',
        exec_instr_TSO tge f i rs (mktsofmem (bufs t) tfm) = Next rs'' (mktsofmem b' tfm) /\
        exists tm', apply_buffer b' tm = Some tm'.
  Proof.
    intros f i rs sm bufs tm t fl sfm rs' sfm' tfm Hembed Hembed' Hmeminv Hbuffer Hexec Hnotalloc.
    destruct i; inv Hnotalloc; simpl in Hexec; eauto.
    (* trivial cases: *)    
    all: simpl; unfold goto_label, tso_goto_label in *; simpl in Hexec; simpl; try discriminate;
      repeat match goal with
             | H : match ?a with _ => _ end = AsmLang.Next _ _ |- _ =>
               destruct a eqn:?Ha; try discriminate; simpl in Ha
             end.
    all:
      match goal with
      | H: AsmLang.Next _ _ = AsmLang.Next _ _ |- _ =>
        simpl; inv H;
          repeat rewrite Hbuffer;
          repeat rewrite tupdate_update_same;
          repeat rewrite symbol_address_eq;
          repeat rewrite eval_addrmode32_eq;
          repeat rewrite eval_addrmode64_eq;
          simpl
      | _ => idtac
      end;
      match goal with
      | |- context[Next ?srs' ?sfm' = Next _ _] =>
        eexists _, _; split; eauto; simpl; eauto
      | _ => idtac
      end.

    (* exec_load *)
    (* unfold exec_load to mem load *)
    all:
      match goal with
      | H: exec_load _ _ _ _ _ _ = _ |- _ =>
        simpl; unfold exec_load in H; unfold exec_load_fp in *; unfold exec_load_TSO;
          destruct Mem.loadv eqn:Hload; inv Hexec;
            unfold Mem.loadv, tsoloadv in *;
            rewrite eval_addrmode_eq; destruct eval_addrmode; try discriminate
      | _ => idtac
      end.
    (* construct TSO load *)
    all:
      repeat match goal with
             | H: Mem.load ?chunk _ ?b ?ofs = Some _ |- context[tsoload ?chunk _ ?b ?ofs] =>
               unfold tsoload; rewrite Hbuffer; simpl; exploit meminv_load_refine'; try exact Hembed; inv Hembed'; eauto;
                 intros A; rewrite A; eexists _, _; split; eauto; simpl; eauto
             end.

    (* exec_store *)
    (* unfold exec_store to mem store *)
    all: 
      match goal with
      | H: exec_store _ _ _ _ _ _ _ = _ |- _ =>
        simpl; unfold exec_store_TSO, exec_store_fp, exec_store, exec_store_fp in *;
          destruct Mem.storev eqn:Hstore; inv H;
            unfold tsostorev, Mem.storev in *;
            try rewrite eval_addrmode_eq; destruct eval_addrmode; try discriminate
      | _ => idtac
      end.
    (* construct SC store and eliminate abort case *)
    all:
      match goal with
      | H: Mem.store _ _ _ _ _ = _ |- _ =>
        exploit (meminv_store_refine' sm tm fl sfm tfm bufs t); eauto; intros (buf' & Hstore' & Happly);
          rewrite Hstore'; eexists _, buf'; simpl; eauto
      | _ => idtac
      end.

    (* cmpu *)
    unfold check_compare_ints_TSO, check_compare_ints in *.
    destruct Val.cmpu_bool eqn:A; try discriminate.
    eapply meminv_cmpu_bool_Some_refine' in A; eauto. destruct A as [? A].
    rewrite Hbuffer in A. rewrite A. do 2 eexists. split. eauto. simpl. eauto.
    

    unfold check_compare_ints_TSO, check_compare_ints in *.
    destruct Val.cmpu_bool eqn:A; try discriminate.
    eapply meminv_cmpu_bool_Some_refine' in A; eauto. destruct A as [? A].
    rewrite Hbuffer in A. rewrite A. do 2 eexists. split. eauto. simpl. eauto.

    (* free *)
    simpl in Ha0. unfold buffer_insert. simpl.
    exploit meminv_load_refine'; try exact Hembed; try exact Ha; (eauto; try inv Hembed'; eauto).
    intros Hload1. rewrite Hload1. 
    exploit meminv_load_refine'; try exact Hembed; try exact Ha0; (eauto; try inv Hembed'; eauto).
    intros Hload2. rewrite Hload2.
    eexists _, _. split. eauto. 
    eapply meminv_free_refine'; eauto.
  Qed.

  


  Lemma match_state_clientsim_properties:
    @clientsim_properties Rc Gc Ic AsmLang sge sge tge match_state.
  Proof.
    constructor.
    { (* init match *)
      intros. exists tc. split.
      unfold AsmTSO.init_core in H. unfold init_core. simpl.
      destruct HSINITGE as [_ HSINITGE'].
      unfold ASM_local.init_core in *.
      erewrite <- symbols_preserved. destruct Genv.find_symbol; [|discriminate].
      erewrite function_ptr_eq. destruct Genv.find_funct_ptr; [auto|discriminate].
      intros. constructor; auto. }
    { (* init None match *)
      intros. unfold AsmTSO.init_core in H. unfold init_core. simpl.
      destruct HSINITGE as [_ HSINITGE'].
      unfold ASM_local.init_core in *.
      erewrite <- symbols_preserved; eauto. destruct Genv.find_symbol; auto.
      erewrite function_ptr_eq; eauto. }
    { (* tau step *)
      intros t sc sm tc tm fl b m tfp tc' b' m' MS Hbuffer Hmem Hfl Hvalideq Hstep tm'.
      exploit match_core. eauto. simpl. intro. subst sc.
      inv Hstep. rename H4 into Hembed'.
      destruct (Classical_Prop.classic (exists sfm, embed sm fl sfm))
        as [[sfm Hembed]|C]; [|right; intros; intro C'; inv C'; eauto].
      assert (Hstrip: strip sfm = sm).
      { inv Hembed; auto. }
      assert (Hstrip': strip fm = memory tm).
      { inv Hembed'; auto. }
      {
        inv H7.
        (* exec instr *)
        { exploit (meminv_exec_instr_eq t sfm (tso_buffers tm) fm). 
          { inv Hembed; inv Hembed'; auto. }
          { exploit match_mem. eauto. simpl. intro HIc. inv Hembed.
            constructor.
            rewrite Hstrip'. destruct tm; simpl; auto.
            destruct MS. auto.
            rewrite Hstrip'. destruct tm; simpl; auto.
            rewrite Hstrip'. destruct tm; simpl; auto. }
          { eauto. }
          { eauto. }
          intros [ (srs' & sfp & sfm' & Hexec & Hexecfp & Hmatch) | Hstuck].
          { (* match step *)
            left. exists sfp, (Core_State srs' lf), (strip sfm').
            split.
            { econstructor; eauto.
              econstructor; eauto.
              rewrite function_ptr_eq; auto. }
            destruct Hmatch as [Hresults|Hconflict]; [left|right; auto].
            { (* not conflict *)
              destruct Hresults as (Hsmile & Hrs & Hfp & Hmeminv' & HGc'). subst srs'.
              (* conflictc *) split. auto.
              (* fp *) split. subst. auto.
              (* Gc? *) split. subst tm'. rewrite Hstrip' in HGc'. destruct tm. auto.
              (* match_state *) split.
              split; simpl; destruct Hmeminv'; auto.
              (* tm_alloc *) split.
              destruct Hmeminv'. inv Hembed; inv Hembed'. subst tm'. auto.
              (* relvb *)
              destruct Hmeminv'. inv Hembed; inv Hembed'. subst tm'. auto.
            }
          }
          { (* stuck *)
            right. intros FP sc'' sm'' C.
            inv C. inv H4. exploit strip_fl_eq_fmem_eq. eauto. inv Hembed. eauto. intro; subst m.
            inv H5; simpl_hypos. discriminate. }
        }
        (* alloc frame *)
        { simpl.
          (* construct allocation *)
          exploit alloc_refine.
          { constructor. exploit match_mem. eauto. simpl.
            instantiate (1:= memory tm). instantiate (1:= tso_buffers tm).
            replace tm with {| tso_buffers := tso_buffers tm; memory := memory tm |} at 1.
            eauto. destruct tm; auto.
            apply match_sep_obj_clt in MS. eauto.
            replace tm with {| tso_buffers := tso_buffers tm; memory := memory tm |} in Hvalideq.
            eauto. destruct tm; auto.
            replace tm with {| tso_buffers := tso_buffers tm; memory := memory tm |} in Hvalideq.
            eauto. destruct tm; auto. }
          { eauto. }
          { eauto. }
          { eauto. }
          intros [HAllocSucceed|C];
            [| exfalso; destruct (Mem.alloc sfm 0 sz); eapply C; eauto].
          destruct HAllocSucceed as (sfp1 & stk' & sfm1 & [Halloc Hsfp1] & [Hmatch|Hconflict0]);[|].
          (* if conflictc, either conflictc as a whole or abort *)
          (* need lemma : conflictc fp -> conflictc (FP.union fp _) *)
          destruct Hmatch as (Hdrf1 & Hsfp1' & Hstk' & Hmeminv1 & HGc1).
          subst stk'.
          (* construct store RSP *)
          exploit store_refine.
          exact Hmeminv1.
          { instantiate (1:= sfm1). constructor; auto.
            erewrite Mem.alloc_freelist; eauto.
            inv Hembed. auto. }
          { instantiate (1:= fmemory bm'). constructor; auto.
            inv Hembed'. inv H2. simpl. auto. }
          { unfold tupdate. destruct peq; [|contradiction]. split; [|eauto].
            replace bm' with {| tbuffer := tbuffer bm'; fmemory := fmemory bm' |} in H4; [|destruct bm'; auto].
            simpl in H4. eauto. }
          intros [HStore1Succeed|C]; [|right].
          (* must succeed, by H4... *)
          destruct HStore1Succeed as (sfp2 & sres & sfm2 & [Hstore Hsfp2] & [Hmatch|Hconflict1]); [|exfalso].
          (* cannot conflict because alloc not conflict... *)
          destruct Hmatch as (Hdrf2 & Hsfp2' & Hres2 & Hmeminv2 & HGc2).
          instantiate (1:= tt) in Hres2. subst sres.
          (* construct store RA *)
          exploit store_refine.
          exact Hmeminv2.
          { instantiate (1:= sfm2). constructor; auto.
            erewrite Mem.store_freelist; eauto. erewrite Mem.alloc_freelist; eauto.
            inv Hembed. auto. }
          { instantiate (1:= fmemory bm2). constructor; auto.
            unfold tsostorev in *. do 2 (destruct Val.offset_ptr; try discriminate).
            unfold tsostore in *. inv H4. inv H5. simpl.
            inv Hembed'. inv H2. simpl. auto. }
          { unfold tupdate. destruct peq; [|contradiction]. split.
            replace bm2 with {| tbuffer := tbuffer bm2; fmemory := fmemory bm2 |} in H5; [|destruct bm2; auto].
            simpl in H5. eauto. eauto. }
          intros [HStore2Succeed|C]; [|right].
          (* must succeed, by H5... *)
          destruct HStore2Succeed as (sfp3 & sres' & sfm3 & [Hstore' Hsfp3] & [Hmatch|Hconflict2]); [|exfalso].
          (* cannot conflict because alloc not conflict... *)
          destruct Hmatch as (Hdrf3 & Hsfp3' & Hres3 & Hmeminv3 & HGc3).
          instantiate (1:= tt) in Hres3. subst sres'.
          (* construct step *)
          left. eexists _, _, _.
          (*(FP.union (tsoalloc_fp stk 0 sz)
                                  (FP.union (store_fp Mptr stk _) (store_fp Mptr stk _))), _, _.*)
          split.
          { econstructor. eauto. econstructor; eauto.
            rewrite function_ptr_eq; auto.
            simpl. rewrite Halloc. rewrite Hstore. rewrite Hstore'. eauto. eauto. }
          (* not conflict *)
          left. split.
          intro.
          
          apply conflictc_union in H3. destruct H3 as [Hc1|Hc23].
          apply Hdrf1; auto.
          apply conflictc_union in Hc23. destruct Hc23 as [Hc2|Hc3].
          apply Hdrf2. eapply conflictc_ext. eauto.
          clear. intros. unfold tupdate. destruct peq; congruence.
          apply Hdrf3. eapply conflictc_ext. eauto.
          clear. intros. unfold tupdate. destruct peq; congruence.
          (* FP *)
          split. simpl. rewrite Halloc.
          unfold tsoalloc_fp, alloc_fp. apply Mem.alloc_result in Halloc. subst stk. 
          apply FP.subset_refl.
          (* Gc *)
          split.
          eapply Gc_trans.
          replace tm with {| tso_buffers := tso_buffers tm; memory := memory tm |} at 1.
          eauto. destruct tm; auto.
          eapply Gc_trans. eauto. subst tm'.
          do 2 rewrite tupdate_update2 in HGc3.
          rewrite tupdate_update2. auto.
          (* match state *)
          split.
          { split; simpl; auto.
            subst tm'; inv Hmeminv3; auto.
            subst tm'; inv Hmeminv3; auto.
            generalize meminv_Ic0; clear. do 2 rewrite tupdate_update2. auto. }
          (* alloc local *)
          split. subst tm'. inv Hmeminv3. do 2 rewrite tupdate_update2 in meminv_alloc_local0. auto.
          (* rel vb *)
          subst tm'. inv Hmeminv3. do 2 rewrite tupdate_update2 in meminv_rel_vb0. auto.
          (* contradictions *)
          { (* by conflict ra fp, then conflict alloc fp, then contradicts *)
            destruct Hconflict2 as [Hc _].
            
            eapply conflict_store_conflict_alloc in Hc. eapply Hdrf1.
            eapply conflictc_ext. eauto. clear. unfold tupdate. intros.
            destruct peq; auto; contradiction.
          }
          {
            intros. intro C'. inv C'.
            assert (sfm = m).
            { eapply TSOAuxDefs.embed_eq. eauto. eauto. } subst m.
            inv H6.
            { rewrite H in H9. inv H9.
              rewrite function_ptr_eq in H10. rewrite H0 in H10. inv H10.
              rewrite H1 in H11. inv H11. simpl in H12.
              rewrite Halloc, Hstore in H12.
              destruct (Mem.store _ _ _ _ (rs Asm.RA)) eqn:C'; try discriminate.
              eapply C. constructor. split; eauto. }
            { rewrite H in H9. inv H9.
              rewrite function_ptr_eq in H10. rewrite H0 in H10. inv H10.
              rewrite H1 in H11. inv H11. }
            { rewrite H in H9. inv H9.
              rewrite function_ptr_eq in H10. rewrite H0 in H10. inv H10. }
          }
          {
            destruct Hconflict1 as [Hc _].
            eapply conflict_store_conflict_alloc in Hc. eapply Hdrf1.
            eapply conflictc_ext. eauto. clear. unfold tupdate. intros.
            destruct peq; auto; contradiction.
          }
          {
            intros. intro C'. inv C'.
            assert (sfm = m).
            { eapply TSOAuxDefs.embed_eq. eauto. eauto. } subst m.
            inv H6.
            { rewrite H in H9. inv H9.
              rewrite function_ptr_eq in H10. rewrite H0 in H10. inv H10.
              rewrite H1 in H11. inv H11. simpl in H12.
              rewrite Halloc in H12.
              destruct (Mem.store _ _ _ _ (rs (Asm.IR Asm.RSP))) eqn:C'; try discriminate.
              eapply C. constructor. split; eauto. }
            { rewrite H in H9. inv H9.
              rewrite function_ptr_eq in H10. rewrite H0 in H10. inv H10.
              rewrite H1 in H11. inv H11. }
            { rewrite H in H9. inv H9.
              rewrite function_ptr_eq in H10. rewrite H0 in H10. inv H10. } 
          }
          {
            destruct Hconflict0 as [Hc _].
            assert (stk = stk').
            { exploit Mem.alloc_result. eauto. intro; subst stk'.
              inversion Hembed. inversion Hembed'. subst fl.  rewrite <- H7 in Hembed.
              inv H2. eapply eq_validity_eq_nextblock; eauto.
              intros. exploit Hvalideq. eauto. rewrite <- H8. eauto.
              simpl. rewrite <- H7. rewrite H2. auto. }
            subst stk'.
            destruct (Mem.store Mptr sfm1 stk (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_link)) (rs (Asm.IR Asm.RSP)))
                     eqn:Hstore1; [|right].
            destruct (Mem.store Mptr m stk (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_ra)) (rs Asm.RA))
                     eqn:Hstore2; [|right].
            left. do 3 eexists. split.
            { econstructor. eauto.
              econstructor; simpl; eauto.
              rewrite function_ptr_eq. eauto.
              simpl. rewrite Halloc, Hstore1, Hstore2. simpl. eauto. eauto. }
            right. split. eapply conflictc_union'. left. auto.
            simpl. rewrite Halloc. unfold alloc_fp, tsoalloc_fp.
            apply Mem.alloc_result in Halloc. subst. apply FP.subset_refl.

            intros. intro C. inv C. rewrite <- function_ptr_eq in H0. inv H6; try congruence.
            rewrite H in H9; inv H9. rewrite H0 in H10; inv H10. rewrite H1 in H11; inv H11.
            simpl in H12. exploit TSOAuxDefs.embed_eq. exact H3. exact Hembed. intro; subst m0.
            rewrite Halloc, Hstore1, Hstore2 in H12. discriminate.

            intros. intro C. inv C. rewrite <- function_ptr_eq in H0. inv H6; try congruence.
            rewrite H in H9; inv H9. rewrite H0 in H10; inv H10. rewrite H1 in H11; inv H11.
            simpl in H12. exploit TSOAuxDefs.embed_eq. exact H3. exact Hembed. intro; subst m.
            rewrite Halloc, Hstore1 in H12. discriminate.            
          }
        }
        (* builtin *)
        {
          (* Ic -> eval builtin args eq... *)
          exploit meminv_eval_builtin_args. eauto.
          { split; eauto. destruct tm; destruct MS; simpl in *; auto. destruct MS; auto. }
          eauto. eauto. eauto. eauto. intros [[vargs' [Heval A]]|Habort];[|right]. 
          eapply genv_match_eval_builtin_args_fp in H4; eauto.
          destruct (Classical_Prop.classic (exists vres', helpers.i64ext_sem ef vargs' vres'))
            as [[vres' Hhelper]|Habort]; [|right].
          left. eexists _, _, _.
          split. econstructor. eauto.
          eapply exec_step_builtin. eauto. rewrite function_ptr_eq. eauto.
          eauto. eauto. eauto. eauto. eauto. eauto. eauto.
          assert (tm' = tm).
          { subst tm'. destruct tm. inv Hembed'. simpl. rewrite H7. clear. simpl.
            f_equal. unfold tupdate. apply functional_extensionality. intro; destruct peq; subst; auto. }
          rewrite H6 in *. clear H6. clear tm'.
          destruct A as [[Hdrf Hvargs]|Hrace];[left; subst|right].
          assert (vres' = vres).
          { exploit helpers_i64ext_sem_det. exact H5. exact Hhelper. auto. }
          subst. split. auto. 
          split. apply FP.subset_refl.
          split. eapply Gc_refl. destruct MS; auto.
          split. constructor; simpl; destruct MS; auto.
          split; auto.
          split. auto. apply FP.subset_refl.

          { intros. intro C. inv C. rewrite <- function_ptr_eq in H0. inv H7.
            { rewrite H in H10. inv H10. rewrite H0 in H11. inv H11. rewrite H1 in H12; inv H12. discriminate. }
            { exploit TSOAuxDefs.embed_eq. exact H6. exact Hembed. intro; subst.
              rewrite H in H10. inv H10. rewrite H0 in H11. inv H11. rewrite H1 in H12; inv H12.
              eapply AsmLang.eval_builtin_args_determ in H14; try exact Heval. subst. eauto. }
            { rewrite H in H10. inv H10. rewrite H0 in H11. inv H11. }
          }
          
          intros. intro. inv H6. rewrite <- function_ptr_eq in H0. inv H8; try congruence.
          rewrite H in H10; inv H10. rewrite H0 in H11; inv H11. rewrite H1 in H12; inv H12.
          simpl in H13. discriminate.
          rewrite H in H10; inv H10. rewrite H0 in H11; inv H11. rewrite H1 in H12; inv H12.
          exploit TSOAuxDefs.embed_eq. exact Hembed. exact H7. intro. subst m'. eapply Habort. eauto.
        }
        (* extcall *)
        {
          (* Ic -> ext args eq... *)
          exploit meminv_extcall_arguments.
          { split; eauto. destruct tm; destruct MS; simpl in *; auto. destruct MS; auto. }
          eauto. eauto. eauto. eauto. intros [(args' & Hargs' & A)|Habort]; [left|right]. 
          eexists tfp, _, _. split. 
          econstructor. eauto. eapply exec_step_to_external; eauto. rewrite function_ptr_eq; auto. eauto.
          assert (tm' = tm).
          { subst tm'. destruct tm. inv Hembed'. simpl. rewrite H4. clear. simpl.
            f_equal. unfold tupdate. apply functional_extensionality. intro; destruct peq; subst; auto. }
          rewrite H3 in *. clear H3. clear tm'.
          destruct A as [[B Hargseq]|B]; [left; subst|right].
          split; auto.
          split; auto. apply FP.subset_refl.
          split. eapply Gc_refl. destruct MS; auto.
          split. constructor; simpl; destruct MS; auto. 
          split; auto.
          split. auto. apply FP.subset_refl.

          intros. intro. inv H3. rewrite <- function_ptr_eq in H0.
          exploit TSOAuxDefs.embed_eq. exact Hembed. exact H4. intro; subst m.
          inv H5; try congruence. rewrite H in H7. inv H7. rewrite H0 in H8; inv H8. eapply Habort. eauto.
        }
        (* helpers *)
        {
          left. do 3 eexists. split.
          econstructor. eauto. 
          econstructor; eauto. rewrite function_ptr_eq. eauto. eauto.
          left. split.
          clear. intro C. inv C.
          inv H1; Locs.unfolds; destruct H2 as ( ? & ? & H2) ;red_boolean_true.
          split. auto. apply FP.subset_refl.
          assert (X: tm' = tm).
          { subst tm'. simpl. destruct tm; simpl; f_equal.
            unfold tupdate. apply functional_extensionality. clear; intro.
            destruct peq; subst; auto. inv Hembed'; auto. }
          rewrite X in *. clear X. clear tm'.
          split.
          { apply Gc_refl. apply match_mem in MS. simpl in MS. auto.  }
          split.
          { constructor; inv MS; simpl in *; auto. }
          split; auto. 
        }
        (* initialize *)
        { assert (stk = Mem.nextblock sfm) as Hstk.
          { revert Hembed Hembed' Hvalideq H0. clear. intros.
            inv H0.
            assert (forall n, In (MemAux.get_block fl n) (GMem.validblocks gm') <->
                         In (MemAux.get_block fl n) (GMem.validblocks (strip sfm))).
            { intros. eapply Hvalideq. eauto. inv Hembed'. rewrite <- H0; auto. }
            inv Hembed; inv Hembed'.
            eapply eq_validity_eq_nextblock; eauto.
            intros. subst b. rewrite H0. eauto. econstructor; eauto.
          }
          destruct tm as [bufs tm].
          exploit meminv_initialize.
          { constructor; destruct MS; eauto. }
          eauto. eauto. eauto. eauto. eauto.
          intros [A|Habort]; [left|right].
          destruct A as (sfm1 & sfm' & Halloc & Hstoreargs & [(HGc & Hmeminv')|Hconflict]).
          destruct Hmeminv' as [Hic' Hsep' Hrelvb' Halloclocal'].
          do 3 eexists. split.
          { econstructor. eauto. econstructor; eauto. eauto. }
          { assert (tsoalloc_fp stk 0 (4 * z) = alloc_fp sfm 0 (4 * z)) as Hfpeq.
            { f_equal. unfold alloc_fp, tsoalloc_fp. congruence. }
            destruct (Classical_Prop.classic (conflictc t (tsoalloc_fp stk 0 (4 * z)) bufs)) as [Hconflict|Hconflict].
            { (* conflict *)
              right. split.
              apply conflictc_union'. left. auto.
              rewrite Hfpeq. apply FP.subset_refl. }
            { (* alloc not conflict... *)
              left. split.
              intro A. apply conflictc_union in A. destruct A as [A|A]. contradiction.
              eapply conflict_store_args_conflict_alloc in A; eauto.
              split. rewrite Hfpeq; auto. apply FP.subset_refl.
              split. auto. 
              split; auto.
              { constructor; auto. }
            }
          }
          
          do 3 eexists. split.
          { econstructor. eauto. econstructor; eauto. eauto. }
          right. split. eapply conflictc_union'. auto.
          subst stk. unfold alloc_fp, tsoalloc_fp. apply FP.subset_refl.
          
          intros. intro C. inv C. inv H3. exploit TSOAuxDefs.embed_eq. exact Hembed. exact H1.
          intro; subst m. rewrite H in H8; inv H8. rewrite H9 in Habort. simpl in Habort.
          eapply Mem.alloc_result in H9. subst. congruence.
        }
      }
    }
    { (* at_external *)
      intros. exploit match_core. eauto. simpl. intro. subst.
      unfold AsmTSO.at_external, ASM_local.at_external.
      destruct tc; auto. destruct f; auto. rewrite invert_symbol_from_string_eq. auto. }
    { (* after_external *)
      intros. exploit match_core. eauto. simpl. intro. subst.
      exists tc'. split; auto. constructor; inv H; auto. }
    { (* after_external None *)
      intros. exploit match_core. eauto. simpl. intro. subst. auto. }
    { (* halt *)
      intros. exploit match_core. eauto. simpl. intro. subst. auto. }
    { (* abort *)
      intros t sc sm tc tm fl m MS Halloclocal Hrelvb Hbuf Hmem Habort.
      destruct tm as [bufs tm]. simpl in *. subst m.
      destruct (Classical_Prop.classic (exists tfm, embed tm fl tfm)) as [[tfm Hembed]|C];
        [left|right; intros tfm C'; apply C; eauto].
      intros FP sc' sm' Hsstep.
      exploit match_core. eauto. simpl. intro. subst tc.
      inv Hsstep. inv H. inv H0.
      { (* exec instr *)
        destruct (Classical_Prop.classic (exists sz ofs_ra ofs_link, i = Pallocframe sz ofs_ra ofs_link))
          as [(sz & ofs_ra & ofs_link & Hallocinstr)| Hnotalloc].
        (* alloc *)
        { subst i. eapply Habort. split.
          econstructor; eauto.
          eapply tso_exec_step_internal_allocframe; eauto.
          rewrite <- function_ptr_eq. eauto.
          econstructor. simpl. eauto. inversion Hembed. rewrite H4. rewrite H0. eauto.
          simpl. unfold tsostore. eauto.
          simpl. unfold tsostore. eauto.
          exploit Pallocframe_succeed_link_ra_inrange. eauto. clear.
          intros [Hinrange_ra Hinrange_link].
          unfold buffer_insert. simpl.
          destruct store eqn:Hstore1; simpl.
          unfold store in Hstore1. simpl in *.
          destruct valid_access_dec; [|discriminate]. inv Hstore1.
          destruct store eqn:Hstore2; simpl. eauto.
          (* contradictions.. *)
          { clear v. unfold store in Hstore2.
            destruct valid_access_dec; [discriminate|].
            unfold valid_access, range_perm in *; simpl in *.
            exfalso; apply n. rewrite Ptrofs.add_zero_l.
            split;[|tauto].
            pose proof (Ptrofs.unsigned_range ofs_ra).
            intros. rewrite PMap.gss. destruct zle, zlt; simpl; try omega; try constructor. }
          { unfold store in Hstore1.
            destruct valid_access_dec; [discriminate|].
            unfold valid_access, range_perm in *; simpl in *.
            exfalso; apply n. rewrite Ptrofs.add_zero_l.
            split;[|tauto].
            pose proof (Ptrofs.unsigned_range ofs_link).
            intros. rewrite PMap.gss. destruct zle, zlt; simpl; try omega; try constructor. }
        }
        (* not alloc *)
        { (* Lemma meminv_exec_instr_eq': *)
          assert (not_alloc_instr i) as Hnotalloc'.
          { revert Hnotalloc. clear. intros. destruct i; simpl; eauto. }
          exploit meminv_exec_instr_eq'.
          econstructor. eauto. instantiate (2:= m). eauto.
          exact Hembed.
          { constructor; destruct MS; eauto. }
          auto. eauto. auto.
          intros (rs'' & b' & Hexec & Happly).
          eapply Habort. split. econstructor; eauto.
          eapply tso_exec_step_internal; eauto.
          rewrite <- function_ptr_eq. auto.
          rewrite <- (Hbuf t). eauto.
          simpl. inv Hembed. eauto.
        }
      }
      { (* builtin *)
        eapply Habort. split.
        econstructor; eauto.
        eapply tso_exec_step_builtin; eauto.
        rewrite <- function_ptr_eq. eauto.
        rewrite <- (Hbuf t). eapply meminv_eval_builtin_args'.
        { constructor; destruct MS; eauto. }
        eauto.
        simpl. econstructor; eauto. eauto. eauto. 
        eapply genv_match_eval_builtin_args_fp. eauto.
        simpl. eauto.
      }
      { (* to external *)
        eapply Habort. split.
        econstructor; eauto.
        eapply tso_exec_step_to_external; eauto.
        rewrite <- function_ptr_eq. eauto.
        (* extcall args eq *)
        rewrite <- (Hbuf t). replace bufs with (tso_buffers {| tso_buffers := bufs; memory := tm |}) by auto.
        eapply meminv_extcall_arguments'; try exact H2; eauto.
        { constructor; destruct MS; eauto. }
        simpl. constructor; auto. 
        simpl. eauto.
      }
      { (* i64ext *)
        eapply Habort. split.
        econstructor; eauto.
        eapply tso_exec_step_i64ext; eauto.
        rewrite <- function_ptr_eq. eauto.
        simpl. eauto.
      }
      { (* initialize *)
        exploit rel_vb_nextblock_eq. replace tm with (strip tfm) in Hrelvb. eauto.
        inv Hembed. auto. auto. inv Hembed; auto. auto. intro Hnext.
        exploit Mem.alloc_result. eauto. intro Hstk.
        exploit store_args_succeed_tso. eauto. eauto. intros (tfm' & Hstoreargs & [m'' Happly]).
        eapply Habort. split.
        econstructor; eauto.
        eapply exec_initialize_call; eauto.
        econstructor. simpl. eauto. inversion Hembed. rewrite H0, H2. eauto.
        eauto.
      }
    }
    { (* after_external None *)
      intros. exploit match_core. eauto. simpl. intro. subst. auto. }
    { (* Rely step *)
      intros. inv H0. inv H; constructor; auto. }
    { (* no atom block *)
      intros. unfold at_external in H0. simpl in H0.
      unfold ASM_local.at_external in H0. destruct sc; try discriminate.
      destruct f; try discriminate.
      destruct invert_symbol_from_string; try discriminate.
      destruct peq; try discriminate; destruct peq; try discriminate; simpl in *.
      inv H0. auto.
    }
  Qed.
    
End MatchStateSim.

(** identity x86 assembly modules satisfies the client simulation *)
Theorem clientsim_hold:
  forall cu
    (HNODUPGD: nodup_gd_ident (cu_defs cu) = true)
    (HNODUPEF: (nodup_ef (cu_defs cu)) = true),
    clientsim Rc Gc Ic AsmLang cu cu.
Proof.
  intros. intros sge sG tge HSINITGE HTINITGE HGENVMATCH.
  exists match_state. inversion HSINITGE. subst sG. clear H0.
  eapply match_state_clientsim_properties; eauto.
Qed.
