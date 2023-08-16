From mathcomp.ssreflect Require Import fintype ssrnat.
Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import CUAST.

Require Import Footprint GMemory FMemory.
Require Import GAST GlobDefs ETrace Blockset DRF.

Require Import Languages.
Require Import GlobSemantics RGRels ClientSim ObjectSim.

Require Import ASM_local.
Require Import AsmLang.
Require Import InteractionSemantics.

Lemma taustar_etrace_star:
  forall State step (s s': State) fp,
    tau_star step s fp s' ->
    exists ls, ETrace.star step s ls fp s'.
Proof.
  induction 1. eexists. econstructor.
  destruct IHtau_star. eexists. econstructor; eauto.
Qed.

Lemma etrace_star_star:
  forall State step (s1 s2: State) ls1 fp1,
    ETrace.star step s1 ls1 fp1 s2 ->
    forall ls2 fp2 s3,
      ETrace.star step s2 ls2 fp2 s3 ->
      ETrace.star step s1 (ls1 ++ ls2) (FP.union fp1 fp2) s3.
Proof.
  induction 1; intros.
  rewrite FP.emp_union_fp. auto.
  apply IHstar in H1. simpl. rewrite <- FP.fp_union_assoc. econstructor; eauto.
Qed.

Lemma thdp_inv_upd:
  forall ge (tp : @ThreadPool.t ge) i 
    (c' : Core.t) (tp' : ThreadPool.t),
    ThreadPool.inv tp ->
    ThreadPool.update tp i c' tp' ->
    ThreadPool.inv tp'.
Proof.
  clear. intros. inv H0. inv H2. inv H. constructor; simpl; auto.
  { intros. destruct (peq i0 i).
    subst. apply tp_finite in H. unfold ThreadPool.get_cs in *. rewrite H in H1. discriminate.
    rewrite PMap.gso; auto. }
  { intros. destruct (peq i0 i).
    subst. rewrite PMap.gss. eauto.
    rewrite PMap.gso; eauto. }
  { intro i0. destruct (peq i0 i). 
    subst. rewrite PMap.gss. intros. inv H.
    eapply ThreadPool.cs_upd_inv_cs. eapply cs_inv. eauto. econstructor. eauto.
    rewrite PMap.gso; auto. }
Qed.

Lemma thdp_upd_next_tid:
  forall GE (tp: @ThreadPool.t GE) t c tp',
    ThreadPool.update tp t c tp' ->
    ThreadPool.next_tid tp' = ThreadPool.next_tid tp.
Proof. clear. intros. inv H. auto. Qed.

Lemma thdp_upd_next_fmap:
  forall GE (tp: @ThreadPool.t GE) t c tp',
    ThreadPool.update tp t c tp' ->
    forall t0, ThreadPool.next_fmap tp' t0 = ThreadPool.next_fmap tp t0.
Proof. clear. intros. inv H. auto. Qed.

Require GDefLemmas.

Lemma core_step_globstep:
  forall GE i_x F c m fp c' m',
    let: Mod := GlobEnv.modules GE i_x in
    let: lang := ModSem.lang Mod in
    let: Ge := ModSem.Ge Mod in
    let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
    step lang Ge fl c m fp c' m' ->
    forall (tp: @ThreadPool.t GE) i sg b cs,
      ThreadPool.get_cs tp i = Some ((Core.Build_t i_x c sg F)::cs)  ->
      exists tp',
        glob_step (Build_ProgConfig GE tp i m b) ETrace.tau fp
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

Lemma core_plus_globstep_plus:
  forall GE i_x F c m fp c' m',
    let: Mod := GlobEnv.modules GE i_x in
    let: lang := ModSem.lang Mod in
    let: Ge := ModSem.Ge Mod in
    let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
    plus (step lang Ge fl) c m fp c' m' ->
    forall (tp: @ThreadPool.t GE) i sg b cs,
      ThreadPool.get_cs tp i = Some (Core.Build_t i_x c sg F :: cs) ->
      exists tp',
        tau_plus glob_step (Build_ProgConfig GE tp i m b) fp
                 (Build_ProgConfig GE tp' i m' b) /\
        ThreadPool.update tp i {| Core.c:=c'; Core.sg:=sg; Core.F:=F |} tp'.
Proof.
  clear. intros GE i_x F c m fp c' m' H.
  induction H; intros.
  {
    eapply core_step_globstep in H; eauto.
    destruct H as (tp'& Hstep & Htp'). eexists; split; [econstructor|]; eauto.
  }
  {
    eapply core_step_globstep in H; eauto.
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

Lemma tau_plus_tau_star:
  forall GE (pc: @ProgConfig GE) fp pc',
    tau_plus glob_step pc fp pc' ->
    tau_star glob_step pc fp pc'.
Proof.
  clear. induction 1. 
  replace fp with (FP.union fp FP.emp) by apply GDefLemmas.fp_union_emp_r.
  eapply tau_star_cons; eauto. constructor.
  eapply tau_star_cons; eauto.
Qed.

Lemma core_star_globstep_star:
  forall GE i_x F c m fp c' m',
    let: Mod := GlobEnv.modules GE i_x in
    let: lang := ModSem.lang Mod in
    let: Ge := ModSem.Ge Mod in
    let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
    star (step lang Ge fl) c m fp c' m' ->
    forall (tp: @ThreadPool.t GE) i sg b cs,
      ThreadPool.get_cs tp i = Some ((Core.Build_t i_x c sg F)::cs) ->
      exists tp',
        tau_star glob_step (Build_ProgConfig GE tp i m b) fp
                 (Build_ProgConfig GE tp' i m' b) /\
        (ThreadPool.update tp i (Core.Build_t i_x c' sg F) tp' \/
         m = m' /\ c = c' /\ tp = tp' /\ fp = FP.emp).
Proof.
  clear. intros GE i_x F c m fp c' m' H.
  destruct H; intros.
  {
    eexists; split; [econstructor|]; eauto.
  }
  {
    eapply GDefLemmas.step_star_plus in H0; eauto.
    eapply core_plus_globstep_plus in H0; eauto.
    destruct H0 as [tp' [Hplus Htp'] ].
    exists tp'. split; eauto.
    apply tau_plus_tau_star. eauto.
  }
Qed.

Lemma range_perm_client_mem:
  forall m b ofs size p,
    Mem.range_perm m b ofs (ofs + size) Memperm.Cur p ->
    (forall b' ofs',
        FMemOpFP.range_locset b ofs size b' ofs' = true ->
        client_mem (strip m) b' ofs').
Proof.
  intros. apply FMemOpFP.range_locset_loc in H0. destruct H0; subst b'.
  unfold Mem.range_perm in H. specialize (H ofs').
  unfold client_mem. unfold strip. simpl.
  unfold Mem.perm, Mem.perm_order' in H.
  destruct ((Mem.mem_access m) !! b ofs' Memperm.Cur) eqn:A.
  exploit Mem.access_max. rewrite A. unfold Mem.perm_order''.
  destruct ((Mem.mem_access m) !! b ofs' Memperm.Max); [|contradiction].
  intro. split; intro; discriminate.
  exfalso. apply H. Lia.lia.
Qed.

Lemma valid_access_client_mem:
  forall m chunk b ofs p,
    Mem.valid_access m chunk b ofs p ->
    (forall b' ofs',
        FMemOpFP.range_locset b ofs (size_chunk chunk) b' ofs' = true ->
        client_mem (strip m) b' ofs').
Proof.
  unfold Mem.valid_access.
  intros m chunk b ofs p [H _].
  eauto using range_perm_client_mem.
Qed.  
  
Lemma loadv_loadv_fp_client_fp:
  forall chunk m v v',
    Mem.loadv chunk m v = Some v' ->
    client_fp (strip m) (strip m) (FMemOpFP.loadv_fp chunk v).
Proof.
  unfold Mem.loadv, FMemOpFP.loadv_fp. destruct v; try discriminate.
  intros. apply Mem.load_valid_access in H.
  unfold FMemOpFP.load_fp. 
  apply client_valid_block_fp.
  unfold FP.locs. Locs.unfolds. simpl. intros. red_boolean_true; try discriminate.
  eauto using valid_access_client_mem.
Qed.

Lemma storev_storev_fp_client_fp:
  forall chunk m v v' m',
    Mem.storev chunk m v v' = Some m' ->
    client_fp (strip m) (strip m') (FMemOpFP.storev_fp chunk v).
Proof.
  unfold Mem.storev, FMemOpFP.storev_fp. destruct v; try discriminate.
  intros. apply Mem.store_valid_access_3 in H.
  unfold FMemOpFP.store_fp. apply client_valid_block_fp.
  unfold FP.locs. Locs.unfolds. simpl. intros. red_boolean_true; try discriminate.
  eauto using valid_access_client_mem.
Qed.

Lemma valid_pointer_client_mem:
  forall m b ofs,
    Mem.valid_pointer m b ofs = true ->
    client_mem (strip m) b ofs.
Proof.
  intros. apply Mem.valid_pointer_nonempty_perm in H.
  unfold client_mem, Mem.perm, Mem.perm_order', strip in *; simpl in *; intros.
  destruct ((Mem.mem_access m) !! b ofs Memperm.Cur) eqn:A; auto.
  destruct ((Mem.mem_access m) !! b ofs Memperm.Max) eqn:B. split; intro; discriminate.
  exploit Mem.access_max. rewrite B. unfold Mem.perm_order''. rewrite A. contradiction.
Qed.

Lemma valid_pointer_client_mem_range_locset:
  forall m b ofs b' ofs',
    Mem.valid_pointer m b ofs = true ->
    FMemOpFP.range_locset b ofs 1 b' ofs' = true ->
    client_mem (strip m) b' ofs'.
Proof.
  intros. unfold FMemOpFP.range_locset in *.
  destruct eq_block; try discriminate.
  destruct zlt, zle; try discriminate.
  assert (ofs' = ofs) by Lia.lia. subst. clear H0 l0 l.
  auto using valid_pointer_client_mem.
Qed.

Lemma weak_valid_pointer_client_mem:
  forall m b ofs b' ofs',
    Mem.weak_valid_pointer m b ofs = true ->
    FP.cmps (FMemOpFP.weak_valid_pointer_fp m b ofs) b' ofs' = true ->
    exists ofs'', client_mem (strip m) b' ofs''.
Proof.
  unfold Mem.weak_valid_pointer, FMemOpFP.weak_valid_pointer_fp; simpl. intros.
  red_boolean_true. rewrite H1 in H0. simpl in H0. eauto using valid_pointer_client_mem_range_locset.
  destruct (Mem.valid_pointer m b ofs) eqn:A; simpl in H0. eauto using valid_pointer_client_mem_range_locset.
  exists (ofs - 1). apply FMemOpFP.range_locset_loc in H0. destruct H0. subst. auto using valid_pointer_client_mem.
Qed.

Lemma valid_pointer_valid_pointer_fp_client_fp:
  forall m b ofs,
    Mem.valid_pointer m b ofs = true ->
    client_fp (strip m) (strip m) (FMemOpFP.valid_pointer_fp b ofs).
Proof.
  unfold FMemOpFP.valid_pointer_fp. intros. apply client_valid_block_fp.
  unfold FP.locs. Locs.unfolds. simpl. intros. red_boolean_true; try discriminate.
  eauto using valid_pointer_client_mem_range_locset.
Qed.

Lemma weak_valid_pointer_weak_valid_pointer_fp_client_fp:
  forall m b ofs,
    Mem.weak_valid_pointer m b ofs = true ->
    client_fp (strip m) (strip m) (FMemOpFP.weak_valid_pointer_fp m b ofs).
Proof.
  unfold FMemOpFP.weak_valid_pointer_fp. intros. 
  apply Mem.weak_valid_pointer_spec in H. destruct H as [Hvalid|Hvalid'].
  rewrite Hvalid. intros. auto using valid_pointer_valid_pointer_fp_client_fp.
  destruct (Mem.valid_pointer m b ofs) eqn:A. auto using valid_pointer_valid_pointer_fp_client_fp.
  apply client_valid_block_fp.
  unfold FP.locs. Locs.unfolds. simpl. intros. red_boolean_true; try discriminate.
  apply FMemOpFP.range_locset_loc in H0. destruct H0. subst. right.
  eauto using valid_pointer_client_mem.
Qed.

Lemma alloc_client_or_unused:
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m', b) ->
    forall ofs, client_mem (strip m') b ofs \/ unused_mem (strip m') b ofs.
Proof.
  intros.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  left.
  exploit Mem.perm_alloc_2. eauto. eauto. instantiate (1:= Memperm.Max).
  exploit Mem.perm_alloc_2. eauto. eauto. instantiate (1:= Memperm.Cur).
  unfold client_mem, Mem.perm, strip; simpl.
  destruct ((Mem.mem_access m') !! b ofs Memperm.Cur);[|inversion 1].
  destruct ((Mem.mem_access m') !! b ofs Memperm.Max);[|inversion 2].
  intros. split; intro; discriminate.
  right.
  unfold unused_mem, strip; simpl.
  destruct ((Mem.mem_access m') !! b ofs Memperm.Max) eqn:C; auto.
  exploit Mem.perm_alloc_3. eauto. unfold Mem.perm. rewrite C. apply Memperm.perm_any_N. Lia.lia.
  right.
  unfold unused_mem, strip; simpl.
  destruct ((Mem.mem_access m') !! b ofs Memperm.Max) eqn:C; auto.
  exploit Mem.perm_alloc_3. eauto. unfold Mem.perm. rewrite C. apply Memperm.perm_any_N. Lia.lia.
Qed.

Lemma alloc_obj_mem_unchg:
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m', b) ->
    forall b' ofs', obj_mem (strip m) b' ofs' <-> obj_mem (strip m') b' ofs'.
Proof.
  intros.
  destruct (peq b b'). subst.
  split; intro; exfalso.
  exploit obj_mem_valid; eauto. pose proof (Mem.fresh_block_alloc _ _ _ _ _ H).
  unfold strip, GMem.valid_block. simpl. contradiction.
  exploit alloc_client_or_unused; eauto. instantiate (1:= ofs').
  unfold obj_mem, client_mem, unused_mem in *. firstorder.
  pose proof (Mem.perm_alloc_4 _ _ _ _ _ H).
  pose proof (Mem.perm_alloc_1 _ _ _ _ _ H).
  specialize (H0 b' ofs').
  specialize (H1 b' ofs').
  unfold obj_mem, Mem.perm in *. simpl in *.
  destruct ((Mem.mem_access m) !! b' ofs' Memperm.Max) eqn:A;
    destruct ((Mem.mem_access m) !! b' ofs' Memperm.Cur) eqn:B;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Max) eqn:C;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Cur) eqn:D;
    try (clear; split; intros [A B]; exfalso; discriminate; fail);
    try (clear; split; (intros [A B]; split; [discriminate | auto]); fail);
    try (clear; tauto; fail).
  exploit H1. rewrite B. apply Memperm.perm_any_N. rewrite D. inversion 1.
  exploit H1. rewrite B. apply Memperm.perm_any_N. rewrite D. inversion 1.
  exploit H0. rewrite D. apply Memperm.perm_any_N. eauto. rewrite B. inversion 1.
  exploit H1. rewrite A. apply Memperm.perm_any_N. rewrite C. inversion 1.
  exploit H1. rewrite A. apply Memperm.perm_any_N. rewrite C. inversion 1.
  exploit H1. rewrite B. apply Memperm.perm_any_N. rewrite D. inversion 1.
  exploit H0. rewrite D. apply Memperm.perm_any_N. eauto. rewrite B. inversion 1.
  exploit H0. rewrite C. apply Memperm.perm_any_N. eauto. rewrite A. inversion 1.
Qed.

Lemma alloc_clt_mem_unchg:
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m', b) ->
    forall b' ofs', b' <> b -> client_mem (strip m) b' ofs' <-> client_mem (strip m') b' ofs'.
Proof.
  intros.
  pose proof (Mem.perm_alloc_4 _ _ _ _ _ H).
  pose proof (Mem.perm_alloc_1 _ _ _ _ _ H).
  specialize (H1 b' ofs').
  specialize (H2 b' ofs').
  unfold client_mem, Mem.perm in *. simpl in *.
  destruct ((Mem.mem_access m) !! b' ofs' Memperm.Max) eqn:A;
    destruct ((Mem.mem_access m) !! b' ofs' Memperm.Cur) eqn:B;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Max) eqn:C;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Cur) eqn:D;
    try (clear; split; intros [A B]; exfalso; discriminate; fail);
    try (clear; split; (intros [A B]; split; [discriminate | discriminate]); fail);
    try (clear; tauto; fail).
  exploit H2. rewrite B. apply Memperm.perm_any_N. rewrite D. inversion 1.
  exploit H2. rewrite A. apply Memperm.perm_any_N. rewrite C. inversion 1.
  exploit H2. rewrite A. apply Memperm.perm_any_N. rewrite C. inversion 1.
  exploit H1. rewrite D. apply Memperm.perm_any_N. eauto. rewrite B. inversion 1.
  exploit H1. rewrite C. apply Memperm.perm_any_N. eauto. rewrite A. inversion 1.
  exploit H1. rewrite C. apply Memperm.perm_any_N. eauto. rewrite A. inversion 1.          
Qed.

Lemma free_obj_mem_unchg:
  forall m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    forall b' ofs', obj_mem (strip m) b' ofs' <-> obj_mem (strip m') b' ofs'.
Proof.
  unfold obj_mem, strip. simpl. intros.
  pose proof (Mem.perm_free_inv _ _ _ _ _ H b' ofs') as H1.
  pose proof (Mem.perm_free_2 _ _ _ _ _ H ofs') as H2.
  pose proof (Mem.perm_free_3 _ _ _ _ _ H b' ofs') as H3.
  unfold Mem.perm in *.
  destruct ((Mem.mem_access m ) !! b' ofs' Memperm.Max) eqn:A;
    destruct ((Mem.mem_access m) !! b' ofs' Memperm.Cur) eqn:B;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Max) eqn:C;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Cur) eqn:D;
    try (clear; split; intros [A B]; exfalso; congruence; fail);
    try (clear; split; (intros [A B]; split; [discriminate | auto]); fail);
    try (clear; tauto; fail);
    exfalso.

  exploit H1. rewrite B. eapply Memperm.perm_any_N.
  intros [[E F]|E];
    [subst b'; eapply H2; [intuition|]; erewrite C; eapply Memperm.perm_any_N 
    | rewrite D in E; inv E].

  exploit H3. rewrite D. eapply Memperm.perm_any_N. rewrite B. inversion 1.
  exploit H3. rewrite D. eapply Memperm.perm_any_N. rewrite B. inversion 1.

  exploit H1. rewrite A. eapply Memperm.perm_any_N.
  intros [[E F]|E]; [| rewrite C in E; inv E].
  subst b'. eapply Mem.free_range_perm in H. apply H in F. unfold Mem.perm in F. rewrite B in F. inv F.

  exploit H3. rewrite C. eapply Memperm.perm_any_N. rewrite A. inversion 1.
  exploit H3. rewrite C. eapply Memperm.perm_any_N. rewrite A. inversion 1.
Qed.

Lemma free_clt_mem':
  forall m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    forall b' ofs', client_mem (strip m') b' ofs' -> client_mem (strip m) b' ofs'.
Proof.
  unfold client_mem, strip. simpl. intros m b lo hi m' Hfree b' ofs' [A' B'].
  pose proof (Mem.perm_free_3 _ _ _ _ _ Hfree b' ofs') as H. unfold Mem.perm in H.
  destruct ((Mem.mem_access m ) !! b' ofs' Memperm.Max) eqn:A;
    destruct ((Mem.mem_access m) !! b' ofs' Memperm.Cur) eqn:B;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Max) eqn:C;
    destruct ((Mem.mem_access m') !! b' ofs' Memperm.Cur) eqn:D;
    try (split; intro; congruence; fail); exfalso.
  exploit H. rewrite D. eapply Memperm.perm_any_N. rewrite B. inversion 1.
  exploit H. rewrite C. eapply Memperm.perm_any_N. rewrite A. inversion 1.
  exploit H. rewrite D. eapply Memperm.perm_any_N. rewrite B. inversion 1.
Qed.
      
Lemma exec_load_client_fp_obj_unchg:
  forall ge chunk m a rs r rs' m',
    sep_obj_client_block (strip m) ->
    exec_load ge chunk m a rs r = AsmLang.Next rs' m' ->
    client_fp (strip m) (strip m') (exec_load_fp ge chunk a rs) /\
    (forall b ofs, obj_mem (strip m) b ofs <-> obj_mem (strip m') b ofs) /\
    sep_obj_client_block (strip m').
Proof.
  unfold exec_load, exec_load_fp. intros. 
  destruct (Mem.loadv chunk m (eval_addrmode ge a rs)) eqn:A; inv H0.
  split; [|tauto].
  eapply loadv_loadv_fp_client_fp; eauto.
Qed.

Lemma exec_store_client_fp_obj_unchg:
  forall ge chunk m a rs r lr rs' m',
    sep_obj_client_block (strip m) ->
    exec_store ge chunk m a rs r lr = AsmLang.Next rs' m' ->
    client_fp (strip m) (strip m') (exec_store_fp ge chunk a rs) /\
    (forall b ofs, obj_mem (strip m) b ofs <-> obj_mem (strip m') b ofs) /\
    sep_obj_client_block (strip m').
Proof.
  unfold exec_store, exec_store_fp. intros.
  destruct (Mem.storev chunk m (eval_addrmode ge a rs)) eqn:A; inv H0.
  split. eapply storev_storev_fp_client_fp; eauto.
  unfold sep_obj_client_block in *.
  unfold obj_mem, client_mem in *. unfold strip in *; simpl in *.
  unfold Mem.storev in *. destruct (eval_addrmode ge a rs); try discriminate.
  erewrite (Mem.store_access chunk m _ _ _ m'); eauto. tauto.
Qed.

Lemma check_true_compare_ints_client_fp:
  forall v1 v2 m,
    sep_obj_client_block (strip m) ->
    check_compare_ints v1 v2 m = true ->
    client_fp (strip m) (strip m) (compare_ints_fp v1 v2 m).
Proof.
  unfold check_compare_ints, compare_ints_fp.
  destruct v1; simpl; try discriminate; eauto using FP.emp_union_fp, client_emp_fp;
    destruct v2; simpl; try discriminate; eauto using FP.emp_union_fp, client_emp_fp;
      destruct Archi.ptr64; simpl; try discriminate; intros.
  { destruct Int.eq; simpl in *; eauto using FP.emp_union_fp, client_emp_fp.
    fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) in H0. rewrite FP.fp_union_emp.
    destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) eqn:A; [|discriminate].
    auto using weak_valid_pointer_weak_valid_pointer_fp_client_fp. }
  { destruct Int.eq; simpl in *; eauto using FP.emp_union_fp, client_emp_fp.
    fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) in H0. rewrite FP.fp_union_emp.
    destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) eqn:A; [|discriminate].
    auto using weak_valid_pointer_weak_valid_pointer_fp_client_fp. }
  { destruct eq_block; subst.
    fold (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i)) in H0.
    fold (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i0)) in H0.
    destruct (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i)) eqn:A; [|discriminate].
    destruct (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i0)) eqn:B; [|discriminate].
    apply client_valid_block_fp. 
    unfold FP.locs; simpl. Locs.unfolds; simpl in *.
    intros; red_boolean_true; simpl in *;
      match goal with
      | H: FP.reads _ _ _ = true |- _ =>
        unfold FMemOpFP.weak_valid_pointer_fp in H;
          destruct Mem.valid_pointer; inv H
      | H: FP.writes _ _ _ = true |- _ =>
        unfold FMemOpFP.weak_valid_pointer_fp in H;
          destruct Mem.valid_pointer; inv H            
      | H: FP.frees _ _ _ = true |- _ =>
        unfold FMemOpFP.weak_valid_pointer_fp in H;
          destruct Mem.valid_pointer; inv H
      | _ => eauto using weak_valid_pointer_client_mem
      end.
    apply client_valid_block_fp.
    unfold FP.locs; simpl. Locs.unfolds; simpl in *.
    destruct (Mem.valid_pointer m b (Ptrofs.unsigned i)) eqn:A; [|discriminate].
    destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned i0)) eqn:B; [|discriminate].
    intros; red_boolean_true; simpl in *; eauto using valid_pointer_client_mem_range_locset.
  }
Qed.

Lemma test_compare_ints_client_fp:
  forall v1 v2 m,
    client_fp (strip m) (strip m) (compare_ints_fp (Val.and v1 v2) Vzero m).
Proof.
  intros; destruct v1, v2; unfold compare_ints_fp;
    rewrite FP.emp_union_fp; auto using client_emp_fp.
Qed.

Lemma compare_longs_client_fp:
  forall v1 v2 m,
    client_fp (strip m) (strip m) (compare_longs_fp v1 v2 m).
Proof.
  intros; destruct v1, v2; unfold compare_longs_fp; simpl;
    rewrite FP.emp_union_fp; auto using client_emp_fp.
Qed.

Lemma fp_locs_fp_union_locs_union_fp_locs:
  forall fp1 fp2,
    FP.locs (FP.union fp1 fp2) = Locs.union (FP.locs fp1) (FP.locs fp2).
Proof.
  destruct fp1, fp2. unfold FP.locs. simpl. repeat rewrite <- Locs.union_assoc_eq.
  do 2 (apply functional_extensionality; intro). Locs.unfolds. 
  repeat match goal with
         | |- ?a || ?b = _ => destruct a; simpl; auto with bool
         | |- _ = ?a || ?b => destruct a; simpl; auto with bool                                                            
         end.
Qed.

Lemma eval_builtin_arg_fp_client_mem:
  forall ge rs v m a b fp,
    eval_builtin_arg ge rs v m a b ->
    @MemOpFP.eval_builtin_arg_fp Asm.preg ge rs v a fp ->
    forall b' ofs', FP.locs fp b' ofs' = true -> client_mem (strip m) b' ofs'.
Proof.
  intros ge rs v m a. induction a; intros; inv H; inv H0; try (inv H1; fail).
  unfold Mem.loadv, FMemOpFP.loadv_fp in *. destruct (Val.offset_ptr v ofs); inv H5. 
  unfold FMemOpFP.load_fp, FP.locs in H1. Locs.unfolds. simpl in *. red_boolean_true; try discriminate.
  apply Mem.load_valid_access in H0. eapply valid_access_client_mem; eauto.
  unfold Mem.loadv, FMemOpFP.loadv_fp in *. destruct (Senv.symbol_address ge id ofs); inv H6. 
  unfold FMemOpFP.load_fp, FP.locs in H1. Locs.unfolds. simpl in *. red_boolean_true; try discriminate.
  apply Mem.load_valid_access in H0. eapply valid_access_client_mem; eauto.
  rewrite fp_locs_fp_union_locs_union_fp_locs in H1. Locs.unfolds. red_boolean_true; eauto.
Qed.

Lemma extcall_arg_fp_client_mem:
  forall rs m r b fp,
    extcall_arg rs m r b ->
    extcall_arg_fp rs r fp ->
    forall b' ofs', FP.locs fp b' ofs' = true -> client_mem (strip m) b' ofs'.
Proof.
  intros. inv H0. inv H1. inv H. unfold Mem.loadv, FMemOpFP.loadv_fp in *.
  destruct Val.offset_ptr; inv H5. apply Mem.load_valid_access in H0.
  unfold FMemOpFP.load_fp, FP.locs in *. Locs.unfolds. simpl in H1.
  red_boolean_true; try discriminate.
  eauto using valid_access_client_mem.
Qed.

Lemma store_args_fmem_mem_validblock_eq:
  forall m stk args tys m',
    loadframe.store_args_fmem m stk args tys = Some m' ->
    Mem.validblocks m' = Mem.validblocks m.
Proof.
  unfold loadframe.store_args_fmem. generalize 0.
  intros z m stk args tys m'. revert z m stk args m'.
  induction tys; intros. destruct args; inv H. auto.
  destruct args. inv H.
  simpl in H. unfold loadframe.store_stack_fmem, Mem.storev in H.
  destruct a;
    repeat match goal with
           | H: context[match ?a with _ => _ end] |- _ => destruct a eqn:?; inv H; auto
           end.
  erewrite <- (Mem.store_validblocks _ m). eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_validblocks _ m). eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_validblocks _ m); [|eauto].
  erewrite <- (Mem.store_validblocks _ m0); [|eauto].
  eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_validblocks _ m). eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_validblocks _ m). eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_validblocks _ m). eapply IHtys. eauto. eauto.
Qed.

Lemma store_args_fmem_mem_access_eq:
  forall m stk args tys m',
    loadframe.store_args_fmem m stk args tys = Some m' ->
    Mem.mem_access m' = Mem.mem_access m.
Proof.
  unfold loadframe.store_args_fmem. generalize 0.
  intros z m stk args tys m'. revert z m stk args m'.
  induction tys; intros. destruct args; inv H. auto.
  destruct args. inv H.
  simpl in H. unfold loadframe.store_stack_fmem, Mem.storev in H.
  destruct a;
    repeat match goal with
           | H: context[match ?a with _ => _ end] |- _ => destruct a eqn:?; inv H; auto
           end.
  erewrite <- (Mem.store_access _ m). eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_access _ m). eapply IHtys. eauto. eauto. 
  erewrite <- (Mem.store_access _ m); [|eauto].
  erewrite <- (Mem.store_access _ m0); [|eauto].
  eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_access _ m). eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_access _ m). eapply IHtys. eauto. eauto.
  erewrite <- (Mem.store_access _ m). eapply IHtys. eauto. eauto.
Qed.



Lemma AsmLang_step_client_fp:
  forall Ge fl c gm fp c' gm',
    sep_obj_client_block gm ->
    step AsmLang Ge fl c gm fp c' gm' ->
    client_fp gm gm' fp /\
    (forall b ofs, obj_mem gm b ofs <-> obj_mem gm' b ofs) /\
    sep_obj_client_block gm'.
Proof.
  clear. intros Ge fl c gm fp c' gm' Hsep Hstep.
  inv Hstep. inv H. inv H0.
  { (* exec_instr *)
    revert Hsep H2 H3. clear. 
    destruct i; simpl; unfold goto_label; intros;
      try discriminate;
      eauto using exec_store_client_fp_obj_unchg,
      exec_load_client_fp_obj_unchg;
      repeat match goal with
             | H: match ?a with _ => _ end = AsmLang.Next _ _ |- _ =>
               destruct a eqn:?; inv H
             | H: AsmLang.Next _ _ = AsmLang.Next _ _ |- _ =>
               inv H
             | |- client_fp _ _ FP.emp /\ _ =>
               split; [apply client_emp_fp; auto|tauto]
             | |- client_fp _ _ (compare_ints_fp _ _ _) /\ _ =>
               split; [auto using check_true_compare_ints_client_fp, test_compare_ints_client_fp|tauto]
             | |- client_fp _ _ (compare_longs_fp _ _ _) /\ _ =>
               split; [auto using compare_longs_client_fp|tauto]
             end.
    (* alloc *)
    { pose proof (Mem.fresh_block_alloc _ _ _ _ _ Heqp) as Hfresh.
      pose proof (Mem.valid_new_block _ _ _ _ _ Heqp) as Hvalid.
      unfold strip, obj_mem, client_mem, unused_mem. simpl.
      split.
      { apply client_alloc_fp. unfold GMem.valid_block, client_mem, unused_mem. simpl. 
        unfold FP.locs. Locs.unfolds. simpl. intros. red_boolean_true.
        (* store cases *)
        repeat rewrite Locs.emp_union_locs in H0. Locs.unfolds. red_boolean_true.
        (* store ofs_link *)
        apply FMemOpFP.range_locset_loc in H. destruct H. subst b0.
        split. auto. split. eapply Mem.store_valid_block_1. eauto. eapply Mem.store_valid_block_1; eauto.
        erewrite Mem.store_access; eauto. erewrite Mem.store_access; eauto.
        
        eapply alloc_client_or_unused; eauto.
        (* store ofs_ra *)
        apply FMemOpFP.range_locset_loc in H. destruct H. subst b0.
        split. auto. split. eapply Mem.store_valid_block_1. eauto. eapply Mem.store_valid_block_1; eauto.
        erewrite Mem.store_access; eauto. erewrite Mem.store_access; eauto.
        eapply alloc_client_or_unused; eauto.
        (* alloc *)
        repeat rewrite Locs.locs_union_emp in H0.
        destruct peq; [|discriminate]; subst b0.
        exploit Mem.alloc_result; eauto. intro. subst b.
        split. auto. split. eapply Mem.store_valid_block_1. eauto. eapply Mem.store_valid_block_1; eauto.
        erewrite Mem.store_access; eauto. erewrite Mem.store_access; eauto.
        eapply alloc_client_or_unused; eauto.
      }
      { split. intros b' ofs'.
        erewrite (Mem.store_access _ m1 _ _ _ m'); eauto.
        erewrite (Mem.store_access _ m0 _ _ _ m1); eauto.
        eapply alloc_obj_mem_unchg; eauto.
        unfold sep_obj_client_block. intros b' ofs1 ofs2.
        unfold obj_mem, client_mem. simpl.
        erewrite Mem.store_access; eauto. erewrite Mem.store_access; eauto. 
        exploit alloc_obj_mem_unchg. eauto. unfold strip, obj_mem, client_mem. simpl.
        intro A. rewrite <- A. clear A. intro.
        assert (b' <> b).
        { intro. subst. destruct H. apply H.
          exploit Mem.fresh_block_alloc; eauto; try contradiction.
          exfalso. apply H. apply Mem.invalid_noaccess. auto. }
        exploit alloc_clt_mem_unchg. eauto. eauto. unfold strip, client_mem. simpl.
        intro A. rewrite <- A. clear A. intro.
        eapply Hsep; eauto.
      }
    }
    (* free *)
    { split.
      { apply client_valid_block_fp.
        unfold strip, obj_mem, client_mem, unused_mem. simpl.
        unfold FP.locs. Locs.unfolds. simpl. Locs.unfolds. simpl in *.
        apply Mem.load_valid_access in Heqo.
        apply Mem.load_valid_access in Heqo0.
        apply Mem.free_range_perm in Heqo1.
        intros. red_boolean_true.
        left. eapply valid_access_client_mem in H0; eauto. unfold client_mem in H0. eauto.
        left. eapply valid_access_client_mem in H0; eauto. unfold client_mem in H0. eauto.
        left. eapply range_perm_client_mem in H0.
        unfold client_mem, strip in H0. eauto. rewrite Z.sub_0_r, Z.add_0_l. eauto. }
      split.
      eapply free_obj_mem_unchg; eauto.
      unfold sep_obj_client_block. intros.
      erewrite <- free_obj_mem_unchg in H; eauto.
      eapply free_clt_mem' in H0; eauto.
    }
  }
  { (* built-in *)
    split; [|tauto]. apply client_valid_block_fp. revert H4 H5. clear. 
    generalize (rs (Asm.IR Asm.RSP)) m' vargs fp. clear. induction args.
    intros. inv H5. inv H.
    intros v m' vargs fp Heval Hevalfp b ofs H.
    inv Heval. inv Hevalfp.
    rewrite fp_locs_fp_union_locs_union_fp_locs in H.
    Locs.unfolds. red_boolean_true. 
    left. eapply eval_builtin_arg_fp_client_mem; eauto.
    eauto.
  }      
  { (* extcall *)
    split; [|tauto]. apply client_valid_block_fp.
    revert H2 H3. clear. unfold extcall_arguments, extcall_arguments_fp.
    generalize (loc_arguments (ef_sig ef)) as typs, m' as m, args as vl, fp as FP. clear.
    induction typs; intros. inv H3. inv H.
    inv H2. inv H3. rewrite fp_locs_fp_union_locs_union_fp_locs in H. Locs.unfolds. red_boolean_true; eauto.
    clear IHtyps H5 H6. revert H0 H4 H2. clear. intros. destruct a.
    inv H4; inv H2.
    left. eapply extcall_arg_fp_client_mem; eauto.
    left. inv H2; inv H4. rewrite fp_locs_fp_union_locs_union_fp_locs in H0. Locs.unfolds.
    red_boolean_true; eauto using extcall_arg_fp_client_mem.
  }
  { split; [auto using client_emp_fp|tauto]. }
  { (* initialize *)
    split.
    { apply client_alloc_fp. intros.
      assert (b = stk).
      { rewrite fp_locs_fp_union_locs_union_fp_locs in H0. Locs.unfolds. red_boolean_true.
        unfold FP.locs in *. Locs.unfolds. simpl in H2.
        destruct peq; [subst b|discriminate].
        exploit Mem.alloc_result. eauto. intro; subst stk; auto.
        revert H2. clear. unfold loadframe.store_args_fp. generalize 0. induction tys.
        intros. inv H2.
        intros. simpl in H2.
        destruct a; repeat rewrite fp_locs_fp_union_locs_union_fp_locs in H2;
          Locs.unfolds; unfold loadframe.store_stack_fp, FMemOpFP.storev_fp in H2;
            repeat match goal with
                   | H: context[match ?a with _ => _ end] |- _ =>
                     destruct a eqn:?; inv H
                   end;
            red_boolean_true; auto; try (eapply IHtys; eassumption; fail);
              repeat match goal with
                     | H: Val.offset_ptr (Vptr _ _) _ = Vptr _ _ |- _ => inv H
                     | H: context[FP.union FP.emp _] |- _ => rewrite FP.emp_union_fp in H
                     | H: context[FP.union _ FP.emp] |- _ => rewrite FP.fp_union_emp in H
                     | H: FP.locs (FMemOpFP.store_fp _ _ _) _ _ = true |- _ =>
                       unfold FP.locs, FMemOpFP.store_fp in H; simpl in H;
                         repeat rewrite Locs.locs_union_emp in H;
                         repeat rewrite Locs.emp_union_locs in H;
                         apply FMemOpFP.range_locset_loc in H; intuition
                     end.
      }
      subst b.
      split. intro. exploit Mem.fresh_block_alloc; eauto.
      split. exploit Mem.valid_new_block; eauto.
      unfold Mem.valid_block. apply store_args_fmem_mem_validblock_eq in H3; eauto. rewrite <- H3. auto.
      unfold client_mem, unused_mem. simpl. erewrite store_args_fmem_mem_access_eq; eauto.
      eapply alloc_client_or_unused; eauto.
    }
    split.
    { intros b' ofs'.
      
      rewrite alloc_obj_mem_unchg; eauto.
      unfold obj_mem. simpl. eapply store_args_fmem_mem_access_eq in H3. rewrite H3. tauto.
    }
    { unfold sep_obj_client_block. 
      unfold obj_mem, client_mem in *. simpl in *.
      eapply store_args_fmem_mem_access_eq in H3.
      rewrite H3. clear H3. intros b' ofs1 ofs2.
      exploit alloc_obj_mem_unchg. eauto. unfold strip, obj_mem, client_mem. simpl.
      intro A. rewrite <- A. clear A. intro.
      assert (b' <> stk).
      { intro. subst. destruct H0. apply H0.
        exploit Mem.fresh_block_alloc; eauto; try contradiction.
        exfalso. apply H0. apply Mem.invalid_noaccess.
        eapply Mem.fresh_block_alloc. eauto. }
      exploit alloc_clt_mem_unchg. eauto. eauto. unfold strip, client_mem. simpl.
      intro A. rewrite <- A. clear A. intro.
      eapply Hsep; eauto.
    }
  }
Qed.
      
  

Lemma SpecLang_step_sep:
  forall ge fl c m fp c' m',
    sep_obj_client_block m ->
    step SpecLang.speclang ge fl c m fp c' m' ->
    sep_obj_client_block m'.
Proof.
  intros. inv H0. inv H2; inv H1; auto.
  { inv H0; auto.
    unfold SpecLang.storemax in H3. destruct Mem.range_perm_dec; inv H3.
    unfold strip. simpl. unfold sep_obj_client_block in *.
    unfold obj_mem, client_mem in *. simpl in *. auto. }
  { inv H0; auto. 
    unfold SpecLang.storemax in *. destruct Mem.range_perm_dec; inv H3.
    unfold strip. simpl. unfold sep_obj_client_block in *.
    unfold obj_mem, client_mem in *. simpl in *. auto. }
  { 
    Local Transparent Mem.alloc.
    unfold Mem.alloc in H0. inv H0. unfold strip. simpl.
    unfold sep_obj_client_block, obj_mem, client_mem in *. simpl in *.
    intros. destruct (peq b (Mem.nextblock m0)). 
    subst. repeat rewrite PMap.gss in *. destruct zle, zlt; simpl in *; firstorder.
    repeat (rewrite PMap.gso in *; auto). eauto.
    Local Opaque Mem.alloc.
  }
Qed.

Require Import Compositionality Soundness.

Inductive abort_behav : behav -> Prop :=
| abort_imm: abort_behav Behav_abort
| abort_cons: forall v B, abort_behav B -> abort_behav (Behav_cons v B).

Lemma non_evt_star_star_step:
  forall state step (pc: state) fp pc',
    non_evt_star step pc fp pc' ->
    exists ll, ETrace.star step pc ll fp pc'.
Proof.
  induction 1. eexists. constructor.
  destruct H.
  destruct IHnon_evt_star. eexists. econstructor; eauto.
  destruct IHnon_evt_star. eexists. econstructor; eauto.
Qed.

Lemma prog_refine_safety_preserved:
  forall NL L ps pt,
    @prog_refine NL L ps pt ->
    forall (mu : Injections.Mu) (sgm : gmem) (sge : GlobEnv.t) 
      (spc : ProgConfig) (ts : tid) (tgm : gmem) (tge : GlobEnv.t)
      (tpc : ProgConfig) (tt : tid),
      InitRel mu sge tge sgm tgm ->
      init_config ps sgm sge spc ts ->
      init_config pt tgm tge tpc tt ->
      safe_state glob_step GlobSemantics.abort spc ->
      safe_state glob_step GlobSemantics.abort tpc.
Proof.
  intros NL L ps pt H. inv H. rename H0 into REF.
  intros mu sgm sge spc ts tgm tge tpc tt H0 H1 H2 H3.
  specialize (REF mu sgm sge spc ts tgm tge tpc tt H0 H1 H2).
  clear mu sgm tgm ts tt H0 H1 H2.
  unfold safe_state in *. intros. intro Habort.
  
  assert (exists B, Etr glob_step GlobSemantics.abort final_state tpc B /\ abort_behav B).
  { revert H Habort; clear. induction 1; intros.
    { eexists. split. eapply Etr_abort. eapply ne_star_refl. auto. constructor. }
    { apply IHstar in Habort. destruct Habort as (B & HEtr & Habort). clear IHstar.
      destruct e.
      { exists B. split. destruct Habort.
        inv HEtr. econstructor. eapply ne_star_step. eauto. eauto. eauto.
        inv HEtr. econstructor. eapply ne_star_step. eauto. eauto. eauto. eauto. eauto. }
      { exists B. split. destruct Habort.
        inv HEtr. econstructor. eapply ne_star_step. eauto. eauto. eauto.
        inv HEtr. econstructor. eapply ne_star_step. eauto. eauto. eauto. eauto. eauto. }
      { exists (Behav_cons v B). split.
        assert (fp1 = FP.emp) by (inv H; auto). subst.
        econstructor. econstructor. eauto. eauto. econstructor. eauto. }
    }
  }
  destruct H0 as (B & HEtr & Habort').
  apply REF in HEtr.

  assert (exists l' fp' spc', ETrace.star glob_step spc l' fp' spc' /\ GlobSemantics.abort spc').
  { revert HEtr Habort'. clear. intros. revert spc HEtr. induction Habort'; intros.
    inv HEtr. eapply non_evt_star_star_step in H. destruct H. eauto.
    inv HEtr. eapply IHHabort' in H3. eapply non_evt_star_star_step in H1.
    destruct H1. destruct H3 as (? & ? & ? & ? & ?).
    do 3 eexists. split. eapply etrace_star_star. eauto. eapply ETrace.star_step; eauto. eauto. }

  destruct H0 as (l' & fp' & spc' & Hstar' & Habort'').
  eapply H3; eauto.
Qed.    
      
Lemma safety_preservation:
  forall NL L scunits tcunits e comps,
    wd_langs scunits ->
    wd_langs tcunits ->
    det_langs tcunits ->
    rc_cunits scunits ->
    cunits_transf comps scunits tcunits ->
    @seqs_correct NL L comps ->
    drf (scunits, e) ->
    safe_prog (scunits, e) ->
    forall mu sgm sge spc ts tgm tge tpc tt,
      InitRel mu sge tge sgm tgm ->
      init_config (scunits, e) sgm sge spc ts ->
      init_config (tcunits, e) tgm tge tpc tt ->
      safe_state glob_step GlobSemantics.abort tpc.
Proof.
  intros NL L scunits tcunits e comps
         Hwd_src Hwd_tgt Hdet_tgt Hrc Hcomp Hcorrect Hdrf Hsafe.
  pose proof (@compositionality NL L) as HSim.
  specialize (HSim _ _ e Hwd_src Hwd_tgt Hrc).
  exploit seqs_correct_fn_preserved; eauto. intro Hfn.
  exploit seqs_correct_ldsims; eauto. intro Hsims. 
  pose proof (NPEquiv.Safe_NPSafe _ _ _ _ Hwd_src Hsafe) as Hnpsafe.
  specialize (HSim Hsims Hfn). apply Flipping.flipping in HSim; auto.
  intros. eapply prog_refine_safety_preserved; eauto.
  eapply framework_sound; eauto.
  eapply Hsafe; eauto.
Qed.


Lemma drf_preservation:
  forall NL L scunits tcunits e comps,
    wd_langs scunits ->
    wd_langs tcunits ->
    det_langs tcunits ->
    rc_cunits scunits ->
    cunits_transf comps scunits tcunits ->
    @seqs_correct NL L comps ->
    drf (scunits, e) ->
    safe_prog (scunits, e) ->
    forall mu sgm sge spc ts tgm tge tpc tt,
      InitRel mu sge tge sgm tgm ->
      init_config (scunits, e) sgm sge spc ts ->
      init_config (tcunits, e) tgm tge tpc tt ->
      ~ star_race_config tpc.
Proof.
  intros NL L scunits tcunits e comps
         Hwd_src Hwd_tgt Hdet_tgt Hrc Hcomp Hcorrect Hdrf Hsafe.
  pose proof (@compositionality NL L) as HSim.
  specialize (HSim _ _ e Hwd_src Hwd_tgt Hrc).
  exploit seqs_correct_fn_preserved; eauto. intro Hfn.
  exploit seqs_correct_ldsims; eauto. intro Hsims. 
  pose proof (NPEquiv.Safe_NPSafe _ _ _ _ Hwd_src Hsafe) as Hnpsafe.
  specialize (HSim Hsims). clear Hsims.
  assert (NPDRF.npdrf (scunits,e)).
  { unfold NPDRF.npdrf. intro. unfold drf in Hdrf. contradict Hdrf.
    apply SmileReorder.NPRace_Race;auto. }
  apply Flipping.flipping in HSim; auto.
  intros mu sgm sge spc ts tgm tge tpc tt INITREL INITSrc INITTgt.
  eapply NPEquiv.NPDRF_DRF_Config;eauto; auto.
  {
    intros. assert(ts = cur_tid spc). inv INITSrc;auto.
    assert(tt = cur_tid tpc). inv INITTgt;auto.
    subst.
    eapply Init.init_pair_valid_tid in H0 as ?;try exact INITSrc;eauto.
    eapply Init.init_free in H0;eauto.
    eapply Init.init_free in H1;eauto.
    clear INITSrc INITTgt.
    eapply GlobUSimRefine.USim_Safe_Config;eauto.
    inv H1;econstructor;eauto. auto.
  }
  {
    
    intros. assert(ts = cur_tid spc). inv INITSrc;auto.
    assert(tt = cur_tid tpc). inv INITTgt;auto.
    subst.
    eapply Init.init_pair_valid_tid in H0 as ?;try exact INITSrc;eauto.
    eapply Init.init_free in H0;eauto.
    eapply Init.init_free in H1;eauto.
    eapply SimDRF.USim_NPDRF_Config in H0 as ?;try apply H1;eauto.
    eapply DRFLemmas.NPDRF_config;eauto.
    eapply Init.init_property_1_alt in H1;eauto.
  }
Qed.     
