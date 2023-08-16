From mathcomp.ssreflect Require Import fintype ssrnat.   
Require Import Coqlib Maps Axioms LibTactics.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import CUAST.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset.

Require Import Languages.
Require Import TSOGlobSem GlobSemantics RGRels ClientSim ObjectSim.

Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.
Require Import InteractionSemantics.

Require Import FMemLemmas TSOMemLemmas.

Ltac simpls := simpl in *.
Local Transparent Mem.load Mem.alloc Mem.store Mem.free.
Local Ltac ex_match2:=
  repeat match goal with
         | H: context[match ?x with _ => _ end]  |- _ => destruct x eqn:?Hx; try discriminate
         | H: _ |- context[match ?x with _ => _ end ] => destruct x eqn:?Hx;try discriminate
         end;try congruence;try contradiction.
Definition Not_lock_instr (i : instruction) :=
  match i with
  | Plock_cmpxchg _ _ => False
  | Plock_dec _ => False
  | _ => True
  end.

Inductive FLs_embed (fls :FLists.t) : tsomem -> Prop :=
  | FLs_embed_unbuffer:
      forall tm
        (Embed: forall flid,
            let fl := FLists.flist_content fls flid in
            exists fm, embed (memory tm) fl fm)
        (UNBS: forall t bi b m', 
            (tso_buffers tm) t = bi :: b ->
            apply_buffer_item bi (memory tm) = Some m' ->
            FLs_embed fls (mktsomem (tupdate t b (tso_buffers tm)) m')),
        FLs_embed fls tm.

Lemma append_ls_still_nil :
  forall {A : Type} (l l' : list A),
    l = l ++ l' -> l' = nil.
Proof.
  intros A l.
  induction l; intros; simpls; eauto.
  eapply IHl.
  inv H.
  rewrite <- H1; eauto.
Qed.

Lemma list_forall2_stable :
  forall {A B : Type} al bl (P P' : A -> B -> Prop),
    (forall (a : A) (b : B), P a b -> P' a b) ->
    list_forall2 P al bl ->
    list_forall2 P' al bl.
Proof.
  intros.
  generalize dependent P'.
  induction H0; simpls; eauto; intros; eauto.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma Memperm_order''_eq_perm_eq :
  forall p1 p2,
    Memperm.perm_order'' p1 p2 ->
    Memperm.perm_order'' p2 p1 ->
    p1 = p2.
Proof.
  intros.
  unfolds Memperm.perm_order''.
  ex_match2; subst; eauto; tryfalse.
  inv H; inv H0; subst; eauto.
Qed.

Lemma gmem_eq_mem_access_eq :
  forall m m' b ofs k,
    GMem.eq m m' ->
    (GMem.mem_access m) !! b ofs k = (GMem.mem_access m') !! b ofs k.
Proof.
  intros.
  inv H.
  clear - eq_access.
  specialize (eq_access b ofs k).
  destruct eq_access.
  lets Hperm_eq : Memperm_order''_eq_perm_eq ___; eauto.
Qed.

Lemma Memperm_order''_impl_Memperm_order' :
  forall m m' b ofs k p,
    Mem.perm_order' ((GMem.mem_access m) !! b ofs k) p ->
    Memperm.perm_order'' ((GMem.mem_access m') !! b ofs k)
                         ((GMem.mem_access m) !! b ofs k) ->
    Mem.perm_order' ((GMem.mem_access m') !! b ofs k) p.
Proof.
  intros.
  unfold Mem.perm_order', Memperm.perm_order'' in *.
  ex_match2; eauto.
  { 
    eapply Memperm.perm_order_trans; eauto.
  }
Qed.

Lemma Memperm_perm_order''_refl :
  forall p,
    Memperm.perm_order'' p p.
Proof.
  intros.
  unfolds Memperm.perm_order''.
  ex_match2; eauto.
  eapply Memperm.perm_refl; eauto.
Qed.

(*+ Lemmas About GMem eq +*)
Lemma gmem_eq_valid_pointer_eq' :
  forall fm1 fm2,
    GMem.eq (strip fm1) (strip fm2) -> 
    Mem.valid_pointer fm1 = Mem.valid_pointer fm2.
Proof.
  intros.
  unfold Mem.valid_pointer.
  eapply functional_extensionality; intros.
  eapply functional_extensionality; intros.
  unfold Mem.perm_dec.
  inv H.
  clear - eq_access.
  specialize (eq_access x x0 Memperm.Cur).
  destruct eq_access.
  lets Ht : Memperm_order''_eq_perm_eq ___; eauto.
  do 2 (rewrite <- Mem_GMem_access_eq in Ht).
  clear - Ht.
  unfold Mem.perm.
  rewrite Ht; eauto.
Qed.

Lemma gmem_eq_valid_pointer_eq :
  forall fm1 fm2 gm1 gm2 fl,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    Mem.valid_pointer fm1 = Mem.valid_pointer fm2.
Proof.
  intros.
  inv H0; inv H1; subst.
  eapply gmem_eq_valid_pointer_eq'; eauto.
Qed.

Lemma gmem_eq_load_still :
  forall m m' c b ofs v,
    GMem.eq m m' ->
    load c m b ofs = Some v ->
    exists v', load c m' b ofs = Some v'.
Proof.
  intros.
  unfolds load.
  ex_match2.
  inv H0; subst; eauto.
  clear - H v0 n.
  contradiction n; clear n.
  unfolds valid_access; inv H.
  destruct v0.
  split; eauto.
  unfolds range_perm; intros.
  eapply H in H1.
  specialize (eq_access b ofs0 Memperm.Max).
  destruct eq_access.
  eapply Memperm_order''_impl_Memperm_order'; eauto.
Qed.

Lemma gmem_eq_Mem_load_still' :
  forall fm fm' c b ofs v,
    GMem.eq (strip fm) (strip fm') -> 
    Mem.load c fm b ofs = Some v ->
    exists v', Mem.load c fm' b ofs = Some v'.
Proof.
  intros.
  unfolds Mem.load.
  ex_match2; eauto; tryfalse.
  contradiction n; clear - v0 H.
  inv H; subst.
  clear - v0 eq_access.
  unfolds Mem.valid_access.
  destruct v0; split; eauto.
  unfolds Mem.range_perm; intros.
  eapply H in H1; eauto.
  clear - H1 eq_access.
  unfolds Mem.perm.
  try rewrite Mem_GMem_access_eq in *.
  specialize (eq_access b ofs0 Memperm.Cur).
  destruct eq_access.
  eapply Memperm_order''_impl_Memperm_order'; eauto.
Qed.

Lemma gmem_eq_Mem_load_still :
  forall m m' fm fm' c b ofs v fl,
    GMem.eq m m' -> embed m fl fm -> embed m' fl fm' ->
    Mem.load c fm b ofs = Some v ->
    exists v', Mem.load c fm' b ofs = Some v'.
Proof.
  intros.
  inv H0; inv H1; subst; eauto.
  eapply gmem_eq_Mem_load_still'; eauto.
Qed.

Lemma gmem_eq_Mem_loadv_still' :
  forall fm fm' c a v,
    GMem.eq (strip fm) (strip fm') -> 
    Mem.loadv c fm a = Some v ->
    exists v', Mem.loadv c fm' a = Some v'.
Proof.
  intros.
  unfolds Mem.loadv; ex_match2; subst.
  eapply gmem_eq_Mem_load_still'; eauto.
Qed.

Lemma gmem_eq_Mem_loadv_still :
  forall m m' fm fm' c a v fl,
    GMem.eq m m' -> embed m fl fm -> embed m' fl fm' ->
    Mem.loadv c fm a = Some v ->
    exists v', Mem.loadv c fm' a = Some v'.
Proof.
  intros.
  unfolds Mem.loadv; ex_match2; subst.
  eapply gmem_eq_Mem_load_still; eauto.
Qed.

Lemma gmem_eq_load_same_v :
  forall m m' v v' c b ofs,
    GMem.eq m m' ->
    load c m b ofs = Some v ->
    load c m' b ofs = Some v' ->
    v = v'.
Proof.
  intros.
  unfolds load.
  ex_match2.
  inv H0; inv H1; subst; simpls.
  inv H; simpls.
  clear - v1 eq_contents.
  assert (Mem.getN (size_chunk_nat c) ofs (GMem.mem_contents m) !! b =
          Mem.getN (size_chunk_nat c) ofs (GMem.mem_contents m') !! b).
  {
    eapply Mem.getN_exten; eauto.
    intros.
    unfolds valid_access.
    destruct v1.
    unfolds range_perm.
    rewrite <- size_chunk_conv in H.
    eapply H0 in H; eauto.
  }
  rewrite H; eauto.
Qed.

Lemma gmem_eq_Mem_load_same_v' :
  forall fm fm' v v' c b ofs,
    GMem.eq (strip fm) (strip fm') ->
    Mem.load c fm b ofs = Some v ->
    Mem.load c fm' b ofs = Some v' ->
    v = v'.
Proof.
  intros.
  eapply load_fm_eq_load_gm in H0.
  eapply load_fm_eq_load_gm in H1.
  eapply gmem_eq_load_same_v; eauto.
Qed.

Lemma gmem_eq_Mem_load_same_v :
  forall m m' fm fm' v v' c b ofs fl,
    GMem.eq m m' -> embed m fl fm -> embed m' fl fm' ->
    Mem.load c fm b ofs = Some v ->
    Mem.load c fm' b ofs = Some v' ->
    v = v'.
Proof.
  intros.
  eapply gmem_eq_Mem_load_same_v'; eauto.
  inv H0; inv H1; subst; eauto.
Qed.

Lemma gmem_eq_mem_loadv_same' :
  forall fm1 fm2 c a v1 v2,
    GMem.eq (strip fm1) (strip fm2) -> 
    Mem.loadv c fm1 a = Some v1 ->
    Mem.loadv c fm2 a = Some v2 ->
    v1 = v2.
Proof.
  intros. 
  unfolds Mem.loadv; ex_match2; tryfalse; subst.
  eapply gmem_eq_Mem_load_same_v'; eauto.
Qed.
  
Lemma gmem_eq_mem_loadv_same :
  forall gm1 gm2 fm1 fm2 fl c a v1 v2,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    Mem.loadv c fm1 a = Some v1 ->
    Mem.loadv c fm2 a = Some v2 ->
    v1 = v2.
Proof.
  intros.
  unfolds Mem.loadv; ex_match2; tryfalse; subst.
  eapply gmem_eq_Mem_load_same_v; eauto.
Qed.

Lemma gmem_eq_Mem_store_still :
  forall gm1 gm2 fm1 fm2 fm1' fl c b ofs v,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    Mem.store c fm1 b ofs v = Some fm1' ->
    exists fm2', Mem.store c fm2 b ofs v = Some fm2'.
Proof.
  intros.
  unfolds Mem.store.
  ex_match2; eauto.
  inv H2; subst.
  contradiction n; clear - H H0 H1 v0.
  inv H0; inv H1.
  inv H; clear - eq_access v0.
  unfolds Mem.valid_access.
  destruct v0; split; eauto.
  unfolds Mem.range_perm; introv Hrange; eapply H in Hrange; eauto.
  clear - eq_access Hrange.
  unfolds Mem.perm.
  try rewrite Mem_GMem_access_eq in *.
  eapply Memperm_order''_impl_Memperm_order'; eauto.
  specialize (eq_access b ofs0 Memperm.Cur).
  destruct eq_access; eauto.
Qed.

Lemma gmem_eq_Mem_storev_still :
  forall gm1 gm2 fm1 fm2 fm1' fl c a v,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    Mem.storev c fm1 a v = Some fm1' ->
    exists fm2', Mem.storev c fm2 a v = Some fm2'.
Proof.
  intros.
  unfolds Mem.storev.
  ex_match2; subst.
  eapply gmem_eq_Mem_store_still; eauto.
Qed.

Lemma store_gmem_eq_stable :
  forall gm1 gm2 gm1' gm2' c b z v,
    GMem.eq gm1 gm2 ->
    store c gm1 b z v = Some gm1' ->
    store c gm2 b z v = Some gm2' ->
    GMem.eq gm1' gm2'.
Proof.
  intros; unfolds store.
  ex_match2.
  inv H0; inv H1; simpls.
  inv H.
  econstructor; simpls; eauto.
  intros.
  eapply eq_contents in H; eauto. 
  destruct (peq b b0); subst; eauto.
  repeat rewrite PMap.gss; eauto. 
  pose proof inrange_or_not. 
  specialize (H0 memval ofs z (encode_val c v)). 
  destruct H0.
  {
    eapply setN_geteq2; destruct H0; eauto.
  }
  {
    do 2 try rewrite Mem.setN_outside; eauto.
  }
  do 2 try rewrite PMap.gso; eauto.
Qed.

Lemma gmem_eq_apply_buf_item_stable :
  forall bi gm gm' gm1,
    GMem.eq gm gm' ->
    apply_buffer_item bi gm = Some gm1 ->
    exists gm2, apply_buffer_item bi gm' = Some gm2.
Proof.
  intros.
  destruct bi; simpls.
  (** alloc *)
  {
    unfold alloc; eauto.
  }
  (** free *)
  {
    unfold free in *.
    ex_match2; eauto.
    clear - r n H.
    unfold range_perm in *.
    contradiction n.
    clear - H r.
    intros.
    eapply r in H0.
    inversion H; subst.
    specialize (eq_access b ofs Memperm.Max).
    destruct eq_access; eauto.
    eapply Memperm_order''_impl_Memperm_order'; eauto.
  }
  (** store *)
  {
    unfold store in *.
    ex_match2; eauto.
    inversion H0; subst; simpls; clear H0.
    clear - v0 n H.
    contradiction n; clear n.
    unfold valid_access in *.
    destruct v0; split; eauto.
    unfold range_perm in *; intros.
    eapply H0 in H2.
    inversion H; subst.
    specialize (eq_access b ofs Memperm.Max).
    destruct eq_access; eapply Memperm_order''_impl_Memperm_order'; eauto.
  }
Qed.

Lemma apply_buf_item_after_Mem_store_original_still :
  forall bi m m' fm b ofs v c,
    apply_buffer_item bi (strip m) = Some m' ->
    Mem.store c fm b ofs v = Some m ->
    exists m'', apply_buffer_item bi (strip fm) = Some m''.
Proof.
  intros.
  unfolds Mem.store.
  ex_match2; inv H0.
  unfolds strip; simpls.
  destruct bi; simpls.
  {
    unfold alloc; simpls; eauto.
  }
  { 
    unfolds free; simpls.
    ex_match2; eauto.
  }
  {
    unfolds store; simpls.
    ex_match2; eauto.
  }
Qed.
  
Lemma gmem_eq_apply_same_buf_item_still :
  forall bi gm1 gm2 gm1' gm2',
    GMem.eq gm1 gm2 ->
    apply_buffer_item bi gm1 = Some gm1' ->
    apply_buffer_item bi gm2 = Some gm2' ->
    GMem.eq gm1' gm2'.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc; simpls; inversion H0; inversion H1; subst; clear H0 H1; simpls.
    inversion H; subst; econstructor; simpls.
    {
      intros. 
      destruct (peq b b0) eqn:?; simpls; subst.
      do 2 (try rewrite PMap.gss in *); eauto.
      do 2 (try rewrite PMap.gso in *); eauto.
    }
    {
      intros.
      destruct (peq b b0) eqn:?; simpls; subst.
      do 2 (try rewrite PMap.gss in *); eauto.
      clear; split; eapply Memperm_perm_order''_refl; eauto.     
      do 2 (try rewrite PMap.gso in *); eauto.
    }
    {
      intros; unfolds GMem.valid_block; simpls.
      clear - eq_validblocks.
      split; intros.
      destruct H; eauto.
      eapply eq_validblocks in H; eauto.
      destruct H; eauto.
      eapply eq_validblocks in H; eauto.
    }
  }
  {
    unfolds free.
    ex_match2.
    clear - H H0 H1.
    inversion H0; inversion H1; subst; clear H0 H1.
    unfold unchecked_free; simpls; inversion H; subst.
    econstructor; simpls; intros.
    {
      destruct (peq b b0); subst; simpls; tryfalse.
      try rewrite PMap.gss in H0; simpls; tryfalse.
      ex_match2; tryfalse.
      eapply eq_contents in H0; eauto.
      rewrite PMap.gso in H0; simpls; eauto.
    }
    {
      destruct (peq b b0); subst; simpls; eauto.
      repeat rewrite PMap.gss; eauto.
      ex_match2; eauto.
      split; eapply Memperm_perm_order''_refl; eauto.
      repeat rewrite PMap.gso; eauto.
    }
    {
      unfolds GMem.valid_block; simpls; eauto.
    }
  }
  {
    eapply store_gmem_eq_stable; eauto.
  }
Qed.

Lemma apply_same_buf_gmem_eq_stable :
  forall bf gm1 gm2 gm1' gm2',
    GMem.eq gm1 gm2 ->
    apply_buffer bf gm1 = Some gm1' ->
    apply_buffer bf gm2 = Some gm2' ->
    GMem.eq gm1' gm2'.
Proof.
  induction bf; intros; simpls; eauto.
  inv H0; inv H1; subst; eauto.
  destruct (apply_buffer_item a gm1) eqn:?; simpls; tryfalse.
  destruct (apply_buffer_item a gm2) eqn:?; simpls; tryfalse.
  eapply IHbf with (gm1 := g) (gm2 := g0); eauto.
  eapply gmem_eq_apply_same_buf_item_still; eauto.
Qed.
  
Lemma gmem_eq_apply_same_buf_still :
  forall bf gm1 gm2 gm1',
    GMem.eq gm1 gm2 ->
    apply_buffer bf gm1 = Some gm1' ->
    exists gm2', apply_buffer bf gm2 = Some gm2'.
Proof.
  induction bf; simpls; eauto; intros.
  destruct (apply_buffer_item a gm1) eqn:?; simpls; tryfalse.
  lets Happly_buf_item : H.
  eapply gmem_eq_apply_buf_item_stable in Happly_buf_item; eauto.
  destruct Happly_buf_item as [gm2'' Happly_buf_item].
  rewrite Happly_buf_item; simpls.
  eapply IHbf; eauto.
  eapply gmem_eq_apply_same_buf_item_still; eauto.
Qed.

Lemma gmem_eq_embed_both :
  forall gm1 gm2 fl fm1,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 ->
    exists fm2, embed gm2 fl fm2 /\ Mem.nextblock fm1 = Mem.nextblock fm2.
Proof.
  intros.
  inv H; inv H0.
  eexists.
  instantiate
    (1 :=
       Mem.mkmem
         (GMem.mem_contents gm2)
         (GMem.mem_access gm2)
         (GMem.validblocks gm2)
         (Mem.freelist fm1)
         (Mem.nextblockid fm1) _ _ _ _ _
    ).
  split; eauto.
  econstructor; eauto.
  unfold strip; simpls; eauto.
  eapply gmem_eq; eauto.
  Unshelve.
  { 
    clear; intros.
    destruct fm1; simpls; eauto.
  }
  {
    intros.
    destruct fm1; unfolds strip, GMem.valid_block; simpls.
    split; intros.
    {
      eapply valid_wd in H.
      eapply H; eauto.
      eapply eq_validblocks; eauto.
    }
    {
      eapply valid_wd in H.
      eapply H in H0; eauto.
      eapply eq_validblocks; eauto.
    }
  }
  {
    intros.
    destruct gm2; simpls; eauto.
    clear - access_max.
    specialize (access_max b ofs); eauto.
  }
  {
    intros.
    destruct gm2; simpls; eauto.
  }
  {
    intros.
    destruct gm2; simpls; eauto.
  }
Qed.
  
Lemma gmem_eq_embed_apply_buf_still :
  forall gm1 gm2 gm1' gm2' fm1' fl bf,
    GMem.eq gm1 gm2 ->
    embed gm1' fl fm1' ->
    apply_buffer bf gm1 = Some gm1' ->
    apply_buffer bf gm2 = Some gm2' ->
    exists fm2', embed gm2' fl fm2' /\ Mem.nextblock fm1' = Mem.nextblock fm2'.
Proof.
  intros.
  lets Ht : apply_same_buf_gmem_eq_stable ___; eauto.
  eapply gmem_eq_embed_both; eauto.
Qed.

Lemma gmem_eq_weak_valid_pointer_fp_eq :
  forall fm1 fm2 b ofs,
    GMem.eq (strip fm1) (strip fm2) ->
    FMemOpFP.weak_valid_pointer_fp fm1 b ofs =
    FMemOpFP.weak_valid_pointer_fp fm2 b ofs.
Proof.
  intros.
  unfolds FMemOpFP.weak_valid_pointer_fp; simpls.
  assert (Mem.valid_pointer fm1 = Mem.valid_pointer fm2).
  {
    eapply gmem_eq_valid_pointer_eq'; eauto.    
  }
  rewrite H0; eauto.
Qed.

Lemma gmem_eq_cmpu_bool_fp_eq :
  forall fm1 fm2 v1 v2 cmp,
    GMem.eq (strip fm1) (strip fm2) ->
    Cop_fp.cmpu_bool_fp fm1 cmp v1 v2 = Cop_fp.cmpu_bool_fp fm2 cmp v1 v2.
Proof.
  intros.
  unfolds Cop_fp.cmpu_bool_fp.
  ex_match2; eauto; subst;
    try erewrite gmem_eq_weak_valid_pointer_fp_eq; eauto.
  erewrite gmem_eq_weak_valid_pointer_fp_eq with (fm1 := fm1) (fm2 := fm2); eauto.
Qed.
  
Lemma gmem_eq_ub_safe_eq:
  forall B gm gm',
    GMem.eq gm gm' ->
    unbuffer_safe (mktsomem B gm) ->
    unbuffer_safe (mktsomem B gm').
Proof.
  intros.
  remember {| tso_buffers := B; memory := gm |} as tm.
  generalize dependent gm.
  generalize dependent gm'.
  generalize dependent B.
  induction H0; intros; subst; simpl in *.
  econstructor; intros; simpl in *.
  {
    eapply ABIS in H1.
    destruct H1 as [m'' H1].
    eapply gmem_eq_apply_buf_item_stable; eauto.
  }
  {
    lets Ht: GMem.eq_sym ___; eauto.
    eapply gmem_eq_apply_buf_item_stable in Ht; eauto.
    destruct Ht as [gm2 Ht].
    eapply H; eauto.
    eapply gmem_eq_apply_same_buf_item_still; eauto.
  }
Qed.

Lemma gmem_eq_embed_still :
  forall gm1 gm2 fl fm1,
    embed gm1 fl fm1 ->
    GMem.eq gm1 gm2 ->
    exists fm2, embed gm2 fl fm2 /\ Mem.nextblockid fm1 = Mem.nextblockid fm2.
Proof.
  intros.
  inv H; inv H0; subst; simpls.
  eexists.
  split.
  {
    econstructor.
    Focus 2.
    instantiate
      (1 := Mem.mkmem
              (GMem.mem_contents gm2)
              (GMem.mem_access gm2)
              (GMem.validblocks gm2)
              (Mem.freelist fm1)
              (Mem.nextblockid fm1) _ _ _ _ _).
    unfold strip; simpls; eauto.
    eapply gmem_eq; eauto.
    simpl; eauto.
  }
  simpl; eauto.
  Unshelve.
  {
    intros.
    destruct fm1; simpls; eauto.
  }
  {
    intros.
    destruct fm1; simpls.
    unfold strip in eq_validblocks; simpls.
    unfold GMem.valid_block in eq_validblocks; simpls.
    split; intros.
    {
      eapply eq_validblocks in H0.
      eapply valid_wd in H0; eauto.
    }
    {
      eapply eq_validblocks.
      eapply valid_wd; eauto.
    }
  }
  {
    intros.
    destruct gm2; simpls; eauto.
    clear - access_max.
    specialize (access_max b ofs); eauto.
  }
  {
    clear; intros.
    destruct gm2; simpls; eauto.
  }
  {
    intros; destruct gm2; simpls; eauto.
  }
Qed.

Lemma gmem_eq_tsoloadv_v_eq' :
  forall bf fm1 fm2 a c v v0,
    GMem.eq (strip fm1) (strip fm2) ->
    tsoloadv c {| tbuffer := bf; fmemory := fm1 |} a = Some v ->
    tsoloadv c {| tbuffer := bf; fmemory := fm2 |} a = Some v0 ->
    v = v0.
Proof.
  intros.
  unfolds tsoloadv.
  destruct a; simpls; tryfalse.
  ex_match2.
  lets Ht : apply_same_buf_gmem_eq_stable ___; eauto.
  eapply gmem_eq_load_same_v; eauto.
Qed.

Lemma gmem_eq_tsoloadv_v_eq :
  forall bf gm1 gm2 fm1 fm2 a c v v0 fl,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    tsoloadv c {| tbuffer := bf; fmemory := fm1 |} a = Some v ->
    tsoloadv c {| tbuffer := bf; fmemory := fm2 |} a = Some v0 ->
    v = v0.
Proof.
  intros.
  inv H0; inv H1; subst; simpls.
  eapply gmem_eq_tsoloadv_v_eq'; eauto.
Qed.

Lemma gmem_eq_tsoloadv_v_still' :
  forall bf fm1 fm2 a c v,
    GMem.eq (strip fm1) (strip fm2) -> 
    tsoloadv c {| tbuffer := bf; fmemory := fm1 |} a = Some v ->
    exists v', tsoloadv c {| tbuffer := bf; fmemory := fm2 |} a = Some v'.
Proof.
  intros.
  unfolds tsoloadv.
  destruct a; simpls; tryfalse.
  ex_match2. 
  eapply gmem_eq_load_still; eauto.
  eapply apply_same_buf_gmem_eq_stable; eauto.
  eapply gmem_eq_apply_same_buf_still in H; eauto.
  destruct H.
  rewrite H in Hx0; tryfalse.
Qed.

Lemma gmem_eq_tsoloadv_v_still :
  forall bf gm1 gm2 fm1 fm2 a c v fl,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    tsoloadv c {| tbuffer := bf; fmemory := fm1 |} a = Some v ->
    exists v', tsoloadv c {| tbuffer := bf; fmemory := fm2 |} a = Some v'.
Proof.
  intros.
  inv H0; inv H1; subst; simpls.
  eapply gmem_eq_tsoloadv_v_still'; eauto.
Qed.

Lemma gmem_eq_exec_load_TSO_still :
  forall ge c buf fm1 fm2 gm1 gm2 a rs rd rs' tsofm1 fl, 
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    exec_load_TSO ge c {| tbuffer := buf; fmemory := fm1 |} a rs rd =
    Next rs' tsofm1 ->
    exists tsofm2, exec_load_TSO ge c {| tbuffer := buf; fmemory := fm2 |} a rs rd =
              Next rs' tsofm2.
Proof.
  intros.
  unfolds exec_load_TSO.
  ex_match2.
  inv H2; subst.
  eapply gmem_eq_tsoloadv_v_eq with (v := v) (v0 := v0) in Hx; eauto; subst.
  eauto.
  eapply gmem_eq_tsoloadv_v_still in Hx; eauto.
  destruct Hx.
  rewrite H3 in Hx0; discriminate.
Qed.

Lemma gmem_eq_tsostorev_still':
  forall c bm1 bm2 a v tsofm1,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    tsostorev c bm1 a v = Some tsofm1 ->
    exists tsofm2, tsostorev c bm2 a v = Some tsofm2.
Proof.
  intros.
  unfolds tsostorev.
  destruct a; simpls; tryfalse; eauto.
  unfolds tsostore.
  eauto.
Qed.

Lemma gmem_eq_tsostorev_still :
  forall c bf fm1 fm2 gm1 gm2 fl a v tsofm1,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    tsostorev c {| tbuffer := bf; fmemory := fm1 |} a v = Some tsofm1 ->
    exists tsofm2, tsostorev c {| tbuffer := bf; fmemory := fm2 |} a v = Some tsofm2.
Proof.
  intros.
  unfolds tsostorev.
  destruct a; simpls; tryfalse; eauto.
  unfolds tsostore.
  eauto.
Qed.

Lemma gmem_eq_exec_store_TSO_still :
  forall ge c buf fm1 fm2 gm1 gm2 a r1 r2 lrs rs' tsofm1 fl, 
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    exec_store_TSO ge c {| tbuffer := buf; fmemory := fm1 |} a r1 r2 lrs =
    Next rs' tsofm1 ->
    exists tsofm2, exec_store_TSO ge c {| tbuffer := buf; fmemory := fm2 |} a r1 r2 lrs =
              Next rs' tsofm2.
Proof.
  intros.
  unfolds exec_store_TSO.
  ex_match2; eauto.
  inv H2; subst; eauto.
  inv H2; subst.
  eapply gmem_eq_tsostorev_still in Hx; eauto.
  destruct Hx as [tsofm2 Hx].
  rewrite Hx in Hx0; tryfalse.
Qed.

Lemma gmem_eq_buf_eq_tsostore_stable :
  forall bm1 bm2 bm1' bm2' c b ofs v,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    tsostore c bm1 b ofs v = Some bm1' ->
    tsostore c bm2 b ofs v = Some bm2' ->
    GMem.eq (strip (fmemory bm1')) (strip (fmemory bm2')) /\
    tbuffer bm1' = tbuffer bm2'.
Proof.
  intros.
  unfolds tsostore.
  inv H1; inv H2.
  split; simpl; eauto.
  rewrite H0; eauto.
Qed.

Lemma gmem_eq_buf_eq_tsostorev_stable :
  forall bm1 bm2 bm1' bm2' c a v,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    tsostorev c bm1 v a = Some bm1' ->
    tsostorev c bm2 v a = Some bm2' ->
    GMem.eq (strip (fmemory bm1')) (strip (fmemory bm2')) /\
    tbuffer bm1' = tbuffer bm2'.
Proof.
  intros.
  unfolds tsostorev.
  ex_match2; subst.
  eapply gmem_eq_buf_eq_tsostore_stable; eauto.
Qed.

Lemma gmem_eq_tso_valid_pointer_eq :
  forall bf fm1 fm2 gm1 gm2 fl,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    tso_valid_pointer {| tbuffer := bf; fmemory := fm1 |} =
    tso_valid_pointer {| tbuffer := bf; fmemory := fm2 |}.
Proof.
  intros.
  inv H0; inv H1; subst; eauto.
  unfolds tso_valid_pointer.
  eapply functional_extensionality; intros.
  eapply functional_extensionality; intros.
  destruct (apply_buffer bf (strip fm1)) eqn:?; simpls; eauto.
  lets Happly_bf : Heqo.
  eapply gmem_eq_apply_same_buf_still in Happly_bf; eauto.
  destruct Happly_bf as [g' Happly_bf].
  rewrite Happly_bf; eauto.
  unfold perm_dec.
  eapply apply_same_buf_gmem_eq_stable in H; eauto.
  inv H; subst.
  clear - eq_access.
  specialize (eq_access x x0 Memperm.Cur).
  destruct eq_access.
  lets Ht : Memperm_order''_eq_perm_eq ___; eauto.
  rewrite Ht; eauto.
  ex_match2; eauto.
  eapply GMem.eq_sym in H.
  eapply gmem_eq_apply_same_buf_still in Hx; eauto.
  destruct Hx as [g' Hx]; rewrite Hx in Heqo; discriminate.
Qed.

Lemma gmem_eq_compare_ints_TSO_eq :
  forall x y rs bf fm1 fm2 fl gm1 gm2,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    compare_ints_TSO x y rs {| tbuffer := bf; fmemory := fm1 |} =
    compare_ints_TSO x y rs {| tbuffer := bf; fmemory := fm2 |}.
Proof.
  intros; unfolds compare_ints_TSO; simpls.
  erewrite gmem_eq_tso_valid_pointer_eq; eauto.
Qed.

Lemma gmem_eq_tso_weak_valid_pointer_fp_eq :
  forall bf fm1 fm2 b ofs,
    GMem.eq (strip fm1) (strip fm2) ->
    tso_weak_valid_pointer_fp {| tbuffer := bf; fmemory := fm1 |} b ofs =
    tso_weak_valid_pointer_fp {| tbuffer := bf; fmemory := fm2 |} b ofs.
Proof.
  intros.
  unfolds tso_weak_valid_pointer_fp; simpls.
  ex_match2; eauto; unfolds perm_dec, Mem.perm_order'_dec.
  eapply apply_same_buf_gmem_eq_stable in H; eauto.
  eapply gmem_eq_mem_access_eq in H; eauto.
  rewrite H in Hx.
  ex_match2.
  eapply gmem_eq_apply_same_buf_still in Hx0; eauto.
  destruct Hx0 as [gm2' Hx0]; rewrite Hx0 in Hx2; tryfalse.
  eapply apply_same_buf_gmem_eq_stable in H; eauto.
  eapply gmem_eq_mem_access_eq in H; eauto.
  rewrite H in Hx.
  ex_match2.
  eapply GMem.eq_sym in H.
  eapply gmem_eq_apply_same_buf_still with (gm2 := strip fm1) in Hx2; eauto.
  destruct Hx2 as [gm2' Hx2]; rewrite Hx2 in Hx0; tryfalse.
Qed.

Lemma gmem_eq_compare_ints_TSO_fp_eq :
  forall x y bf fm1 fm2,
    GMem.eq (strip fm1) (strip fm2) ->
    compare_ints_TSO_fp x y {| tbuffer := bf; fmemory := fm1 |} =
    compare_ints_TSO_fp x y {| tbuffer := bf; fmemory := fm2 |}.
Proof.
  intros.
  unfolds compare_ints_TSO_fp.
  ex_match2; eauto; subst.
  unfolds tso_cmpu_bool_fp_total.
  ex_match2; eauto; subst.
  erewrite gmem_eq_tso_weak_valid_pointer_fp_eq; eauto.
  erewrite gmem_eq_tso_weak_valid_pointer_fp_eq; eauto.
  erewrite gmem_eq_tso_weak_valid_pointer_fp_eq; eauto.
  erewrite gmem_eq_tso_weak_valid_pointer_fp_eq with (fm1 := fm1) (fm2 := fm2);
    eauto.
Qed.

(*+ Aux LTac +*)
Ltac inv_next :=
  match goal with
  | H : Next _ _ = Next _ _ |- _ => inv H; subst; eauto
  end.

Ltac elim_embed :=
  match goal with
  | H : embed _ _ _ |- _ => inv H; subst
  end.

Ltac same_elim :=
  match goal with
  | H1 : ?A = _, H2 : ?A = _ |- _ =>
    rewrite H1 in H2; inv H2; tryfalse
  | _ => idtac
  end.

Ltac elim_load_eq_value_case :=
  match goal with
  | H1 : GMem.eq ?gm1 ?gm2,
         H2 : embed ?gm1 ?fl ?fm1,
              H3 : embed ?gm2 ?fl ?fm2,
                   H4 : Mem.loadv _ ?fm1 _ = Some ?v1,
                        H5 : Mem.loadv _ ?fm2 _ = Some ?v2 |- _ =>
    let H := fresh in
    lets H : H1;
    eapply gmem_eq_mem_loadv_same in H; eauto; subst; eauto; tryfalse
  end.

Ltac elim_load_eq_value_case' :=
  match goal with
  | H1 : GMem.eq (strip ?fm1) (strip ?fm2),
         H2 : Mem.loadv _ ?fm1 _ = Some ?v1,
              H3 : Mem.loadv _ ?fm2 _ = Some ?v2 |- _ =>
    let H := fresh in
    lets H : H1;
    eapply gmem_eq_mem_loadv_same' in H; eauto; subst; eauto; tryfalse
  end.

Ltac load_eq_gmem_some_none_false :=
  match goal with
  | H1 : GMem.eq ?gm1 ?gm2,
         H2 : embed ?gm1 ?fl ?fm1,
              H3 : embed ?gm2 ?fl ?fm2,
                   H4 : Mem.loadv _ ?fm1 _ = Some ?v1,
                        H5 : Mem.loadv _ ?fm2 _ = None |- _ =>
    eapply gmem_eq_Mem_loadv_still in H4; eauto; destruct H4 as [?x H4]; same_elim
  end.

Ltac load_eq_gmem_some_none_false' :=
  match goal with
  | H1 : GMem.eq (strip ?fm1) (strip ?fm2),
         H2 : Mem.loadv _ ?fm1 _ = Some ?v1,
              H3 : Mem.loadv _ ?fm2 _ = None |- _ =>
    eapply gmem_eq_Mem_loadv_still' in H2; eauto; destruct H2 as [?x H2]; same_elim
  end.

Ltac store_eq_gmem_some_none_false :=
  match goal with
  | H1 : GMem.eq ?gm1 ?gm2,
         H2 : embed ?gm1 ?fl ?fm1,
              H3 : embed ?gm2 ?fl ?fm2,
                   H4 : Mem.storev _ ?fm1 _ _ = Some ?fm1',
                        H5 : Mem.storev _ ?fm2 _ _ = None |- _ =>
    try elim_load_eq_value_case;
    eapply gmem_eq_Mem_storev_still in H4; eauto;
    destruct H4 as [?fm2' H4]; same_elim
  end.

Ltac store_eq_gmem_none_some_false :=
  match goal with
  | H1 : GMem.eq ?gm1 ?gm2,
         H2 : embed ?gm1 ?fl ?fm1,
              H3 : embed ?gm2 ?fl ?fm2,
                   H4 : Mem.storev _ ?fm1 _ _ = None,
                        H5 : Mem.storev _ ?fm2 _ _ = Some ?fm2' |- _ =>
    try elim_load_eq_value_case; 
    eapply GMem.eq_sym in H1;
    eapply gmem_eq_Mem_storev_still in H5; eauto; destruct H5 as [?fm2' H5];
    same_elim
  end.

Ltac valid_pointer_eq_case := 
  match goal with
  | H1 : GMem.eq ?gm1 ?gm2,
         H2 : embed ?gm1 ?fl ?fm1,
              H3 : embed ?gm2 ?fl ?fm2,
                   H4 : context [Mem.valid_pointer ?fm1],
                        H5 : context [Mem.valid_pointer ?fm2] |- _ =>
    try elim_load_eq_value_case;
    eapply gmem_eq_valid_pointer_eq in H1; eauto;
    rewrite H1 in H4; eauto; try same_elim
  end.

Ltac valid_pointer_eq_case' := 
  match goal with
  | H1 : GMem.eq (strip ?fm1) (strip ?fm2),
         H2 : context [Mem.valid_pointer ?fm1],
              H3 : context [Mem.valid_pointer ?fm2] |- _ =>
    try elim_load_eq_value_case;
    eapply gmem_eq_valid_pointer_eq' in H1; eauto;
    rewrite H1 in H2; eauto; try same_elim
  end.

Ltac prev_process :=
  ex_match2; repeat inv_next; repeat elim_embed; eauto.

Ltac solve_load_store_valid_ptr_case :=
  ex_match2; eauto; tryfalse; inv_next;
  try solve [store_eq_gmem_none_some_false];
  try solve [store_eq_gmem_some_none_false];
  try solve [valid_pointer_eq_case];
  try solve [load_eq_gmem_some_none_false];
  try solve [elim_load_eq_value_case].

Ltac solve_tso_store_gmem_buf_eq_stable :=
  match goal with
  | H1 : GMem.eq (strip (fmemory ?bm1)) (strip (fmemory ?bm2)),
         H2 : tsostorev ?c ?bm1 ?a ?v = Some ?bm1',
              H3 : tsostorev ?c ?bm2 ?a ?v = Some ?bm2' |- _ =>
    let H := fresh in
    lets H : H1; eapply gmem_eq_buf_eq_tsostorev_stable in H; eauto;
    destruct H
  end.

Ltac solve_gmem_buf_eq_tsostorev_some_none :=
  match goal with
  | H1 : GMem.eq (strip (fmemory ?bm1)) (strip (fmemory ?bm2)),
         H2 : tbuffer ?bm1 = tbuffer ?bm2,
              H3 : tsostorev ?c ?bm1 ?a ?v = Some _,
                   H4 : tsostorev ?c ?bm2 ?a ?v = None |- _ =>
    eapply gmem_eq_tsostorev_still' in H3; eauto;
    destruct H3 as [?t H3]; rewrite H3 in H4; tryfalse
  end.

Ltac strip_mem_elim :=
  match goal with
  | H : strip _ = memory _ |- context [strip _] =>
    rewrite H; eauto
  end.

Lemma gmem_eq_tsoalloc_stable' :
  forall bf gm1 gm2 fm1 fm2 lo hi fl bm1 stk,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    tsoalloc {| tbuffer := bf; fmemory := fm1 |} lo hi (bm1, stk) ->
    exists bm2 stk', tsoalloc {| tbuffer := bf; fmemory := fm2 |} lo hi (bm2, stk') /\
                GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) /\ stk = stk' /\
                tbuffer bm1 = tbuffer bm2.
Proof.
  intros.
  inv H2; simpls.
  inv H0; inv H1.
  lets Happly_buf : gmem_eq_apply_same_buf_still ___; eauto.
  destruct Happly_buf as [gm2' Happly_buf].
  lets Hembed : H.
  eapply gmem_eq_embed_apply_buf_still in Hembed; eauto.
  destruct Hembed as [fm2' [Hembed Hnext_blk_eq]].
  do 2 eexists.
  split.
  econstructor; eauto.
  rewrite H0; eauto.
  repeat (split; simpls; eauto).
  rewrite Hnext_blk_eq; eauto.
Qed.

Lemma gmem_eq_tsoalloc_stable :
  forall bf gm1 gm2 fm1 fm2 lo hi fl bm1 stk,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    tsoalloc {| tbuffer := bf; fmemory := fm1 |} lo hi (bm1, stk) ->
    exists bm2, tsoalloc {| tbuffer := bf; fmemory := fm2 |} lo hi (bm2, stk) /\
           GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) /\
           tbuffer bm1 = tbuffer bm2.
Proof.
  intros.
  eapply gmem_eq_tsoalloc_stable' in H2; eauto.
  destruct H2 as [bm2 [stk' [Htsoalloc [Hgmem_eq [Hstk Htbuffer]]]]]; subst.
  eexists.
  split; eauto.
Qed.

Lemma gmem_eq_tsostore_stable :
  forall bm1 bm2 bm1' c b ofs v,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    tsostore c bm1 b ofs v = Some bm1' ->
    exists bm2', tsostore c bm2 b ofs v = Some bm2' /\
            GMem.eq (strip (fmemory bm1')) (strip (fmemory bm2')) /\
            tbuffer bm1' = tbuffer bm2'.
Proof.
  intros.
  unfolds tsostore.
  inv H1.
  eexists; split; eauto.
  split; eauto.
  unfolds buffer_insert.
  rewrite H0; eauto.
Qed.

Lemma exec_load_TSO_gmem_eq_same_buf_stable :
  forall ge c bf fm1 fm2 gm1 gm2 fl a rs rd rs' tsofm1 tsofm2,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    exec_load_TSO ge c {| tbuffer := bf; fmemory := fm1 |} a rs rd =
    Next rs' tsofm1 ->
    exec_load_TSO ge c {| tbuffer := bf; fmemory := fm2 |} a rs rd =
    Next rs' tsofm2 ->
    tbuffer tsofm1 = tbuffer tsofm2 /\
    GMem.eq (strip (fmemory tsofm1)) (strip (fmemory tsofm2)).
Proof.
  intros.
  unfolds exec_load_TSO.
  ex_match2; tryfalse.
  repeat inv_next.
  lets Ht : H.
  eapply gmem_eq_tsoloadv_v_eq in Ht; eauto; subst; simpls; eauto.
  split; eauto.
  repeat elim_embed; eauto.
Qed.

Lemma exec_store_TSO_gmem_eq_same_buf_stable :
  forall ge c bf fm1 fm2 gm1 gm2 fl a rs rd rs' tsofm1 tsofm2 ls,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    exec_store_TSO ge c {| tbuffer := bf; fmemory := fm1 |} a rs rd ls =
    Next rs' tsofm1 ->
    exec_store_TSO ge c {| tbuffer := bf; fmemory := fm2 |} a rs rd  ls =
    Next rs' tsofm2 ->
    tbuffer tsofm1 = tbuffer tsofm2 /\
    GMem.eq (strip (fmemory tsofm1)) (strip (fmemory tsofm2)).
Proof.
  intros.
  unfolds exec_store_TSO.
  ex_match2; tryfalse.
  repeat inv_next.
  unfolds tsostorev; ex_match2.
  unfolds tsostore; inv Hx0; inv Hx; simpls.
  repeat elim_embed.
  split; eauto.
Qed.

Lemma tso_goto_label_gmem_eq_same_buf_stable :
  forall bf fm1 fm2 gm1 gm2 fl tsofm1 tsofm2 f l rs rs',
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    tso_goto_label f l rs {| tbuffer := bf; fmemory := fm1 |} = Next rs' tsofm1 ->
    tso_goto_label f l rs {| tbuffer := bf; fmemory := fm2 |} = Next rs' tsofm2 ->
    tbuffer tsofm1 = tbuffer tsofm2 /\
    GMem.eq (strip (fmemory tsofm1)) (strip (fmemory tsofm2)).
Proof.
  intros.
  unfolds tso_goto_label.
  ex_match2.
  repeat inv_next; repeat elim_embed; eauto.
Qed.

Lemma Mem_store_gmem_eq_stable :
  forall c fm1 fm2 fm1' fm2' b ofs v,
    GMem.eq (strip fm1) (strip fm2) ->
    Mem.store c fm1 b ofs v = Some fm1' ->
    Mem.store c fm2 b ofs v = Some fm2' ->
    GMem.eq (strip fm1') (strip fm2').
Proof. 
  intros.
  eapply store_fm_eq_store_gm in H0.
  eapply store_fm_eq_store_gm in H1.
  eapply store_gmem_eq_stable; eauto.
Qed.

Lemma Mem_storev_gmem_eq_stable :
  forall fm1 fm2 c v a fm1' fm2',
    GMem.eq (strip fm1) (strip fm2) ->
    Mem.storev c fm1 a v = Some fm1' ->
    Mem.storev c fm2 a v = Some fm2' ->
    GMem.eq (strip fm1') (strip fm2').
Proof.
  intros.
  unfolds Mem.storev.
  ex_match2; subst.
  eapply Mem_store_gmem_eq_stable; eauto.
Qed.
 
Lemma exec_instr_TSO_gmem_eq_stable :
  forall ge f i rs rs' buf fm1 fm2 gm1 gm2 tsofm1 fl,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    exec_instr_TSO ge f i rs {| tbuffer := buf; fmemory := fm1 |} =
    Next rs' tsofm1 ->
    exists tsofm2, exec_instr_TSO ge f i rs {| tbuffer := buf; fmemory := fm2 |} =
              Next rs' tsofm2.
Proof.
  intros.
  destruct i; simpls; tryfalse; 
    try solve
        [inv_next ; eauto];
    try solve
        [ex_match2; eapply gmem_eq_exec_load_TSO_still; eauto];
    try solve
        [ex_match2; eapply gmem_eq_exec_store_TSO_still; eauto];
    try solve [ex_match2; inv_next];
    try solve [ex_match2; inv_next;
               erewrite gmem_eq_compare_ints_TSO_eq
               with (fm1 := fm1) (fm2 := fm2); eauto];
    try solve [unfolds tso_goto_label; ex_match2; inv H2; subst; eauto].
  { ex_match2. inv H2.
    erewrite gmem_eq_compare_ints_TSO_eq with (fm1 := fm1) (fm2 := fm2); eauto.
    unfold check_compare_ints_TSO in *. erewrite gmem_eq_tso_valid_pointer_eq in Hx0; eauto. congruence. }
  { ex_match2. inv H2.
    erewrite gmem_eq_compare_ints_TSO_eq with (fm1 := fm1) (fm2 := fm2); eauto.
    unfold check_compare_ints_TSO in *. erewrite gmem_eq_tso_valid_pointer_eq in Hx0; eauto. congruence. }
  {
    ex_match2; eauto; tryfalse; repeat inv_next.
    assert (v0 = v2).
    clear - Hx0 Hx3 H H0 H1.
    eapply gmem_eq_tsoloadv_v_eq in H; eauto; subst; eauto.
    assert (v = v1).
    clear - Hx Hx2 H H0 H1.
    eapply gmem_eq_tsoloadv_v_eq in H; eauto; subst; eauto.
    subst; eauto.  
    eapply gmem_eq_tsoloadv_v_still in Hx0; eauto; destruct Hx0 as [v0' Hx0].
    rewrite Hx0 in Hx3; discriminate.
    eapply gmem_eq_tsoloadv_v_still in Hx; eauto; destruct Hx as [v' Hx].
    rewrite Hx in Hx2; discriminate.
  }
  {
    ex_match2; eauto; tryfalse; repeat inv_next.
    elim_load_eq_value_case.
    store_eq_gmem_some_none_false.
    load_eq_gmem_some_none_false.
  } 
  {
    solve_load_store_valid_ptr_case.
  }
  {
    solve_load_store_valid_ptr_case.
    elim_load_eq_value_case.
    inv H2; subst; eauto.
    elim_load_eq_value_case.
    inv H2; subst; store_eq_gmem_some_none_false.
  }
Qed.

Lemma gmem_eq_exec_instr_TSO_buf_eq_stable :
  forall ge f i rs rs' bf gm1 gm2 fm1 fm2 fl tsofm1 tsofm2,
    GMem.eq gm1 gm2 -> embed gm1 fl fm1 -> embed gm2 fl fm2 ->
    exec_instr_TSO ge f i rs {| tbuffer := bf; fmemory := fm1 |} =
    Next rs' tsofm1 ->
    exec_instr_TSO ge f i rs {| tbuffer := bf; fmemory := fm2 |} =
    Next rs' tsofm2 ->
    tbuffer tsofm1 = tbuffer tsofm2 /\
    GMem.eq (strip (fmemory tsofm1)) (strip (fmemory tsofm2)).
Proof.
  intros.
  destruct i; simpls; tryfalse;
    try solve [repeat elim_embed; repeat inv_next; eauto];
    try solve [ex_match2; eapply exec_load_TSO_gmem_eq_same_buf_stable; eauto];
    try solve [eapply exec_store_TSO_gmem_eq_same_buf_stable; eauto];
    try solve [ex_match2; eapply tso_goto_label_gmem_eq_same_buf_stable; eauto];
    try solve [ex_match2; repeat inv_next; repeat elim_embed; eauto];
    try solve [ex_match2;
               [eapply tso_goto_label_gmem_eq_same_buf_stable; eauto |
                prev_process .. ]].
  {
    ex_match2; subst.
    repeat inv_next; repeat elim_embed.
    simpls; split; eauto.
    eapply Mem_storev_gmem_eq_stable; eauto.
  }
  {
    ex_match2; subst; simpls;
      try solve [repeat inv_next; repeat elim_embed; try split; eauto].
    repeat inv_next; repeat elim_embed.
    simpl; split; eauto.
    eapply Mem_storev_gmem_eq_stable; eauto.
    repeat inv_next; simpls; split; eauto.
    elim_load_eq_value_case.
    valid_pointer_eq_case.
    repeat inv_next; simpls; split; eauto.
    valid_pointer_eq_case.
  }
  {
    ex_match2; subst; simpls.
    repeat inv_next; split; simpls; eauto.
    elim_load_eq_value_case.
    inv H2; repeat elim_embed.
    eapply Mem_storev_gmem_eq_stable; eauto.
  }
Qed.

Lemma gmem_eq_exec_instr_TSO_fp_eq :
  forall fm1 fm2 f i rs bf ge,
    GMem.eq (strip fm1) (strip fm2) ->
    exec_instr_TSO_fp ge f i rs {| tbuffer := bf; fmemory := fm1 |} =
    exec_instr_TSO_fp ge f i rs {| tbuffer := bf; fmemory := fm2 |}.
Proof.
  intros.
  destruct i; simpls; eauto;
    try solve [eapply gmem_eq_compare_ints_TSO_fp_eq; eauto].
  { 
    ex_match2; subst; eauto; tryfalse; try elim_load_eq_value_case';
      try erewrite gmem_eq_cmpu_bool_fp_eq with (fm1 := fm1) (fm2 := fm2); eauto;
        try solve [valid_pointer_eq_case'];
        try solve [elim_load_eq_value_case'];
        try solve [load_eq_gmem_some_none_false'];
        try solve [eapply GMem.eq_sym in H; eauto; load_eq_gmem_some_none_false'].  
  }
Qed.

Lemma gmem_eq_eval_builtin_arg_still : 
  forall ge (rs : Asm.preg -> val) sp bm1 bm2 a b,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    eval_builtin_arg ge rs sp bm1 a b ->
    eval_builtin_arg ge rs sp bm2 a b.
Proof.
  intros.
  generalize dependent bm2.
  induction H1; simpls; subst; intros;
    try solve [econstructor; eauto].

  Ltac eval_arg_tsoload bm1 bm2 :=
    econstructor; eauto;
    destruct bm1, bm2; simpls;
    let Hloadv := fresh in 
    lets Hloadv : gmem_eq_tsoloadv_v_still' ___; eauto;
    destruct Hloadv as [v' Hloadv];
    match goal with
    | H : GMem.eq _ _ |- _ =>
      eapply gmem_eq_tsoloadv_v_eq' in H; eauto
    end; subst; eauto.

  eval_arg_tsoload bm1 bm2.
  eval_arg_tsoload bm1 bm2.
Qed.

Lemma gmem_eq_eval_builtin_args_still :
  forall ge (rs : Asm.preg -> val) sp bm1 bm2 args vargs,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    eval_builtin_args ge rs sp bm1 args vargs ->
    eval_builtin_args ge rs sp bm2 args vargs.
Proof.
  intros.
  unfolds eval_builtin_args.
  eapply list_forall2_stable with (P := eval_builtin_arg ge rs sp bm1); eauto.
  intros.
  eapply gmem_eq_eval_builtin_arg_still; eauto.
Qed.

Lemma gmem_eq_extcall_arg_still :
  forall rs bm1 bm2 l v,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    extcall_arg rs bm1 l v ->
    extcall_arg rs bm2 l v.
Proof.
  intros.
  inv H1; econstructor; eauto.
  lets Ht : H.
  destruct bm1, bm2; simpls.
  eapply gmem_eq_tsoloadv_v_still' in H; eauto.
  destruct H as [v' H].
  eapply gmem_eq_tsoloadv_v_eq' in Ht; eauto; subst.
  eauto.
Qed.

Lemma gmem_eq_extcall_arg_pair_still :
  forall rs bm1 bm2 a b,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    extcall_arg_pair rs bm1 a b ->
    extcall_arg_pair rs bm2 a b.
Proof.
  intros.
  generalize dependent bm2.
  induction H1; simpls; intros; eauto;
    try solve [econstructor; eauto].
  {
    econstructor; eauto.
    eapply gmem_eq_extcall_arg_still; eauto.
  }
  {
    econstructor; try solve [eapply gmem_eq_extcall_arg_still; eauto].    
  }
Qed.

Lemma gmem_eq_extcall_arguments_still' :
  forall rs bm1 bm2 args vargs,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    list_forall2 (extcall_arg_pair rs bm1) args vargs ->
    list_forall2 (extcall_arg_pair rs bm2) args vargs.
Proof.
  intros.
  eapply list_forall2_stable with (P := extcall_arg_pair rs bm1); eauto.
  intros.
  eapply gmem_eq_extcall_arg_pair_still; eauto.
Qed.  

Lemma gmem_eq_extcall_arguments_still :
  forall (rs : Asm.preg -> val) bm1 bm2 sg args,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    extcall_arguments rs bm1 sg args ->
    extcall_arguments rs bm2 sg args.
Proof. 
  intros.
  unfolds extcall_arguments.
  unfolds loc_arguments.
  ex_match2.
  destruct sg; simpls.
  eapply gmem_eq_extcall_arguments_still'; eauto.
Qed.

Lemma gmem_eq_store_args_fmem_still' :
  forall args bm1 bm2 stk bm1' tys ofs,
    GMem.eq (strip (fmemory bm1)) (strip (fmemory bm2)) ->
    tbuffer bm1 = tbuffer bm2 ->
    store_args_rec_fmem bm1 stk ofs args tys = Some bm1' ->
    exists bm2', store_args_rec_fmem bm2 stk ofs args tys = Some bm2' /\
            GMem.eq (strip (fmemory bm1')) (strip (fmemory bm2')) /\
            tbuffer bm1' = tbuffer bm2'.
Proof.
  induction args; intros; eauto; simpls.
  {
    ex_match2; subst.
    inv H1.
    eexists; repeat (split; eauto).
  }
  {
    unfolds store_stack_fmem.
    ex_match2; subst;
      try solve [solve_tso_store_gmem_buf_eq_stable;
                 eapply IHargs with (bm1 := t0) (bm2 := t1); eauto];
      try solve [solve_gmem_buf_eq_tsostorev_some_none].
    {
      solve_tso_store_gmem_buf_eq_stable.
      clear H H0.
      solve_tso_store_gmem_buf_eq_stable.
      eapply IHargs with (bm1 := t1) (bm2 := t3); eauto.
    }
    {
      solve_tso_store_gmem_buf_eq_stable.
      solve_gmem_buf_eq_tsostorev_some_none.
    }
  }
Qed.
  
Lemma gmem_eq_store_args_fmem_still :
  forall bm1 bm2 gm1 gm2 fl stk bm1' tys args,
    GMem.eq gm1 gm2 ->
    embed gm1 fl (fmemory bm1) -> embed gm2 fl (fmemory bm2) ->
    tbuffer bm1 = tbuffer bm2 ->
    store_args_fmem bm1 stk args tys = Some bm1' ->
    exists bm2', store_args_fmem bm2 stk args tys = Some bm2' /\
            GMem.eq (strip (fmemory bm1')) (strip (fmemory bm2')) /\
            tbuffer bm1' = tbuffer bm2'.
Proof.
  intros.
  inv H0; inv H1.
  unfolds store_args_fmem.
  eapply gmem_eq_store_args_fmem_still'; eauto.
Qed.

Lemma gmem_eq_ub_gmem_eq:
  forall B gm1 gm1' t B' gm2,
    GMem.eq gm1 gm1' ->
    unbuffer (mktsomem B gm1) t = Some (mktsomem B' gm2) ->
    exists gm2', unbuffer (mktsomem B gm1') t = Some (mktsomem B' gm2') /\
            GMem.eq gm2 gm2'.
Proof.
  intros.
  unfolds unbuffer; simpls.
  ex_match2.
  {
    inversion H0; subst.
    eexists; split; eauto.
    eapply gmem_eq_apply_same_buf_item_still; eauto.
  }
  {
    eapply gmem_eq_apply_buf_item_stable in Hx0; eauto.
    destruct Hx0 as [gm2' Hx0].
    rewrite Hx1 in Hx0; discriminate.
  }
Qed.

(*+ Unbuffer Safe Lemmas +*)
Lemma embed_unbuffer_stable :
  forall fls tm tm' fm t n,
    FLs_embed fls tm ->
    unbuffer tm t = Some tm' ->
    embed (memory tm) (FLists.get_fl fls n) fm ->
    exists fm', embed (memory tm') (FLists.get_fl fls n) fm'.
Proof.
  intros.
  unfolds unbuffer.
  ex_match2; simpls.
  inv H0; simpls.
  inv H.
  eapply UNBS in Hx0; eauto.
  clear - Hx0.
  inv Hx0; simpls.
  clear - Embed.
  specialize (Embed n).
  eauto.
Qed.

(*+ TSO Step Lemmas +*)
Lemma gmem_buffer_eq_corestep_eq:
  forall ge fl c1 gm1 buf1 fp c2 gm2 buf2 gm1',
    tsostep ge fl c1 (buf1, gm1) fp c2 (buf2, gm2) ->
    GMem.eq gm1 gm1' ->
    exists gm2',
      tsostep ge fl c1 (buf1, gm1') fp c2 (buf2, gm2') /\
      GMem.eq gm2 gm2'.
Proof. 
  clear. intros. inv H.
  lets Hembed : gmem_eq_embed_still ___; eauto.
  destruct Hembed as [fm2 [Hembed Hnextblock_eq]].
  inv H9; simpls; subst.
  (** normal step *)
  {
    lets Ht1 : exec_instr_TSO_gmem_eq_stable ___; eauto.
    destruct Ht1 as [tsofm2 Ht1].
    lets Ht2 : gmem_eq_exec_instr_TSO_buf_eq_stable ___; eauto.
    destruct Ht2 as [Htbuffer Hgmem_eq].
    eexists; split.  
    econstructor.
    {
      instantiate (1 := fm2); eauto.
    }
    {
      eapply tso_exec_step_internal; eauto.
      eapply gmem_eq_exec_instr_TSO_fp_eq; eauto.
      inv H6; inv Hembed.
      eapply GMem.eq_sym; eauto.
    }
    eauto.
    eauto.
    eauto.
  }
  (** alloc step *)
  {
    eapply gmem_eq_tsoalloc_stable in H3; eauto. 
    destruct H3 as [bm2' [Htsoalloc [Hgmem_eq1 Hbuf_eq1]]]. 
    eapply gmem_eq_tsostore_stable in H5; eauto. 
    destruct H5 as [bm3' [Htsostore1 [Hgmem_eq2 Hbuf_eq2]]].
    eapply gmem_eq_tsostore_stable in H7; eauto.
    destruct H7 as [bm4' [Htsostore2 [Hgmem_eq3 Hbuf_eq3]]].
    eexists.
    split.
    econstructor.
    {
      instantiate (1 := fm2); eauto.
    }
    {  
      eapply tso_exec_step_internal_allocframe; eauto.
    }
    eauto.
    eauto.
    eauto.
  }
  (** buildin *)
  {
    eexists.
    split.
    econstructor.
    {
      instantiate (1 := fm2); eauto.
    }
    {
      eapply tso_exec_step_builtin; eauto.
      eapply gmem_eq_eval_builtin_args_still with
      (bm1 := {| tbuffer := buf1; fmemory := fm |}); eauto.
      simpl.
      inv H6; inv Hembed; subst; eauto.
    }
    eauto.
    eauto.
    simpl; inv H6; inv Hembed; eauto.
  }
  (** extcall *)
  {
    eexists.
    split.
    econstructor; eauto.
    {
      econstructor; eauto.
      inv H6; inv Hembed.
      eapply gmem_eq_extcall_arguments_still with
      (bm1 := {| tbuffer := buf1; fmemory := fm |}); eauto.
    }
    eauto.
    inv H6; inv Hembed; eauto.
  }
  (** extcall2 *)
  {
    eexists.
    split.
    {
      econstructor; eauto.
      econstructor; eauto.
      eauto.
    }
    inv H6; inv Hembed; eauto.
  }
  (** initialization *)
  { 
    eapply gmem_eq_tsoalloc_stable in H1; eauto.
    destruct H1 as [bm2 [Htsoalloc [Hgmem_eq1 Hbuf_eq1]]].
    eapply gmem_eq_store_args_fmem_still' in H3; eauto.
    destruct H3 as [bm3 [Hstore_args [Hgmem_eq2 Hbuf_eq2]]].
    eexists.
    split.
    {  
      econstructor; eauto.
      econstructor; eauto.
    }
    eauto.
  }
Qed.

(*+ TSO Execution Lemmas +*)
Ltac inv_some := 
  match goal with
  | H : Some ?A = Some ?B |- _ => inv H
  end.

Lemma exec_load_TSO_buf_add :
  forall ge c bm a rs rd rs' bm',
    exec_load_TSO ge c bm a rs rd = Next rs' bm' ->
    exists bf, tbuffer bm' = tbuffer bm ++ bf.
Proof.
  intros.
  unfolds exec_load_TSO; ex_match2.
  inv_next; eauto.
  eexists nil. rewrite app_nil_r; eauto.
Qed.

Lemma exec_store_TSO_buf_add :
  forall ge c bm a rs rd ls rs' bm',
    exec_store_TSO ge c bm a rs rd ls = Next rs' bm' ->
    exists bf, tbuffer bm' = tbuffer bm ++ bf.
Proof.
  intros.
  unfolds exec_store_TSO.
  ex_match2; eauto.
  inv_next; eauto.
  unfolds tsostorev.
  ex_match2.
  unfolds tsostore.
  inv Hx.
  unfold buffer_insert; simpls; eauto.
Qed.

Lemma tso_goto_label_buf_add :
  forall f l rs bm rs' bm',
    tso_goto_label f l rs bm = Next rs' bm' ->
    exists bf, tbuffer bm' = tbuffer bm ++ bf.
Proof.
  intros.
  unfolds tso_goto_label.
  ex_match2.
  inv H.
  eexists nil. rewrite app_nil_r; eauto.
Qed.

Lemma exec_instr_TSO_buf_add :
  forall ge f i rs rs' bm bm',
    exec_instr_TSO ge f i rs bm = Next rs' bm' ->
    exists bf, tbuffer bm' = tbuffer bm ++ bf.
Proof.
  intros.
  destruct i; simpls; ex_match2;
    try solve [inv_next; eexists nil; rewrite app_nil_r; eauto];
    try solve [eapply exec_load_TSO_buf_add; eauto];
    try solve [eapply exec_store_TSO_buf_add; eauto];
    try solve [eapply tso_goto_label_buf_add; eauto].
  inv H; unfold buffer_insert; simpls; eauto.
Qed.

Lemma tsoalloc_buf_add :
  forall bm bm' lo hi stk,
    tsoalloc bm lo hi (bm', stk) ->
    exists bf, tbuffer bm' = tbuffer bm ++ bf.
Proof.
  intros.
  inv H; simpls; eauto.
Qed.

Lemma store_args_fmem_buf_add :
  forall args bm b ofs tys bm',
    store_args_rec_fmem bm b ofs args tys = Some bm' ->
    exists bf, tbuffer bm' = tbuffer bm ++ bf.
Proof.
  induction args; intros; simpls; eauto.
  ex_match2; subst. inv H.
  eexists nil. rewrite app_nil_r; eauto.
  
  ex_match2; subst;
    unfolds store_stack_fmem, tsostorev; ex_match2;
      unfolds tsostore, buffer_insert; simpls; inv_some;
        eapply IHargs in H; simpls;
          destruct H as [bf H]; rewrite H; simpl;
            rewrite app_assoc_reverse; eauto.
  inv_some; simpls.
  repeat (rewrite app_assoc_reverse).
  eauto.
Qed.

Lemma unbuffer_remove_bf_head :
  forall tm tm' t,
    unbuffer tm t = Some tm' ->
    tso_buffers tm' t = tl (tso_buffers tm t).
Proof.
  intros.
  unfolds unbuffer.
  ex_match2.
  inv_some; eauto.
  simpls.
  rewrite tupdate_b_get; eauto.
Qed.

Lemma tsoalloc_gm_stable :
  forall bm lo hi bm' stk,
    tsoalloc bm lo hi (bm', stk) ->
    strip (fmemory bm) = strip (fmemory bm').
Proof.
  intros.
  inv H; simpls; eauto.
Qed.

Lemma exec_load_TSO_gm_stable :
  forall ge c bm a rs rd rs' bm',
    exec_load_TSO ge c bm a rs rd = Next rs' bm' ->
    strip (fmemory bm) = strip (fmemory bm').
Proof.
  intros.
  unfolds exec_load_TSO.
  ex_match2; eauto.
Qed.

Lemma exec_store_TSO_gm_stable :
  forall ge c bm a rs rd ls rs' bm',
    exec_store_TSO ge c bm a rs rd ls = Next rs' bm' ->
    strip (fmemory bm) = strip (fmemory bm').
Proof.
  intros.
  unfolds exec_store_TSO.
  ex_match2.
  inv_next.
  unfolds tsostorev.
  unfolds tsostore.
  ex_match2.
  inv Hx; eauto.
Qed.

Lemma tso_goto_label_gm_stable :
  forall f l rs rs' bm bm',
    tso_goto_label f l rs bm = Next rs' bm' ->
    strip (fmemory bm) = strip (fmemory bm').
Proof.
  intros.
  unfolds tso_goto_label.
  ex_match2.
Qed.

Lemma exec_instr_TSO_buf_not_empty_gm_stable :
  forall ge f i rs rs' bm bm',
    tbuffer bm <> nil ->
    exec_instr_TSO ge f i rs bm = Next rs' bm' ->
    strip (fmemory bm) = strip (fmemory bm').
Proof.
  intros.
  destruct i; simpls; ex_match2; simpls; tryfalse;
    try solve [repeat inv_next; eauto];
    try solve [eapply exec_load_TSO_gm_stable; eauto];
    try solve [eapply exec_store_TSO_gm_stable; eauto];
    try solve [eapply tso_goto_label_gm_stable; eauto].
Qed.

Lemma store_args_fmem_gm_stable :
  forall args tys bm a ofs bm',
    store_args_rec_fmem bm a ofs args tys = Some bm' ->
    strip (fmemory bm) = strip (fmemory bm').
Proof.
  induction args; intros; simpls.
  ex_match2; eauto.
  ex_match2; unfolds store_stack_fmem, tsostorev, tsostore;
    ex_match2; inv_some;
      try solve [eapply IHargs in H; eauto].
  inv_some.
  eapply IHargs in H; eauto.
Qed.

Lemma tsoload_apply_buf_hd_still :
  forall bi b fm fm' stk ofs v v0 c,
    apply_buffer_item bi (strip fm) = Some (strip fm') ->
    tsoload c {| tbuffer := bi :: b; fmemory := fm |} stk ofs = Some v ->
    tsoload c {| tbuffer := b; fmemory := fm' |} stk ofs = Some v0 ->
    v = v0.
Proof.
  intros.
  unfolds tsoload.
  ex_match2.
  simpl in Hx0.
  rewrite H in Hx0; simpls.
  rewrite Hx0 in Hx.
  inv_some.
  rewrite H0 in H1.
  inv_some; eauto.
Qed.

Lemma tsostore_apply_buf_m_eq :
  forall c bi bf fm fm' b ofs v bm bm',
    apply_buffer_item bi (strip fm) = Some (strip fm') ->
    tsostore c {| tbuffer := bi :: bf; fmemory := fm |} b ofs v = Some bm ->
    tsostore c {| tbuffer := bf; fmemory := fm' |} b ofs v = Some bm' ->
    tbuffer bm' = tl (tbuffer bm) /\ fm' = fmemory bm'.
Proof.
  intros.
  unfolds tsostore.
  repeat inv_some; simpls.
  split; eauto.
Qed.

Lemma exec_load_TSO_unbuffer_still :
  forall ge c tm tm' fm fm' t a rs rd rs' tsofm',
    unbuffer tm t = Some tm' -> strip fm = memory tm -> strip fm' = memory tm' ->
    exec_load_TSO ge c {| tbuffer := tso_buffers tm t; fmemory := fm |} a rs rd = 
    Next rs' tsofm' ->
    exec_load_TSO ge c {| tbuffer := tso_buffers tm' t; fmemory := fm' |} a rs rd =
    Next rs' {| tbuffer := tl (tbuffer tsofm'); fmemory := fm' |}.
Proof.
  intros.
  unfolds exec_load_TSO; simpls.
  ex_match2; eauto.
  inv_next; simpls.
  unfolds unbuffer.
  ex_match2; simpls; inv_some; simpls.
  unfolds tsoloadv.
  ex_match2.
  try rewrite tupdate_b_get in *.
  subst.
  rewrite <- H0 in Hx2.
  eapply tsoload_apply_buf_hd_still in Hx2; eauto; subst; eauto.
  unfolds unbuffer.
  ex_match2; simpls; inv_some; simpls.
  unfolds tsoloadv.
  ex_match2.
  repeat inv_next; simpls.
  rewrite <- H0 in Hx2.
  rewrite Hx2 in Hx.
  simpls.
  rewrite tupdate_b_get in Hx0; eauto.
  ex_match2.
Qed.

Lemma exec_store_TSO_unbuffer_still :
  forall ge c tm tm' fm fm' t a rs rd rs' tsofm' ls,
    unbuffer tm t = Some tm' -> strip fm = memory tm -> strip fm' = memory tm' ->
    exec_store_TSO ge c {| tbuffer := tso_buffers tm t; fmemory := fm |} a rs rd ls
    = Next rs' tsofm' ->
    exec_store_TSO ge c {| tbuffer := tso_buffers tm' t; fmemory := fm' |} a rs rd ls
    = Next rs' {| tbuffer := tl (tbuffer tsofm'); fmemory := fm' |}.
Proof.
  intros.
  unfolds exec_store_TSO.
  ex_match2; simpls; repeat inv_next; repeat inv_some; simpls.
  unfolds tsostorev; ex_match2.
  unfolds unbuffer.
  ex_match2; simpls.
  inv_some; simpls; subst.
  rewrite tupdate_b_get in Hx0.
  rewrite <- H0 in Hx3.
  eapply tsostore_apply_buf_m_eq in Hx3; eauto.
  destruct Hx3.
  rewrite <- H; subst.
  destruct t1; simpls; eauto.
  unfolds tsostorev.
  ex_match2.
Qed.

Lemma unbuffer_tso_valid_pointer_eq :
  forall b bi fm fm',
    apply_buffer_item bi (strip fm) = Some (strip fm') ->
    tso_valid_pointer {| tbuffer := b; fmemory := fm' |} =
    tso_valid_pointer {| tbuffer := bi :: b; fmemory := fm |}.
Proof.
  intros.
  unfolds tso_valid_pointer.
  eapply functional_extensionality; intros.
  eapply functional_extensionality; intros.
  ex_match2; simpls.
  rewrite H in Hx0; simpls.
  rewrite Hx in Hx0; simpls; inv_some; eauto.
  rewrite H in Hx0; simpls.
  rewrite Hx in Hx0; tryfalse.
  rewrite H in Hx0; simpls.
  rewrite Hx in Hx0; tryfalse.
Qed.

Lemma unbuffer_compare_ints_TSO_eq :
  forall fm fm' x y bi b rs,
    apply_buffer_item bi (strip fm) = Some (strip fm') -> 
    compare_ints_TSO x y rs {| tbuffer := b; fmemory := fm' |} =
    compare_ints_TSO x y rs {| tbuffer := bi :: b; fmemory := fm |}.
Proof.
  intros.
  unfolds compare_ints_TSO.
  erewrite <- unbuffer_tso_valid_pointer_eq; eauto.
Qed.

Lemma unbuffer_tso_goto_label_still :
  forall f l rs rs' tm tm' fm fm' t bm,
    unbuffer tm t = Some tm' -> strip fm = memory tm -> strip fm' = memory tm' ->
    tso_goto_label f l rs {| tbuffer := tso_buffers tm t; fmemory := fm |} =
    Next rs' bm ->
    tso_goto_label f l rs {| tbuffer := tso_buffers tm' t; fmemory := fm' |} =
    Next rs' {| tbuffer := tl (tbuffer bm); fmemory := fm' |}.
Proof.
  intros.
  unfolds tso_goto_label.
  ex_match2.
  inv_next; simpls.
  unfolds unbuffer.
  ex_match2; inv_some; simpls.
  rewrite tupdate_b_get; eauto.
Qed.
  
Lemma exec_instr_TSO_unbuffer_still :
  forall ge f i rs rs' tm tm' fm fm' fl tsofm' t,
    unbuffer tm t = Some tm' ->
    embed (memory tm) fl fm -> embed (memory tm') fl fm' ->
    exec_instr_TSO ge f i rs {| tbuffer := tso_buffers tm t; fmemory := fm |} =
    Next rs' tsofm' ->
    exec_instr_TSO ge f i rs {| tbuffer := tso_buffers tm' t; fmemory := fm' |} =
    Next rs' {| tbuffer := tl (tbuffer tsofm'); fmemory := fm' |}.
Proof.
  intros. 
  destruct i; simpls; eauto; inv H0; inv H1; try inv_next; simpls; eauto;
    try solve [unfolds unbuffer;
               ex_match2; inv_some; simpls;
               rewrite tupdate_b_get; eauto];
    try solve [eapply exec_load_TSO_unbuffer_still; eauto];
    try solve [eapply exec_store_TSO_unbuffer_still; eauto];
    try solve [ex_match2; inv_next; simpls; unfolds unbuffer; ex_match2; simpls;
               inv_some; simpls; rewrite tupdate_b_get; eauto];
    try solve [unfolds unbuffer; ex_match2; inv_next; inv_some;
               simpls; subst; simpls; rewrite tupdate_b_get;
               erewrite unbuffer_compare_ints_TSO_eq; [eauto | strip_mem_elim]];
    try solve [ex_match2; eapply unbuffer_tso_goto_label_still; eauto].
  { ex_match2; simpl; unfolds unbuffer; unfold check_compare_ints_TSO in *;
      ex_match2; inv_next; inv_some.
    simpls. subst. simpls. rewrite tupdate_b_get.
    erewrite unbuffer_compare_ints_TSO_eq; eauto. strip_mem_elim.
    simpl in *. rewrite tupdate_b_get in Hx2. erewrite unbuffer_tso_valid_pointer_eq in Hx2.
    rewrite Hx2 in Hx3. discriminate. strip_mem_elim. congruence.
  }
  { ex_match2; simpl; unfolds unbuffer; unfold check_compare_ints_TSO in *;
      ex_match2; inv_next; inv_some.
    simpls. subst. simpls. rewrite tupdate_b_get.
    erewrite unbuffer_compare_ints_TSO_eq; eauto. strip_mem_elim.
    simpl in *. rewrite tupdate_b_get in Hx2. erewrite unbuffer_tso_valid_pointer_eq in Hx2.
    rewrite Hx2 in Hx3. discriminate. strip_mem_elim. congruence.
  }
  {
    ex_match2. eapply unbuffer_tso_goto_label_still; eauto.
    inv_next; simpls.
    unfolds unbuffer; ex_match2; simpls; subst.
    inv_some; simpls. rewrite tupdate_b_get; eauto.
  }
  {
    ex_match2. eapply unbuffer_tso_goto_label_still; eauto.
    inv_next; simpls.
    unfolds unbuffer; ex_match2; simpls; subst.
    inv_some; simpls. rewrite tupdate_b_get; eauto.
    inv_next; simpls.
    unfolds unbuffer; ex_match2; simpls; subst.
    inv_some; simpls. rewrite tupdate_b_get; eauto.
  }
  {
    unfolds unbuffer.
    ex_match2; inv_next; inv_some; subst; simpls.
    rewrite <- H4 in Hx3; try rewrite Hx3 in *; simpls.
    try rewrite tupdate_b_get in *; subst; simpls.
    ex_match2.
    rewrite Hx in Hx4; inv_some.
    rewrite Hx0 in Hx5; inv_some.
    unfold buffer_insert; simpls; eauto.
    rewrite <- H4 in Hx3; try rewrite Hx3 in *; simpls.
    try rewrite tupdate_b_get in *; subst; simpls.
    ex_match2.
    rewrite <- H4 in Hx3; try rewrite Hx3 in *; simpls.
    try rewrite tupdate_b_get in *; subst; simpls.
    ex_match2.
  }
  {
    ex_match2.
    eapply unbuffer_tso_goto_label_still; eauto.
    unfolds unbuffer.
    inv_next; ex_match2; simpls.
    inv_some; simpls.
    rewrite tupdate_b_get; eauto.
  }
Qed. 

(*+ Unbuffer Safe Lemmas +*)

Lemma unbuffer_safe_addition_original_still :
  forall tm t bf,
    unbuffer_safe (tsoupd tm t (tso_buffers tm t ++ bf) (memory tm)) ->
    unbuffer_safe tm.
Proof.
  intros.
  remember (tsoupd tm t (tso_buffers tm t ++ bf) (memory tm)) as tm'.
  generalize dependent tm.
  generalize dependent t.
  generalize dependent bf.
  induction H; simpls; intros; subst; simpls; eauto.
  econstructor; intros.
  {
    clear - ABIS H0.
    destruct (peq t t0); subst.
    {
      specialize (ABIS t0 bi (b ++ bf)).
      rewrite tupdate_b_get in ABIS; eauto.
      rewrite H0 in ABIS.
      assert ((bi :: b) ++ bf = bi :: b ++ bf); eauto.
    }
    {
      specialize (ABIS t0 bi b).
      rewrite tupdate_not_eq_get in ABIS; eauto.
    }
  }
  {
    destruct (peq t t0); subst.
    {
      eapply H.
      
      instantiate (3 := t0).
      instantiate (2 := bi).
      instantiate (1 := b ++ bf).
      rewrite tupdate_b_get; eauto.
      rewrite H0; eauto.

      eauto.

      simpl. instantiate (2 := t0). instantiate (1 := bf).
      unfold tsoupd; simpls.
      repeat (rewrite tupdate_same_tid_eq; eauto).
      rewrite tupdate_b_get; eauto.
    }
    {
      clear - UNBS H0 H1 n H.
      eapply H.

      instantiate (1 := b). instantiate (1 := bi). instantiate (1 := t0).
      rewrite tupdate_not_eq_get; eauto.

      eauto.

      unfold tsoupd; simpls.
      instantiate (3 := t).
      rewrite tupdate_not_eq_get; eauto.
      rewrite tupdate_tid_neq_twice_rev; eauto.
    }
  }
Qed.

Lemma unbuffer_safe_addition_multi_thread_original_still :
  forall tm tm',
    unbuffer_safe tm -> memory tm = memory tm' ->
    (forall t, exists bis, tso_buffers tm t = tso_buffers tm' t ++ bis) ->
    unbuffer_safe tm'.
Proof.
  introv Hunbuf_safe.
  revert tm'.
  induction Hunbuf_safe; intros; simpls.
  econstructor; eauto; intros.
  {
    specialize (H1 t).
    destruct H1 as [bis H1].
    rewrite H2 in H1; simpls.
    eapply ABIS in H1.
    rewrite <- H0; eauto.
  }
  {
    lets Happend : H1.
    specialize (H1 t).
    destruct H1 as [bis H1].
    rewrite H2 in H1; simpls.
    rewrite <- H0 in H3.
    eapply H in H1; eauto.
    intros.
    unfold tupdate.
    ex_match2; subst; simpls.
    ex_match2; eauto.
    ex_match2; eauto.
  }
Qed.
  
Lemma unbuffer_safe_Mem_store_stable :
  forall tm fm m c b ofs v,
    unbuffer_safe {| tso_buffers := tso_buffers tm; memory := strip m |} ->
    strip fm = memory tm ->
    Mem.store c fm b ofs v = Some m ->
    unbuffer_safe tm.
Proof.
  intros.
  destruct tm; simpls.
  eapply unbuffer_safe_mem_access_same_stable; eauto.
  subst.
  clear - H1.
  unfolds Mem.store.
  ex_match2.
  inv H1; simpls; eauto.
Qed.

Lemma unbuffer_upd_original_still :
  forall tm t bf tm',
    tso_buffers tm t <> nil ->
    unbuffer (tsoupd tm t (tso_buffers tm t ++ bf) (memory tm)) t = Some tm' ->
    exists tm'', unbuffer tm t = Some tm'' /\ memory tm' = memory tm'' /\
            tso_buffers tm' =
            tupdate t (tl (tso_buffers tm t ++ bf)) (tso_buffers tm'').
Proof.
  intros.
  destruct (tso_buffers tm t) eqn:?; simpls; tryfalse.
  unfolds unbuffer; simpls.
  rewrite tupdate_b_get in H0.
  rewrite Heqb; simpls.
  ex_match2; simpls.
  rewrite tupdate_same_tid_eq in H0; eauto.
  inv H0; simpls.
  eexists.
  split; eauto.
  split; eauto.
  simpls.
  rewrite tupdate_same_tid_eq; eauto.
Qed.

Lemma unbuffer_safe_unbuffer_still :
  forall tm tm' t,
    unbuffer_safe tm -> unbuffer tm t = Some tm' ->
    unbuffer_safe tm'.
Proof. 
  intros.
  inv H.
  unfolds unbuffer.
  ex_match2; simpls.
  inv_some; simpls.
  eapply UNBS; eauto.
Qed.

Ltac unfolds_exec_load_TSO :=
  unfolds exec_load_TSO; ex_match2; simpls; inv_next; simpls.

Ltac unfolds_exec_store_TSO :=
  unfolds exec_store_TSO; ex_match2; unfolds tsostorev; ex_match2;
  unfolds tsostore; inv_some; inv_next; simpls.

Lemma unbuffer_safe_after_exec_instr_TSO_unbuffer_safe_original :
  forall ge f i tm fm rs rs' bm t,
    unbuffer_safe (tsoupd tm t (tbuffer bm) (strip (fmemory bm))) ->
    strip fm = memory tm ->
    exec_instr_TSO ge f i rs {| tbuffer := tso_buffers tm t; fmemory := fm |} =
    Next rs' bm ->
    unbuffer_safe tm.
Proof.
  intros.
  destruct i; simpls; try inv_next; simpls;
    try solve [rewrite H0 in H; simpls; unfolds tsoupd;
               rewrite buffer_unchange in H; destruct tm; simpls; eauto];
    try solve [unfolds_exec_load_TSO; unfolds tsoupd; rewrite buffer_unchange in H;
               rewrite H0 in H; destruct tm; simpls; eauto];
    try solve [unfolds_exec_store_TSO; rewrite H0 in H;
               eapply unbuffer_safe_addition_original_still; eauto];
    try solve [unfolds tso_goto_label; ex_match2; inv_next; simpls;
               rewrite H0 in H; unfolds tsoupd; rewrite buffer_unchange in H;
               destruct tm; simpls; eauto].
  ex_match2; inv_next; simpls; rewrite H0 in H;
    eapply unbuffer_safe_addition_original_still; eauto.
  ex_match2; unfolds_exec_load_TSO; unfolds tsoupd; rewrite H0 in H.
  rewrite buffer_unchange1 in H; destruct tm; simpls; eauto. 
  {
    ex_match2.
    inv_next; simpls.
    unfolds tsoupd.
    rewrite tupdate_same_eq in H; eauto.
    unfolds Mem.storev; simpls.
    ex_match2.
    eapply unbuffer_safe_Mem_store_stable; eauto.
  }
  {
    ex_match2.
    inv_next; simpls.
    unfolds tsoupd.
    rewrite tupdate_same_eq in H; eauto.
    unfolds Mem.storev; simpls.
    ex_match2.
    eapply unbuffer_safe_Mem_store_stable; eauto.
    inv_next; simpls.
    unfolds tsoupd.
    rewrite tupdate_same_eq in H; eauto.
    rewrite H0 in H; destruct tm; simpls; eauto.
  }
  {
    ex_match2.
    inv_next; simpls.
    unfolds tsoupd.
    rewrite tupdate_same_eq in H; eauto.
    unfolds Mem.storev; ex_match2; simpls.
    eapply unbuffer_safe_Mem_store_stable; eauto.
  }
Qed.
  
Lemma unbuffer_safe_after_tsostep_unbuffer_safe_original :
  forall ge fl c fp c' buf' gm' t tm,
    tsostep ge fl c (tso_buffers tm t, memory tm) fp c' (buf', gm') ->
    unbuffer_safe (tsoupd tm t buf' gm') ->
    unbuffer_safe tm.
Proof.
  intros.
  inv H. inv H6.
  inv H9.
  (** normal step *)
  {
    eapply unbuffer_safe_after_exec_instr_TSO_unbuffer_safe_original; eauto.
  }
  (** alloc frame *)
  {
    inv H4; simpls.
    unfolds tsostore; repeat inv_some; simpls.
    repeat (rewrite app_assoc_reverse in H0).
    rewrite H1 in H0.
    eapply unbuffer_safe_addition_original_still; eauto.
  }
  (** builtin *)
  {
    simpls.
    rewrite H1 in H0.
    clear - H0.
    unfolds tsoupd.
    rewrite buffer_unchange in H0; destruct tm; simpls; eauto.
  }
  (** extcall *)
  {
    simpls.
    rewrite H1 in H0.
    clear - H0.
    unfolds tsoupd.
    rewrite buffer_unchange in H0; destruct tm; simpls; eauto.
  }
  (** extcall2 *)
  {
    simpls. rewrite H1 in H0.
    unfolds tsoupd.
    rewrite buffer_unchange in H0; destruct tm; simpls; eauto.
  }
  (** initialization *)
  {
    inv H2.
    unfolds store_args_fmem.
    lets Hstore_args_buf : H4.
    lets Hstore_args_mem : H4.
    eapply store_args_fmem_buf_add in Hstore_args_buf.
    eapply store_args_fmem_gm_stable in Hstore_args_mem.
    simpls.
    destruct Hstore_args_buf as [bf Hstore_args_buf].
    rewrite <- Hstore_args_mem in H0. rewrite Hstore_args_buf in H0.
    rewrite app_assoc_reverse in H0; eauto.
    rewrite H1 in H0.
    eapply unbuffer_safe_addition_original_still; eauto.
  }
Qed.

Lemma tso_valid_pointer_same_compare_ints_TSO_fp_eq :
  forall bm bm' x y,
    (forall b ofs, tso_valid_pointer bm b ofs = tso_valid_pointer bm' b ofs) ->
    compare_ints_TSO_fp x y bm = compare_ints_TSO_fp x y bm'.
Proof.
  intros.
  unfolds compare_ints_TSO_fp.
  unfolds tso_cmpu_bool_fp_total.
  unfolds tso_weak_valid_pointer_fp.
  ex_match2.
Qed.

Lemma rs_eq_fp_eq :
  forall ge f i rs bm bm',
    (forall b ofs, tso_valid_pointer bm b ofs = tso_valid_pointer bm' b ofs) ->
    Not_lock_instr i ->
    exec_instr_TSO_fp ge f i rs bm = exec_instr_TSO_fp ge f i rs bm'.
Proof.
  intros.
  destruct i; simpls; tryfalse; eauto;
    try solve [eapply tso_valid_pointer_same_compare_ints_TSO_fp_eq; eauto].
Qed.

Lemma unbuffer_eval_builtin_arg_still :
  forall tm tm' fm fm' t ge a b (rs : Asm.preg -> val) sp,
    unbuffer tm t = Some tm' ->
    strip fm = memory tm -> strip fm' = memory tm' ->
    eval_builtin_arg ge rs sp {| tbuffer := tso_buffers tm t; fmemory := fm |}
                     a b ->
    eval_builtin_arg ge rs sp {| tbuffer := tso_buffers tm' t; fmemory := fm' |}
                     a b.
Proof.
  intros.
  remember {| tbuffer := tso_buffers tm t; fmemory := fm |} as bm.
  generalize dependent tm.
  generalize dependent tm'.
  generalize dependent fm.
  generalize dependent fm'.
  generalize dependent t.
  induction H2; simpls; intros; subst; eauto;
    try solve [econstructor; eauto].
  {
    econstructor; eauto.
    unfolds unbuffer; ex_match2.
    unfolds tsoloadv; simpls; inv_some; simpls.
    ex_match2.
    rewrite <- H2 in Hx0.
    rewrite Hx0 in Hx2; simpls.
    rewrite tupdate_b_get in Hx3; eauto.
    subst.
    rewrite Hx2 in Hx3; inv Hx3; eauto.
    subst.
    rewrite <- H2 in Hx0.
    rewrite Hx0 in Hx2; simpls.
    rewrite tupdate_b_get in Hx3; eauto.
    tryfalse.
  }
  {
    econstructor; eauto.
    unfolds tsoloadv, unbuffer; simpls; ex_match2; simpls.
    inv_some; simpls; subst; simpls.
    rewrite tupdate_b_get in Hx3; eauto.
    rewrite <- H2 in Hx0.
    rewrite Hx0 in Hx2; simpls.
    rewrite Hx2 in Hx3; inv Hx3; eauto.
    inv_some; simpls; subst; simpls.
    rewrite <- H2 in Hx0; rewrite Hx0 in Hx2; simpls.
    rewrite tupdate_b_get in Hx3; eauto.
    tryfalse.
  }
Qed.
  
Lemma unbuffer_eval_builtin_args_still :
  forall tm tm' t fm fm' (rs : Asm.preg -> val) sp ge args vargs,
    strip fm = memory tm -> strip fm' = memory tm' ->
    unbuffer tm t = Some tm' ->
    eval_builtin_args ge rs sp {| tbuffer := tso_buffers tm t; fmemory := fm |}
                      args vargs ->
    eval_builtin_args ge rs sp {| tbuffer := tso_buffers tm' t; fmemory := fm' |}
                      args vargs.
Proof.
  intros.
  eapply list_forall2_stable with
  (P := eval_builtin_arg ge rs sp
                         {| tbuffer := tso_buffers tm t; fmemory := fm |}); eauto.
  intros.
  eapply unbuffer_eval_builtin_arg_still; eauto.
Qed.

Lemma unbuffer_extcall_arg_still :
  forall tm tm' fm fm' t a b rs,
    unbuffer tm t = Some tm' ->
    strip fm = memory tm -> strip fm' = memory tm' ->
    extcall_arg rs {| tbuffer := tso_buffers tm t; fmemory := fm |} a b ->
    extcall_arg rs {| tbuffer := tso_buffers tm' t; fmemory := fm' |} a b.
Proof.
  intros.
  inv H2; simpls; econstructor; eauto; simpls.
  unfolds tsoloadv, unbuffer, tsoload.
  ex_match2; simpls; inv_some; simpls; subst; simpls;
    rewrite <- H0 in Hx3; rewrite Hx3 in Hx0; simpls;
      try solve [rewrite tupdate_b_get in Hx4; rewrite Hx0 in Hx4; inv_some; eauto];
      try solve [rewrite tupdate_b_get in Hx4; rewrite Hx0 in Hx4; tryfalse].
Qed.

Lemma unbuffer_extcall_arg_pair_still :
  forall tm tm' fm fm' t a b rs,
    unbuffer tm t = Some tm' ->
    strip fm = memory tm -> strip fm' = memory tm' ->
    extcall_arg_pair rs {| tbuffer := tso_buffers tm t; fmemory := fm |} a b ->
    extcall_arg_pair rs {| tbuffer := tso_buffers tm' t; fmemory := fm' |} a b.
Proof.
  intros.
  inv H2; econstructor; eauto;
    eapply unbuffer_extcall_arg_still; eauto.
Qed. 

Lemma store_args_rec_fmem_apply_buf_hd_still :
  forall args bi bf fm fm' b ofs tys bm,
    apply_buffer_item bi (strip fm) = Some (strip fm') ->
    store_args_rec_fmem {| tbuffer := bi :: bf; fmemory := fm |} b ofs args tys
    = Some bm ->
    store_args_rec_fmem {| tbuffer := bf; fmemory := fm' |} b ofs args tys =
    Some {| tbuffer := tl (tbuffer bm); fmemory := fm' |}.
Proof.
  induction args; simpls; intros; ex_match2; try inv_some; eauto;
  unfolds store_stack_fmem, tsostorev; ex_match2; unfolds tsostore;
    repeat inv_some; subst; unfolds buffer_insert; simpls;
      try solve [eapply IHargs; eauto].
Qed.

(*+ TSO Step and TSO Thread Lemmas +*)
Lemma tso_step_buf_add :
  forall ge fl c c' gm gm' buf buf' fp,
    tsostep ge fl c (buf, gm) fp c' (buf', gm') ->
    exists buf'', buf' = buf ++ buf''.
Proof.
  intros.
  inv H.
  inv H8; simpls; eauto.
  (** normal step *)
  {
    eapply exec_instr_TSO_buf_add in H3; eauto.
  }
  (** alloc frame *)
  {
    eapply tsoalloc_buf_add in H2; eauto.
    destruct H2 as [bf1 H2]; simpls.
    unfolds tsostore.
    inv H4; inv H6.
    unfold buffer_insert; simpls.
    rewrite H2; simpls.
    repeat rewrite app_assoc_reverse.
    eauto.
  }
  (** builtin *)
  {
    eexists nil. rewrite app_nil_r; eauto.
  }
  (** extcall *)
  {
    eexists nil. rewrite app_nil_r; eauto.
  }
  (** extcall2 *)
  {
    eexists nil. rewrite app_nil_r; eauto.
  }
  (** initialization *)
  {
    eapply tsoalloc_buf_add in H0; eauto.
    destruct H0 as [bf H0].
    unfolds store_args_fmem.
    eapply store_args_fmem_buf_add in H2; eauto.
    destruct H2 as [bf1 H2].
    rewrite H0 in H2; simpls.
    rewrite H2; rewrite app_assoc_reverse; eauto.
  }
Qed.

Lemma tso_step_buf_not_empty_gm_stable :
  forall ge fl c c' gm gm' buf buf' fp,
    buf <> nil ->
    tsostep ge fl c (buf, gm) fp c' (buf', gm') ->
    gm = gm'.
Proof.
  intros.
  inv H0.
  inv H6; inv H9; subst; simpls; eauto.
  (** core step *)
  {
    eapply exec_instr_TSO_buf_not_empty_gm_stable in H4; eauto.
  }
  (** alloc frame *)
  {
    eapply tsoalloc_gm_stable in H3; simpls.
    clear - H3 H5 H6.
    unfolds tsostore, buffer_insert; simpls.
    inv H5; inv H6; simpls; eauto.
  }
  (** initialization *)
  {
    eapply tsoalloc_gm_stable in H1; simpls.
    clear - H1 H3.
    unfolds store_args_fmem.
    eapply store_args_fmem_gm_stable in H3; eauto.
    rewrite H1; eauto.
  }
Qed.

Lemma tsofstep_unbuffer_still :
  forall ge c c' tm tm' fm fm' fl fp tsofm' t,
    unbuffer tm t = Some tm' -> embed (memory tm) fl fm ->
    tsofstep ge c {| tbuffer := tso_buffers tm t; fmemory := fm |} fp
             c' tsofm' ->
    embed (memory tm') fl fm' ->
    tsofstep ge c {| tbuffer := tso_buffers tm' t; fmemory := fm' |} fp
             c' {| tbuffer := (tl (tbuffer tsofm')); fmemory := fm'  |}.
Proof.
  intros.
  inv H1; simpls; eauto.
  (** normal step *)
  {
    eapply tso_exec_step_internal; eauto.
    eapply exec_instr_TSO_unbuffer_still; eauto.
    eapply rs_eq_fp_eq; eauto.
    {
      clear - H H0 H2.
      inv H0; inv H2.
      unfolds unbuffer.
      ex_match2.
      inv_some; subst; simpls.
      rewrite H3; rewrite Hx0; simpls.
      rewrite tupdate_b_get; subst; eauto.
    }
    {
      unfolds unbuffer.
      ex_match2.
      clear - H7.
      destruct i; simpls; eauto; tryfalse.
    }
  }
  (** alloc frame *)
  { 
    inv H0; inv H2.
    unfolds unbuffer.
    ex_match2.
    inv_some; simpls; subst; simpls.
    inv H6. 
    eapply tso_exec_step_internal_allocframe; eauto.
    {
      instantiate (1 := 
                     buffer_insert {| tbuffer := b1; fmemory := fm' |}
                                   (BufferedAlloc (Mem.nextblock fm'0) 0 sz)).
      rewrite tupdate_b_get; eauto; econstructor.
      instantiate (1 := gm').
      clear - Hx0 H12 H7.
      simpl in H12.
      rewrite <- H7 in Hx0; rewrite Hx0 in H12; simpls; eauto.
      rewrite H0; eauto.
    }
    {
      unfold tsostorev; simpls.
      unfold tsostore.
      eauto.
    }
    {
      unfolds tsostore.
      repeat inv_some; simpls.
      unfolds tsostore.
      unfold buffer_insert; simpls; eauto.
    }
  }
  (** builtin *)
  {
    lets Htm' : H.
    eapply unbuffer_remove_bf_head in Htm'; eauto.
    rewrite <- Htm'.
    eapply tso_exec_step_builtin; eauto.
    inv H0; inv H2.
    eapply unbuffer_eval_builtin_args_still with (tm := tm) (tm' := tm'); eauto.
  }
  (** extcall *)
  {
    lets Htm' : H.
    eapply unbuffer_remove_bf_head in Htm'; eauto.
    rewrite <- Htm'.
    eapply tso_exec_step_to_external; eauto.
    inv H0; inv H2.
    clear - H H7 H1 H5.
    unfolds extcall_arguments; simpls.
    eapply list_forall2_stable with
    (P := extcall_arg_pair rs {| tbuffer := tso_buffers tm t; fmemory := fm |});
      eauto.
    intros.
    eapply unbuffer_extcall_arg_pair_still; eauto.
  }
  (** extcall2 *)
  {
    lets Htm' : H.
    eapply unbuffer_remove_bf_head in Htm'; eauto.
    rewrite <- Htm'.
    eapply tso_exec_step_i64ext; eauto.
  }
  (** initialization *)
  {
    inv H4; inv H0; inv H2.
    eapply exec_initialize_call; eauto.
    econstructor; eauto.
    {
      instantiate (1 := gm').
      clear - H H10 H4 H1.
      unfolds unbuffer; ex_match2; simpls.
      inv_some; simpls.
      rewrite tupdate_b_get; eauto.
      subst; simpls.
      rewrite <- H4 in Hx0; rewrite Hx0 in H10; simpls; eauto.
    }
    {
      rewrite H0; eauto.
    }
    clear - H H6 H4 H1 H0.
    unfolds unbuffer; ex_match2; simpls;
      inv_some; simpls; subst; unfolds buffer_insert; simpls;
        rewrite tupdate_b_get; rewrite <- H4 in Hx1; unfolds store_args_fmem;
          try solve [eapply store_args_rec_fmem_apply_buf_hd_still; eauto].
  }
Qed.
  
Lemma tsostep_unbuffer_still :
  forall ge fl fls c c' tm gm gm' buf buf' fp t tm' n,
    FLs_embed fls tm -> FLists.get_fl fls n = fl ->
    tso_buffers tm t = buf -> memory tm = gm ->
    tsostep ge fl c (buf, gm) fp c' (buf', gm') ->
    unbuffer tm t = Some tm' ->
    tsostep ge fl c (tso_buffers tm' t, memory tm') fp c'
            (tl buf', memory tm').
Proof.
  intros.
  inv H1; simpls.
  inv H3; eauto.
  lets Hembed : H7.
  eapply embed_unbuffer_stable in Hembed; eauto.
  destruct Hembed as [fm' Hembed].
  econstructor; eauto. 
  instantiate (1 := mktsofmem (tl (tbuffer tsofm')) fm').
  eapply tsofstep_unbuffer_still; eauto.
  simpls.
  inv Hembed.
  rewrite H1; eauto.
  simpls; eauto.
Qed.
  
(** Thread Lemmas *)
Lemma thrdpool_tupdate_valid_original_valid :
  forall {GE : TSOGlobEnv.t} (thdp thdp' : @TSOThrdPool.t GE) (t t' : tid) c,
    TSOThrdPool.update thdp t' c thdp' ->
    TSOThrdPool.valid_tid thdp' t ->
    TSOThrdPool.valid_tid thdp t.
Proof.
  intros.
  inv H; subst; simpls.
  inv H0; subst; eauto.
Qed.

Lemma thrdpool_tupdate_valid_still_valid :
  forall {GE : TSOGlobEnv.t} (thdp thdp' : @TSOThrdPool.t GE) (t t' : tid) c,
    TSOThrdPool.update thdp t' c thdp' ->
    TSOThrdPool.valid_tid thdp t ->
    TSOThrdPool.valid_tid thdp' t.
Proof.
  intros.
  inv H; subst; simpls.
  inv H0; subst; eauto.
Qed.

Lemma thrdpool_push_valid_original_valid :
  forall {GE : TSOGlobEnv.t} (thdp thdp' : @TSOThrdPool.t GE) (t t' : tid) c new_ix sg,
    TSOThrdPool.push thdp t' new_ix c sg = Some thdp' ->
    TSOThrdPool.valid_tid thdp' t ->
    TSOThrdPool.valid_tid thdp t.
Proof.
  intros.
  unfolds TSOThrdPool.push; simpls.
  ex_match2; simpls.
  inv_some; simpls.
  unfolds TSOThrdPool.valid_tid; simpls; eauto.
Qed.

Lemma thrdpool_pop_valid_original_valid :
  forall {GE : TSOGlobEnv.t} (thdp thdp' : @TSOThrdPool.t GE) (t t' : tid),
    TSOThrdPool.pop thdp t' = Some thdp' ->
    TSOThrdPool.valid_tid thdp' t ->
    TSOThrdPool.valid_tid thdp t.
Proof.
  intros.
  unfolds TSOThrdPool.pop.
  ex_match2.
  inv_some; simpls.
  unfolds TSOThrdPool.valid_tid; simpls; eauto.
Qed.

Ltac unfold_unchanged_perm :=
  unfolds unchanged_perm;
  unfolds unchanged_validity; unfolds GMem.eq_perm;
  unfolds GMem.valid_block; unfolds GMem.perm.

Ltac unfold_belongsto :=
  unfolds belongsto; unfolds Locs.belongsto.

Ltac unfold_effects :=
  unfolds effects; do 4 unfolds Locs.union. 

Lemma buf_item_unbuf_locality_1 :
  forall bi m m',
    unbuf_locality_1 bi m m'.
Proof.
  intros.
  unfolds unbuf_locality_1; intros.
  destruct bi; simpls.
  
  (** alloc *)
  {
    unfolds alloc.
    inv H.
    eexists; split; eauto.
    unfold MemPost, unchanged_content; simpls.
    split.
    {
      inv H0.
      unfold_unchanged_perm; simpls.
      unfolds FMemOpFP.uncheck_alloc_fp.
      unfold_effects; simpls.
      unfold_belongsto.
      split; intros.
      ex_match2; subst.
      split; intro; eauto.
      ex_match2; subst.
      do 2 rewrite PMap.gss; eauto.
      split; intro; eauto.
    }
    {
      unfolds GMem.perm; simpls.
      intros.
      unfold_belongsto.
      unfold_effects; simpls.
      ex_match2; subst.
      rewrite PMap.gss in H1; eauto.
      ex_match2; tryfalse.
      do 2 rewrite PMap.gss; eauto.
    }
  }
  (** free *)
  {
    unfolds free.
    inv H0. 
    ex_match2; inv H.
    {
      eexists; split; eauto.
      unfold MemPost, unchanged_content, unchecked_free; simpls.
      unfold_belongsto; unfold_effects; simpls.
      unfolds FMemOpFP.range_locset.
      split.
      {
        unfold_unchanged_perm; simpls.
        split; intros.
        ex_match2; subst.
        unfolds range_perm.
        rewrite Zplus_minus in H.
        destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse.
        assert (z <= ofs < z0); eauto.
        split; intros.
        { 
          clear - r0 H H0.
          eapply r0 in H0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m0))); eauto.
          eapply GMem.invalid_noaccess with (ofs := ofs) (k := Memperm.Max) in H1.
          unfolds Mem.perm_order'.
          rewrite H1 in H0; simpls; tryfalse.
        }
        {
          clear - r H H0.
          eapply r in H0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m))); eauto.
          eapply GMem.invalid_noaccess with (ofs := ofs) (k := Memperm.Max) in H1.
          unfolds Mem.perm_order'.
          rewrite H1 in H0; simpls; tryfalse.
        }
        
        ex_match2; subst.
        rewrite Zplus_minus in H.
        do 2 rewrite PMap.gss; eauto. 
        destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse.
        split; intro; tryfalse.
      }
      {
        intros.
        unfolds GMem.perm; simpls.
        ex_match2; subst.
        rewrite PMap.gss in H0; simpls.
        rewrite Zplus_minus in H.
        destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse.
      }
    }
    {
      contradiction n; clear - r EffectPermEqPre.
      unfolds range_perm; intros.
      lets Hrange : H.
      eapply r in H.
      specialize (EffectPermEqPre b ofs).
      unfold_belongsto.
      unfold_effects; simpls.
      assert (FMemOpFP.range_locset b z (z0 - z) b ofs = true).
      {
        unfold FMemOpFP.range_locset.
        ex_match2; subst; rewrite Zplus_minus.
        destruct (zle z ofs); destruct (zlt ofs z0); simpls;
          tryfalse; try Lia.lia; eauto.
      }
      {
        clear - H0 H EffectPermEqPre.
        unfolds Mem.perm_order'.
        unfolds GMem.perm.
        ex_match2; tryfalse.
        eapply EffectPermEqPre in H0; clear EffectPermEqPre.
        unfolds Memperm.perm_order'.
        rewrite Hx in H0.
        rewrite Hx0 in H0.
        eapply H0 in H; eauto.
        eapply EffectPermEqPre in H0; clear EffectPermEqPre.
        unfolds Memperm.perm_order'.
        rewrite Hx in H0; rewrite Hx0 in H0.
        eapply H0; eauto.
      }
    }
  }
  (** store *)
  {
    inv H0.
    unfolds store.
    ex_match2.
    {
      eexists; split; eauto.
      inv H; simpls.
      unfold MemPost, unchanged_content; simpls.
      split.
      {
        unfold_unchanged_perm; simpls.
        split; intros; eauto.
        unfold_belongsto.
        unfold_effects.
        unfolds FMemOpFP.store_fp; simpls.
        unfolds FMemOpFP.range_locset.
        ex_match2; subst.
        unfolds Locs.emp; simpls.
        destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m1));
          simpls; tryfalse.
        split; intros; eauto.
        { 
          clear - v1 l l0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m0))); eauto.
          unfolds valid_access, range_perm.
          destruct v1.
          assert (z <= ofs < z + size_chunk m1); eauto.
          eapply H0 in H2.
          unfolds Mem.perm_order'.
          eapply GMem.invalid_noaccess in H.
          rewrite H in H2; simpls; tryfalse.
        }
        { 
          clear - v0 l l0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m))); eauto.
          unfolds valid_access, range_perm.
          destruct v0.
          assert (z <= ofs < z + size_chunk m1); eauto.
          eapply H0 in H2.
          eapply GMem.invalid_noaccess in H.
          unfolds Mem.perm_order'.
          rewrite H in H2; simpls; tryfalse.
        }
      }
      {
        intros.
        unfolds GMem.perm; simpls.
        unfold_belongsto.
        unfold_effects; simpls.
        unfolds FMemOpFP.range_locset.
        ex_match2; subst.
        destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m1));
          simpls; tryfalse.
        assert (z <= ofs < z + size_chunk m1); eauto.
        do 2 rewrite PMap.gss; eauto.
        eapply setN_geteq2; eauto.
        rewrite encode_val_length.
        rewrite <- size_chunk_conv; eauto.
      }
    }
    {
      inv H. 
      contradiction n; clear - v0 EffectPermEqPre.
      unfolds valid_access, range_perm; simpls.
      destruct v0.
      split; eauto.
      intros.
      lets Hrange : H1.
      eapply H in H1.
      specialize (EffectPermEqPre b ofs).
      unfold_belongsto.
      unfold_effects; simpls.
      unfolds FMemOpFP.range_locset.
      ex_match2; subst.
      destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m1));
        tryfalse; try Lia.lia; simpls.
      assert (true = true); eauto.
      eapply EffectPermEqPre in H2.
      unfolds GMem.perm.
      eapply H2; eauto.
    }
  }
Qed.