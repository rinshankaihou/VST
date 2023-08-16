From mathcomp.ssreflect Require Import fintype ssrnat.                  
Require Import Coqlib Maps Axioms.  
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
 
Require Import Asm. 

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Memdata Memperm MemAux FMemLemmas GMemory FMemory Footprint TSOMem.
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe. 
 
Require CminorLang. 
Require SpecLang. 
Require Import ASM_local InteractionSemantics.
Require Import AsmLang.
Require Import AsmTSO TSOMem.

Require Import Coq.Lists.Streams.

Require Import RGRels.
Require Import LibTactics.

Require Import code.
Require Import ObjectSim.
Require Import TSOGlobSem.
Require Import InvRG. 
Require Import AuxTacLemmas.
Require Import FMemLemmas.

(** * Lemmas about TSO memory *)

(** ** Auxiliary Definitions *)
Fixpoint remove_nth {A : Type} n (l : list A) :=
  match n with
  | 0 => match l with
        | nil => l
        | a :: l' => l'
        end 
  | n'.+1 => match l with
            | nil => l
            | a :: l' => a :: remove_nth n' l'
            end
  end. 

Fixpoint get_nth {A : Type} n (l : list A) :=
  match n with
  | 0 => match l with
        | nil => None
        | a :: l' => Some a
        end
  | n'.+1 => match l with
            | nil => None
            | a :: l' => get_nth n' l'
            end
  end.

Lemma after_remove_nth_in_origin :
  forall {A : Type} n {l1 l2 : list A} b,
    remove_nth n l2 = l1 ->
    In b l1 -> In b l2.
Proof.
  induction n; intros.
  {
    destruct l2; simpls; eauto; subst; tryfalse.
    eauto.
  }
  {
    destruct l2; simpls; subst.
    tryfalse.
    simpl in H0.
    destruct H0; eauto.
  }
Qed.
  
(** ** Auxiliary LTac *)
Local Transparent Mem.load Mem.alloc Mem.store Mem.free.
Ltac memunfolds:=
  unfold Mem.load,Mem.alloc,Mem.store,Mem.free,load,store,free,alloc,strip,
  Mem.valid_access,Mem.range_perm,range_perm,Mem.perm,GMem.perm,SpecLang.loadmax,SpecLang.storemax in *;
  simpl in *.

Ltac dis_if_else :=
  let Heqe := fresh in
  match goal with
  | H : context [if ?x then _ else _] |- _ =>
    destruct x eqn:Heqe; try discriminate
  | _ => idtac
  end.

(** ** Auxiliary Lemmas *)
Lemma remove_eq_b_neq_in_still :
  forall A n {l1 l2 : list A} b b0,
    remove_nth n l2 = l1 -> get_nth n l2 = Some b0 -> b <> b0 ->
    In b l2 -> In b l1.
Proof.
  induction n; intros.
  { 
    destruct l2; simpls; tryfalse; subst.
    inversion H0; subst.
    destruct H2; simpl; eauto.
    subst; tryfalse.
  }
  {
    simpls.
    destruct l2; tryfalse.
    destruct l1; tryfalse.
    inversion H; subst.
    simpls.
    destruct H2; eauto.
  }
Qed.  

Lemma in_or_app_rev :
  forall A l m (a : A),
    In a (l ++ m) -> In a l \/ In a m.
Proof.
  intros A l.
  induction l; intros.
  {
    simpls; eauto.
  }
  {
    simpls.
    destruct H; eauto.
    eapply IHl in H.
    destruct H; eauto.
  }
Qed.

Lemma PMap_set_same_Mem_eq :
  forall p a (m : ZMap.t memval),
    (snd m) ! p = Some a ->
    PMap.set p a m = m.
Proof.
  intros p.
  induction p; intros; try destruct m; simpls.
  {
    destruct t; tryfalse.
    specialize (IHp a (m, t2)).
    simpl in IHp.
    eapply IHp in H.
    clear - H.
    unfolds PMap.set.
    simpls.
    inversion H; subst.
    rewrite PTree.set2.
    eauto.
  }
  {
    destruct t; tryfalse.
    specialize (IHp a (m, t1)).
    simpl in IHp.
    eapply IHp in H.
    clear - H.
    unfolds PMap.set.
    simpls.
    inversion H; subst.
    rewrite PTree.set2.
    eauto.
  }
  {
    destruct t; simpls; tryfalse.
    subst.
    eauto.
  }
Qed.

Lemma PTree_set_not_leaf :
  forall A p (a : A) m,
    PTree.set p a m = PTree.Leaf -> False.
Proof.
  intros A p.
  induction p; intros; simpls; destruct m; tryfalse.
Qed.

Lemma vl_not_null_not_leaf :
  forall vl p m,
    vl <> nil ->
    snd (Mem.setN vl p m) <> PTree.Leaf.
Proof.
  intro vl.
  induction vl; intros; tryfalse.
  destruct vl.
  simpl.
  intro.
  destruct m; simpls.
  eapply PTree_set_not_leaf in H0; tryfalse. 
  assert (Mem.setN (a :: m0 :: vl) p m =
          Mem.setN (m0 :: vl) (p + 1)%Z (ZMap.set p a m)).
  eauto.
  rewrite H0.
  assert (m0 :: vl <> nil); intro; tryfalse.
  eapply IHvl in H1.
  contradiction H1.
  eauto.
Qed.

Lemma vl_set_1_fisrt :
  forall vl p m a t1 t2 o,
    (0 < p)%Z -> (snd m) ! 1 = Some a -> 
    snd (Mem.setN vl p m) = PTree.Node t1 o t2 ->
    o = Some a.
Proof.
  induction vl; intros; tryfalse.
  {
    simpls.
    destruct m; simpls.
    destruct t; simpls.
    tryfalse.
    inversion H1; subst; eauto.
  }
  {
    simpl in H1.
    eapply IHvl in H1; eauto.
    Lia.lia.
    clear - H H0.
    unfold ZMap.set.
    unfold PMap.set.
    destruct m; simpls.
    destruct t; tryfalse.
    subst.
    ex_match2.
    eapply PTree_set_not_leaf in Hx; tryfalse.
    destruct p; simpls; try Lia.lia.
    inversion Hx; eauto.
    inversion Hx; eauto.
  }
Qed.

Lemma vl_set_p0_get_left :
  forall vl p1 p m a t1 t2 o,
    (Z.pos p < p1)%Z -> (snd m) ! (p~0) = Some a -> 
    snd (Mem.setN vl p1 m) = PTree.Node t1 o t2 ->
    t1 ! p = Some a.
Proof.
  induction vl; intros; tryfalse.
  {
    simpls.
    destruct m; simpls.
    subst; eauto.
  }
  {
    simpl in H1.
    eapply IHvl in H1; eauto.
    Lia.lia.
    clear - H H0. 
    destruct m; simpls.
    destruct t; simpls; tryfalse.
    destruct (PTree.set (ZIndexed.index p1) a (PTree.Node t1 o t2))
             eqn:?; tryfalse.
    eapply PTree_set_not_leaf in Heqt; tryfalse.
    clear - H Heqt H0. 
    destruct (ZIndexed.index p1) eqn:?; simpls.
    inversion Heqt; subst; eauto.
    inversion Heqt; subst; eauto.
    destruct (PTree.set p0 a t1) eqn:?; tryfalse.
    eapply PTree_set_not_leaf in Heqt0; tryfalse.
    inversion Heqt0; subst.
    rewrite PTree.gso; eauto.
    intro; subst.
    clear - H Heqp0.
    destruct p1; simpls; try Lia.lia; tryfalse.
    inversion Heqp0; subst; try Lia.lia.
    inversion Heqt; subst.
    eauto.
  }
Qed.

Lemma vl_set_p1_get_right :
  forall vl p1 p m a t1 t2 o,
    (Z.neg p < p1)%Z -> (snd m) ! (p~1) = Some a -> 
    snd (Mem.setN vl p1 m) = PTree.Node t1 o t2 ->
    t2 ! p = Some a.
Proof.
  induction vl; intros; tryfalse.
  {
    simpls.
    destruct m; simpls.
    subst; eauto.
  }
  {
    simpl in H1.
    eapply IHvl in H1; eauto.
    Lia.lia.
    clear - H H0. 
    destruct m; simpls.
    destruct t; simpls; tryfalse.
    destruct (PTree.set (ZIndexed.index p1) a (PTree.Node t1 o t2))
             eqn:?; tryfalse.
    eapply PTree_set_not_leaf in Heqt; tryfalse.
    clear - H Heqt H0.  
    destruct (ZIndexed.index p1) eqn:?; simpls.
    inversion Heqt; subst; eauto.
    rewrite PTree.gso; eauto.
    intro; subst.
    clear - H Heqp0.
    destruct p1; simpls; try Lia.lia; tryfalse.
    inversion Heqp0; subst.
    Lia.lia.
    inversion Heqt; subst; eauto.
    inversion Heqt; subst; eauto.
  }
Qed.

Lemma le_setN_get_same :
  forall p2 p1 vl a m,
    (p2 < p1)%Z ->
    (snd (Mem.setN vl p1 (PMap.set (ZIndexed.index p2) a m)))
      ! (ZIndexed.index p2) = Some a.
Proof. 
  intro p2.
  induction p2; simpl; intros.
  {
    destruct (snd (Mem.setN vl p1 (PMap.set 1 a m))) eqn:Heqe.
    {
      destruct vl.
      simpls.
      destruct m; simpls.
      destruct t; simpls; tryfalse.
      eapply vl_not_null_not_leaf in Heqe; tryfalse.
      intro; tryfalse.
    }
    {
      destruct vl.
      simpls.
      destruct m; simpls.
      destruct t; simpls; tryfalse.
      inversion Heqe; eauto.
      inversion Heqe; eauto.
      eapply vl_set_1_fisrt; eauto.
      unfold PMap.set.
      destruct m; simpls.
      destruct t; eauto.
    }
  }
  {
    destruct (snd (Mem.setN vl p1 (PMap.set p~0 a m))) eqn:Heqe.
    {
      destruct vl.
      destruct m; simpls.
      destruct t; simpls; tryfalse. 
      eapply vl_not_null_not_leaf in Heqe; tryfalse.
      intro; tryfalse.
    }
    {
      eapply vl_set_p0_get_left; eauto.
      destruct m; simpl.
      destruct t; simpl.
      rewrite PTree.gss; eauto.
      rewrite PTree.gss; eauto.
    }
  }
  {
    destruct (snd (Mem.setN vl p1 (PMap.set p~1 a m))) eqn:Heqe.
    {
      destruct vl.
      destruct m; simpls.
      destruct t; simpls; tryfalse.
      eapply vl_not_null_not_leaf in Heqe; tryfalse.
      intro; tryfalse.
    }
    {
      eapply vl_set_p1_get_right; eauto.
      destruct m; simpl.
      destruct t; simpl.
      rewrite PTree.gss; eauto.
      rewrite PTree.gss; eauto.
    }
  }
Qed.

Lemma PTree_set_twice_not_same_reorder_eq :
  forall A b b' (a a' : A) m,
    b <> b' ->
    PTree.set b a (PTree.set b' a' m) = PTree.set b' a' (PTree.set b a m).
Proof.
  induction b; induction b'; intros;
    try solve [simpl; destruct m; simpls; try solve [f_equal; eauto]].
  {
    simpl.
    assert (b <> b').
    intro.
    contradiction H.
    subst; eauto.
    destruct m; simpls; f_equal; eauto.
  }
  {
    simpl.
    assert (b <> b').
    intro.
    contradiction H.
    subst; eauto.
    destruct m; simpls; f_equal; eauto.
  }
  {
    tryfalse.
  }
Qed.
  
Lemma PMap_set_twice_not_same_reorder_eq :
  forall A b b' (a a' : A) m,
    b <> b' ->
    PMap.set b a (PMap.set b' a' m) = PMap.set b' a' (PMap.set b a m).
Proof.
  intros.
  unfold PMap.set.
  destruct m; simpl.
  rewrite PTree_set_twice_not_same_reorder_eq; eauto.
Qed.

Lemma Mem_setN_PMap_set_g_reorder_eq :
  forall vl p1 p2 a m,
    (p2 < p1)%Z ->
    Mem.setN vl p1 (PMap.set (ZIndexed.index p2) a m) =
    PMap.set (ZIndexed.index p2) a (Mem.setN vl p1 m).
Proof.
  induction vl; intros; simpls; eauto.
  unfold ZMap.set.
  rewrite <- IHvl; eauto.
  rewrite PMap_set_twice_not_same_reorder_eq; eauto.
  intro.
  eapply ZIndexed.index_inj in H0.
  subst; Lia.lia.
  Lia.lia.
Qed.

Lemma Mem_setN_ZMap_set_g_reorder_eq :
  forall vl p1 p2 a m,
    (p2 < p1)%Z ->
    Mem.setN vl p1 (ZMap.set p2 a m) =
    ZMap.set p2 a (Mem.setN vl p1 m).
Proof.
  intros.
  unfolds ZMap.set.
  eapply Mem_setN_PMap_set_g_reorder_eq; eauto.
Qed.

Lemma Mem_setN_twice_same_eq :
  forall vl p m,
    Mem.setN vl p (Mem.setN vl p m) = Mem.setN vl p m.
Proof.
  intro vl.
  induction vl; intros; eauto.
  simpl.
  specialize (IHvl (p+1)%Z (ZMap.set p a m)).
  rewrite <- IHvl at 2.
  assert (ZMap.set p a (Mem.setN vl (p + 1) (ZMap.set p a m)) =
          Mem.setN vl (p + 1) (ZMap.set p a m)).
  { 
    unfold ZMap.set.
    eapply PMap_set_same_Mem_eq; eauto.
    rewrite le_setN_get_same; eauto.
    Lia.lia.
  }
  rewrite H.
  eauto.
Qed.

Lemma Mem_setN_same_place_eq_setN_once :
  forall (vl vl' : list memval) p m,
    Datatypes.length vl = Datatypes.length vl' ->
    Mem.setN vl p (Mem.setN vl' p m) = Mem.setN vl p m.
Proof.
  induction vl; induction vl'; intros; simpls; eauto; tryfalse.
  assert (Mem.setN vl' (p + 1) (ZMap.set p a0 m) =
          ZMap.set p a0 (Mem.setN vl' (p + 1) m)).
  {
    unfold ZMap.set.
    rewrite Mem_setN_PMap_set_g_reorder_eq; eauto.
    Lia.lia.
  }
  rewrite H0.
  rewrite ZMap.set2.
  rewrite Mem_setN_ZMap_set_g_reorder_eq.
  rewrite IHvl; eauto.
  rewrite Mem_setN_ZMap_set_g_reorder_eq; eauto.
  Lia.lia.
  Lia.lia.
Qed. 

Definition get_bi_block (bi : buffer_item) :=
  match bi with
  | BufferedAlloc b _ _ => b
  | BufferedFree b _ _ => b
  | BufferedStore _ b _ _ => b
  end.

Lemma block_not_in_bf_buffer_item_block_neq :
  forall L tm t bi rest,
    (forall t, ~ In L (get_tsom_b t tm)) ->
    tso_buffers tm t = bi :: rest ->
    (get_bi_block bi) <> L.
Proof.
  intros.
  unfolds get_tsom_b.
  destruct tm; simpls.
  specialize (H t).
  rewrite H0 in H.
  destruct bi; simpls; intro; subst; contradiction H; eauto.
Qed.

Lemma nat_add_nochange_zero :
  forall n,
    n.+1 = 1 -> n = 0.
Proof.
  intros.
  Lia.lia.
Qed.

(** ** GMemory and TSOMemory Lemmas *)
Lemma next_block_not_in_validblock :
  forall fm,
    ~ In (Mem.nextblock fm) (Mem.validblocks fm).
Proof.
  intros; intro.
  destruct fm; simpls.
  unfolds Mem.nextblock; simpls.
  assert (get_block freelist nextblockid = get_block freelist nextblockid); eauto.
  eapply valid_wd in H0; eauto.
  eapply H0 in H.
  Lia.lia.
Qed.

Lemma mem_strip_gm_vb_eq :
  forall m,
    Mem.validblocks m = (GMem.validblocks (strip m)).
Proof.
  intros.
  destruct m; eauto.
Qed.

Lemma Mem_writable_imp_readable :
  forall m b ofs k sz,
    Mem.range_perm m b ofs sz k Memperm.Writable ->
    Mem.range_perm m b ofs sz k Memperm.Readable.
Proof. 
  intros.
  unfolds Mem.range_perm.
  intros.
  eapply H in H0.
  unfolds Mem.perm.
  unfolds Mem.perm_order'.
  clear H.
  destruct ((Mem.mem_access m) !! b ofs0 k); tryfalse.
  inversion H0; subst; eauto.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma gmem_perm_strip_mem_perm_eq : 
  forall fm b ofs k p,
    GMem.perm (strip fm) b ofs k p <-> Mem.perm fm b ofs k p.
Proof.
  intros.
  split; intros; unfolds GMem.perm, Mem.perm;
    try rewrite Mem_GMem_access_eq; eauto.
Qed.
 
Lemma store_succ_read_perm :
  forall m m' b ofs c v,
    store c m b ofs v = Some m' ->
    range_perm m' b ofs (ofs + size_chunk c) Max Readable.
Proof.
  intros. 
  unfolds store. 
  dis_if_else.
  destruct m.
  simpls. 
  inversion H; subst.
  lets Hrange_perm : v0.
  clear - Hrange_perm.
  unfolds valid_access, range_perm.
  simpls.
  intros.
  eapply Hrange_perm in H.
  unfolds Mem.perm_order'.
  ex_match2.
  eapply perm_order_trans with (p2 := Writable); eauto.
  constructor.
Qed.

Lemma store_succ_write_perm :
  forall m m' b ofs c v,
    store c m b ofs v = Some m' ->
    range_perm m' b ofs (ofs + size_chunk c) Max Writable.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  destruct m.
  simpls.
  inversion H; subst. 
  lets Hrange_perm : v0. 
  clear - Hrange_perm.
  unfolds valid_access, range_perm.
  simpls.
  intros.
  eapply Hrange_perm in H.
  eauto.
Qed.

Lemma GMem_writable_imp_readable :
  forall m b ofs k sz,
    range_perm m b ofs sz k Memperm.Writable ->
    range_perm m b ofs sz k Memperm.Readable.
Proof. 
  intros.
  unfolds range_perm.
  intros.
  eapply H in H0.
  unfolds Mem.perm_order'.
  clear H.
  destruct ((GMem.mem_access m) !! b ofs0 k); tryfalse.
  inversion H0; subst; eauto.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma Mem_range_perm_cur_max :
  forall fm b lo hi p,
    Mem.range_perm fm b lo hi Memperm.Cur p ->
    Mem.range_perm fm b lo hi Memperm.Max p.
Proof.
  intros.
  unfolds Mem.range_perm.
  intros.
  eapply H in H0.
  eapply Mem.perm_cur_max; eauto.
Qed.

Lemma Mem_GMem_access_eq :
  forall fm,
    Mem.mem_access fm = GMem.mem_access (strip fm).
Proof.
  intros.
  destruct fm.
  simpls.
  eauto.
Qed.

Lemma Mem_GMem_contents_eq :
  forall fm,
    GMem.mem_contents (strip fm) = Mem.mem_contents fm.
Proof.
  intros.
  destruct fm.
  eauto.
Qed.

Lemma Mem_store_mem_access_stable :
  forall fm fm' c b ofs v,
    Mem.store c fm b ofs v = Some fm' ->
    Mem.mem_access fm = Mem.mem_access fm'.
Proof.
  intros.
  unfolds Mem.store.
  ex_match2.
  inv H.
  eauto.
Qed.

Lemma GMem_range_perm_Mem_range_perm :
  forall fm b ofs c k p,
    range_perm (strip fm) b ofs (ofs + size_chunk c) k p ->
    Mem.range_perm fm b ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds range_perm, Mem.range_perm.
  unfold Mem.perm.
  intros.
  eapply H in H0.
  rewrite Mem_GMem_access_eq; eauto.
Qed.

Lemma Mem_range_perm_GMem_range_perm :
  forall fm b ofs c k p,
    Mem.range_perm fm b ofs (ofs + size_chunk c) k p ->
    range_perm (strip fm) b ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds Mem.range_perm.
  unfold range_perm.
  introv Hrange.
  eapply H in Hrange.
  unfolds Mem.perm.
  rewrite <- Mem_GMem_access_eq; eauto.
Qed.

Lemma load_in_validblocks :
  forall c m b ofs v,
    load c m b ofs = Some v ->
    In b (GMem.validblocks m).
Proof. 
  intros.
  unfolds load.
  dis_if_else.
  destruct m; simpls.
  lets Ht : v0.
  clear - Ht.
  unfolds valid_access, range_perm.
  simpls.
  destruct Ht as [Ht Halign].
  specialize (Ht ofs).
  assert ((ofs <= ofs < ofs + size_chunk c)%Z).
  split; try destruct c; simpls; try Lia.lia.
  eapply Ht in H.
  clear - invalid_noaccess H.
  unfolds Mem.perm_order'.
  destruct (mem_access !! b ofs Max) eqn:?; tryfalse.
  lets Hcls : Classical_Prop.classic (In b validblocks);
    destruct Hcls as [Hcls | Hcls]; eauto.
  eapply invalid_noaccess in Hcls.
  rewrite Heqo in Hcls; tryfalse.
Qed.

Lemma range_perm_alloc_still :
  forall fsm fsm' stk' b ofs c k p lo hi,
    range_perm (strip fsm) b ofs (ofs + size_chunk c) k p ->
    Mem.alloc fsm lo hi = (fsm', stk') ->
    range_perm (strip fsm') b ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds Mem.alloc. 
  inversion H0; subst. 
  clear H0.
  unfold strip.
  simpl.
  unfolds range_perm.
  simpls.
  introv Hrange.
  eapply H in Hrange.  
  clear - Hrange.
  destruct fsm.
  simpls.
  unfold Mem.nextblock.
  simpl.
  unfolds Mem.perm_order'.
  unfold get_block.
  destruct (mem_access !! b ofs0 k) eqn:Hmem_access; tryfalse.
  rewrite PMap.gso; eauto.
  rewrite Hmem_access; eauto.
  assert (get_block freelist nextblockid = Str_nth nextblockid freelist).
  {
    unfold get_block.
    eauto.
  }
  eapply valid_wd in H.
  lets Ht : (Classical_Prop.classic (In (Str_nth nextblockid freelist) validblocks)).
  destruct Ht.
  eapply H in H0.
  Lia.lia.
  lets Ht : (Classical_Prop.classic (In b validblocks)).
  destruct Ht.
  intro; subst; tryfalse.
  eapply invalid_noaccess in H1.
  rewrite Hmem_access in H1; tryfalse.
Qed.

Lemma range_perm_alloc_still' :
  forall m m' b L ofs c k p lo hi,
    range_perm m L ofs (ofs + size_chunk c) k p ->
    alloc m b lo hi = Some m' -> b <> L ->
    range_perm m' L ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds alloc.
  inversion H0; subst; simpls.
  clear - H H1.
  unfolds range_perm.
  simpls.
  intros.
  eapply H in H0.
  rewrite PMap.gso; eauto.
Qed.

Lemma range_perm_alloc_still'_rev :
  forall m m' b L ofs c k p lo hi,
    range_perm m' L ofs (ofs + size_chunk c) k p ->
    alloc m b lo hi = Some m' -> b <> L ->
    range_perm m L ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds alloc.
  inversion H0; subst; simpls.
  clear - H H1.
  unfolds range_perm.
  simpls.
  intros.
  eapply H in H0.
  rewrite PMap.gso in H0; eauto.
Qed.

Lemma range_perm_free_still' :
  forall m m' b L ofs c k p lo hi,
    range_perm m L ofs (ofs + size_chunk c) k p ->
    free m b lo hi = Some m' -> b <> L ->
    range_perm m' L ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds free.
  dis_if_else.
  inversion H0; subst; simpls.
  clear - H H1.
  unfolds range_perm.
  simpls.
  intros.
  eapply H in H0.
  rewrite PMap.gso; eauto.
Qed.

Lemma range_perm_free_still'_rev :
  forall m m' b L ofs c k p lo hi,
    range_perm m' L ofs (ofs + size_chunk c) k p ->
    free m b lo hi = Some m' -> b <> L ->
    range_perm m L ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds free.
  dis_if_else.
  inversion H0; subst; simpls.
  clear - H H1.
  unfolds range_perm.
  simpls.
  intros.
  eapply H in H0.
  rewrite PMap.gso in H0; eauto.
Qed.

Lemma range_perm_store_still' :
  forall m m' b L ofs ofs' v c c' k p,
    range_perm m L ofs (ofs + size_chunk c) k p ->
    store c' m b ofs' v = Some m' ->
    range_perm m' L ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H0; subst; eauto.
Qed.

Lemma range_perm_store_still'_rev :
  forall m m' b L ofs ofs' v c c' k p,
    range_perm m' L ofs (ofs + size_chunk c) k p ->
    store c' m b ofs' v = Some m' ->
    range_perm m L ofs (ofs + size_chunk c) k p.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H0; subst; eauto.
Qed.

Lemma range_perm_store_still'' :
  forall m m' b L ofs' v lo hi c' k p,
    range_perm m L lo hi k p ->
    store c' m b ofs' v = Some m' ->
    range_perm m' L lo hi k p.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H0; subst; eauto.
Qed.

Lemma range_perm_store_still''_rev :
  forall m m' b L ofs' v lo hi c' k p,
    range_perm m' L lo hi k p ->
    store c' m b ofs' v = Some m' ->
    range_perm m L lo hi k p.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H0; subst; eauto.
Qed.

Lemma Mem_valid_access_impl_GMem_valid_access :
  forall fm c b ofs k
    (HMem_valid_access : Mem.valid_access fm c b ofs k),
    range_perm (strip fm) b ofs (ofs + size_chunk c) Memperm.Max k.
Proof.
  intros.
  unfolds Mem.valid_access.
  destruct HMem_valid_access as [HMem_range_perm Halign].
  unfolds Mem.range_perm.
  unfolds range_perm.
  unfolds Mem.perm.
  introv Hrange.
  eapply HMem_range_perm in Hrange.
  eapply InteractionSemantics.perm_order'_''.
  rewrite Mem_GMem_access_eq in Hrange.
  eauto.
Qed.

Lemma GMem_contents_get_block_alloc_eq :
  forall fsm fsm' stk' b lo hi,
    Mem.alloc fsm lo hi = (fsm', stk') -> In b (Mem.validblocks fsm) ->
    (GMem.mem_contents (strip fsm)) !! b =
    (GMem.mem_contents (strip fsm')) !! b.
Proof.
  intros.
  unfolds Mem.alloc.
  inversion H; subst.
  unfold strip.
  simpls.
  clear H.
  destruct fsm; simpls.
  unfold Mem.nextblock.
  simpls.
  rewrite PMap.gso; eauto.
  introv Hcontr.
  symmetry in Hcontr.
  eapply valid_wd in Hcontr.
  eapply Hcontr in H0; Lia.lia.
Qed.

Lemma range_perm_cur_max:
  forall m b lo hi p,
    Mem.range_perm m b lo hi Memperm.Cur p->
    Mem.range_perm m b lo hi Memperm.Max p.
Proof.
  memunfolds;intros.
  eapply Mem.perm_cur_max;eauto.
  eapply H;eauto.
Qed.

Lemma gmem_eq:
  forall m1 m2,
    GMem.mem_contents m1 = GMem.mem_contents m2 ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    GMem.validblocks m1 = GMem.validblocks m2 ->
    m1 = m2.
Proof.
  destruct m1,m2;simpl.
  intros. subst.
  rewrite proof_irr with(a1:=access_max)(a2:=access_max0).
  rewrite proof_irr with(a1:=contents_default)(a2:=contents_default0).
  rewrite proof_irr with(a1:=invalid_noaccess)(a2:=invalid_noaccess0).
  auto.
Qed.

Lemma load_fm_eq_load_gm :
  forall c fm b ofs v,
    Mem.load c fm b ofs = Some v -> 
    load c (strip fm) b ofs = Some v.
Proof. 
  memunfolds;intros;simpl.
  destruct Mem.valid_access_dec;try discriminate.
  destruct TSOMem.valid_access_dec;auto.
  contradict n.
  inv v0.
  constructor;auto.
  eapply range_perm_cur_max;eauto.
Qed.

Lemma load_gm_embed_load_fm :
  forall m fl fm b ofs v c,
    (forall ofs',
        (ofs <= ofs' < ofs + size_chunk c)%Z ->
        exists p,
        ((GMem.mem_access (strip fm)) !! b ofs' Memperm.Cur =
         Some p /\ Memperm.perm_order p Memperm.Writable)) ->
    embed m fl fm -> 
    load c m b ofs = Some v ->
    Mem.load c fm b ofs = Some v.
Proof.
  intros.
  inversion H0; subst; eauto.
  memunfolds; simpls.
  dis_if_else. 
  clear H2 H0.
  ex_match2.
  contradiction n.
  unfold Mem.valid_access; eauto.
  split; eauto.
  unfold Mem.range_perm.
  intros.
  eapply H in H0.
  destruct H0 as [p [Hperm Hperm_order]].
  unfold Mem.perm.
  rewrite Hperm.
  unfold Mem.perm_order'.
  eapply perm_order_trans; eauto.
  constructor.
  clear - v0.
  unfolds valid_access.
  split_and v0; eauto.
Qed.
 
Lemma store_fm_eq_store_gm :
  forall fm b ofs c v fm' ,
    Mem.store c fm b ofs v = Some fm' ->
    store c (strip fm) b ofs v = Some (strip fm'). 
Proof.
  intros.
  unfolds Mem.store.
  unfold store.
  dis_if_else.
  lets HMem_valid_access : v0.
  eapply Mem_valid_access_impl_GMem_valid_access in HMem_valid_access.
  ex_match2.
  inversion H; subst.
  unfold strip.
  simpl.
  f_equal.
  destruct fm; simpl.
  eapply gmem_eq; eauto.
  clear - v0 n.
  unfolds Mem.valid_access.
  destruct v0.
  contradiction n.
  unfold valid_access.
  split; eauto.
  eapply range_perm_cur_max in H.
  eapply Mem_range_perm_GMem_range_perm; eauto.
Qed.

Lemma gm_store_v_load_same :
  forall m b ofs n m',
    store Mint32 m b ofs (Vint n) = Some m' ->
    load Mint32 m' b ofs = Some (Vint n).
Proof.
  intros. 
  lets Hrange_perm : store_succ_read_perm ___; eauto.
  unfolds store.
  unfold load. 
  dis_if_else.
  renames H0 to Heqe.
  ex_match2.
  inversion H; subst. 
  unfold GMem.mem_contents.
  rewrite PMap.gss.
  unfold size_chunk_nat.
  simpl Z.to_nat.
  assert (Pos.to_nat 4 =
          Datatypes.length (inj_bytes (encode_int 4 (Int.unsigned n)))).
  {
    unfold encode_int.
    unfold rev_if_be.
    destruct Archi.big_endian eqn:?; tryfalse.
    simpl; eauto.
  }
  rewrite H0.
  rewrite Mem.getN_setN_same.
  pose proof decode_encode_val_general (Vint n) Mint32 Mint32.
  simpl in H1.
  rewrite H1; eauto.
  contradiction n0.
  clear - v Hrange_perm.
  unfolds valid_access.
  destruct v; eauto.
Qed.

Lemma load_gm_load_spec_m :
  forall sm b v m fl,
    load Mint32 sm b 0 = Some v ->
    embed sm fl m ->
    SpecLang.loadmax m b = Some v.
Proof. 
  memunfolds;intros.
  inv H0.
  ex_match2;auto.
  clear Hx0;contradict n. inversion v0;subst.
  memunfolds. eauto.
Qed.
  
Lemma load_spec_m_load_gm :
  forall sm b v m fl,
    SpecLang.loadmax m b = Some v ->
    embed sm fl m ->
    load Mint32 sm b 0 = Some v.
Proof.
  memunfolds;inversion 2;subst.
  ex_match2;auto.
  memunfolds.
  clear Hx0.
  contradict n. split;auto.
  simpl. 
  apply Zmod_divide;auto;  Lia.lia.
Qed.

Lemma store_v_load_eq_spec_m :
  forall m m' b n,
    SpecLang.storemax m b (Vint n) = Some m' ->
    SpecLang.loadmax m' b = Some (Vint n).
Proof.  
  intros.
  unfolds SpecLang.storemax. 
  unfold SpecLang.loadmax.   
  destruct (Mem.range_perm_dec m b 0 (size_chunk Mint32)
                               Memperm.Max Memperm.Writable) eqn:?; tryfalse.

  lets Ht : Mem_writable_imp_readable ___; eauto.
  destruct (Mem.range_perm_dec _ _ _ _ _ Memperm.Readable) eqn:?; tryfalse. 
  assert(R: Mem.mem_contents m' =  PMap.set b
                              (Mem.setN (encode_val Mint32 (Vint n)) 0
                                 (Mem.mem_contents m) !! b) 
                              (Mem.mem_contents m)).
  inversion H; subst. auto.
  rewrite R. clear H.
 
  pose FMemory.Mem.getN_setN_same.
  rewrite PMap.gsspec.
  destruct peq;try contradiction.
  assert (Datatypes.length (encode_val Mint32 (Vint n)) = size_chunk_nat Mint32).
  simpl.
  unfold inj_bytes. unfold encode_int, size_chunk_nat.
  simpl.
  unfold rev_if_be.
  destruct Archi.big_endian eqn:?; tryfalse.
  eauto.
  rewrite <- H.
  rewrite Mem.getN_setN_same.
  pose proof decode_encode_val_general (Vint n) Mint32 Mint32.
  simpl in *. 
  clear - H0. 
  congruence.

  clear Heqs0.
  contradict n0.
  unfold Mem.range_perm, Mem.perm in *.
  inversion H; subst.
  simpl.
  eauto.
Qed.  

Lemma store_gm_embed_store_fm :
  forall m m' fl fm b ofs v c,
    (forall ofs',
        (ofs <= ofs' < ofs + size_chunk c)%Z ->
        exists p,
          ((GMem.mem_access (strip fm)) !! b ofs' Memperm.Cur =
           Some p /\ Memperm.perm_order p Memperm.Writable)) ->
    store c m b ofs v = Some m' ->
    embed m fl fm ->
    exists fm', Mem.store c fm b ofs v = Some fm' /\ embed m' fl fm'.
Proof.
  intros.
  inversion H1; subst.
  unfolds store.
  dis_if_else.
  clear H2.
  inversion H0; subst; eauto.
  clear H0.
  eexists.
  split.
  unfold Mem.store.
  ex_match2.
  eauto.
  contradiction n.
  clear - H v0.
  unfold Mem.valid_access.
  split.
  unfold Mem.range_perm.
  intros.
  eapply H in H0.
  unfold Mem.perm.
  destruct H0 as [p [Hperm Hperm_order]].
  rewrite Mem_GMem_access_eq.
  unfold Mem.perm_order'.
  rewrite Hperm; eauto.
  unfolds valid_access.
  destruct v0; eauto.
  constructor; eauto.
  unfold strip; simpl.
  eapply gmem_eq; eauto.
Qed.
  
Lemma store_gm_store_spec_m :
  forall sm b n sm' fl fsm,
    store Mint32 sm b 0 (Vint n) = Some sm' ->
    embed sm fl fsm ->
    exists fsm', SpecLang.storemax fsm b (Vint n) = Some fsm' /\ embed sm' fl fsm'.
Proof.
  memunfolds;intros.
  inv H0.
  ex_match2.
  Esimpl;eauto. econstructor;eauto.
  memunfolds;simpl.
  inv H.
  apply gmem_eq;simpl;auto.

  clear Hx0.
  contradict n0. inversion v.
  unfold strip,range_perm in H0.
  simpl in *;auto.
Qed.

Lemma store_gm_embed_store_tsofmem :
  forall m L m' fl fm n,
    store Mint32 m L 0 (Vint n) = Some m' ->
    embed m fl fm ->
    exists tm', tsostorev Mint32 {| tbuffer := nil; fmemory := fm |}
              (Vptr L (Ptrofs.repr 0)) (Vint n) = Some tm'.
Proof.
  intros.
  unfold tsostorev.
  unfold tsostore.
  eauto.
Qed.

Lemma tsostorev_in_bf :
  forall tm bm' t fm fl L n,
    embed (memory tm) fl fm ->
    tsostorev Mint32 {| tbuffer := tso_buffers tm t; fmemory := fm |}
              (Vptr L (Ptrofs.repr 0)) (Vint n) = 
    Some bm' ->
    In (BufferedStore Mint32 L 0 (Vint n))
       (tupdate t (tbuffer bm') (tso_buffers tm) t).
Proof.
  intros.
  unfolds tsostorev.
  unfolds tsostore.
  unfold tupdate.
  destruct (peq t t); tryfalse.
  inversion H0; subst.
  simpl.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0%Z.
  eapply in_or_app; eauto.
  right.
  simpl; eauto.
Qed.

Lemma Mem_alloc_gm_alloc :
  forall fsm fsm' stk',
    Mem.alloc fsm 0 0 = (fsm', stk') ->
    alloc (strip fsm) stk' 0 0 = Some (strip fsm').
Proof.
  intros.
  unfolds Mem.alloc.
  simpls.
  inversion H; subst.
  unfold strip.
  destruct fsm.
  simpl.
  unfold alloc; eauto.
  f_equal.
  unfold Mem.nextblock.
  simpl.
  eapply gmem_eq; simpl; eauto.
Qed.
  
Lemma tso_store_not_imm :
  forall tsofm tsofm' n m L,
    load Mint32 (strip (fmemory tsofm)) L 0 = Some (Vint m) ->
    tsostorev Mint32 tsofm (Vptr L (Ptrofs.repr 0)) (Vint n) = 
    Some tsofm' ->
    load Mint32 (strip (fmemory tsofm')) L 0 = Some (Vint m).
Proof.
  intros.
  unfolds tsostorev.
  unfolds tsostore.
  inversion H0; subst.
  simpl.
  eauto.
Qed.

Lemma load_Mem_alloc_still :
  forall c fsm b ofs v lo hi fsm' stk',
    load c (strip fsm) b ofs = Some v ->
    Mem.alloc fsm lo hi = (fsm', stk') ->
    load c (strip fsm') b ofs = Some v.
Proof.
  intros.
  unfolds load.
  dis_if_else.  
  lets Hrange_perm : v0.
  unfold valid_access in Hrange_perm.
  destruct Hrange_perm as [Hrange_perm Halign].
  eapply range_perm_alloc_still in Hrange_perm; eauto.
  ex_match2.
  erewrite <- GMem_contents_get_block_alloc_eq; eauto.
  lets Ht : v0.
  unfold valid_access in Ht.
  destruct Ht as [Ht Halign1].
  clear - Ht.
  unfolds range_perm.
  specialize (Ht ofs).
  assert ((ofs <= ofs < ofs + size_chunk c)%Z).
  split.
  Lia.lia.
  destruct c; simpls; Lia.lia.
  eapply Ht in H.
  clear - H.
  unfolds Mem.perm_order'.
  destruct ((GMem.mem_access (strip fsm)) !! b ofs Max) eqn:?; tryfalse.
  destruct fsm; simpls.
  lets Ht : Classical_Prop.classic (In b validblocks).
  destruct Ht; eauto.
  eapply invalid_noaccess in H0; eauto.
  rewrite Heqo in H0; tryfalse.
  clear - Hrange_perm n v0.
  contradiction n.
  unfolds valid_access.
  destruct v0; eauto.
Qed.

Lemma tsostorev_append_bf :
  forall m fm fl bfs n tsofm L t,
    embed m fl fm ->
    tsostorev Mint32 {| tbuffer := bfs t; fmemory := fm |}
              (Vptr L (Ptrofs.repr 0)) (Vint n) = Some tsofm ->
    append_t_buffer t {| tso_buffers := bfs; memory := m |}
                    (BufferedStore Mint32 L 0 (Vint n)) =
    {|
      tso_buffers := tupdate t (tbuffer tsofm) bfs;
      memory := strip (fmemory tsofm) |}.
Proof.
  intros.
  unfolds tsostorev.
  unfolds tsostore.
  simpls.
  inversion H0; subst.
  simpls.
  unfold append_t_buffer.
  simpl.
  inversion H; subst.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0%Z.
  eauto.
Qed.

Lemma gm_store_succ_store_again :
  forall sm b ofs n n' sm',
    store Mint32 sm b ofs (Vint n) = Some sm' ->
    exists sm'', store Mint32 sm' b ofs (Vint n') = Some sm''.
Proof.
  memunfolds.
  intros.
  ex_match2.
  Esimpl;eauto.
  clear Hx0.
  contradict n0.
  inversion v;split;auto.
  inv H;auto.
Qed.

Lemma Mem_load_fm_load_tm_eq :
  forall tm fl fm n b t,
    embed (memory tm) fl fm ->
    tso_buffers tm t = nil ->
    load Mint32 (memory tm) b 0 = Some (Vint n) ->
    tsoloadv Mint32 {| tbuffer := nil; fmemory := fm |}
             (Vptr b (Ptrofs.repr 0)) = Some (Vint n).
Proof.
  intros.
  unfold tsoloadv.
  unfold tsoload.
  simpl.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0%Z.
  inv H. congruence.
Qed.

Lemma tsoalloc_bf_nil_succ_sz0 :
  forall fm,
  exists tm stk,
    tsoalloc {| tbuffer := nil; fmemory := fm |} 0 0 (tm, stk).
Proof.
  intros.
  do 2 eexists.
  econstructor; simpl; eauto.
  instantiate (1 := fm).
  econstructor; eauto.
Qed.

Lemma embed_alloc_succ :
  forall sm fl fsm,
    embed sm fl fsm ->
    exists fsm', Mem.alloc fsm 0 0 = (fsm', Mem.nextblock fsm).
Proof.
  intros.
  Transparent Mem.alloc.
  unfold Mem.alloc.
  simpl.
  eauto.
Qed.

Lemma speclang_store_impl_obj_mem :
  forall fsm L fsm' ofs n,
    obj_mem (strip fsm) L ofs ->
    SpecLang.storemax fsm L (Vint n) = Some fsm' ->
    (0 <= ofs < 4)%Z -> obj_mem (strip fsm') L ofs.
Proof.
  intros.
  unfolds SpecLang.storemax.
  destruct (Mem.range_perm_dec fsm L 0 (size_chunk Mint32)
                               Memperm.Max Memperm.Writable) eqn:Heqe;
    tryfalse.
  unfold obj_mem.
  inversion H0; subst.
  simpl.
  clear H0.
  unfolds obj_mem.
  eauto.
Qed.

Lemma GMem_writeable_store_succ :
  forall fm b n,
    Mem.range_perm fm b 0 4 Memperm.Cur Memperm.Writable ->
    exists fm', Mem.store Mint32 fm b 0 (Vint n) = Some fm'.
Proof.
  intros.
  pose Mem.valid_access_store.
  enough(  Mem.valid_access fm Mint32 b 0 Memperm.Writable).
  apply Mem.valid_access_store with(v:=Vint n) in H0.
  destruct H0.
  eauto.
  econstructor; eauto.
  simpl.
  eapply Zmod_divide.
  Lia.lia.
  eauto.
Qed.

Lemma buffer_unchange :
  forall t tm,
    tupdate t (tso_buffers tm t) (tso_buffers tm) = tso_buffers tm.
Proof.
  intros.
  eapply functional_extensionality; eauto.
  intro.
  unfold tupdate.
  destruct (peq x t) eqn : Heqe; eauto.
  subst.
  eauto.
Qed.

Lemma buffer_unchange' :
  forall t bfs,
    tupdate t (bfs t) bfs = bfs.
Proof.
  intros.
  eapply functional_extensionality; eauto.
  intro.
  unfold tupdate.
  destruct (peq x t) eqn : Heqe; eauto.
  subst.
  eauto.
Qed.

Lemma in_tbf_upd_oth_stillin :
  forall t t' bfs bf,
    t <> t' ->
    (tupdate t' bf bfs) t = bfs t.
Proof.
  intros.
  unfold tupdate.
  destruct (peq t t') eqn:?; tryfalse; eauto.
Qed.

Lemma buffer_unchange1 :
  forall t tm bf,
    tso_buffers tm t = bf ->
    tupdate t bf (tso_buffers tm) = tso_buffers tm.
Proof.
  intros.
  subst.
  eapply buffer_unchange; eauto.
Qed.
  
Lemma tm_unchange :
  forall tm fm fl t
    (Hembed : embed (memory tm) fl fm),
    {| tso_buffers := tupdate t (tso_buffers tm t) (tso_buffers tm);
       memory := strip fm |} = tm.
Proof.
  intros.
  inversion Hembed; subst.
  rewrite H0.
  rewrite buffer_unchange.
  destruct tm.
  simpl.
  eauto.
Qed.

Lemma tm_unchange1 :
  forall tm fm fl t bf
    (Hembed : embed (memory tm) fl fm)
    (Ht_bf : tso_buffers tm t = bf),
    {| tso_buffers := tupdate t bf (tso_buffers tm);
       memory := strip fm |} = tm.
Proof.
  intros.
  subst.
  eapply tm_unchange; eauto.
Qed.

Lemma get_buffer_b_app :
  forall l1 l2,
    get_buffer_b (l1 ++ l2) = get_buffer_b l1 ++ get_buffer_b l2.
Proof.
  intro l1.
  induction l1; intros.
  -
    simpls; eauto.
  -
    simpl.
    destruct a;
      rewrite IHl1;
      eauto.
Qed.

Lemma count_occ_app :
  forall A (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) (x : A),
    count_occ eq_dec (l1 ++ l2) x = count_occ eq_dec l1 x + count_occ eq_dec l2 x.
Proof.
  intros A eq_dec l1.
  induction l1; intros.
  -
    simpls; eauto.
  -
    simpls.
    destruct (eq_dec a x) eqn:?; tryfalse.
    rewrite IHl1.
    eauto.
    rewrite IHl1; eauto.
Qed.

Lemma bf_not_in_add_count_one :
  forall t tm L fl tsofm' fm,
    embed (memory tm) fl fm ->
    ~ In L (get_tsom_b t tm) ->
    tsostorev Mint32 {| tbuffer := tso_buffers tm t; fmemory := fm |}
              (Vptr L (Ptrofs.repr 0)) (Vint Int.one) = 
    Some tsofm' ->
    count_occ Pos.eq_dec
              (get_buffer_b (tupdate t (tbuffer tsofm')
                                     (tso_buffers tm) t)) L = 1.
Proof.
  intros.
  destruct tm.
  simpls.
  unfolds tsostore.
  inversion H1; subst.
  simpls.
  unfold tupdate.
  destruct (peq t t); tryfalse.
  rewrite get_buffer_b_app.
  rewrite count_occ_app.
  simpl.
  destruct (Pos.eq_dec L L); tryfalse.
  eapply count_occ_not_In in H0.
  rewrite H0.
  eauto.
Qed.

Lemma GMem_store_alloc_store :
  forall fm fm' stk' c b ofs v M lo hi,
    store c (strip fm) b ofs v = Some M ->
    Mem.alloc fm lo hi = (fm', stk') ->
    exists M', store c (strip fm') b ofs v = Some M'.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  unfold valid_access in v0.
  destruct v0 as [Hrange_perm Halign].
  lets Ht : range_perm_alloc_still ___; eauto.
  ex_match2.
  eauto.
  clear - Ht Halign n.
  contradiction n.
  unfold valid_access; eauto.
Qed.

Lemma SpecLang_store_store_gm :
  forall fsm fsm' b n,
    SpecLang.storemax fsm b (Vint n) = Some fsm' ->
    store Mint32 (strip fsm) b 0 (Vint n) = Some (strip fsm').
Proof.
  memunfolds; intros.
  dis_if_else.
  inversion H; subst; clear H; simpl.
  ex_match2.
  f_equal.
  eapply gmem_eq; eauto.
  contradiction n0.
  clear - r.
  unfold valid_access.
  split; eauto.
  simpl.
  eapply Z.divide_0_r.
Qed.

Lemma tsoalloc_append :
  forall fm stk tm t bm1 fl,
    embed (memory tm) fl fm ->
    tsoalloc {| tbuffer := tso_buffers tm t; fmemory := fm |} 0 0 (bm1, stk) ->
    append_t_buffer t tm (BufferedAlloc stk 0 0) =
    {|
      tso_buffers := tupdate t (tbuffer bm1) (tso_buffers tm);
      memory := strip (fmemory bm1) |}.
Proof.
  intros.
  inversion H0; subst; simpls.
  inversion H; subst.
  unfold append_t_buffer.
  rewrite H2.
  eauto.
Qed.

Ltac solve_m_unchange_objinv tm Hobj_inv :=
  try rewrite buffer_unchange;
  try inversion Hembed; subst;
  destruct tm;
  try
    match goal with
    | H : strip _ = _ |- _ =>
      clear - Hobj_inv H; simpls; subst; eauto
    end.

Ltac solve_m_unchange_objinv1 tm :=
  match goal with
  | H : obj_inv _ _ tm, H1 : embed _ _ _ |- _ =>
    rename H1 into Hembed;
    solve_m_unchange_objinv tm H
  end.

Lemma apply_buffer_item_in_validbloks_stable :
  forall b bi m m',
    In b (GMem.validblocks m) ->
    apply_buffer_item bi m = Some m' ->
    In b (GMem.validblocks m').
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H0; subst; simpl; eauto.
  }
  {
    unfolds free.
    dis_if_else.
    inversion H0; subst; eauto.
  }
  {
    unfolds store.
    dis_if_else.
    inversion H0; subst; eauto.
  }
Qed.
  
Lemma apply_buffer_in_validblocks_stable :
  forall bf m m' b,
    In b (GMem.validblocks m) ->
    apply_buffer bf m = Some m' ->
    In b (GMem.validblocks m').
Proof.
  intro bf.
  induction bf; simpls; intros.
  {
    inversion H0; subst; eauto.
  }
  {
    unfold optbind in H0.
    destruct (apply_buffer_item a m) eqn:?; tryfalse.
    eapply IHbf with (m := g); eauto.
    eapply apply_buffer_item_in_validbloks_stable; eauto.
  }
Qed.

Lemma in_bf_stable1 :
  forall L t b bfs bi,
    bfs t = bi :: b ->
    In L (get_buffer_b (tupdate t b bfs t)) ->
    In L (get_buffer_b (bfs t)).
Proof.
  intros.
  try rewrite H in *.
  unfolds tupdate.
  destruct (peq t t); tryfalse.
  simpl; eauto.
  destruct bi; simpl; eauto.
Qed.

Lemma in_bf_stable2 :
  forall L t t0 b bfs bi,
    bfs t = bi :: b -> t <> t0 ->
    In L (get_buffer_b (tupdate t b bfs t0)) ->
    In L (get_buffer_b (bfs t0)).
Proof.
  intros.
  unfolds tupdate.
  destruct (peq t0 t); tryfalse.
  eauto.
Qed.

Lemma speclang_not_change_perm :
  forall fm fm' L n,
    SpecLang.storemax fm L (Vint n) = Some fm' ->
    Mem.mem_access fm = Mem.mem_access fm'.
Proof.
  intros.
  unfolds SpecLang.storemax.
  dis_if_else.
  inversion H; subst; simpls; eauto.
Qed.

Lemma store_vb_eq :
  forall m c b ofs v m',
    store c m b ofs v = Some m' ->
    GMem.validblocks m = GMem.validblocks m'.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H; subst; eauto.
Qed.

Lemma speclang_store_vb_eq :
  forall m b n m',
    SpecLang.storemax m b (Vint n) = Some m' ->
    Mem.validblocks m = Mem.validblocks m'.
Proof.
  intros.
  unfolds SpecLang.storemax.
  dis_if_else.
  inversion H; subst; eauto.
Qed.

Lemma store_succ_load_succ :
  forall c m b ofs v m',
    store c m b ofs v = Some m' ->
    exists v', load c m b ofs = Some v'.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  renames H0 to Heqe.
  unfold load.
  unfold valid_access in v0.
  destruct v0 as [Hrange_perm Halign].
  clear Heqe.
  eapply GMem_writable_imp_readable in Hrange_perm; eauto.
  inversion H; subst.
  clear H.
  ex_match2.
  eauto.
  contradiction n.
  unfold valid_access.
  split; eauto.
Qed.

Lemma load_alloc_val_same :
  forall c m m' L v ofs lo hi b,
    load c m L ofs = Some v ->
    alloc m b lo hi = Some m' -> b <> L ->
    load c m' L ofs = Some v.
Proof.
  intros.
  unfolds load.
  dis_if_else. 
  renames H2 to Heqe.
  clear Heqe.
  unfold valid_access in v0.
  destruct v0 as [Hrange_perm Halign].
  lets Ht : range_perm_alloc_still' ___; eauto.
  ex_match2.
  clear - H H0 H1.
  unfolds alloc.
  inversion H0; simpls.
  clear - H H1.
  rewrite PMap.gso; eauto.
  contradiction n.
  unfold valid_access; eauto.
Qed. 

Lemma load_alloc_val_same_rev :
  forall c m m' L v ofs lo hi b,
    alloc m b lo hi = Some m' -> b <> L ->
    load c m' L ofs = Some v ->
    load c m L ofs = Some v.
Proof.
  intros.
  unfolds load.
  dis_if_else.
  renames H2 to Heqe.
  clear Heqe.
  unfold valid_access in v0.
  destruct v0 as [Hrange_perm Halign].
  lets Ht : range_perm_alloc_still'_rev ___; eauto.
  ex_match2.
  clear - H H0 H1.
  unfolds alloc.
  inversion H; subst.
  simpls.
  clear - H0 H1.
  rewrite PMap.gso in H1; eauto.
  contradiction n.
  unfold valid_access; eauto.
Qed.

Lemma store_alloc_still :
  forall m m' m'' L ofs lo hi b c v,
    store c m L ofs v = Some m' ->
    alloc m b lo hi = Some m'' -> b <> L ->
    exists m''', store c m'' L ofs v = Some m'''.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  renames H2 to Heqe.
  clear Heqe.
  unfold valid_access in v0.
  destruct v0 as [Hrange_perm Halign].
  lets Ht : range_perm_alloc_still' ___; eauto.
  ex_match2.
  inversion H; subst.
  eauto.
  contradiction n.
  unfold valid_access; eauto.
Qed.

Lemma load_free_other_val_same :
  forall c v m m' L b ofs lo hi,
    load c m L ofs = Some v ->
    free m b lo hi = Some m' -> b <> L ->
    load c m' L ofs = Some v.
Proof.
  intros.
  unfolds load.
  dis_if_else.
  renames H2 to Heqe.
  clear Heqe.
  unfold valid_access in v0.
  destruct v0.
  lets Ht : range_perm_free_still' ___; eauto.
  ex_match2.
  clear - H H0 H1.
  unfolds free.
  dis_if_else.
  inversion H0; subst.
  eauto.
  contradiction n.
  unfold valid_access; eauto.
Qed.

Lemma load_free_other_val_same_rev :
  forall c v m m' L b ofs lo hi,
    load c m' L ofs = Some v ->
    free m b lo hi = Some m' -> b <> L ->
    load c m L ofs = Some v.
Proof.
  intros.
  unfolds load.
  dis_if_else.
  renames H2 to Heqe.
  clear Heqe.
  unfold valid_access in v0.
  destruct v0 as [Hrange_perm Halign].
  lets Ht : range_perm_free_still'_rev ___; eauto.
  ex_match2.
  clear - H H0 H1.
  unfolds free.
  dis_if_else.
  inversion H0; subst.
  clear - H H1.
  simpls; eauto.
  contradiction n.
  unfold valid_access; eauto.
Qed.

Lemma store_free_other_still :
  forall m m' m'' b L ofs c v lo hi,
    store c m L ofs v = Some m' ->
    free m b lo hi = Some m'' -> b <> L ->
    exists m''', store c m'' L ofs v = Some m'''.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  renames H2 to Heqe.
  clear Heqe.
  unfold valid_access in v0.
  destruct v0 as [Hrange Halign].
  lets Ht : range_perm_free_still' ___; eauto.
  ex_match2.
  eauto.
  contradiction n.
  unfold valid_access; eauto.
Qed.

Lemma load_store_other_val_same :
  forall m m' c1 c b L ofs ofs' v v1,
    load c1 m L ofs = Some v1 ->
    store c m b ofs' v = Some m' -> b <> L ->
    load c1 m' L ofs = Some v1.
Proof.
  intros.
  unfolds load.
  dis_if_else.
  renames H2 to Heqe.
  clear Heqe; unfold valid_access in v0.
  destruct v0 as [Hrange Halign].
  lets Ht : range_perm_store_still' ___; eauto.
  ex_match2.
  clear - H H1 H0.
  unfolds store.
  dis_if_else.
  inversion H0; subst; eauto.
  simpls.
  clear - H H1.
  rewrite PMap.gso; eauto.
  contradiction n.
  unfold valid_access.
  split; eauto.
Qed. 

Lemma load_store_other_val_same_rev :
  forall m m' c1 c b L ofs ofs' v v1,
    load c1 m' L ofs = Some v1 ->
    store c m b ofs' v = Some m' -> b <> L ->
    load c1 m L ofs = Some v1.
Proof.
  intros.
  unfolds load.
  dis_if_else.
  renames H2 to Heqe.
  clear Heqe; unfold valid_access in v0.
  destruct v0 as [Hrange Halign].
  lets Ht : range_perm_store_still'_rev ___; eauto.
  ex_match2.
  clear - H H0 H1.
  unfolds store.
  dis_if_else.
  inversion H0; subst.
  clear - H H1.
  simpls.
  rewrite PMap.gso in H; eauto.
  contradiction n.
  unfold valid_access; eauto.
Qed.

Lemma store_store_other_still :
  forall m m' m'' c c1 L b ofs ofs' v v1,
    store c m L ofs v = Some m' ->
    store c1 m b ofs' v1 = Some m'' ->
    exists m''', store c m'' L ofs v = Some m'''.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  renames H1 to Heqe.
  inversion H0; subst; simpls.
  clear H0.
  dis_if_else.
  destruct (valid_access_dec m c L ofs Writable) eqn:?;
           tryfalse.
  inversion H; subst.
  clear H.
  ex_match2; eauto.
  contradiction n.
Qed.

Lemma alloc_store_still :
  forall c v m b ofs m' m'' b0 lo hi,
    store c m b ofs v = Some m' ->
    alloc m b0 lo hi = Some m'' ->
    exists m''', alloc m' b0 lo hi = Some m'''.
Proof.
  intros.
  unfold alloc.
  eauto.
Qed.

Lemma alloc_store_still_rev :
  forall c v m b ofs m' m'' b0 lo hi,
    store c m b ofs v = Some m' ->
    alloc m' b0 lo hi = Some m'' ->
    exists m''', alloc m b0 lo hi = Some m'''.
Proof.
  intros.
  unfold alloc.
  eauto.
Qed.

Lemma free_store_still :
  forall c v m m' m'' b ofs b0 lo hi,
    store c m b ofs v = Some m' ->
    free m b0 lo hi = Some m'' ->
    exists m''', free m' b0 lo hi = Some m'''.
Proof.
  intros.
  unfolds free.
  dis_if_else.
  renames H1 to Heqe.
  inversion H0; subst.
  lets Ht : range_perm_store_still'' ___; eauto.
  ex_match2.
  eauto.
Qed.

Lemma free_store_still_rev :
  forall c v m m' m'' b b0 ofs lo hi,
    store c m b ofs v = Some m' -> b <> b0 ->
    free m' b0 lo hi = Some m'' ->
    exists m''', free m b0 lo hi = Some m'''.
Proof.
  intros.
  unfolds free.
  dis_if_else.
  renames H2 to Heqe.
  inversion H1; subst.
  lets Ht : range_perm_store_still''_rev ___; eauto.
  ex_match2.
  eauto.
Qed.

Lemma store_store_still :
  forall m m' m'' c c1 b b0 ofs ofs0 v v1,
    store c1 m b ofs v1 = Some m' ->
    store c m b0 ofs0 v = Some m'' ->
    exists m''', store c m' b0 ofs0 v = Some m'''.
Proof.
  intros.  
  unfold store in H.
  dis_if_else.
  renames H1 to Heqe.
  inversion H; subst.
  clear H.
  unfolds store.
  destruct (valid_access_dec m c b0 ofs0 Writable)
           eqn:?; tryfalse.
  ex_match2; eauto.
  contradiction n.
Qed.

Lemma store_store_still_rev :
  forall m m' m'' c c1 b b0 ofs ofs0 v v1,
    store c1 m b ofs v1 = Some m' ->
    store c m' b0 ofs0 v = Some m'' ->
    exists m''', store c m b0 ofs0 v = Some m'''.
Proof.
  intros.  
  unfold store in H0.
  dis_if_else.
  renames H1 to Heqe.
  inversion H0; subst.
  clear H0.
  unfolds store. 
  destruct (valid_access_dec m c1 b ofs Writable)
           eqn:?; tryfalse.
  ex_match2; eauto.
  contradiction n.
  inversion H; subst.
  clear H Heqe.
  unfolds valid_access, range_perm; simpls.
  clear - v0.
  destruct v0.
  split; eauto.
Qed.

Lemma store_store_other_val :
  forall c m m' b ofs v v',
    store c m b ofs v = Some m' ->
    exists m'', store c m b ofs v' = Some m''.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  eauto.
Qed.

Lemma store_again_mem_eq :
  forall c m m' b ofs v,
    store c m b ofs v = Some m' ->
    store c m' b ofs v = Some m'.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  renames H0 to Heqe.
  inversion H; subst.
  ex_match2.
  f_equal. 
  eapply gmem_eq; eauto; simpls.
  rewrite PMap.set2.
  rewrite PMap.gss.
  rewrite Mem_setN_twice_same_eq; eauto.
  contradiction n.
Qed.

Lemma store_twice_eq_store_dir :
  forall c b ofs v v' m m' m'',
    store c m b ofs v = Some m' ->
    store c m' b ofs v' = Some m'' ->
    store c m b ofs v' = Some m''.
Proof.
  memunfolds; intros.
  dis_if_else.
  inversion H0; subst; clear H0; eauto.
  dis_if_else.
  inversion H; subst; clear H; eauto.
  simpls.
  f_equal.
  eapply gmem_eq; eauto.
  simpl.
  rewrite PMap.gss.
  rewrite Mem_setN_same_place_eq_setN_once; eauto.
  rewrite PMap.set2.
  eauto.
  clear.
  do 2 rewrite encode_val_length.
  eauto.
Qed.

Lemma store_alloc_eq_alloc_store :
  forall m m1 m2 m1' m2' v c b ofs b1 lo hi,
    store c m b ofs v = Some m1 ->
    alloc m1 b1 lo hi = Some m2 ->
    alloc m b1 lo hi = Some m1' ->
    store c m1' b ofs v = Some m2' ->
    b <> b1 ->
    m2 = m2'.
Proof.
  memunfolds; intros. 
  dis_if_else.
  inversion H2; subst; clear H2; simpls.
  inversion H1; subst; clear H1; simpls.
  inversion H0; subst; clear H0; simpls.
  dis_if_else.
  inversion H; subst; clear H; simpls.
  clear - H3.
  eapply gmem_eq; eauto; simpls.
  rewrite PMap.gso; eauto.
  rewrite PMap_set_twice_not_same_reorder_eq; eauto.
Qed.

Lemma store_free_eq_free_store :
  forall m m1 m1' m2 m2' c b b1 ofs v lo hi,
    store c m b ofs v = Some m1 ->
    free m1 b1 lo hi = Some m2 ->
    free m b1 lo hi = Some m1' ->
    store c m1' b ofs v = Some m2' ->
    b <> b1 ->
    m2 = m2'.
Proof.
  memunfolds; intros.
  dis_if_else.
  inversion H2; subst; clear H2; simpls.
  dis_if_else.
  inversion H1; subst; clear H1; simpls.
  dis_if_else.
  inversion H0; subst; clear H0; simpls.
  dis_if_else.
  inversion H; subst; clear H; simpls.
  clear - H3.
  unfold unchecked_free.
  simpls.
  eapply gmem_eq; eauto.
Qed.

Lemma store_store_eq_store_store :
  forall c c0 m m1 m1' m2 m2' b ofs b' ofs' v v',
    store c m b ofs v = Some m1 ->
    store c0 m1 b' ofs' v' = Some m2 ->
    store c0 m b' ofs' v' = Some m1' ->
    store c m1' b ofs v = Some m2' ->
    b <> b' ->
    m2 = m2'.
Proof.
  memunfolds; intros.
  dis_if_else.
  inversion H2; subst; clear H2; eauto; simpls.
  dis_if_else.
  inversion H1; subst; clear H1; eauto; simpls. 
  dis_if_else.
  inversion H0; subst; clear H0; eauto; simpls.
  dis_if_else.
  inversion H; subst; clear H; eauto; simpls.
  clear - H3.
  eapply gmem_eq; eauto; simpl.
  do 2 (rewrite PMap.gso; eauto).
  rewrite PMap_set_twice_not_same_reorder_eq; eauto.
Qed.
 
Lemma apply_buffer_item_store_still :
  forall m b bi ofs m' m'' c v,
    store c m b ofs v = Some m' ->
    apply_buffer_item bi m = Some m'' ->
    exists m''', apply_buffer_item bi m' = Some m'''.
Proof.
  intros. 
  unfolds apply_buffer_item.
  destruct bi.
  {
    eapply alloc_store_still; eauto.
  }
  {
    eapply free_store_still; eauto.
  }
  {
    eapply store_store_still; eauto.
  }
Qed.

Lemma not_in_apply_buffer_load_eq :
  forall bf c gm gm' b ofs v,
    apply_buffer bf gm = Some gm' -> ~ In b (get_buffer_b bf) ->
    load c gm' b ofs = Some v ->
    load c gm b ofs = Some v.
Proof.
  intro bf.
  induction bf; intros.
  -
    simpls; eauto.
    inversion H; subst; eauto.
  -
    simpl in H.
    unfolds optbind.
    destruct (apply_buffer_item a gm) eqn:?; tryfalse.
    eapply IHbf in H; eauto.
    clear - H0 Heqo H.
    unfolds apply_buffer_item.
    destruct a.
    {
      assert (b <> b0).
      intro.
      subst.
      eapply H0.
      simpl; eauto.
      eapply load_alloc_val_same_rev; eauto.
    }
    {
      assert (b <> b0).
      intro.
      subst.
      eapply H0.
      simpl; eauto.
      eapply load_free_other_val_same_rev; eauto.
    }
    {
      assert (b <> b0).
      intro.
      subst.
      eapply H0.
      simpl; eauto.
      eapply load_store_other_val_same_rev; eauto.
    }

    intro.
    eapply H0.
    simpl; auto.
    destruct a; simpl; eauto.
Qed.

Lemma not_in_apply_buffer_load_eq_rev :
  forall bf c gm gm' b ofs v,
    apply_buffer bf gm = Some gm' -> ~ In b (get_buffer_b bf) ->
    load c gm b ofs = Some v ->
    load c gm' b ofs = Some v.
Proof.
  intro bf.
  induction bf; intros.
  -
    simpls; eauto.
    inversion H; subst; eauto.
  - 
    simpl in H.
    unfolds optbind. 
    destruct (apply_buffer_item a gm) eqn:?; tryfalse. 
    eapply IHbf in H; eauto.
    intro.
    eapply H0.
    simpl; eauto.
    destruct a; simpl; eauto.  
    clear - H0 Heqo H1. 
    unfolds apply_buffer_item.
    destruct a.
    { 
      assert (b <> b0).
      intro.
      subst.
      eapply H0.
      simpl; eauto.
      eapply load_alloc_val_same; eauto.
    }
    {
      assert (b <> b0).
      intro.
      subst.
      eapply H0.
      simpl; eauto.
      eapply load_free_other_val_same; eauto.
    }
    {
      assert (b <> b0).
      intro.
      subst.
      eapply H0.
      simpl; eauto.
      eapply load_store_other_val_same; eauto.
    }
Qed.

Lemma block_not_in_bf_bi_block_neq' :
  forall bfs (t : tid) bi rest L,
    bfs t = bi :: rest ->
    ~ In L (get_buffer_b (bfs t)) ->
    get_bi_block bi <> L.
Proof.
  intros.
  rewrite H in H0.
  intro; subst.
  contradiction H0.
  clear H0.
  destruct bi; simpls; eauto.
Qed.

Lemma alloc_apply_buf_block_neq_reorder_succ :
  forall m b lo hi m1 m2 bi,
    alloc m b lo hi = Some m1 ->
    apply_buffer_item bi m1 = Some m2 ->
    get_bi_block bi <> b ->
    exists m' m'', apply_buffer_item bi m = Some m' /\
          alloc m' b lo hi = Some m''.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H; inversion H0; subst; clear H H0.
    do 2 eexists.
    split; eauto.
  }
  {
    unfolds alloc; unfolds free.
    dis_if_else.
    inversion H; subst; clear H.
    unfolds unchecked_free; simpls; subst; clear H0.
    clear - H1 r.
    do 2 eexists; split; eauto.
    ex_match2; eauto.
    contradiction n.
    unfolds range_perm; simpls.
    intros.
    eapply r in H.
    rewrite PMap.gso in H; eauto.
  }
  {
    unfolds alloc; unfolds store; simpls.
    inversion H; subst; clear H; simpls.
    dis_if_else.
    do 2 eexists; split; eauto.
    ex_match2; eauto.
    contradiction n.
    clear - v0 H1.
    unfolds valid_access; simpls.
    destruct v0.
    split; eauto.
    unfolds range_perm; simpls.
    intros.
    eapply H in H2; eauto.
    rewrite PMap.gso in H2; eauto.
  }
Qed.

Lemma apply_buf_mem_cont_access_eq_stable :
  forall m1 m2 m1' bi,
    apply_buffer_item bi m1 = Some m1' ->
    GMem.mem_contents m1 = GMem.mem_contents m2 ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    exists m2', apply_buffer_item bi m2 = Some m2'.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfold alloc; eauto.
  }
  {
    unfolds free.
    dis_if_else.
    clear H2.
    eexists.
    ex_match2; eauto.
    contradiction n.
    clear - H1 r.
    unfolds range_perm.
    intros.
    eapply r in H.
    rewrite <- H1; eauto.
  }
  {
    unfolds store.
    dis_if_else.
    inversion H; subst; clear H.
    ex_match2; eauto.
    contradiction n.
    clear - v0 H1.
    unfolds valid_access.
    destruct v0.
    split; eauto.
    unfolds range_perm.
    intros.
    eapply H in H2.
    rewrite <- H1; eauto.
  }
Qed.

Lemma apply_same_buf_item_cont_access_eq_preserve :
  forall m1 m2 m1' m2' bi,
    apply_buffer_item bi m1 = Some m1' ->
    apply_buffer_item bi m2 = Some m2' ->
    GMem.mem_contents m1 = GMem.mem_contents m2 ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    GMem.mem_contents m1' = GMem.mem_contents m2' /\
    GMem.mem_access m1' = GMem.mem_access m2'.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H; inversion H0; subst; clear H H0; simpls.
    rewrite H1; rewrite H2; eauto.
  }
  {
    unfolds free.
    dis_if_else.
    dis_if_else.
    clear - H H0 H1 H2.
    inversion H; inversion H0; unfolds unchecked_free; subst; simpls.
    rewrite H1; rewrite H2; eauto.
  }
  {
    unfolds store.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; simpls.
    rewrite H1; rewrite H2; eauto.
  }
Qed.

Lemma unbuffer_safe_cont_access_eq_stable :
  forall bfs m1 m2,
    unbuffer_safe {| tso_buffers := bfs; memory := m1 |} ->
    GMem.mem_contents m1 = GMem.mem_contents m2 ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    unbuffer_safe {| tso_buffers := bfs; memory := m2 |}.
Proof.
  introv Hunbuffer_safe.
  remember {| tso_buffers := bfs; memory := m1 |} as bm.
  generalize dependent bfs.
  generalize dependent m1.
  generalize dependent m2.
  induction Hunbuffer_safe; intros; subst; simpls.
  econstructor; simpl; intros.
  {
    eapply ABIS in H2.
    destruct H2 as [m1' Happly_buffer].
    eapply apply_buf_mem_cont_access_eq_stable; eauto.
  }
  {
    lets Hcons : H2.
    lets Happly_buffer : H3.
    eapply apply_buf_mem_cont_access_eq_stable with (m2 := m1) in Happly_buffer;
      eauto.
    destruct Happly_buffer as [m1' Happly_buffer].
    lets Hmem_cont_access_eq : H0.
    eapply apply_same_buf_item_cont_access_eq_preserve in Hmem_cont_access_eq;
      eauto.
    destruct Hmem_cont_access_eq as [Hmem_cont_eq Hmem_access_eq].
    eapply H in Hcons.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
  }
Qed.

Lemma block_not_in_bf_bi_block_neq :
  forall tm t bi rest L,
    tso_buffers tm t = bi :: rest ->
    ~ In L (get_tsom_b t tm) ->
    get_bi_block bi <> L.
Proof.
  intros.
  unfolds get_tsom_b.
  destruct tm; simpls.
  eapply block_not_in_bf_bi_block_neq'; eauto.
Qed.

Lemma tupdate_same_tid_eq :
  forall t b1 b2 bfs,
    tupdate t b1 (tupdate t b2 bfs) = tupdate t b1 bfs.
Proof.
  intros.
  eapply functional_extensionality; eauto.
  intros.
  unfold tupdate.
  destruct (peq x t) eqn:?; tryfalse; eauto.
Qed.

Lemma tupdate_same_eq :
  forall bfs t b,
    bfs t = b ->
    tupdate t b bfs = bfs.
Proof.
  intros.
  eapply functional_extensionality; eauto.
  intros.
  unfold tupdate.
  destruct (peq x t); tryfalse; subst; eauto.
Qed.

Lemma tupdate_b_get :
  forall t b bfs,
    tupdate t b bfs t = b.
Proof.
  intros.
  unfold tupdate.
  destruct (peq t t); tryfalse; eauto.
Qed.

Lemma tupdate_not_eq_get :
  forall t0 b bfs t,
    t <> t0 ->
    tupdate t0 b bfs t = bfs t.
Proof.
  intros.
  unfold tupdate.
  destruct (peq t t0); tryfalse.
  eauto.
Qed.

Lemma tupdate_tid_neq_twice_rev :
  forall t t0 b0 b bfs,
    t0 <> t ->
    tupdate t0 b0 (tupdate t b bfs) = tupdate t b (tupdate t0 b0 bfs).
Proof.
  intros.
  eapply functional_extensionality; eauto.
  intros.
  unfold tupdate.
  destruct (peq x t0); tryfalse; eauto.
  subst.
  destruct (peq t0 t); tryfalse; eauto.
Qed.

Lemma apply_buf_item_alloc_b_neq_still :
  forall m m' m1 b lo hi bi,
    alloc m b lo hi = Some m' -> get_bi_block bi <> b ->
    apply_buffer_item bi m = Some m1 ->
    exists m2, apply_buffer_item bi m' = Some m2.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H; inversion H1; subst; simpls.
    eexists; eauto.
  }
  {
    unfolds alloc, free, unchecked_free; simpls.
    dis_if_else.
    inversion H; inversion H1; subst; clear H H1; simpls.
    eexists.
    ex_match2; eauto.
    contradiction n.
    clear - r H0.
    unfolds range_perm; simpls.
    intros.
    eapply r in H.
    rewrite PMap.gso; eauto.
  }
  {
    unfolds alloc, store; simpls.
    dis_if_else.
    inversion H; inversion H1; subst; clear H H1; simpls.
    eexists.
    ex_match2; eauto.
    contradiction n.
    clear - v0 H0.
    unfolds valid_access, range_perm; simpls.
    destruct v0.
    split; eauto.
    intros.
    eapply H in H2.
    rewrite PMap.gso; eauto.
  }
Qed.

Lemma in_valid_block_not_in_free_list_cons_still :
  forall bf b b0 m1 m2 m1' m2' fl n n',
    (forall n, b0 <> get_block fl n) ->
    apply_buffer bf m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' ->
    remove_nth n' (GMem.validblocks m2) = GMem.validblocks m1 ->
    get_nth n'(GMem.validblocks m2) = Some b0 -> 
    get_block fl n = b ->
    In b (GMem.validblocks m2') ->
    In b (GMem.validblocks m1').
Proof.
  induction bf; intros.
  {
    simpls.
    inversion H0; subst m1'; inversion H1; subst m2'.
    eapply remove_eq_b_neq_in_still; eauto.
    intro; subst.
    specialize (H n); tryfalse.
  }
  {  
    simpl in H0, H1.
    assert (exists m1'', apply_buffer_item a m1 = Some m1'').
    {
      clear - H0.
      destruct (apply_buffer_item a m1) eqn:?; tryfalse; eauto.
    }
    destruct H6 as [m1'' H6].
    assert (exists m2'', apply_buffer_item a m2 = Some m2'').
    {
      clear - H1.
      destruct (apply_buffer_item a m2) eqn:?; tryfalse; eauto.
    }
    destruct H7 as [m2'' H7].
    rewrite H6 in H0; rewrite H7 in H1; simpl in H0, H1.
    destruct a; simpls.
    {
      unfolds alloc; simpls.
      inversion H6; inversion H7; subst; clear H6 H7; simpl.
      eapply IHbf with (n' := n'.+1); eauto. 
      simpl; rewrite H2; eauto.
    }
    {
      unfolds free; simpls.
      inversion H6; inversion H7; subst; clear H6 H7; simpl.
      dis_if_else.
      dis_if_else.
      inversion H9; inversion H10; subst; clear H9 H10; simpl.
      eapply IHbf with (n' := n'); eauto.
    }
    {
      unfolds store; simpls.
      dis_if_else.
      dis_if_else.      
      inversion H6; inversion H7; subst; clear H6 H7; simpl.
      eapply IHbf with (n' := n'); eauto.
    }
  }
Qed.

Lemma in_valid_block_cons_still :
  forall bf b b0 m1 m2 m1' m2' n',
    apply_buffer bf m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' ->
    remove_nth n' (GMem.validblocks m2) = GMem.validblocks m1 ->
    get_nth n' (GMem.validblocks m2) = Some b0 -> 
    In b (GMem.validblocks m1') ->
    In b (GMem.validblocks m2').
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst.
    eapply after_remove_nth_in_origin; eauto.
  }
  {
    assert (exists m1'', apply_buffer_item a m1 = Some m1'').
    {
      clear - H.
      destruct (apply_buffer_item a m1) eqn:?; tryfalse; eauto.
    }
    destruct H4 as [m1'' H4].
    assert (exists m2'', apply_buffer_item a m2 = Some m2'').
    {
      clear - H0.
      destruct (apply_buffer_item a m2) eqn:?; tryfalse; eauto.
    }
    destruct H5 as [m2'' H5].
    rewrite H4 in H; rewrite H5 in H0; simpls.
    destruct a; simpls.
    {
      unfolds alloc.
      inversion H4; inversion H5; subst; clear H4 H5; simpls. 
      eapply IHbf with (m1' := m1') (n' := n'.+1); simpl; eauto.
      simpl.
      rewrite H1; eauto.
    }
    {
      unfolds free.
      dis_if_else.
      dis_if_else.
      inversion H4; inversion H5; clear H4 H5; simpls.
      unfolds unchecked_free; simpls.
      inversion H9; inversion H10; subst; eauto.
    }
    {
      unfolds store.
      dis_if_else.
      dis_if_else.
      inversion H4; inversion H5; subst; clear H4 H5; simpls.
      eapply IHbf with (m1' := m1') (n' := n'); eauto.
    }
  }
Qed.

Lemma in_valid_block_eq_apply_same_buf_item_still :
  forall bi m1 m2 m1' m2',
    apply_buffer_item bi m1 = Some m1' ->
    apply_buffer_item bi m2 = Some m2' ->
    GMem.validblocks m1 = GMem.validblocks m2 ->
    GMem.validblocks m1' = GMem.validblocks m2'.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc; simpls.
    inversion H; inversion H0; subst; clear H H0; simpls.
    rewrite H1; eauto.
  }
  {
    unfolds free; simpls.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0; simpls.
    eauto.
  }
  {
    unfolds store; simpls.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0; simpls.
    eauto.
  }
Qed.
  
Lemma in_valid_block_eq_apply_same_buf_still :
  forall bf m1 m2 m1' m2',
    apply_buffer bf m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' ->
    GMem.validblocks m1 = GMem.validblocks m2 ->
    GMem.validblocks m1' = GMem.validblocks m2'.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; clear H H0.
    eauto.
  }
  {
    assert (exists m1'', apply_buffer_item a m1 = Some m1'').
    {
      clear - H.
      destruct (apply_buffer_item a m1) eqn:?; tryfalse; eauto.
    }
    destruct H2 as [m1'' H2].
    assert (exists m2'', apply_buffer_item a m2 = Some m2'').
    {
      clear - H0.
      destruct (apply_buffer_item a m2) eqn:?; tryfalse; eauto.
    }
    destruct H3 as [m2'' H3].
    rewrite H2 in H; rewrite H3 in H0.
    simpl in H, H0.
    eapply IHbf; eauto.
    eapply in_valid_block_eq_apply_same_buf_item_still; eauto.
  }
Qed.

Lemma in_valid_block_not_in_free_list_still_rev :
  forall bi m m' m1 m2 fl n b bf,
    (forall n, get_bi_block bi <> get_block fl n) ->
    apply_buffer_item bi m = Some m' ->
    apply_buffer bf m = Some m1 ->
    apply_buffer bf m' = Some m2 ->
    get_block fl n = b ->
    In b (GMem.validblocks m2) ->
    In b (GMem.validblocks m1).
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H0; subst; clear H0. 
    eapply in_valid_block_not_in_free_list_cons_still
    with (m2' := m2); simpls; eauto.
    simpl.
    instantiate (1 := 0); eauto.
    simpl; eauto.
  }
  {
    lets Ht : H1.
    eapply in_valid_block_eq_apply_same_buf_still with (m2' := m2) in Ht; eauto.
    rewrite Ht; eauto.
    unfolds free.
    dis_if_else.
    inversion H0; subst.
    unfold unchecked_free; eauto.
  }
  {
    lets Ht : H1.
    eapply in_valid_block_eq_apply_same_buf_still with (m2' := m2) in Ht; eauto.
    rewrite Ht; eauto.
    unfolds store.
    dis_if_else.
    inversion H0; subst; eauto.
  }
Qed. 

Lemma in_valid_block_update_still :
  forall m m' m1 m2 bf bi b,
    apply_buffer_item bi m = Some m' ->
    apply_buffer bf m = Some m1 ->
    apply_buffer bf m' = Some m2 ->
    In b (GMem.validblocks m1) ->
    In b (GMem.validblocks m2).
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H; subst; eauto; clear H.
    eapply in_valid_block_cons_still with (m1' := m1); eauto.
    simpl.
    instantiate (1 := 0); eauto.
    instantiate (1 := b0); eauto.
  }
  {
    lets Ht : H0.
    eapply in_valid_block_eq_apply_same_buf_still with (m2 := m') in Ht; eauto.
    rewrite <- Ht; eauto.
    unfolds free; simpls.
    dis_if_else.
    inversion H; subst.
    unfold unchecked_free; eauto.
  }
  {
    lets Ht : H0.
    eapply in_valid_block_eq_apply_same_buf_still with (m2 := m') in Ht; eauto.
    rewrite <- Ht; eauto.
    unfolds store; simpls.
    dis_if_else.
    inversion H; subst; eauto.
  }
Qed.

Lemma embed_appply_buffer_update_not_in_freelist_stable :
  forall bf bi m m' m1 m2 fm1 fl,
    (forall n, get_bi_block bi <> get_block fl n) ->
    apply_buffer_item bi m = Some m' ->
    apply_buffer bf m = Some m1 -> embed m1 fl fm1 ->
    apply_buffer bf m' = Some m2 ->
    exists fm2, embed m2 fl fm2 /\ Mem.nextblock fm1 = Mem.nextblock fm2.
Proof.
  intros.
  inversion H2; subst.
  eexists.
  instantiate
    (1 :=
       Mem.mkmem
         (GMem.mem_contents m2)
         (GMem.mem_access m2)
         (GMem.validblocks m2)
         (Mem.freelist fm1)
         (Mem.nextblockid fm1) _ _ _ _ _
    ).
  split; try solve [simpl; eauto].
  econstructor.
  simpl; eauto.
  unfold strip; simpl.
  eapply gmem_eq; eauto.
  Unshelve.
  {
    clear.
    destruct fm1; simpls.
    eapply freelist_wd; eauto.
  }
  {  
    destruct fm1; simpls.
    unfold strip in H1; simpl in H1.
    remember
      {|
         GMem.mem_contents := mem_contents;
         GMem.mem_access := mem_access;
         GMem.validblocks := validblocks;
         GMem.access_max := access_max;
         GMem.invalid_noaccess := invalid_noaccess;
         GMem.contents_default := contents_default |} as m1.
    assert (Hvalidblocks : GMem.validblocks m1 = validblocks).
    subst; eauto.  
    clear - valid_wd H H0 H3 H1 Hvalidblocks.
    intros.
    split; intros.
    { 
      destruct (Classical_Prop.classic (In b validblocks)); eauto.
      eapply valid_wd; eauto.
      contradiction H5.
      eapply in_valid_block_not_in_free_list_still_rev in H4; eauto.
      rewrite Hvalidblocks in H4; tryfalse.
    }
    {
      eapply valid_wd in H2.
      eapply H2 in H4.
      eapply in_valid_block_update_still; eauto.
      rewrite Hvalidblocks; eauto.
    }
  }
  {
    clear.
    destruct m2; simpls; eauto.
  }
  {
    clear.
    destruct m2; simpls; eauto.
  }
  {
    clear.
    destruct m2; simpls; eauto.
  }
Qed.

Lemma unbuffer_safe_apply_buffer :
  forall bfs t m,
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    exists m', apply_buffer (bfs t) m = Some m'.
Proof.
  intros bfs t.
  remember (bfs t) as bf.
  generalize dependent bfs.
  generalize dependent t.
  induction bf; intros.
  {
    simpl; eauto.
  }
  {
    inversion H; subst; simpls.
    lets Happly_buffer : Heqbf.
    symmetry in Happly_buffer.
    eapply ABIS in Happly_buffer; eauto.
    destruct Happly_buffer as [m' Happly_buffer].
    rewrite Happly_buffer; simpl.
    specialize (IHbf t (tupdate t bf bfs)).
    eapply IHbf; eauto.
    rewrite tupdate_b_get; eauto.
  }
Qed.
  
Lemma unbuffer_safe_apply_buffer_stable :
  forall bfs t0 t bi b m m',
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    bfs t0 = bi :: b -> t <> t0 ->
    apply_buffer_item bi m = Some m' ->
    exists m'', apply_buffer (bfs t) m' = Some m''.
Proof.
  intros.
  inversion H; subst; simpls.
  eapply UNBS in H0; eauto.
  clear - H0 H1.
  assert (bfs t = tupdate t0 b bfs t).
  {
    rewrite tupdate_not_eq_get; eauto.
  }
  rewrite H.
  eapply unbuffer_safe_apply_buffer; eauto.
Qed.

Lemma alloc_apply_buf_block_neq_mem_cont_access_eq :
  forall m m1 m2 m1' m2' b lo hi bi,
    alloc m b lo hi = Some m1 ->
    apply_buffer_item bi m1 = Some m2 ->
    apply_buffer_item bi m = Some m1' ->
    alloc m1' b lo hi = Some m2' ->
    get_bi_block bi <> b ->
    GMem.mem_contents m2 = GMem.mem_contents m2' /\
    GMem.mem_access m2 = GMem.mem_access m2'.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H; inversion H0; inversion H1; inversion H2;
      simpls; subst; clear H H0 H1 H2; simpls.
    rewrite PMap_set_twice_not_same_reorder_eq; eauto.
    split; eauto.
    rewrite PMap_set_twice_not_same_reorder_eq; eauto.
  }
  {
    unfolds alloc; unfolds free; unfolds unchecked_free; simpls.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; inversion H1; inversion H2;
      subst; clear H H0 H1 H2; simpls.
    split; eauto.
    rewrite PMap.gso; eauto.
    rewrite PMap_set_twice_not_same_reorder_eq; eauto.
  }
  {
    unfolds alloc; unfolds store; simpls.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; inversion H1; inversion H2;
      subst; clear H H0 H1 H2; simpls.
    split.
    rewrite PMap.gso; eauto.
    rewrite PMap_set_twice_not_same_reorder_eq; eauto.
    eauto.
  }
Qed.

Lemma unbuffer_safe_alloc_preserve :
  forall m m' fl bfs lo hi idx b,
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    alloc m b lo hi = Some m' -> b = get_block fl idx ->
    (forall t, ~ In b (get_buffer_b (bfs t))) ->
    unbuffer_safe {| tso_buffers := bfs; memory := m' |}.
Proof.
  introv Hp.
  remember {| tso_buffers := bfs; memory := m |} as tm.
  generalize dependent m.
  generalize dependent m'.
  generalize dependent fl.
  generalize dependent bfs.
  generalize dependent lo.
  generalize dependent hi.
  generalize dependent idx.
  generalize dependent b.
  lets Ht : Hp.
  induction Hp; intros; subst; simpls. 
  econstructor; intros; simpls.
  {
    lets Hbfs_t : H1.
    eapply ABIS in H1.
    clear - H0 H2 H1 Hbfs_t.
    destruct H1 as [m'' H1].
    assert (get_bi_block bi <> get_block fl idx).
    {
      clear - H2 Hbfs_t.
      specialize (H2 t).
      intro.
      rewrite Hbfs_t in H2.
      contradiction H2.
      destruct bi; simpls; subst; tryfalse; eauto.
    }
    eapply apply_buf_item_alloc_b_neq_still; eauto.
  }
  {
    assert (Hb_neq : get_bi_block bi <> get_block fl idx).
    {
      clear - H2 H1.
      specialize (H2 t).
      intro.
      rewrite H1 in H2.
      contradiction H2.
      destruct bi; simpls; subst; tryfalse; eauto.
    }
    lets Halloc_apply_buf : alloc_apply_buf_block_neq_reorder_succ ___; eauto.
    destruct Halloc_apply_buf as [m1 [m2 [Happly_buf Halloc]]].    
    lets Hcons : H1. 
    eapply H in Hcons.
    2 : instantiate (1 := m1); eauto.
    Focus 2.
    clear - UNBS H1 Happly_buf.
    eapply UNBS; eauto.
    2 : eauto.
    2 : eauto.
    2 : eauto.
    Focus 2.
    clear - H2 H1 .
    intros; intro.
    specialize (H2 t0).
    contradiction H2.
    destruct (peq t t0) eqn:?; subst.
    rewrite tupdate_b_get in H.
    rewrite H1; destruct bi; simpl; eauto.
    rewrite in_tbf_upd_oth_stillin in H; eauto.
    lets Ht1 : H0.
    eapply alloc_apply_buf_block_neq_mem_cont_access_eq
    with (m1 := m') (m2 := m'0) (m1' := m1) in Ht1; eauto. 
    destruct Ht1 as [Hcont_eq Haccess_eq].
    eapply unbuffer_safe_cont_access_eq_stable; eauto.
  }
Qed.

Lemma store_perm_nochange :
   forall m m' L ofs p k c v,
     (GMem.mem_access m) !! L ofs k = Some p ->
     store c m L 0 v = Some m' ->
     (GMem.mem_access m') !! L ofs k = Some p.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H0; subst; eauto.
Qed.

Lemma alloc_nochange_orig_perm :
  forall b L ofs m lo hi m' p k,
    (GMem.mem_access m) !! L ofs k = Some p ->
    alloc m b lo hi = Some m' -> L <> b ->
    (GMem.mem_access m') !! L ofs k = Some p.
Proof.
  intros.
  unfolds alloc.
  inversion H0; subst; simpls; eauto.
  rewrite PMap.gso; eauto.
Qed.

Lemma free_not_eq_nochange_orig_perm :
  forall b L ofs m lo hi m' p k,
    (GMem.mem_access m) !! L ofs k = Some p ->
    free m b lo hi = Some m' -> L <> b ->
    (GMem.mem_access m') !! L ofs k = Some p.
Proof.
  intros.
  unfolds free.
  dis_if_else.
  inversion H0; subst; eauto.
  unfold unchecked_free.
  simpl.
  rewrite PMap.gso; eauto.
Qed.

Lemma store_not_eq_nochange_orig_perm :
  forall c b L ofs ofs1 v m m' k p,
    (GMem.mem_access m) !! L ofs k = Some p ->
    store c m b ofs1 v = Some m' ->
    (GMem.mem_access m') !! L ofs k = Some p.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H0; simpls; subst.
  eauto.
Qed.

Lemma Mem_alloc_nochange_orig_perm :
  forall L ofs m lo hi m' k p stk',
    (GMem.mem_access (strip m)) !! L ofs k = Some p ->
    Mem.alloc m lo hi = (m', stk') ->
    (GMem.mem_access (strip m')) !! L ofs k = Some p.
Proof.
  intros.
  unfolds Mem.alloc.
  inversion H0; subst; simpls.
  clear H0.
  rewrite PMap.gso; eauto.
  destruct m; simpls.
  unfold Mem.nextblock; simpls.
  intro.
  symmetry in H0.
  lets Ht : Classical_Prop.classic (In L validblocks).
  destruct Ht; tryfalse.
  eapply valid_wd in H0.
  eapply H0 in H1.
  Lia.lia.
  eapply invalid_noaccess in H1.
  rewrite H1 in H.
  tryfalse.
Qed.

Lemma Mem_alloc_nochange_orig_perm' :
  forall L ofs m lo hi m' k stk',
    (GMem.mem_access (strip m)) !! L ofs k <> None ->
    Mem.alloc m lo hi = (m', stk') ->
    (GMem.mem_access (strip m')) !! L ofs k <> None.
Proof.
  intros.
  unfolds Mem.alloc.
  inversion H0; subst; simpls.
  clear H0.
  rewrite PMap.gso; eauto.
  destruct m; simpls.
  unfold Mem.nextblock; simpls.
  intro.
  symmetry in H0.
  lets Ht : Classical_Prop.classic (In L validblocks).
  destruct Ht; tryfalse.
  eapply valid_wd in H0.
  eapply H0 in H1.
  Lia.lia.
  eapply invalid_noaccess in H1.
  rewrite H1 in H.
  tryfalse.
Qed.

Lemma mem_perm_max_alloc_cur_none_stable :
  forall fm fm' stk' b ofs lo hi,
    (GMem.mem_access (strip fm)) !! b ofs Max <> None ->
    (GMem.mem_access (strip fm)) !! b ofs Cur = None ->
    Mem.alloc fm lo hi = (fm', stk') ->
    (GMem.mem_access (strip fm')) !! b ofs Cur = None.
Proof.
  intros.
  unfolds Mem.alloc.
  simpls.
  inversion H1; subst.
  simpls.
  clear H1.
  destruct fm; simpls.
  unfold Mem.nextblock.
  simpls.
  rewrite PMap.gso; eauto.
  intro.
  symmetry in H1.
  lets Ht : Classical_Prop.classic (In b validblocks).
  destruct Ht; eauto.
  eapply valid_wd in H1.
  eapply H1 in H2.
  Lia.lia.
Qed.

Lemma obj_mem_alloc_stable :
  forall fm fm' b ofs lo hi stk',
    obj_mem (strip fm) b ofs ->
    Mem.alloc fm lo hi = (fm', stk') ->
    obj_mem (strip fm') b ofs.
Proof.
  intros.
  unfolds obj_mem.
  destruct H.
  split. 
  {
    eapply Mem_alloc_nochange_orig_perm'; eauto.
  }
  {
    eapply mem_perm_max_alloc_cur_none_stable; eauto.
  }
Qed.

Lemma b_in_gmvb_in_apply_bf_m_vb :
  forall bf b m m',
    In b (GMem.validblocks m) ->
    apply_buffer bf m = Some m' ->
    In b (GMem.validblocks m').
Proof.
  induction bf; intros; simpls; eauto.
  inversion H0; subst; eauto.
  assert (exists m'', apply_buffer_item a m = Some m'').
  {
    destruct (apply_buffer_item a m) eqn:?; tryfalse.
    eauto.
  }
  destruct H1 as [m'' H1].
  rewrite H1 in H0.
  simpl in H0.
  eapply apply_buffer_item_in_validbloks_stable in H1; eauto.
Qed.

Lemma b_in_bf_alloc_in_apply_bf_m_vb :
  forall bf b lo hi m m',
    In (BufferedAlloc b lo hi) bf ->
    apply_buffer bf m = Some m' ->
    In b (GMem.validblocks m').
Proof.
  induction bf; intros; simpls; tryfalse.  
  assert (exists m'', apply_buffer_item a m = Some m'').
  {
    destruct (apply_buffer_item a m) eqn:?; tryfalse.
    eauto.
  }
  destruct H; subst.
  {
    destruct H1 as [m'' H1].
    rewrite H1 in H0.
    simpl in H0.
    eapply b_in_gmvb_in_apply_bf_m_vb; eauto.
    simpl in H1.
    clear - H1.
    unfolds alloc; simpls.
    inversion H1; subst; simpls.
    eauto.
  }
  {
    destruct H1 as [m'' H1].
    rewrite H1 in H0; simpls.
    eauto.
  }
Qed.

Lemma in_apply_bf_item_mvb_in_origin_or_item :
  forall a m m' b,
    In b (GMem.validblocks m') ->
    apply_buffer_item a m = Some m' ->
    In b (GMem.validblocks m) \/ (exists lo hi, a = BufferedAlloc b lo hi).
Proof.
  intros.
  destruct a; simpls.
  {
    unfolds alloc.
    inversion H0; subst; simpls; clear H0.
    destruct H; subst; eauto.
  }
  {
    unfolds free.
    dis_if_else.
    inversion H0; subst.
    clear - H.
    unfolds unchecked_free; simpls.
    eauto.
  }
  {
    unfolds store.
    dis_if_else.
    inversion H0; subst; simpls; clear H0.
    eauto.
  }
Qed.
  
Lemma in_apply_bf_mvb_in_orgin_m_or_bf_alloc :
  forall bf b m m',
    In b (GMem.validblocks m') ->
    apply_buffer bf m = Some m' ->
    In b (GMem.validblocks m) \/
    (exists lo hi, In (BufferedAlloc b lo hi) bf).
Proof.
  induction bf; intros; simpls.
  {
    inversion H0; subst; eauto.
  }
  {
    assert (exists m'', apply_buffer_item a m = Some m'').
    {
      destruct (apply_buffer_item a m) eqn:?; tryfalse; eauto.
    }
    destruct H1 as [m'' H1].
    rewrite H1 in H0.
    simpl in H0.
    eapply IHbf in H0; eauto. 
    destruct H0.
    {
      eapply in_apply_bf_item_mvb_in_origin_or_item in H0; eauto.
      destruct H0; eauto.
      right.
      destruct H0 as [lo [hi H0]].
      do 2 eexists; eauto.
    }
    {
      destruct H0 as [lo [hi H0]].
      right.
      exists lo hi; eauto.
    }
  }
Qed.

Lemma rel_tm_gm_vb_impl_alloc_same_block :
  forall tm sm fl t gm' fm',
    rel_tm_gm_vb sm tm fl t ->
    apply_buffer (tso_buffers tm t) (memory tm) = Some gm' ->
    embed gm' fl fm' ->
    exists fsm, embed sm fl fsm /\ Mem.nextblock fm' = Mem.nextblock fsm.
Proof.
  intros.
  unfolds rel_tm_gm_vb; simpls.
  destruct sm; simpls.
  inversion H1; subst; eauto.
  eexists (Mem.mkmem mem_contents mem_access validblocks
                     (Mem.freelist fm') (Mem.nextblockid fm') _ _ _ _ _).
  split.
  econstructor; eauto.
  unfold strip; simpl.
  eapply gmem_eq; eauto.
  unfold Mem.nextblock; eauto.
  Unshelve.
  eapply Mem.freelist_wd; eauto.
  intros.
  lets Heq_vb : H2.
  eapply H in Heq_vb; eauto.
  split; intros.
  { 
    eapply Mem.valid_wd; eauto.
    rewrite mem_strip_gm_vb_eq; eauto.
    eapply Heq_vb; eauto.
  }
  {
    eapply Mem.valid_wd in H3; eauto.
    rewrite mem_strip_gm_vb_eq in H3; eauto.
    eapply Heq_vb; eauto.
  }
Qed.

(** ** Additional Memory Lemmas *)
(** *** Auxiliary Lemmas *)
Lemma inrange_or_not :
  forall A ofs i (v : list A),
    (i <= ofs < i + Z.of_nat (Datatypes.length v))%Z \/
    ((ofs < i)%Z \/ (ofs >= i + Z.of_nat (Datatypes.length v))%Z).
Proof.
  intros.
  Lia.lia.
Qed.

Lemma inrange_or_not1 :
  forall ofs i sz,
    (i <= ofs < i + sz)%Z \/ ((ofs < i)%Z \/ (ofs >= i + sz)%Z).
Proof.
  intros.
  Lia.lia.
Qed.

Lemma unbuffer_safe_apply_buffer' :
  forall tm t,
    unbuffer_safe tm ->
    exists m', apply_buffer (tso_buffers tm t) (memory tm) = Some m'.
Proof.
  intros.
  destruct tm; simpls.
  eapply unbuffer_safe_apply_buffer; eauto.
Qed.

Lemma apply_same_item_perm_eq_stable :
  forall bi m1 m2 m1' m2' b ofs,
    apply_buffer_item bi m1 = Some m1' ->
    apply_buffer_item bi m2 = Some m2' ->
    (GMem.mem_access m1) !! b ofs = (GMem.mem_access m2) !! b ofs ->
    (GMem.mem_access m1') !! b ofs = (GMem.mem_access m2') !! b ofs.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H; inversion H0; subst; clear H H0; simpl.
    destruct (peq b b0); subst; eauto.
    do 2 rewrite PMap.gss; eauto.
    do 2 (rewrite PMap.gso; eauto).
  }
  {
    unfolds free.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0.
    clear - H1.
    unfold unchecked_free; simpls.
    destruct (peq b b0); subst; eauto.
    do 2 rewrite PMap.gss; eauto.
    rewrite H1; eauto.
    do 2 (rewrite PMap.gso; eauto).
  }
  {
    unfolds store.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0; eauto.
  }
Qed.

Lemma apply_buf_item_not_b_contents_stable :
  forall a m1 m1' m2 m2' b ofs,
    apply_buffer_item a m1 = Some m1' ->
    apply_buffer_item a m2 = Some m2' ->
    ZMap.get ofs (GMem.mem_contents m1) !! b =
    ZMap.get ofs (GMem.mem_contents m2) !! b ->
    ZMap.get ofs (GMem.mem_contents m1') !! b =
    ZMap.get ofs (GMem.mem_contents m2') !! b.
Proof.
  intros.
  destruct a; simpls.
  {
    unfolds alloc.
    inversion H; inversion H0; subst; clear H H0; simpls.
    destruct (peq b b0); subst.
    do 2 (rewrite PMap.gss; eauto).
    do 2 (rewrite PMap.gso; eauto).
  }
  {
    unfolds free.
    dis_if_else.
    dis_if_else.
    clear - H H0 H1 H2.
    inversion H; inversion H0; unfolds unchecked_free; subst; simpls.
    eauto.
  }
  {
    unfolds store.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; simpls.
    destruct (peq b b0); subst.
    do 2 (rewrite PMap.gss; eauto).
    clear - H1.
    destruct (inrange_or_not memval ofs z (encode_val m v)).
    {
      eapply setN_geteq2; eauto.
      Lia.lia.
      Lia.lia.
    }
    {
      do 2 (rewrite Mem.setN_outside; eauto).
    }
    do 2 (rewrite PMap.gso; eauto).
  }
Qed.

Lemma apply_same_item_perm_eq_stable' :
  forall bi m1 m2 m1' m2' b ofs k,
    apply_buffer_item bi m1 = Some m1' ->
    apply_buffer_item bi m2 = Some m2' ->
    (GMem.mem_access m1) !! b ofs k = (GMem.mem_access m2) !! b ofs k ->
    (GMem.mem_access m1') !! b ofs k = (GMem.mem_access m2') !! b ofs k.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inversion H; inversion H0; subst; clear H H0; simpl.
    destruct (peq b b0); subst; eauto.
    do 2 rewrite PMap.gss; eauto.
    do 2 (rewrite PMap.gso; eauto).
  }
  {
    unfolds free.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0.
    clear - H1.
    unfold unchecked_free; simpls.
    destruct (peq b b0); subst; eauto.
    do 2 rewrite PMap.gss; eauto.
    rewrite H1; eauto.
    do 2 (rewrite PMap.gso; eauto).
  }
  {
    unfolds store.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0; eauto.
  }
Qed.

Lemma apply_same_bf_perm_eq_stable :
  forall bf m1 m2 m1' m2' b ofs,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' ->
    (GMem.mem_access m1) !! b ofs = (GMem.mem_access m2) !! b ofs ->
    (GMem.mem_access m1') !! b ofs = (GMem.mem_access m2') !! b ofs.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpl in H; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpl in H0; tryfalse.
    eapply IHbf; eauto.
    eapply apply_same_item_perm_eq_stable; eauto.
  }
Qed.

Lemma apply_buf_item_maccess_eq_still :
  forall a m1 m2 m1' m2',
    apply_buffer_item a m1 = Some m1' ->
    apply_buffer_item a m2 = Some m2' ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    GMem.mem_access m1' = GMem.mem_access m2'.
Proof.
  intros.
  destruct a; simpls.
  {
    unfolds alloc.
    inversion H; inversion H0; clear H H0; subst; simpls.
    rewrite H1; eauto.
  }
  {
    unfolds free.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; unfold unchecked_free; simpls.
    rewrite H1; eauto.
  }
  {
    unfolds store.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; eauto.
  }
Qed.
  
Lemma apply_buf_maccess_eq_still :
  forall bf m1 m2 m1' m2',
    apply_buffer bf m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    GMem.mem_access m1' = GMem.mem_access m2'.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf; eauto.
    eapply apply_buf_item_maccess_eq_still; eauto.
  }
Qed.

Lemma gm_cont_eq_apply_same_buf_stable :
  forall bf m1 m2 m1' m2' b ofs,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' ->
    ZMap.get ofs (GMem.mem_contents m1) !! b =
    ZMap.get ofs (GMem.mem_contents m2) !! b ->
    ZMap.get ofs (GMem.mem_contents m1') !! b =
    ZMap.get ofs (GMem.mem_contents m2') !! b.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf; eauto.
    eapply apply_buf_item_not_b_contents_stable; eauto.
  } 
Qed.

Lemma gm_cont_eq_apply_buf_not_alloc_stable :
  forall bf m1 m2 m1' m2' b ofs stk lo hi,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer (bf ++ (BufferedAlloc stk lo hi) :: nil) m2 = Some m2' ->
    stk <> b ->
    ZMap.get ofs (GMem.mem_contents m1) !! b =
    ZMap.get ofs (GMem.mem_contents m2) !! b ->
    ZMap.get ofs (GMem.mem_contents m1') !! b =
    ZMap.get ofs (GMem.mem_contents m2') !! b.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; clear H H0; simpls.
    rewrite PMap.gso; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf; eauto.
    eapply apply_buf_item_not_b_contents_stable; eauto.
  }
Qed.

Lemma not_in_apply_bf_vb_not_in_orign :
  forall bf b m m',
    ~ In b (GMem.validblocks m') ->
    apply_buffer bf m = Some m' ->
    ~ In b (GMem.validblocks m).
Proof.
  intros.
  intro.
  contradiction H.
  eapply apply_buffer_in_validblocks_stable; eauto.
Qed.

Lemma apply_buffer_not_in_vb_not_alloc_in_bf :
  forall bf m m' b,
    apply_buffer bf m = Some m' ->
    ~ In b (GMem.validblocks m') ->
    ~ (exists lo hi, In (BufferedAlloc b lo hi) bf).
Proof.
  induction bf; intros.
  {
    simpls; intro.
    split_and H1; tryfalse.
  }
  {
    simpl in H. 
    destruct (apply_buffer_item a m) eqn:?; simpls; tryfalse.
    lets Happly_buf : H.
    eapply IHbf in H; eauto.
    intro.
    destruct H1 as [lo [hi H1]].
    destruct H1; subst. 
    eapply not_in_apply_bf_vb_not_in_orign in H0; eauto.
    clear - Heqo H0.
    contradiction H0; clear H0.
    simpls.
    unfolds alloc.
    inv Heqo; simpls; eauto.
    contradiction H; eauto.
  }
Qed.

Lemma in_buffer_app_or :
  forall bf1 bf2 b ofs,
    in_buffer (bf1 ++ bf2) b ofs ->
    in_buffer bf1 b ofs \/ in_buffer bf2 b ofs.
Proof.
  intros.
  inversion H; subst.
  eapply in_or_app_rev in H0.
  destruct H0.
  left.
  econstructor; eauto.
  right.
  econstructor; eauto.
Qed.

Lemma in_buffer_app_or_rev :
  forall bf1 bf2 b ofs,
    in_buffer bf1 b ofs \/ in_buffer bf2 b ofs ->
    in_buffer (bf1 ++ bf2) b ofs.
Proof.
  intros.
  destruct H.
  {
    inversion H; subst.
    econstructor; eauto.
    eapply in_or_app; eauto.
  }
  {
    inversion H; subst.
    econstructor; eauto.
    eapply in_or_app; eauto.
  }
Qed.
  
Lemma in_buffer_item_get_bi_blk_b :
  forall bi b ofs,
    in_buffer_item bi b ofs ->
    get_bi_block bi = b.
Proof.
  intros.
  inversion H; inversion H; subst; simpls; eauto.
Qed.

Lemma bi_in_bf_b_in_getbf_block :
  forall bf bi,
    In bi bf -> In (get_bi_block bi) (get_buffer_b bf).
Proof.
  induction bf; intros; simpls; tryfalse.
  destruct H; subst; eauto.
  {
    destruct bi; simpls; eauto.
  }
  {
    destruct a; simpls; eauto.
  }
Qed.

Lemma alloc_in_buf_apply_buf_in_vb :
  forall bf b lo hi m m',
    In (BufferedAlloc b lo hi) bf ->
    apply_buffer bf m = Some m' ->
    In b (GMem.validblocks m').
Proof.
  induction bf; simpls; intros; tryfalse.
  destruct H; subst; eauto.
  {
    destruct (apply_buffer_item (BufferedAlloc b lo hi) m) eqn:?; simpls; tryfalse.
    eapply apply_buffer_in_validblocks_stable; eauto.
    clear - Heqo.
    unfolds alloc; inversion Heqo; subst; simpls; eauto.
  }
  {
    destruct (apply_buffer_item a m) eqn:?; simpls; tryfalse; eauto.
  }
Qed.

Lemma apply_sub_bf_orign_b_impl_stable :
  forall bf1 bf2 m1 m1' m2 m2' b,
    apply_buffer (bf1 ++ bf2) m1 = Some m1' ->
    apply_buffer bf1 m2 = Some m2' ->
    GMem.validblocks m1 = GMem.validblocks m2 ->
    In b (GMem.validblocks m2') ->
    In b (GMem.validblocks m1').
Proof.
  induction bf1; intros; simpls.
  {
    inversion H0; subst.
    rewrite <- H1 in H2.
    eapply apply_buffer_in_validblocks_stable; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf1; eauto.
    eapply in_valid_block_eq_apply_same_buf_item_still; eauto.
  }
Qed.

Lemma apply_buf_alloc_mem_access_b_not_new_access_eq :
  forall bf stk b m1 m1' m2 m2' lo hi ofs,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer (bf ++ BufferedAlloc stk lo hi :: nil) m2 = Some m2' ->
    (GMem.mem_access m1) !! b ofs = (GMem.mem_access m2) !! b ofs ->
    b <> stk ->
    (GMem.mem_access m1') !! b ofs = (GMem.mem_access m2') !! b ofs.
Proof.
  induction bf; simpls; intros.
  {
    inversion H; inversion H0; subst; clear H H0; simpls.
    rewrite H1.
    rewrite PMap.gso; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf; eauto.
    eapply apply_same_item_perm_eq_stable; eauto.
  }
Qed.

Lemma apply_buf_alloc_mem_access_b_not_new_contents_eq :
  forall bf stk b m1 m1' m2 m2' lo hi ofs,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer (bf ++ BufferedAlloc stk lo hi :: nil) m2 = Some m2' ->
    ZMap.get ofs (GMem.mem_contents m1) !! b  =
    ZMap.get ofs (GMem.mem_contents m2) !! b ->
    b <> stk ->
    ZMap.get ofs (GMem.mem_contents m1') !! b =
    ZMap.get ofs (GMem.mem_contents m2') !! b.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; eauto; simpls; clear H H0.
    rewrite H1.
    rewrite PMap.gso; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf; eauto.
    eapply apply_buf_item_not_b_contents_stable; eauto.
  }
Qed.

Lemma alloc_add_new_vb :
  forall m m' b lo hi,
    alloc m b lo hi = Some m' ->
    b :: (GMem.validblocks m) = GMem.validblocks m'.
Proof.
  intros.
  unfolds alloc.
  inversion H; subst; simpls; eauto.
Qed.

Lemma alloc_nb_access :
  forall m m' b lo hi ofs k,
    alloc m b lo hi = Some m' ->
    (GMem.mem_access m') !! b ofs k =
    (if zle lo ofs && zlt ofs hi then Some Freeable else None).
Proof.
  intros.
  unfolds alloc; simpls.
  inversion H; subst; simpls; clear H.
  rewrite PMap.gss; eauto.
Qed.

Lemma alloc_nb_content :
  forall m m' b lo hi ofs,
    alloc m b lo hi = Some m' ->
    ZMap.get ofs (GMem.mem_contents m') !! b = Undef.
Proof.
  intros.
  unfolds alloc; simpls.
  inversion H; subst; simpls; clear H.
  rewrite PMap.gss; eauto.
  rewrite ZMap.gi; eauto.
Qed.

Lemma apply_buf_tail_alloc_nb_access :
  forall bf m m' b lo hi ofs k,
    apply_buffer (bf ++ (BufferedAlloc b lo hi) :: nil) m = Some m' ->
    (GMem.mem_access m') !! b ofs k =
    (if zle lo ofs && zlt ofs hi then Some Freeable else None).
Proof.
  induction bf; intros; simpls; eauto.
  {
    inversion H; subst; simpls; clear H.
    rewrite PMap.gss; eauto.
  }
  {
    destruct (apply_buffer_item a m); simpls; tryfalse.
    eapply IHbf; eauto.
  }
Qed.

Lemma apply_buf_tail_alloc_nb_contents :
  forall bf m m' b lo hi ofs,
    apply_buffer (bf ++ (BufferedAlloc b lo hi) :: nil) m = Some m' ->
    ZMap.get ofs (GMem.mem_contents m') !! b = Undef.
Proof.
  induction bf; intros; simpls; eauto.
  {
    inversion H; subst; simpls; clear H.
    rewrite PMap.gss; eauto.
    rewrite ZMap.gi; eauto.
  }
  {
    destruct (apply_buffer_item a m); simpls; tryfalse.
    eapply IHbf; eauto.
  }
Qed.

Lemma apply_buf_not_b_access_stable :
  forall bf stk lo hi m1 m1' m2 m2' b ofs k,
    apply_buffer (bf ++ (BufferedAlloc stk lo hi) :: nil) m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' -> b <> stk ->
    (GMem.mem_access m1) !! b ofs k = (GMem.mem_access m2) !! b ofs k ->
    (GMem.mem_access m1') !! b ofs k = (GMem.mem_access m2') !! b ofs k.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; simpls; clear H H0.
    rewrite PMap.gso; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; tryfalse; simpls.
    destruct (apply_buffer_item a m2) eqn:?; tryfalse; simpls.
    eapply IHbf; eauto.
    eapply apply_same_item_perm_eq_stable'; eauto.
  }
Qed.

Lemma access_eq_apply_same_buf_item_still :
  forall bi m1 m2 m1' m2',
    apply_buffer_item bi m1 = Some m1' ->
    apply_buffer_item bi m2 = Some m2' ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    GMem.mem_access m1' = GMem.mem_access m2'.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc; simpls.
    inversion H; inversion H0; subst; clear H H0; simpls.
    rewrite H1; eauto.
  }
  {
    unfolds free; simpls.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0; simpls.
    rewrite H1; eauto.
  }
  {
    unfolds store; simpls.
    dis_if_else.
    dis_if_else.
    inversion H; inversion H0; subst; clear H H0; simpls.
    eauto.
  }
Qed.
  
Lemma apply_buf_not_b_contents_stable :
  forall bf stk lo hi m1 m1' m2 m2' b ofs,
    apply_buffer (bf ++ (BufferedAlloc stk lo hi) :: nil) m1 = Some m1' ->
    apply_buffer bf m2 = Some m2' -> b <> stk ->
    ZMap.get ofs (GMem.mem_contents m1) !! b =
    ZMap.get ofs (GMem.mem_contents m2) !! b ->
    ZMap.get ofs (GMem.mem_contents m1') !! b =
    ZMap.get ofs (GMem.mem_contents m2') !! b.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; inversion H0; subst; simpls; clear H H0.
    rewrite PMap.gso; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; tryfalse; simpls.
    destruct (apply_buffer_item a m2) eqn:?; tryfalse; simpls.
    eapply IHbf; eauto.
    eapply apply_buf_item_not_b_contents_stable; eauto.
  }
Qed.

Lemma alloc_not_nb_access_stable :
  forall m m' stk lo hi b k ofs,
    alloc m stk lo hi = Some m' ->
    b <> stk ->
    (GMem.mem_access m) !! b ofs k = (GMem.mem_access m') !! b ofs k.
Proof.
  intros.
  unfolds alloc.
  inversion H; subst; clear H; simpls.
  rewrite PMap.gso; eauto.
Qed.

Lemma apply_buf_prefix_in_apply_more_still :
  forall bf1 bf2 m1 m2 m1' m2' b,
    apply_buffer bf1 m1 = Some m1' ->
    apply_buffer (bf1 ++ bf2) m2 = Some m2' ->
    GMem.validblocks m1 = GMem.validblocks m2 ->
    In b (GMem.validblocks m1') ->
    In b (GMem.validblocks m2').
Proof.
  induction bf1; simpls; intros.
  {
    inversion H; subst.
    rewrite H1 in H2.
    eapply apply_buffer_in_validblocks_stable; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf1; eauto.
    clear - H1 Heqo Heqo0 H2.
    eapply in_valid_block_eq_apply_same_buf_item_still in H1; eauto.
  }
Qed.

Lemma apply_buf_orign_vb_eq_add_store_item_vb_eq_still :
  forall bf m1 m2 m1' m2' c b ofs v,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer (bf ++ BufferedStore c b ofs v :: nil) m2 = Some m2' ->
    GMem.validblocks m1 = GMem.validblocks m2 ->
    GMem.validblocks m1' = GMem.validblocks m2'.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; subst.
    destruct (store c m2 b ofs v) eqn:?; simpls; tryfalse.
    inversion H0; subst.
    rewrite H1.
    clear - Heqo.
    unfolds store.
    dis_if_else.
    inversion Heqo; subst; simpls; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; tryfalse; simpls.
    destruct (apply_buffer_item a m2) eqn:?; tryfalse; simpls.
    eapply IHbf; eauto.
    clear - H1 Heqo Heqo0.
    eapply in_valid_block_eq_apply_same_buf_item_still; eauto.
  }
Qed.

Lemma apply_buf_orign_access_eq_add_store_item_access_eq_still :
  forall bf m1 m2 m1' m2' c b ofs v,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer (bf ++ BufferedStore c b ofs v :: nil) m2 = Some m2' ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    GMem.mem_access m1' = GMem.mem_access m2'.
Proof.
  induction bf; intros; simpls.
  {
    inversion H; subst.
    destruct (store c m2 b ofs v) eqn:?; simpls; tryfalse.
    inversion H0; subst.
    rewrite H1.
    clear - Heqo.
    unfolds store.
    dis_if_else.
    inversion Heqo; subst; simpls; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; tryfalse; simpls.
    destruct (apply_buffer_item a m2) eqn:?; tryfalse; simpls.
    eapply IHbf; eauto.
    clear - H1 Heqo Heqo0.
    eapply access_eq_apply_same_buf_item_still; eauto.
  }
Qed.

Lemma apply_bf_tail_store_not_same_block_cont_stable :
  forall bf m1 m2 m1' m2' b ofs b0 ofs0 v c,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer (bf ++ BufferedStore c b ofs v :: nil) m2 = Some m2' ->
    ZMap.get ofs0 (GMem.mem_contents m1) !! b0 =
    ZMap.get ofs0 (GMem.mem_contents m2) !! b0 ->
    b0 <> b ->
    ZMap.get ofs0 (GMem.mem_contents m1') !! b0 =
    ZMap.get ofs0 (GMem.mem_contents m2') !! b0.
Proof.
  induction bf; intros; simpls.
  {
    destruct (store c m2 b ofs v) eqn:?; simpls; tryfalse.
    inversion H; inversion H0; subst.
    rewrite H1.
    clear - Heqo H2.
    unfolds store.
    dis_if_else.
    inversion Heqo; subst; clear Heqo; simpls.
    rewrite PMap.gso; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf; eauto.
    clear - Heqo Heqo0 H1.
    eapply apply_buf_item_not_b_contents_stable; eauto.
  }
Qed.

Lemma apply_bf_tail_store_not_same_range_cont_stable :
  forall bf m1 m2 m1' m2' b ofs ofs0 n,
    apply_buffer bf m1 = Some m1' ->
    apply_buffer (bf ++ BufferedStore Mint32 b ofs (Vint n) :: nil) m2 = Some m2' ->
    ZMap.get ofs0 (GMem.mem_contents m1) !! b =
    ZMap.get ofs0 (GMem.mem_contents m2) !! b ->
    ((ofs0 < ofs)%Z \/ (ofs0 >= ofs + size_chunk Mint32)%Z) ->
    ZMap.get ofs0 (GMem.mem_contents m1') !! b =
    ZMap.get ofs0 (GMem.mem_contents m2') !! b.
Proof.
  induction bf; intros; simpls.
  {
    destruct (store Mint32 m2 b ofs (Vint n)) eqn:?; simpls; tryfalse.
    inversion H; inversion H0; subst.
    rewrite H1.
    clear - Heqo H2.
    unfolds store.
    dis_if_else.
    inversion Heqo; subst; clear Heqo; simpls.
    rewrite PMap.gss; eauto.
    rewrite Mem.setN_outside; eauto.
  }
  {
    destruct (apply_buffer_item a m1) eqn:?; simpls; tryfalse.
    destruct (apply_buffer_item a m2) eqn:?; simpls; tryfalse.
    eapply IHbf; eauto.
    clear - Heqo Heqo0 H1.
    eapply apply_buf_item_not_b_contents_stable; eauto.
  }
Qed.

Lemma loc_stable_valid_access_stable :
  forall m m' b c p z,
    (forall ofs, (z <= ofs < z + size_chunk c)%Z -> loc_stable m m' b ofs) ->
    valid_access m c b z p ->
    valid_access m' c b z p.
Proof.
  intros.
  unfolds valid_access.
  destruct H0.
  split; eauto.
  unfolds range_perm; intros.
  lets Ht : H2.
  eapply H0 in H2.
  simpls.
  eapply H in Ht.
  unfolds loc_stable; clear H.
  split_and Ht.
  rewrite <- H3; eauto.
Qed.

Lemma not_obj_mem_upd_obj_mem_loc_stable :
  forall M b ofs L z c,
    (forall ofs : Z, (z <= ofs < z + size_chunk c)%Z -> obj_mem M L ofs) ->
    ~ obj_mem M b ofs ->
    b <> L \/
    (b = L /\ ((ofs < z)%Z \/
              (ofs >= z + size_chunk c)%Z)).
Proof.
  intros.
  destruct (peq b L); subst; eauto.
  {
    right.
    split; eauto. 
    lets Ht : inrange_or_not1 ofs z (size_chunk c).
    destruct Ht; eauto.
    eapply H in H1; tryfalse.
  }
Qed.

Lemma loc_stable_cont_stable :
  forall m m' b ofs,
    loc_stable m m' b ofs ->
    ZMap.get ofs (GMem.mem_contents m) !! b =
    ZMap.get ofs (GMem.mem_contents m') !! b.
Proof.
  intros.
  unfolds loc_stable.
  split_and H.
  rewrite H0; eauto.
Qed.

Lemma loc_stable_load_same :
  forall m m' b v c z,
    (forall ofs, (z <= ofs < z + size_chunk c)%Z -> loc_stable m m' b ofs) ->
    load c m b z = Some v ->
    load c m' b z = Some v.
Proof.
  intros.
  unfolds load.
  dis_if_else.
  inversion H0; subst; clear H0.
  lets Ht1 : v0.
  eapply loc_stable_valid_access_stable in Ht1; eauto.
  ex_match2.
  erewrite get_eq_getN_eq; eauto.
  intros.
  rewrite <- size_chunk_conv in H0.
  eapply H in H0.
  symmetry.
  eapply loc_stable_cont_stable; eauto.
Qed.  

Lemma store_succ_invb :
  forall c m m' b ofs v,
    store c m b ofs v = Some m' ->
    In b (GMem.validblocks m).
Proof.
  intros.
  unfolds store.
  dis_if_else.
  clear H H0.
  unfolds valid_access.
  destruct v0.
  unfolds range_perm.
  assert ((ofs <= ofs < ofs + size_chunk c)%Z).
  {
    destruct c; simpls; Lia.lia.
  }
  destruct (Classical_Prop.classic (In b (GMem.validblocks m))); eauto.
  eapply H in H1.
  eapply GMem.invalid_noaccess in H2; eauto.
  rewrite H2 in H1.
  simpls; tryfalse.
Qed.

Lemma loc_stable_store_still :
  forall m m' m'' b z v c,
    store c m b z v = Some m'' ->
    (forall ofs, (z <= ofs < z + size_chunk c)%Z -> loc_stable m m' b ofs) ->
    exists m0, store c m' b z v = Some m0.
Proof.
  intros.
  unfolds store.
  ex_match2.
  inversion H; subst.
  eauto.
  clear - v0 n H0.
  unfolds valid_access.
  destruct v0.
  contradiction n.
  clear n.
  split; eauto.
  unfolds range_perm.
  intros. 
  lets Hrange_perm : H2.
  eapply H in H2.
  eapply H0 in Hrange_perm.
  clear - H2 Hrange_perm.
  unfolds loc_stable.
  split_and Hrange_perm.
  rewrite <- H0; eauto.
Qed.

Lemma in_bf_after_unbuffer_in_orign_bf :
  forall t' tm tm' b t,
    In b (get_tsom_b t tm') ->
    unbuffer tm t' = Some tm' ->
    In b (get_tsom_b t tm).
Proof. 
  intros t' tm.
  remember ((tso_buffers tm) t') as bf.
  generalize dependent t'.
  generalize dependent tm.
  destruct bf; simpls; intros; eauto.
  {
    unfolds get_tsom_b; simpls.
    destruct tm, tm'; simpls.
    unfolds unbuffer; simpls.
    rewrite <- Heqbf in H0.
    tryfalse.
  }
  {
    destruct (peq t t'); subst.
    {
      destruct tm, tm'; simpls.
      unfolds unbuffer; simpls.
      rewrite <- Heqbf in H0; simpls.
      ex_match2.
      inversion H0; subst.
      rewrite tupdate_b_get in H; eauto.
      rewrite <- Heqbf.
      simpl; destruct b; simpl; eauto.
    }
    {
      destruct tm, tm'; simpls.
      unfolds unbuffer; simpls.
      rewrite <- Heqbf in H0.
      ex_match2.
      inversion H0; subst.
      rewrite in_tbf_upd_oth_stillin in H; eauto.
    }
  }
Qed.

Lemma wfbis_in_loc_in_buffer :
  forall bf b,
    In b (get_buffer_b bf) -> wfbis bf ->
    exists ofs, in_buffer bf b ofs.
Proof.
  induction bf; intros; simpls; tryfalse.
  destruct a; simpls.
  {
    destruct H; subst.
    exists z.
    econstructor; eauto.
    simpl; eauto.
    unfolds wfbis.
    assert (In (BufferedAlloc b z z0) (BufferedAlloc b z z0 :: bf));
      simpl; eauto.
    eapply H0 in H; simpls.
    econstructor; eauto.
    eapply IHbf in H; eauto.
    destruct H as [ofs H].
    exists ofs.
    inversion H; subst.
    econstructor; eauto.
    simpl; eauto.
    clear - H0.
    unfolds wfbis; intros.
    eapply H0; eauto.
    simpl; eauto.
  }
  {
    destruct H; subst; eauto.
    exists z.
    econstructor; eauto.
    simpl; eauto.
    unfolds wfbis.
    assert (In (BufferedFree b z z0) (BufferedFree b z z0 :: bf)); simpl; eauto.
    eapply H0 in H.
    simpls.
    econstructor; eauto.
    Lia.lia.
    eapply IHbf in H; eauto.
    destruct H as [ofs H].
    exists ofs.
    inversion H; subst.
    econstructor; simpls; eauto.
    unfolds wfbis.
    intros.
    eapply H0; simpl; eauto.
  }
  {
    destruct H; subst.
    exists z.
    econstructor; simpl; eauto.
    econstructor; eauto.
    destruct m; simpls; Lia.lia.
    eapply IHbf in H; eauto.
    destruct H as [ofs H].
    exists ofs.
    inversion H; subst.
    econstructor; eauto.
    simpl; eauto.
    unfolds wfbis.
    intros.
    eapply H0; eauto.
    simpl; eauto.
  }
Qed.

Lemma obj_mem_other_ofs_not_touch :
  forall bis L M M',
    GMem.forward M M' ->
    In L (get_buffer_b bis) ->
    (forall ofs, (0 <= ofs < 4)%Z -> obj_mem M L ofs) ->
    (forall ofs k p,
        (ofs >= 4)%Z \/ (ofs < 0)%Z -> ~ GMem.perm M L ofs k p) ->
    (forall b ofs,
        in_buffer bis b ofs ->
        ~ obj_mem M b ofs /\ (exists k p, GMem.perm M' b ofs k p)) ->
    wfbis bis -> In L (GMem.validblocks M) ->
    In L (get_buffer_b bis) -> False.
Proof.
  introv Hgm_forward.
  intros.
  eapply wfbis_in_loc_in_buffer in H5; eauto.
  destruct H5 as [ofs H5].
  eapply H2 in H5; eauto.
  destruct H5.
  pose proof inrange_or_not1.
  specialize (H7 ofs 0%Z 4%Z); simpls.
  destruct H7.
  {
    eapply H0 in H7; tryfalse.
  }
  {
    assert ((ofs >= 4)%Z \/ (ofs < 0)%Z); try solve [destruct H7; eauto].
    destruct H6 as [k [p H6]].
    eapply H1 with (k := k) (p := p) in H8; eauto.
    inversion Hgm_forward; subst.
    clear - H8 H4 alloc_forward H6.
    unfolds GMem.perm.
    eapply alloc_forward in H4; eauto; tryfalse.
  }
Qed.

Lemma store_diff_block_loc_stable :
  forall c m m' v b z ofs L,
    store c m L z v = Some m' ->
    b <> L ->
    loc_stable m m' b ofs.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H; subst; clear H; simpls.
  unfold loc_stable; simpls.
  rewrite PMap.gso; eauto.
Qed.

Lemma store_ofs_not_inrange_loc_stable :
  forall m m' b ofs c z v,
    store c m b z v = Some m' ->
    ((ofs < z)%Z \/ (ofs >= z + size_chunk c)%Z) ->
    loc_stable m m' b ofs.
Proof.
  intros.
  unfolds store.
  dis_if_else.
  inversion H; subst; clear H; simpls.
  unfolds loc_stable; simpls.
  split; eauto.
  rewrite PMap.gss; eauto.
  rewrite Mem.setN_outside; eauto.
  rewrite encode_val_length.
  rewrite <- size_chunk_conv; eauto.
Qed.

Lemma inrange_loc_belongsto :
  forall b ofs ofs0 sz,
    (ofs <= ofs0 < ofs + sz)%Z ->
    Locs.belongsto (inrange b ofs sz) b ofs0.
Proof.
  intros.
  unfolds Locs.belongsto, inrange.
  ex_match2.
  destruct (zle ofs ofs0); destruct (zlt ofs0 (ofs + sz));
    simpls; tryfalse; try Lia.lia.
Qed.

Lemma inrange_loc_belongsto_rev :
  forall b ofs ofs0 sz,
    Locs.belongsto (inrange b ofs sz) b ofs0 ->
    (ofs <= ofs0 < ofs + sz)%Z.
Proof.
  intros.
  unfolds Locs.belongsto, inrange.
  ex_match2.
  destruct (zle ofs ofs0); destruct (zlt ofs0 (ofs + sz));
    simpls; tryfalse; try Lia.lia.
Qed.

Lemma not_in_buffer_apply_buf_item_loc_eq :
  forall bi m m' b ofs sz,
    apply_buffer_item bi m = Some m' ->
    ~ (exists ofs, in_buffer_item bi b ofs) ->
    gmem_loc_eq (inrange b ofs sz) m m'.
Proof.
  intros.
  unfold gmem_loc_eq. 
  unfold gmem_loc_content_eq, gmem_loc_perm_eq.
  destruct bi; simpls.
  (** alloc *)
  {
    unfolds alloc; inv H; simpls.
    assert (b <> b0).
    {
      intro; subst.
      contradiction H0; clear H0.
      exists z.
      econstructor; eauto.
    }
    split; intros.
    assert (b1 = b).
    {
      unfolds Locs.belongsto, inrange.
      ex_match2.
    }
    subst; rewrite PMap.gso; eauto.
    assert (b1 = b).
    {
      unfolds Locs.belongsto, inrange.
      ex_match2.
    }
    subst; rewrite PMap.gso; eauto.
  }
  (** free *)
  { 
    unfolds free, unchecked_free; simpls.
    ex_match2.
    inv H; simpls.
    split; intros; eauto.
    assert (b = b1).
    {
      unfolds Locs.belongsto, inrange; simpls; ex_match2.
    }
    subst.
    destruct (peq b0 b1); subst.
    {
      rewrite PMap.gss; eauto.
      ex_match2.
      assert ((z <= ofs0 < z0)%Z).
      {
        clear - Hx0.
        destruct (zle z ofs0); destruct (zlt ofs0 z0); simpls; eauto; tryfalse.
      }
      contradiction H0.
      exists ofs0. econstructor; eauto.
    }
    {
      rewrite PMap.gso; eauto.
    }
  }
  (** store *)
  {
    unfolds store.
    ex_match2.
    inv H; simpls.
    split; intros; eauto.
    assert (b = b1).
    {
      unfolds Locs.belongsto, inrange.
      ex_match2; eauto.
    }
    destruct (peq b b0); subst.
    {
      rewrite PMap.gss; eauto.
      rewrite Mem.setN_outside; eauto.
      pose proof inrange_or_not1.
      rewrite encode_val_length.
      rewrite <- size_chunk_conv.
      specialize (H1 ofs0 z (size_chunk m0)).
      destruct H1; eauto.
      contradiction H0; clear - H1.
      exists ofs0. econstructor; eauto.
    }
    {
      rewrite PMap.gso; eauto.
    }
  }
Qed.
  
Lemma gmem_load_loc_eq_load_same_val :
  forall b ofs c m m' v,
    gmem_loc_eq (inrange b ofs (size_chunk c)) m m' ->
    load c m b ofs = Some v ->
    load c m' b ofs = Some v.
Proof.
  intros.
  unfolds gmem_loc_eq.
  destruct H.
  unfolds load.
  ex_match2.
  erewrite get_eq_getN_eq; eauto.
  intros.
  symmetry.
  unfolds gmem_loc_content_eq.
  eapply inrange_loc_belongsto with (b := b) in H2.
  rewrite <- size_chunk_conv in H2.
  eapply H; eauto.
  contradiction n.
  clear - H1 v0.
  unfolds valid_access, range_perm.
  destruct v0; split; eauto.
  intros.
  lets Hrange : H2.
  eapply H in H2.
  unfolds gmem_loc_perm_eq.
  eapply inrange_loc_belongsto with (b := b) in Hrange.
  eapply H1 with (k := Max) in Hrange.
  clear - H2 Hrange.
  unfolds Mem.perm_order'.
  rewrite <- Hrange.
  eauto.
Qed.

Lemma not_in_buf_item_apply_load_stable :
  forall bi m m' c b ofs v,
    load c m b ofs = Some v ->
    apply_buffer_item bi m = Some m' ->
    ~ (exists ofs, in_buffer_item bi b ofs) ->
    load c m' b ofs = Some v.
Proof.
  intros.
  eapply gmem_load_loc_eq_load_same_val; eauto.
  eapply not_in_buffer_apply_buf_item_loc_eq; eauto.
Qed.
  
Lemma load_orignal_loc_not_in_bf_apply_buf_same_val :
  forall bf m m' c b ofs v,
    load c m b ofs = Some v ->
    (forall ofs, ~ in_buffer bf b ofs) ->
    apply_buffer bf m = Some m' ->
    load c m' b ofs = Some v.
Proof.
  induction bf; intros; simpls.
  inv H1; eauto.
  destruct (apply_buffer_item a m) eqn:?; simpls; tryfalse.
  eapply IHbf with (m := g); eauto.
  {
    eapply not_in_buf_item_apply_load_stable; eauto.
    clear - H0.
    intro.
    destruct H as [ofs H].
    specialize (H0 ofs).
    contradiction H0; econstructor; simpl; eauto.
  }
  {
    clear - H0.
    intros; intro.
    specialize (H0 ofs).
    contradiction H0.
    inv H.
    econstructor; eauto.
    simpl; eauto.
  }
Qed.

Lemma gmem_load_loc_perm_eq_store_still :
  forall b ofs c m m' m1 v,
    gmem_loc_perm_eq (inrange b ofs (size_chunk c)) m m' ->
    store c m b ofs v = Some m1 ->
    exists m2, store c m' b ofs v = Some m2.
Proof.
  intros.
  unfolds gmem_loc_perm_eq.
  unfolds store.
  ex_match2.
  inv H0; simpls; eauto.
  inv H0; simpls.
  contradiction n; clear - H v0.
  unfolds valid_access, range_perm; simpls.
  destruct v0; split; eauto.
  intros.
  lets Hrange : H2.
  eapply H0 in H2.
  eapply inrange_loc_belongsto in Hrange.
  eapply H in Hrange.
  rewrite <- Hrange; eauto.
Qed.

Lemma store_outrange_stable :
  forall b ofs c m m' v,
    store c m b ofs v = Some m' ->
    gmem_loc_eq (outrange b ofs (size_chunk c)) m m'.
Proof.
  intros.
  unfolds store.
  ex_match2; inv H.
  unfold gmem_loc_eq, gmem_loc_content_eq, gmem_loc_perm_eq; simpls.
  split; intros; eauto.
  {
    unfolds Locs.belongsto, outrange.
    ex_match2; subst.
    rewrite PMap.gss; eauto.
    rewrite Mem.setN_outside; eauto.
    destruct (zle ofs ofs0); destruct (zlt ofs0 (ofs + size_chunk c));
      simpls; tryfalse; try Lia.lia.
    rewrite encode_val_length; rewrite <- size_chunk_conv.
    eauto.
    rewrite PMap.gso; eauto.
  }
Qed.

Lemma not_in_buf_item_apply_store_stable :
  forall bi m m' m1 c b ofs v,
    store c m b ofs v = Some m1 ->
    apply_buffer_item bi m = Some m' ->
    ~ (exists ofs, in_buffer_item bi b ofs) ->
    exists m2, store c m' b ofs v = Some m2.
Proof.
  intros.
  eapply gmem_load_loc_perm_eq_store_still; eauto.
  eapply not_in_buffer_apply_buf_item_loc_eq; eauto.
Qed.

Lemma not_in_buf_item_apply_perm_stable :
  forall bi m m' b ofs k p,
    (GMem.mem_access m) !! b ofs k = Some p ->
    apply_buffer_item bi m = Some m' ->
    ~ (exists ofs, in_buffer_item bi b ofs) ->
    (GMem.mem_access m') !! b ofs k = Some p.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc; inv H0; simpls.
    assert (b0 <> b).
    {
      intro; subst.
      contradiction H1; exists z.
      econstructor; eauto.
    }
    rewrite PMap.gso; eauto.
  }
  {
    unfolds free, unchecked_free.
    ex_match2.
    inv H0; simpls.
    destruct (peq b0 b); subst.
    {
      rewrite PMap.gss; eauto.
      ex_match2.
      contradiction H1; clear - Hx0.
      exists ofs.
      destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse;
        econstructor; eauto.
    }
    {
      rewrite PMap.gso; eauto.
    }
  }
  {
    unfolds store.
    ex_match2; simpls.
    inv H0; simpls; eauto.
  }
Qed.

Lemma obj_mem_loc_stable_still :
  forall M M' L ofs,
    obj_mem M L ofs -> loc_stable M M' L ofs -> obj_mem M' L ofs.
Proof.
  intros.
  unfolds loc_stable. 
  split_and H0.
  unfolds obj_mem.
  rewrite <- H2; eauto.
Qed.

Lemma not_in_buf_item_apply_perm_stable' :
  forall m m' bi b ofs k p,
    ~ GMem.perm m b ofs k p ->
    apply_buffer_item bi m = Some m' ->
    ~ (exists ofs, in_buffer_item bi b ofs) ->
    ~ GMem.perm m' b ofs k p.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inv H0; unfolds GMem.perm; simpls.
    destruct (peq b0 b); subst.
    contradiction H1.
    eexists 0%Z.
    econstructor; eauto.
    rewrite PMap.gso; eauto.
  }
  {
    unfolds free, unchecked_free.
    ex_match2.
    inv H0; unfolds GMem.perm; simpls.
    destruct (peq b0 b); subst.
    rewrite PMap.gss; eauto.
    ex_match2.
    intro.
    simpls; tryfalse.
    rewrite PMap.gso; eauto.
  }
  {
    unfolds store; ex_match2.
    inv H0; unfolds GMem.perm; simpls.
    eauto.
  }
Qed.

Lemma in_buffer_cons_split :
  forall bi bf b ofs,
    in_buffer (bi :: bf) b ofs ->
    in_buffer_item bi b ofs \/ in_buffer bf b ofs.
Proof.
  intros.
  inv H.
  simpl in H0.
  destruct H0; subst; eauto.
  right.
  econstructor; eauto.
Qed.

Lemma unbuffer_safe_block_not_alloc_and_invb_not_in_buffer :
  forall tm b ofs t,
    unbuffer_safe tm ->
    ~ In b (GMem.validblocks (memory tm)) ->
    (forall t lo hi, ~ In (BufferedAlloc b lo hi) (tso_buffers tm t)) ->
    in_buffer (tso_buffers tm t) b ofs ->
    False.
Proof.
  introv Hunb_safe.
  generalize dependent b.
  generalize dependent ofs.
  generalize dependent t.
  induction Hunb_safe; simpls; intros.
  destruct (tso_buffers tso t) eqn:?; simpls.
  {
    clear - H2.
    inv H2; simpl; tryfalse.
  }
  {
    eapply in_buffer_cons_split in H2.
    destruct H2.
    {
      inv H2.
      (** alloc *)
      {
        specialize (H1 t lo hi).
        contradiction H1.
        rewrite Heqb0; simpl; eauto.
      }
      (** free *)
      {
        eapply ABIS in Heqb0.
        destruct Heqb0 as [m' Heqb0].
        clear - Heqb0 H3 H0.
        simpls.
        unfolds free.
        ex_match2.
        clear - H0 r H3.
        unfolds range_perm.
        eapply r in H3.
        clear - H0 H3.
        eapply GMem.invalid_noaccess with (ofs := ofs) (k := Max) in H0.
        unfolds Mem.perm_order'.
        rewrite H0 in H3; tryfalse.
      }
      (** store *)
      {
        eapply ABIS in Heqb0.
        destruct Heqb0 as [m' Heqb0].
        clear - H0 Heqb0 H3; simpls.
        unfolds store.
        ex_match2.
        clear - v0 H0 H3.
        unfolds valid_access, range_perm.
        destruct v0.
        eapply H in H3.
        eapply GMem.invalid_noaccess with (ofs := ofs) (k := Max) in H0.
        clear - H0 H3.
        unfolds Mem.perm_order'.
        rewrite H0 in H3; tryfalse.
      }
    }
    {
      lets Happly_buf_item : Heqb0.
      eapply ABIS in Happly_buf_item.
      destruct Happly_buf_item as [m' Happly_buf_item].
      eapply H in Heqb0; eauto.
      instantiate (1 := b).
      {
        clear - H0 Heqb0 Happly_buf_item H1.
        destruct b0; simpls.
        (** alloc *)
        {
          unfolds alloc.
          inv Happly_buf_item; simpls.
          intro.
          destruct H; subst.
          specialize (H1 t z z0).
          rewrite Heqb0 in H1.
          contradiction H1; simpls; eauto.
          tryfalse.
        }
        (** free *)
        {
          unfolds free.
          ex_match2.
          inv Happly_buf_item.
          unfolds unchecked_free; simpls; eauto.
        }
        (** store *)
        {
          unfolds store.
          ex_match2.
          inv Happly_buf_item; simpls; eauto.
        }
      }
      clear - H1 Heqb0.
      intros; intro. 
      specialize (H1 t0 lo hi).
      contradiction H1.
      unfolds tupdate.
      ex_match2; subst; eauto.
      rewrite Heqb0; simpl; eauto.
      instantiate (2 := t).
      instantiate (1 := ofs).
      rewrite tupdate_b_get; eauto.
    }
  }
Qed.

Lemma in_bf_after_unbuffer_in_orign_bf1 :
  forall t' tm tm' b ofs t,
    in_buffer (tso_buffers tm' t) b ofs ->
    unbuffer tm t' = Some tm' ->
    in_buffer (tso_buffers tm t) b ofs.
Proof.
  intros.
  unfolds unbuffer.
  destruct (tso_buffers tm t') eqn:?; tryfalse.
  ex_match2.
  inv H0; simpls.
  unfolds tupdate.
  ex_match2; subst.
  rewrite Heqb0.
  clear - H.
  inv H; econstructor; simpl; eauto.
Qed.

Lemma apply_buffer_split :
  forall bf1 bf2 m m',
    apply_buffer (bf1 ++ bf2) m = Some m' ->
    exists m'', apply_buffer bf1 m = Some m'' /\ apply_buffer bf2 m'' = Some m'.
Proof.
  induction bf1; intros; simpls.
  eexists.
  split; eauto.
  destruct (apply_buffer_item a m) eqn:?; simpls.
  eapply IHbf1 in H; eauto.
  tryfalse.
Qed.

Lemma mem_access_eq_apply_buf_item_stable :
  forall bi m1 m2 m1',
    apply_buffer_item bi m1 = Some m1' ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    exists m2', apply_buffer_item bi m2 = Some m2'.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc; eauto.
  }
  {
    unfolds free; simpls.
    ex_match2; eauto.
    clear - r n H0.
    contradiction n; clear n.
    unfolds range_perm.
    intros.
    rewrite <- H0; eauto.
  }
  {
    unfolds store.
    ex_match2; eauto.
    clear - v0 n H0.
    contradiction n; clear n.
    unfolds valid_access.
    destruct v0; split; eauto.
    unfolds range_perm; simpls.
    rewrite <- H0; intros; eauto.
  }
Qed.

Lemma unbuffer_safe_mem_access_same_stable :
  forall bfs m1 m2,
    unbuffer_safe {| tso_buffers := bfs; memory := m1 |} ->
    GMem.mem_access m1 = GMem.mem_access m2 ->
    unbuffer_safe {| tso_buffers := bfs; memory := m2 |}.
Proof.
  intros.
  remember ({| tso_buffers := bfs; memory := m1 |}) as tm.
  generalize dependent m1.
  generalize dependent m2.
  generalize dependent bfs.
  induction H; simpls; intros; subst; simpls.
  econstructor; intros; simpls.
  {
    eapply ABIS in H1.
    destruct H1 as [m1' H1].
    eapply mem_access_eq_apply_buf_item_stable; eauto.
  }
  {
    lets Ht : H1.
    eapply ABIS in Ht; eauto.
    destruct Ht as [m'' Ht].
    renames m' to m2', m'' to m1'.
    lets Hmem_access : H0.
    eapply apply_buf_item_maccess_eq_still in Hmem_access; eauto.
  }
Qed.

Lemma unbuffer_safe_storev_still' :
  forall tm t c b ofs v' v,
    (forall t, ~ (exists ofs, in_buffer (tso_buffers tm t) b ofs)) ->
    (exists m', store c (memory tm) b ofs v' = Some m') ->
    unbuffer_safe tm ->
    unbuffer_safe
      {|
        tso_buffers := tupdate t
                         (tso_buffers tm t ++
                           BufferedStore c b ofs v :: nil) (tso_buffers tm);
        memory := memory tm |}.
Proof.
  intros.
  induction H1; simpls; intros.
  econstructor; intros; simpls.
  {
    destruct (peq t t0); subst.
    {
      rewrite tupdate_b_get in H2.
      destruct (tso_buffers tso t0) eqn:?; simpls.
      {
        inv H2.
        clear - H0.
        destruct H0; simpl.
        eapply store_store_other_val; eauto.
      }
      {
        inv H2.
        eapply ABIS; eauto.
      }
    }
    {
      rewrite in_tbf_upd_oth_stillin in H2; eauto.
    }
  }
  {
    destruct (peq t t0); subst.
    {
      rewrite tupdate_b_get in H2; simpls.
      destruct (tso_buffers tso t0) eqn:?; simpls.
      {
        inv H2.
        rewrite tupdate_same_tid_eq; eauto.
        rewrite tupdate_same_eq; eauto.
        simpl in H3.
        assert (unbuffer_safe {| tso_buffers := tso_buffers tso;
                                 memory := memory tso |}).
        {
          econstructor; eauto.
        }
        eapply unbuffer_safe_mem_access_same_stable; eauto.
        clear - H3; unfolds store; ex_match2.
        inv H3; eauto.
      }
      {
        inv H2.
        rewrite tupdate_same_tid_eq; eauto.
        eapply H1 in Heqb1.
        rewrite tupdate_b_get in Heqb1.
        rewrite tupdate_same_tid_eq in Heqb1.
        2 : eauto.
        eauto.
        clear - H Heqb1 H3.
        intros; intro.
        destruct H0 as [ofs H0].
        specialize (H t).
        contradiction H.
        exists ofs.
        unfolds tupdate.
        ex_match2; subst; eauto.
        rewrite Heqb1.
        inv H0; econstructor; simpls; eauto.
        clear - H H3 H0 Heqb1.
        destruct H0 as [m'' H0].
        eapply not_in_buf_item_apply_store_stable; eauto.
        specialize (H t0).
        rewrite Heqb1 in H; clear - H.
        intro. destruct H0 as [ofs H0].
        contradiction H.
        exists ofs.
        econstructor; simpl; eauto.
      }
    }
    { 
      rewrite in_tbf_upd_oth_stillin in H2; simpls; eauto.
      eapply H1 in H2.
      rewrite in_tbf_upd_oth_stillin in H2; eauto.
      rewrite tupdate_tid_neq_twice_rev; eauto.
      eauto.
      clear - H H2 n.
      intros; intro.
      destruct H0 as [ofs H0].
      unfolds tupdate.
      ex_match2; subst; eauto.
      specialize (H t0).
      contradiction H.
      exists ofs.
      rewrite H2.
      inv H0; econstructor; simpls; eauto.
      specialize (H t1).
      contradiction H.
      exists ofs. eauto.
      destruct H0 as [m'' H0].
      eapply not_in_buf_item_apply_store_stable; eauto.
      clear - H H2.
      specialize (H t0).
      intro.
      contradiction H.
      destruct H0 as [ofs H0].
      rewrite H2.
      exists ofs.
      econstructor; simpl; eauto.
    }
  }
Qed.
  
Lemma unbuffer_safe_storev_still :
  forall tm fm c t fl b ofs v bm v',
    (forall t, ~ (exists ofs, in_buffer (tso_buffers tm t) b ofs)) ->
    embed (memory tm) fl fm ->
    (exists m', store c (memory tm) b
                (Ptrofs.unsigned (Ptrofs.repr ofs)) v' = Some m') ->
    tsostorev c {| tbuffer := tso_buffers tm t; fmemory := fm |}
              (Vptr b (Ptrofs.repr ofs)) v = Some bm ->
    unbuffer_safe tm ->
    unbuffer_safe {| tso_buffers :=
                       tupdate t (tbuffer bm) (tso_buffers tm);
                     memory := strip (fmemory bm) |}.
Proof.
  intros.
  inv H0.
  unfolds tsostorev, tsostore.
  inv H2; simpls.
  rewrite H5.
  eapply unbuffer_safe_storev_still'; eauto.
Qed.

Lemma embed_appply_buffer_update_not_in_freelist_stable' :
  forall bf bi m m' m1 m2 fm1 fl,
    (forall b lo hi n, bi = BufferedAlloc b lo hi -> b <> get_block fl n) ->
    apply_buffer_item bi m = Some m' ->
    apply_buffer bf m = Some m1 -> embed m1 fl fm1 ->
    apply_buffer bf m' = Some m2 ->
    exists fm2, embed m2 fl fm2 /\ Mem.nextblock fm1 = Mem.nextblock fm2.
Proof.
  intros.
  destruct bi; simpls.
  (** alloc *)
  {
    assert (forall n, b <> get_block fl n).
    {
      intros.
      eapply H; eauto.
    }
    unfolds alloc.
    inv H2.
    inv H0; simpls.
    eexists
      (Mem.mkmem (GMem.mem_contents m2)
                 (GMem.mem_access m2)
                 (GMem.validblocks m2)
                 (Mem.freelist fm1)
                 (Mem.nextblockid fm1) _ _ _ _ _).
    split.
    econstructor; eauto.
    unfold strip; simpl.
    eapply gmem_eq; eauto.
    eauto.
    Unshelve.
    {
      intros.
      destruct fm1; simpls; eauto.
    }
    {
      intros.
      destruct fm1; simpls.
      unfold strip in H1; simpls.
      split; intro.
      { 
        lets Ht : H0.
        eapply valid_wd in Ht.
        eapply Ht. 
        eapply in_valid_block_not_in_free_list_cons_still
        with (b0 := b) (m1 := m) in H2; eauto; simpls.
        eauto.
        instantiate (1 := 0); simpl; eauto.
        simpl; eauto.
      }
      {
        lets Ht : H0.
        eapply valid_wd in Ht.
        eapply Ht in H2.
        eapply in_valid_block_cons_still with (m1 := m); eauto; simpls.
        instantiate (1 := 0); simpl; eauto.
        simpl; eauto.
      }
    }
    {
      destruct m2; simpls; eauto.
    }
    {
      destruct m2; simpls; eauto.
    }
    {
      destruct m2; simpls; eauto.
    }
  }
  (** store *)
  {
    inv H2.
    unfolds free.
    ex_match2; simpls.
    unfolds unchecked_free.
    inv H0; simpls.
    eexists
      (Mem.mkmem (GMem.mem_contents m2)
                 (GMem.mem_access m2)
                 (GMem.validblocks m2)
                 (Mem.freelist fm1)
                 (Mem.nextblockid fm1) _ _ _ _ _).
    split.
    econstructor; eauto.
    unfold strip; simpl.
    eapply gmem_eq; eauto.
    simpl; eauto.
    Unshelve.
    {
      intros; destruct fm1; simpls; eauto.
    }
    {
      intros; destruct fm1; simpls.
      unfold strip in H1; simpls.
      split; intros.
      {
        lets Ht : H0.
        eapply valid_wd in Ht.
        eapply Ht.
        eapply in_valid_block_eq_apply_same_buf_still in H1; simpls; eauto.
        rewrite H1 in H2; eauto.
      }
      {
        lets Ht : H0.
        eapply valid_wd in Ht.
        eapply Ht in H2.
        eapply in_valid_block_eq_apply_same_buf_still in H1; simpls; eauto.
        rewrite H1; eauto.
      }
    }
    {
      destruct m2; simpls; eauto.
    }
    {
      destruct m2; simpls; eauto.
    }
    {
      destruct m2; simpls; eauto.
    }
  }
  (** free *)
  {
    inv H2.
    unfolds store.
    ex_match2.
    inv H0; simpls.
    eexists
      (Mem.mkmem (GMem.mem_contents m2)
                 (GMem.mem_access m2)
                 (GMem.validblocks m2)
                 (Mem.freelist fm1)
                 (Mem.nextblockid fm1) _ _ _ _ _).
    split.
    econstructor; eauto.
    unfold strip; simpl; eauto.
    eapply gmem_eq; eauto.
    simpl; eauto. 
    Unshelve.
    {
      intros; destruct fm1; simpls; eauto.
    }
    {
      intros; destruct fm1; simpls.
      unfold strip in H1; simpls.
      split; intros.
      {
        lets Ht : H0.
        eapply valid_wd in Ht.
        eapply Ht.
        eapply in_valid_block_eq_apply_same_buf_still in H1; simpls; eauto.
        rewrite H1 in H2; eauto.
      }
      {
        lets Ht : H0.
        eapply valid_wd in Ht.
        eapply Ht in H2.
        eapply in_valid_block_eq_apply_same_buf_still in H1; simpls; eauto.
        rewrite H1; eauto.
      }
    }
    {
      destruct m2; simpls; eauto.
    }
    {
      destruct m2; simpls; eauto.
    }
    {
      destruct m2; simpls; eauto.
    }
  }
Qed.

Lemma unbuffer_safe_noalloc_noperm_not_inbuffer :
  forall tm L ofs t,
    unbuffer_safe tm ->
    (forall t, ~ (exists lo hi, In (BufferedAlloc L lo hi) (tso_buffers tm t))) ->
    (forall p k, ~ GMem.perm (memory tm) L ofs k p) ->
    ~ in_buffer (tso_buffers tm t) L ofs.
Proof.
  intros.
  generalize dependent L.
  generalize dependent ofs.
  generalize dependent t.
  induction H; simpls; intros.
  intro.
  destruct (tso_buffers tso t) eqn:?; simpls.
  inv H2; simpls; tryfalse.
  lets Happly_buf : Heqb.
  eapply ABIS in Happly_buf.
  destruct Happly_buf as [m' Happly_buf].
  lets Hcons : Heqb.
  eapply H in Hcons.
  2 : eauto.
  Focus 2.
  instantiate (1 := L). 
  clear - H0 Heqb.
  intros; intro.
  destruct H as (lo & hi & H).
  unfolds tupdate. 
  ex_match2; subst.
  specialize (H0 t).
  contradiction H0.
  rewrite Heqb; simpl; eauto.
  specialize (H0 t0).
  contradiction H0.
  eauto.
  contradiction Hcons.
  instantiate (1 := ofs).
  instantiate (1 := t). 
  clear - Heqb H2 Happly_buf H1 H0.
  rewrite tupdate_b_get; eauto.
  inv H2; subst.
  econstructor; eauto.
  simpls.
  destruct H; subst; eauto.
  assert ((GMem.mem_access (memory tso)) !! L ofs Max = None).
  { 
    clear - H1.
    unfolds GMem.perm, perm_order'.
    specialize (H1 Nonempty Max).
    ex_match2; eauto.
    contradiction H1; eauto.
    econstructor; eauto.
  }  
  destruct bi; simpls. 
  specialize (H0 t).
  inv H3.
  rewrite Heqb in H0.
  contradiction H0.
  simpl; eauto.
  inv H3.
  unfolds free.
  ex_match2.
  unfolds range_perm.
  eapply r in H8.  
  rewrite H in H8.
  inv H8.
  inv H3.
  unfolds store.
  ex_match2.
  inv Happly_buf.
  unfolds valid_access.
  destruct v0.
  unfolds range_perm.
  eapply r in H9.
  rewrite H in H9.
  unfolds Mem.perm_order'.
  tryfalse.
 
  intros; intro.
  destruct b; simpls.
  assert (b <> L).
  {
    intro; subst.
    specialize (H0 t).
    contradiction H0.
    rewrite Hcons; simpl; eauto.
  }
  clear - H1 Happly_buf H3 H4.
  unfolds alloc.
  inv Happly_buf; simpls.
  specialize (H1 p k).
  contradiction H1.
  clear - H3 H4.
  unfolds GMem.perm; simpls.
  rewrite PMap.gso in H3; simpls; eauto. 
  clear - Happly_buf H1 Happly_buf H3.
  unfolds free.
  ex_match2.
  inv Happly_buf.
  unfolds range_perm.
  unfolds unchecked_free.
  unfolds GMem.perm; simpls.
  destruct (Pos.eq_dec b L); subst.
  {
    rewrite PMap.gss in H3.
    ex_match2; tryfalse.
    eapply H1; eauto.
  }
  {
    rewrite PMap.gso in H3; simpls; eauto.
    eapply H1; eauto.
  }
  unfolds store.
  ex_match2.
  inv Happly_buf.
  unfolds GMem.perm; simpls.
  eapply H1; eauto.
Qed.