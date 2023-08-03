Require Import Coqlib InteractionSemantics FMemory FMemOpFP MemOpFP GMemory Footprint Values InteractionSemantics MemAux loadframe AsmLang Cop_fp.

Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Ltac ex_match:=
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?Hx; try discriminate
         end;try congruence.
Ltac ex_match2:=
  repeat match goal with
         | H: context[match ?x with _ => _ end]  |- _ => destruct x eqn:?Hx; try discriminate
         | H: _ |- context[match ?x with _ => _ end ] => destruct x eqn:?Hx;try discriminate
         end;try congruence.
Lemma eq_access_eq_perm:
    forall m1 m2,
    (forall b ofs k,
        Memperm.perm_order''
          (Maps.PMap.get b (GMem.mem_access (strip m1)) ofs k)
          (Maps.PMap.get b (GMem.mem_access (strip m2)) ofs k) /\
        Memperm.perm_order''
          (Maps.PMap.get b (GMem.mem_access (strip m2)) ofs k)
          (Maps.PMap.get b (GMem.mem_access (strip m1)) ofs k))->
    (
      forall b ofs k,
        (Maps.PMap.get b (Mem.mem_access  m1) ofs k) = (Maps.PMap.get b (Mem.mem_access m2) ofs k)).
Proof.
  intros.
  specialize (H b ofs k).
  eapply GMem.eq_access_eq_perm;eauto.
Qed.
Lemma strip_eq_perm:
  forall m1 m2 ,
    (forall b ofs k,
        (Maps.PMap.get b (Mem.mem_access m1) ofs k) = (Maps.PMap.get b (Mem.mem_access m2) ofs k)) ->
    forall chunk b z p,
      Mem.valid_access m1 chunk b z p ->
      Mem.valid_access m2 chunk b z p.
Proof.
  unfold Mem.valid_access.
  intros. destruct H0.
  split;auto.
  unfold Mem.range_perm in *.
  intros. specialize (H0 _ H2).
  Hsimpl.
  unfold Mem.perm in *.
  unfold strip in H. simpl in H.
  erewrite H in H0 ;eauto.
Qed.
  
Definition fmem_eq (m1 m2: mem) : Prop :=
      GMem.eq (strip m1) (strip m2) /\
      Mem.freelist m1 = Mem.freelist m2 /\
      Mem.nextblockid m1 = Mem.nextblockid m2.

Lemma fmem_eq_refl:forall m,fmem_eq m m. econstructor;eauto. apply GMem.eq_refl. Defined.
Lemma fmem_eq_sym:forall m1 m2,fmem_eq m1 m2 ->fmem_eq m2 m1. unfold fmem_eq;intros;Hsimpl;Esimpl;eauto. apply GMem.eq_sym. auto. Defined.

Lemma fmem_eq_access_eq:
  forall m1 m2 chunk b z p,
    fmem_eq m1 m2 ->
    Mem.valid_access m1 chunk b z p ->
    Mem.valid_access m2 chunk b z p.
Proof.
  intros. destruct H as [[] []].
  pose proof eq_access_eq_perm _ _ eq_access.
  eapply strip_eq_perm;eauto.
Qed.
Record gmem_fl_wd(gm:GMemory.gmem)(fl:freelist)(nextblockid:nat):=
  {
    freelist_wd0 : forall n n' : nat,
                  n <> n' -> get_block fl n <> get_block fl n';
    valid_wd0 : forall (n : nat) (b : block),
               get_block fl n = b ->
               List.In b (GMem.validblocks gm)<-> (n < nextblockid)%nat;
  }.
Lemma fmem_strip_fl_wd:
  forall m,
    gmem_fl_wd (strip m) m.(Mem.freelist) m.(Mem.nextblockid).
Proof. destruct m;constructor;simpl;intros;eauto. Qed.
Lemma gmem_fl_wd_eqrefl:
  forall m m',
    GMem.eq m m'->
    forall fl n,
      gmem_fl_wd m fl n->
      gmem_fl_wd m' fl n.
Proof.
  destruct 2.
  split;auto.
  intros.
  specialize (valid_wd1 n0 b H0).
  pose proof GMem.eq_validblocks _ _ H.
  split;intro;try apply valid_wd1;apply H1;try apply valid_wd1;auto.
Qed.
Definition combine(gm:gmem)(fl:freelist)(n:nat)(g:gmem_fl_wd gm fl n):=
  Mem.mkmem
    (GMem.mem_contents gm)
    (GMem.mem_access gm)
    (GMem.validblocks gm)
    (fl)
    (n)
    (freelist_wd0 gm fl n g)
    (valid_wd0 gm fl n g)
    (GMem.access_max gm)
    (GMem.invalid_noaccess gm)
    (GMem.contents_default gm).

Lemma strip_combine:
  forall gm fl n (wd:gmem_fl_wd gm fl n),
    strip (combine gm fl n wd) = gm.
Proof. unfold combine. unfold strip. simpl. destruct gm;auto. Qed.
       
Lemma gmem_fl_wd_embed:
  forall gm fl n (wd:gmem_fl_wd gm fl n),
    embed gm fl (combine gm fl n wd).
Proof.
  intros.
  econstructor;eauto. rewrite strip_combine;auto.
Qed.
Lemma mem_eq_combine_eq:
  forall m1 m2 fl n (wd1:gmem_fl_wd m1 fl n) (Gmemeq:GMem.eq m1 m2),
    fmem_eq (combine m1 fl n wd1)(combine m2 fl n (gmem_fl_wd_eqrefl m1 m2 Gmemeq fl n wd1)).
Proof.
  unfold fmem_eq. intros.
  Esimpl;eauto. do 2 rewrite strip_combine. auto.
Qed.

Lemma combine_equiv:
  forall m l i wd wd',
    combine m l i wd = combine m l i wd'.
Proof.
  intros.
  pose ProofIrrelevance.proof_irrelevance.
  unfold combine. f_equal.
  apply e. apply e.
Qed.
Lemma combine_equiv2:
  forall m fl1 fl2 i1 i2 wd1 wd2,
    fl1 = fl2 ->
    i1 = i2 ->
    combine m fl1 i1 wd1= combine m fl2 i2 wd2.
Proof.
  intros. subst. apply combine_equiv.
Qed.
Lemma combine_refl:
    
  forall x,
    x = combine (strip x)(Mem.freelist x)(Mem.nextblockid x)(fmem_strip_fl_wd x).
Proof.
  destruct x;unfold combine,strip.
  simpl.
  f_equal;apply ProofIrrelevance.proof_irrelevance.
Qed.


Lemma eq_mem_eq_fmem:
  forall gm1 gm2 fl m1,
    GMemory.GMem.eq gm1 gm2 ->
    FMemory.embed gm1 fl m1 ->
    exists m2,FMemory.embed gm2 fl m2 /\
          fmem_eq m1 m2.
Proof.
  intros. 
  pose proof fmem_strip_fl_wd m1.
  inversion H0;subst.
  pose proof mem_eq_combine_eq (strip m1) gm2 (Mem.freelist m1)(Mem.nextblockid m1) H1 H.
  eexists;split;eauto.
  eapply gmem_fl_wd_embed;eauto.
Qed.

Local Transparent Mem.load Mem.store Mem.alloc Mem.free.
Lemma fmem_eq_load:
  forall m1 m2 chunk b z,
    fmem_eq m1 m2 ->
    FMemory.Mem.load chunk m1 b z = 
    FMemory.Mem.load chunk m2 b z.
Proof.
  intros.
  unfold Mem.load.
  destruct H as [[] []].
  pose proof eq_access_eq_perm _ _ eq_access.
  pose proof strip_eq_perm _ _ H1.
  symmetry in H1.
  pose proof strip_eq_perm _ _ H1.
  do 2 destruct Mem.valid_access_dec;eauto;try (contradict n;eauto).
  f_equal; f_equal.
  remember (size_chunk_nat chunk) as i.
  remember (BinInt.Z.add z (BinInt.Z.of_nat i)) as j.
  assert(z = BinInt.Z.sub j (BinInt.Z.of_nat i)). Omega.omega.
  rewrite H4.
  assert(forall k, (k<= i)%nat ->  Mem.getN k (BinInt.Z.sub j (BinInt.Z.of_nat k))(Maps.PMap.get b (Mem.mem_contents m1)) = Mem.getN k (BinInt.Z.sub j (BinInt.Z.of_nat k))(Maps.PMap.get b (Mem.mem_contents m2))).
  induction k;intros;auto.
  assert(k<=i)%nat. Omega.omega. Hsimpl.
  simpl.
  rewrite Znat.Zpos_P_of_succ_nat.
  assert((BinInt.Z.add (BinInt.Z.sub j (BinInt.Z.succ (BinInt.Z.of_nat k))) 1) =  (BinInt.Z.sub j (BinInt.Z.of_nat k))).
  Omega.omega.
  rewrite H7. clear H7.
  rewrite IHk. f_equal.
  apply eq_contents. simpl.
  destruct v. apply Mem.perm_cur_max, H7. split. Omega.omega.
  rewrite size_chunk_conv. rewrite <- Heqi. Omega.omega.
  eapply H5;eauto.
Qed.
Lemma fmem_alloc_exists:
  forall m l h,
  exists m' b, Mem.alloc m l h = (m',b).
Proof. unfold Mem.alloc. eauto. Qed.
Lemma fmem_eq_alloc:
  forall m1 m2 lo hi m1' b1 m2' b2,
    fmem_eq m1 m2 ->
    FMemory.Mem.alloc m1 lo hi = (m1', b1) ->
    FMemory.Mem.alloc m2 lo hi = (m2', b2) ->
    fmem_eq m1' m2' /\ b1 = b2.
Proof.
  unfold fmem_eq.
  intros. inversion H1;subst;clear H1. inversion H0;subst;clear H0.
  unfold strip. simpl.
  Hsimpl.
  assert(Mem.nextblock m1 = Mem.nextblock m2).
  unfold Mem.nextblock;congruence.
  assert(forall b , List.In b (Mem.validblocks m1)<->List.In b (Mem.validblocks m2)).
  destruct H.
  unfold strip,GMem.valid_block in eq_validblocks;simpl in *;eauto.
  Esimpl;eauto.
  
  econstructor;simpl;simpl.
  Focus 3. unfold GMem.valid_block. simpl.
  split;intro;destruct H4;[left|right|left|right];try congruence;apply H3;auto.

  intros;rewrite <- H2.
  do 2 rewrite Maps.PMap.gsspec. destruct Coqlib.peq eqn:?;auto.
  destruct H. apply eq_contents. simpl. rewrite Maps.PMap.gsspec in H4. rewrite Heqs in H4. auto.

  intros. rewrite <-H2. apply GMem.eq_access_eq_perm.
  do 2 rewrite Maps.PMap.gsspec. destruct Coqlib.peq eqn:?;auto.
  destruct H. apply GMem.eq_access_eq_perm. apply eq_access.
Qed.
  

Lemma setN_geteq:
  forall i v j z p p',
    (i < length v)%nat ->
    j = BinInt.Z.of_nat i ->
    Maps.ZMap.get (BinInt.Z.add z j) (Mem.setN v z p) = Maps.ZMap.get (BinInt.Z.add z j) (Mem.setN v z p').
Proof.
  induction i;induction v;intros;rewrite H0.
  inversion H. 
  assert(BinInt.Z.add z 0 = z). Omega.omega.
  simpl. rewrite H1.
  do 2 (rewrite Mem.setN_outside;try Omega.omega).
  do 2 rewrite Maps.ZMap.gss;auto.

  inversion H.
  simpl in H.
  assert(i< length v)%nat. Omega.omega.
  assert(BinInt.Z.of_nat i = BinInt.Z.of_nat i). auto.
  eapply IHi in H1;try apply H2;eauto.

  assert(BinInt.Z.add z (BinInt.Z.of_nat (S i)) = BinInt.Z.add (BinInt.Z.succ z)(BinInt.Z.of_nat i)). simpl. Lia.lia.
  rewrite H3. eauto.
Qed.

Lemma Z_of_nat_zify : forall x, BinInt.Z.le 0 x ->BinInt.Z.of_nat (BinInt.Z.to_nat x) = x.
Proof.
  intros.
  destruct x.
  - rewrite Znat.Z2Nat.id; reflexivity.
  - rewrite Znat.Z2Nat.inj_pos. Lia.lia.
  - rewrite Znat.Z2Nat.inj_neg. Lia.lia.
Qed.  

Lemma setN_geteq2:
  forall ofs v i p p',
    BinInt.Z.le i ofs -> BinInt.Z.lt ofs (BinInt.Z.add i (BinInt.Z.of_nat (length v))) ->
    Maps.ZMap.get ofs (Mem.setN v i p) =
    Maps.ZMap.get ofs (Mem.setN v i p').
Proof.
  intros.
  remember (BinInt.Z.to_nat(BinInt.Z.sub ofs i)) as k.
  assert(k<length v)%nat.
  rewrite Heqk. rewrite <- Znat.Nat2Z.id.  
  apply Znat.Z2Nat.inj_lt;try Omega.omega.
  assert(ofs = BinInt.Z.add i (BinInt.Z.sub ofs i)). Omega.omega.
  rewrite H2.
  eapply setN_geteq  in H1;eauto.
  rewrite Heqk. rewrite Z_of_nat_zify;Omega.omega.
Qed.
Lemma fmem_eq_store:
  forall m1 m2 chunk b z v m1',
    fmem_eq m1 m2 ->
    FMemory.Mem.store chunk m1 b z v = Some m1' ->
    exists m2', FMemory.Mem.store chunk m2 b z v = Some m2' /\
           fmem_eq m1' m2'.
Proof.
  intros.
  unfold Mem.store in H0.
  destruct Mem.valid_access_dec;inversion H0;clear H0;subst.
  eapply fmem_eq_access_eq in v0 as v1;eauto.
  eapply Mem.valid_access_store with(v:=v) in v1 as [m2' STORE];eauto.
  Esimpl;eauto.
  unfold Mem.store in STORE.
  destruct Mem.valid_access_dec;inversion STORE;clear STORE;subst.
  unfold fmem_eq,strip in *. simpl.
  Hsimpl;Esimpl;eauto.
  destruct H;constructor;simpl in *;unfold GMem.valid_block;eauto.

  intros. do 2 rewrite Maps.PMap.gsspec.
  destruct Coqlib.peq;auto. subst.
  destruct (ZArith_dec.Z_lt_dec ofs z).
  do 2 (erewrite (Mem.setN_outside);eauto).
  assert(BinInt.Z.ge ofs z). destruct (Coqlib.zlt ofs z);congruence.
  destruct (ZArith_dec.Z_lt_dec ofs (BinInt.Z.add z (BinInt.Z.of_nat (length (encode_val chunk v))))).
  Focus 2. do 2 (erewrite (Mem.setN_outside);eauto).
  
  apply BinInt.Z.ge_le_iff in H2.
  eapply setN_geteq2;eauto.
Qed.

Lemma fmem_eq_free:
  forall m1 m2 b lo hi m1',
    fmem_eq m1 m2 ->
    FMemory.Mem.free m1 b lo hi = Some m1' ->
    exists m2', FMemory.Mem.free m2 b lo hi = Some m2' /\
           fmem_eq m1' m2'.
Proof.
  pose proof Mem.range_perm_free.

  intros.
  unfold Mem.free in H0.
  destruct Mem.range_perm_dec;inversion H0;subst;clear H0.

  assert(Mem.range_perm m2 b lo hi Memperm.Cur Memperm.Freeable).
  unfold Mem.range_perm in *.
  intros.
  specialize (r ofs H0).
  unfold Mem.perm in *. unfold Mem.perm_order' in *.
  destruct (Maps.PMap.get b (Mem.mem_access m1) ofs Memperm.Cur) eqn:?.
  Focus 2. inversion r.
  destruct H as [[] []].
  eapply eq_access_eq_perm in eq_access;eauto.
  erewrite <-eq_access;eauto.
  rewrite Heqo;auto.

  eapply X in H0 as [m2' FREE].
  exists m2';split;auto.

  unfold Mem.free in FREE.
  destruct Mem.range_perm_dec ;inversion FREE;subst;clear FREE.

  unfold Mem.unchecked_free,fmem_eq,strip;simpl.
  destruct H as [[] []].
  Esimpl;eauto. simpl in *.
  econstructor;simpl.
  {
    intros. rewrite Maps.PMap.gsspec in H1.
    destruct Coqlib.peq;subst;eauto.
    destruct   (Coqlib.proj_sumbool (Coqlib.zle lo ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs hi))%bool eqn:?;[inversion H1|eauto].
  }
  {
    intros. apply GMem.eq_access_eq_perm.
    rewrite Maps.PMap.gsspec. destruct Coqlib.peq;subst.
    rewrite Maps.PMap.gss.
    destruct  (Coqlib.proj_sumbool (Coqlib.zle lo ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs hi))%bool;eauto.
    eapply GMem.eq_access_eq_perm;eauto.
    rewrite Maps.PMap.gso;auto. apply GMem.eq_access_eq_perm;eauto.
  }
  {
    unfold GMem.valid_block;simpl. auto.
  }
Qed.  


Lemma fmem_eq_valid_pointer:
  forall m1 m2 b z,
    fmem_eq m1 m2 ->
    FMemory.Mem.valid_pointer m1 b z = true <->
    FMemory.Mem.valid_pointer m2 b z = true.
Proof.
  intros. 
  destruct H. destruct H. specialize (eq_access b z Memperm.Cur).
  apply GMemory.GMem.eq_access_eq_perm in eq_access. clear eq_contents eq_validblocks H0.
  unfold FMemory.strip in *; simpl in *.
  unfold FMemory.Mem.valid_pointer.
  destruct FMemory.Mem.perm_dec; simpl in *; 
    destruct (FMemory.Mem.perm_dec m2 _ _ _ _); simpl in *; try tauto.
  split; auto. exfalso. apply n. clear n. unfold FMemory.Mem.perm, FMemory.Mem.perm_order' in *.
  rewrite <- eq_access; auto.
  split; auto. exfalso. apply n. clear n. unfold FMemory.Mem.perm, FMemory.Mem.perm_order' in *.
  rewrite eq_access; auto.
Qed.
Lemma fmem_eq_valid_pointer_eq:
  forall m1 m2 ,
    fmem_eq m1 m2 ->
    FMemory.Mem.valid_pointer m1 = FMemory.Mem.valid_pointer m2 .
Proof.
  intros.
  eapply FunctionalExtensionality.functional_extensionality_dep.
  intro.
  eapply FunctionalExtensionality.functional_extensionality_dep.
  intro.
  destruct Mem.valid_pointer eqn:?.
  apply fmem_eq_sym in H.
  eapply fmem_eq_valid_pointer in Heqb;eauto.
  destruct (Mem.valid_pointer m2 x x0) eqn:?.
  eapply fmem_eq_valid_pointer in Heqb0;eauto.
  auto.
Qed.



(** Forward *)
Lemma alloc_forward:
  forall m fl m0 b lo hi m1,
    FMemory.embed m fl m0 ->
    FMemory.Mem.alloc m0 lo hi = (m1, b) ->
    GMemory.GMem.forward m (FMemory.strip m1).
Proof.
  intros. inv H.
  exploit FMemory.Mem.alloc_validblocks; eauto.
  exploit FMemory.Mem.alloc_result; eauto.
  intros. constructor. 
  destruct m0; unfold GMemory.GMem.valid_block; subst; simpl in *; intros. 
  rewrite H1. unfold FMemory.Mem.nextblock in *; simpl in *. auto.
  intros.
  exploit FMemory.Mem.perm_alloc_4; eauto.
  subst. unfold GMemory.GMem.valid_block in *. destruct m0; simpl in *.
  unfold FMemory.Mem.nextblock in *; simpl in *.
  intro. subst. eapply valid_wd in H2; eauto. omega.
Qed.

Lemma store_forward:
  forall m fl m0 chunk b ofs v m1,
    FMemory.embed m fl m0 ->
    FMemory.Mem.store chunk m0 b ofs v = Some m1 ->
    GMemory.GMem.forward m (FMemory.strip m1).
Proof.
  intros. inv H.
  exploit FMemory.Mem.store_access; eauto.
  exploit FMemory.Mem.store_validblocks; eauto. intros.
  constructor; unfold GMemory.GMem.valid_block, GMemory.GMem.validblocks; destruct m0; destruct m1;
    intros; simpl in *; congruence.
Qed.
  
Lemma free_forward:
  forall m fl m0 b lo hi m1,
    FMemory.embed m fl m0 ->
    FMemory.Mem.free m0 b lo hi = Some m1 ->
    GMemory.GMem.forward m (FMemory.strip m1).
Proof.
  intros. inv H.
  exploit FMemory.Mem.free_validblocks; eauto. intros.
  constructor; unfold GMemory.GMem.valid_block, GMemory.GMem.validblocks; destruct m0; destruct m1;
    intros; simpl in *; try congruence.
  exploit FMemory.Mem.perm_free_3; eauto.
Qed.


(** embed *)
Lemma embed_refl:
  forall m,
    FMemory.embed (FMemory.strip m) (FMemory.Mem.freelist m) m.
Proof. destruct m; simpl; constructor; auto. Qed.

Lemma fmem_eq_cmpu_bool_fp_eq:
  forall m m',
    fmem_eq m m'->
    Cop_fp.cmpu_bool_fp m' = Cop_fp.cmpu_bool_fp m.
Proof.
  intros.
  unfold Cop_fp.cmpu_bool_fp.
  eapply FunctionalExtensionality.functional_extensionality_dep;intro.
  eapply FunctionalExtensionality.functional_extensionality_dep;intro.
  eapply FunctionalExtensionality.functional_extensionality_dep;intro.
  destruct x0 eqn:?,x1 eqn:?,Archi.ptr64 eqn:?;auto.
  destruct Integers.Int.eq,Values.Val.cmp_different_blocks;auto.
  f_equal.
  unfold FMemOpFP.weak_valid_pointer_fp.
  erewrite fmem_eq_valid_pointer_eq;eauto. apply fmem_eq_sym;auto.
  
  destruct Integers.Int.eq,Values.Val.cmp_different_blocks;auto.
  f_equal.
  unfold FMemOpFP.weak_valid_pointer_fp;erewrite fmem_eq_valid_pointer_eq;eauto;apply fmem_eq_sym;auto.

  destruct Values.eq_block;auto. subst.
  f_equal. f_equal;unfold FMemOpFP.weak_valid_pointer_fp;erewrite fmem_eq_valid_pointer_eq;eauto;apply fmem_eq_sym;auto.
Qed.
Ltac gmem_unfolds:=
  try unfold strip in *;
  try unfold FMemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp,effects in *;
  try unfold Locs.belongsto,notbelongsto in *;
  try unfold LocalAlloc in *;
  try unfold unchanged_content in *;
  try unfold unchanged_perm in *;
  try unfold unchanged_validity in *;
  try unfold GMem.valid_block in *;
  try unfold GMem.eq_perm in *;
  try unfold GMem.perm in *;
  try unfold Mem.nextblock in *;
  
  simpl in *.
Lemma mem_free_fleq:
  forall m0 i sz m b,
    Mem.free m0 i sz b= Some m->
    Mem.freelist m0 = Mem.freelist m.
Proof. intros;symmetry; eapply Mem.free_freelist;eauto.  Qed.

Lemma mem_free_eff:
  forall m0 i sz m b0,
    Mem.free m0 i sz b0= Some m->
    LEffect (strip m0)(strip m)(FMemOpFP.free_fp i sz b0) m0.(Mem.freelist).
Proof.
  Transparent Mem.free.
  unfold Mem.free.
  intros.
  ex_match.
  inv H.
  constructor.
  {
    constructor;gmem_unfolds;intros;auto.
    constructor;auto. constructor;intros. split;auto.
    inv H. rewrite Locs.emp_union_locs in H1.
    rewrite Maps.PMap.gsspec. destruct peq;subst;[|split];auto.
    unfold FMemOpFP.range_locset in H1.
    ex_match. assert(sz + (b0 - sz) = b0). OmegaPlugin.omega.
    rewrite <- H,H1. split;auto.

    constructor;auto. split;auto.
    intros.
    inv H.
    unfold FMemOpFP.range_locset in H1.
    ex_match. subst. rewrite Maps.PMap.gss.
    assert(sz + (b0 - sz) = b0). OmegaPlugin.omega.
    rewrite <- H,H1. split;auto.
    rewrite Maps.PMap.gso;auto. split;auto.
    
    inv H;gmem_unfolds. 
    rewrite Maps.PMap.gsspec in H1.
    unfold FMemOpFP.range_locset.
    destruct peq;subst;try congruence.
    destruct Values.eq_block;try congruence.
    assert(sz + (b0 - sz) = b0). OmegaPlugin.omega.
    rewrite H. clear H.
    destruct (zle sz ofs && zlt ofs b0);auto.

    rewrite Maps.PMap.gsspec in H1.
    unfold FMemOpFP.range_locset.
    destruct peq;subst;try congruence.
    destruct Values.eq_block;try congruence.
    assert(sz + (b0 - sz) = b0). OmegaPlugin.omega.
    rewrite H. clear H.
    destruct (zle sz ofs && zlt ofs b0);auto.
  }
  {
    gmem_unfolds. intros. congruence.
  }
Qed.
Lemma mem_alloc_fleq:
  forall m0 i sz m b0,
    Mem.alloc m0 i sz = (m, b0)->
    Mem.freelist m0 = Mem.freelist m.
Proof. intros;symmetry; eapply Mem.alloc_freelist;eauto.  Qed.
Lemma mem_alloc_eff:
  forall m0 i sz m b0,
    Mem.alloc m0 i sz = (m, b0)->
    LEffect (strip m0)(strip m)(FMemOpFP.alloc_fp m0 i sz) m0.(Mem.freelist).
Proof.
  intros.
  Transparent Mem.alloc.
  unfold Mem.alloc in H.
  inv H.
  unfold strip;simpl.
  constructor.
  constructor.
  {
    (*    apply unchanged_content_equiv. *)
    constructor.
    constructor.
    all: gmem_unfolds;try rewrite Locs.emp_union_locs;intros.
    destruct peq;inv H.
    split;auto.
    intros [];congruence.

    destruct peq;inv H.
    split;intro;auto.
    
    rewrite Maps.PMap.gsspec.
    destruct (peq b (MemAux.get_block (Mem.freelist m0)(Mem.nextblockid m0)));try congruence.

    rewrite Maps.PMap.gsspec in H.
    destruct peq;try congruence.
    
    destruct peq;try congruence.

    intros.
    inv H.
    rewrite Maps.PMap.gso;auto.
  }
  {
    gmem_unfolds.
    constructor.
    split;auto;intro.
    destruct H0;auto.
    inv H. ex_match.

    intros. inv H. ex_match.
    rewrite Maps.PMap.gso;try congruence. split;auto.
  }
  {
    gmem_unfolds.
    intros.
    unfold Locs.belongsto.
    inv H;gmem_unfolds;
    destruct peq;auto;rewrite Maps.PMap.gso in H1;auto.
  }
  {
    gmem_unfolds;auto.
  }
  {
    gmem_unfolds.
    intros. destruct H0;try congruence. subst. 
    unfold MemAux.get_block, MemAux.in_fl. eauto.
  }    
Qed.    
Lemma mem_storev_fleq:
  forall m m' a b c,
    Mem.storev a m b c = Some m'->
    Mem.freelist m = Mem.freelist m'.
Proof.
  unfold Mem.storev;intros;ex_match.
  subst. symmetry. eapply Mem.store_freelist;eauto.
Qed.
Lemma mem_storev_eff:
  forall m m' a b c,
    Mem.storev a m b c = Some m'->
    LEffect (strip m)(strip m') (MemOpFP.storev_fp a b)m.(Mem.freelist).
Proof.
  intros. unfold FMemOpFP.storev_fp.
  unfold Mem.storev in H.
  ex_match;subst.
  unfold FMemOpFP.store_fp.
  Transparent Mem.store.
  unfold Mem.store in H.
  ex_match.
  inv H. unfold strip. simpl.
  constructor.
  constructor.
  {
    constructor. constructor. constructor.
    all: gmem_unfolds;try rewrite Locs.locs_union_emp in *;auto.
    split;auto.
    {
      intros.
      simpl.
      rewrite Maps.PMap.gsspec. destruct peq;subst;auto.
      inv H.
      unfold FMemOpFP.range_locset in H2.
      destruct Values.eq_block;try congruence.
      rewrite Mem.setN_outside. auto.
      destruct zle eqn:?;[|left;Omega.omega].
      destruct zlt eqn:?;inv H2.
      right. rewrite encode_val_length. auto.
      rewrite <-size_chunk_conv.
      auto.
    }
  }
  {
    constructor;simpl.
    {
      unfold unchanged_validity,GMem.valid_block;simpl. split;auto.
    }
    {
      unfold GMem.eq_perm,GMem.perm;simpl. split;auto.
    }
  }
  {
    simpl.
    intros.
    inv H;unfold GMem.perm in *;simpl in *;congruence.
  }
  {
    unfold GMem.valid_block. simpl. auto.
  }
  {
    unfold LocalAlloc.
    unfold GMem.valid_block.
    simpl. intros. congruence.
  }
Qed.

Lemma FreelistEq_mem_fl_wd:
  forall m gm,
    FreelistEq (strip m) gm (Mem.freelist m)->
    gmem_fl_wd gm m.(Mem.freelist) m.(Mem.nextblockid).
Proof.
  destruct m;unfold FreelistEq,GMem.valid_block,strip;simpl.
  constructor;auto.
  unfold MemAux.get_block.
  unfold MemAux.in_fl in H.
  split;intro.
  eapply H in H1;eauto.
  eapply valid_wd;eauto.

  eapply valid_wd in H1;eauto.
  eapply H;eauto.
Qed.
Lemma MemPostemp:
  forall m m',
    MemPost m m' FP.emp.
Proof.
  constructor;gmem_unfolds;Esimpl;try(intros;inv H).
Qed.  
Lemma unchanged_perm_access_eq:
  forall m1 m2 chunk b z p,
    unchanged_perm (belongsto(FMemOpFP.range_locset b z (size_chunk chunk))) (strip m1)(strip m2) ->
    Mem.valid_access m1 chunk b z p ->
    Mem.valid_access m2 chunk b z p.
Proof.
  gmem_unfolds.
  unfold Mem.valid_access, Mem.range_perm.
  unfold FMemOpFP.range_locset,Locs.belongsto,belongsto.
  unfold Locs.belongsto.
  intros;Hsimpl.
  split;auto.
  intros.

  specialize (H0 ofs H3).
  eapply H2;eauto.

  destruct Values.eq_block;try congruence.
  destruct zle,zlt;try omega;auto.
Qed.
Lemma range_locset_belongsto:
  forall b0 i a (b : Values.block) (ofs : Z),
    belongsto
      (FMemOpFP.range_locset b0 i a) b
      ofs <->
    b = b0 /\  i <=ofs < (i + a).
Proof.
  unfold FMemOpFP.range_locset,belongsto,Locs.belongsto;intros.
  destruct Values.eq_block;split;try congruence;intro;Hsimpl;
    try (split;auto;destruct zle,zlt;inv H;auto).
  destruct zle,zlt;try omega;auto.
  congruence.
Qed.
Lemma range_locset_belongsto2:
  forall  i a (b : Values.block) (ofs : Z),
    belongsto
      (FMemOpFP.range_locset b i a) b
      ofs <->
    i <=ofs <(i+a).
Proof.
  unfold FMemOpFP.range_locset,belongsto,Locs.belongsto;intros.
  destruct Values.eq_block;split;try congruence;intro;Hsimpl;
    try (split;auto;destruct zle,zlt;inv H;auto).
  destruct zle,zlt;try omega;auto.
Qed.
Lemma get_eq_getN_eq:
  forall i k p0 p1,
    (forall ofs,i <= ofs < i+ Z.of_nat k-> Maps.ZMap.get ofs p0 = Maps.ZMap.get ofs p1) ->
    Mem.getN k i p0 = Mem.getN k i p1.
Proof.
  intros.

  assert(forall t, (t<=k)%nat-> Mem.getN t (i+Z.of_nat (k-t)) p0 = Mem.getN t (i+Z.of_nat (k-t)) p1).
  induction t;intros;auto.
  assert(t<=k)%nat. omega. Hsimpl.
  simpl.
  assert(i + Z.of_nat (k - S t) + 1 = i + Z.of_nat(k - t)).
  Lia.lia.
  rewrite H2. clear H2.
  rewrite IHt.
  f_equal.
  apply H. Lia.lia.

  specialize (H0 k).
  assert(i + Z.of_nat (k - k) = i). Lia.lia.
  rewrite H1 in H0.
  apply H0. auto.
Qed.
  
Lemma MemPre_mem_loadv_eq:
  forall m m' a b v  (Fleq: FreelistEq (strip m) m' (Mem.freelist m)),
    MemPre (strip m) m' (FMemOpFP.loadv_fp a b) ->
    Mem.loadv a m b = Some v->
    Mem.loadv a (combine m' (Mem.freelist m)(Mem.nextblockid m) (FreelistEq_mem_fl_wd _ _ Fleq)) b = Some v.
Proof.
  unfold Mem.loadv,FMemOpFP.loadv_fp.
  intros. ex_match;subst.
  unfold FMemOpFP.load_fp in *.
  Transparent Mem.load.
  unfold Mem.load in *.
  destruct H. unfold effects in *. simpl in *.
  destruct Mem.valid_access_dec;inv H0.
  assert(Mem.valid_access (combine m' (Mem.freelist m)(Mem.nextblockid m) (FreelistEq_mem_fl_wd m m' Fleq)) a b0 (Integers.Ptrofs.unsigned i) Memperm.Readable).
  destruct ReadMemEq. eapply unchanged_perm_access_eq;eauto.
  destruct Mem.valid_access_dec;try congruence.
  f_equal. f_equal.

  destruct ReadMemEq.
  unfold Mem.valid_access,Mem.range_perm in v.
  destruct v as [v v'].
  assert(forall ofs : Z,
       Integers.Ptrofs.unsigned i <= ofs < Integers.Ptrofs.unsigned i + size_chunk a ->
       Maps.ZMap.get ofs (Maps.PMap.get b0 (GMem.mem_contents m')) =
       Maps.ZMap.get ofs (Maps.PMap.get b0 (Mem.mem_contents m))).
  intros.
  eapply H1.
  eapply range_locset_belongsto2;eauto.
  eapply v in H2 as ?.
  eapply H0;eauto. eapply range_locset_belongsto2;eauto.
  apply perm_order'_'';auto.
  rewrite size_chunk_conv in H2.
  eapply get_eq_getN_eq;eauto.
Qed. 

Lemma MemPre_mem_loadv_eq2:
  forall m m' a b v  (Fleq: FreelistEq (strip m) (strip m') (Mem.freelist m)),
    MemPre (strip m) (strip m') (FMemOpFP.loadv_fp a b) ->
    Mem.loadv a m b = Some v->
    Mem.loadv a m' b = Some v.
Proof.
  unfold Mem.loadv,FMemOpFP.loadv_fp.
  intros. ex_match;subst.
  unfold FMemOpFP.load_fp in *.
  Transparent Mem.load.
  unfold Mem.load in *.
  destruct H. unfold effects in *. simpl in *.
  destruct Mem.valid_access_dec;inv H0.
  assert(Mem.valid_access m' a b0 (Integers.Ptrofs.unsigned i) Memperm.Readable).
  destruct ReadMemEq. eapply unchanged_perm_access_eq;eauto.
  destruct Mem.valid_access_dec;try congruence.
  f_equal. f_equal.

  destruct ReadMemEq.
  unfold Mem.valid_access,Mem.range_perm in v.
  destruct v as [v v'].
  assert(forall ofs : Z,
       Integers.Ptrofs.unsigned i <= ofs < Integers.Ptrofs.unsigned i + size_chunk a ->
       Maps.ZMap.get ofs (Maps.PMap.get b0 (Mem.mem_contents m')) =
       Maps.ZMap.get ofs (Maps.PMap.get b0 (Mem.mem_contents m))).
  intros.
  eapply H1.
  eapply range_locset_belongsto2;eauto.
  eapply v in H2 as ?.
  eapply H0;eauto. eapply range_locset_belongsto2;eauto.
  apply perm_order'_'';auto.

  rewrite size_chunk_conv in H2.
  eapply get_eq_getN_eq;eauto.
Qed. 


Lemma MemPost_effect_emp:
  forall m m' fp,
    Locs.eq (effects fp) Locs.emp ->
    MemPost m m' fp.
Proof.
  intros.
  constructor;gmem_unfolds;Esimpl;intros;Locs.unfolds;inv H0;try congruence.
Qed.
Lemma loadv_fp_emp_effects:
  forall a b,
    Locs.eq (effects (FMemOpFP.loadv_fp a b)) Locs.emp.
Proof.
  intros. unfold effects;Locs.unfolds.
  intros. unfold FMemOpFP.loadv_fp.
  destruct b;auto.
Qed.
Lemma MemPost_loadv_fp:
  forall m m' a b,
    MemPost m m' (FMemOpFP.loadv_fp a b).
Proof.
  intros.
  apply MemPost_effect_emp.
  apply loadv_fp_emp_effects.
Qed.
Lemma LPre_mem_storev_LPost:
  forall m m' m1 a b c
    (mempre:MemPre (strip m) m' (FMemOpFP.storev_fp a b))
    (Fleq:FreelistEq (strip m) m' (Mem.freelist m)),
    Mem.storev a m b c = Some m1 ->
    exists m'1, Mem.storev a (combine m' (Mem.freelist m)(Mem.nextblockid m) (FreelistEq_mem_fl_wd m m' Fleq)) b c = Some m'1 /\ LPost (strip m1)(strip m'1)(FMemOpFP.storev_fp a b)(Mem.freelist m) /\ Mem.freelist m'1 = Mem.freelist m1 /\ Mem.nextblockid m'1 = Mem.nextblockid m1.
Proof.
  unfold Mem.storev,FMemOpFP.storev_fp.
  intros. ex_match.
  inv Hx.
  unfold Mem.store in *. ex_match;inv H.
  unfold FMemOpFP.store_fp in *. simpl in *.
  assert(Mem.valid_access  (combine m' (Mem.freelist m) (Mem.nextblockid m) (FreelistEq_mem_fl_wd m m' Fleq)) a b0 (Integers.Ptrofs.unsigned i) Memperm.Writable).

  unfold Mem.valid_access in *. Hsimpl;Esimpl;auto.
  unfold Mem.range_perm in *.
  intros. specialize (r ofs H) as ?.
  destruct mempre as [_ _ R1].
  unfold effects in R1. simpl in R1. rewrite Locs.locs_union_emp in R1.
  eapply range_locset_belongsto2 in H as ?.
  eapply R1 in H1.  eapply H1 in H0;eauto.

  destruct (Mem.valid_access_dec(combine m' (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)) a b0 (Integers.Ptrofs.unsigned i));try congruence.

  eexists;split;eauto.
  unfold strip. simpl. Esimpl;auto.
  constructor;unfold FreelistEq in *;gmem_unfolds;auto.

  constructor. constructor. 
  all: gmem_unfolds;simpl;try rewrite Locs.locs_union_emp in *;intros.

  + apply range_locset_belongsto in H0 as [];subst.
    assert(Mem.valid_block (combine m' (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)) b0).
    eauto with mem.
    assert(Mem.valid_block m b0). eauto with mem.
    split;auto.
  + apply range_locset_belongsto in H0 as [];subst.
    destruct mempre as [_ _ ?].
    unfold effects in *. simpl in *. rewrite Locs.locs_union_emp in *.
    eapply range_locset_belongsto2 in H1 as ?.
    eapply EffectPermEqPre in H0;eauto.

  + destruct mempre as [_ _ ?].
    unfold effects in *;simpl in *;rewrite Locs.locs_union_emp in *.
    apply range_locset_belongsto in H0 as [];subst.
    do 2 rewrite Maps.PMap.gss.
    destruct H2.
    eapply setN_geteq2;eauto.
    rewrite encode_val_length,<-size_chunk_conv.
    auto.
Qed.
Lemma LPre_mem_storev_LPost2:
  forall m m' m1 a b c
    (mempre:MemPre (strip m) (strip m') (FMemOpFP.storev_fp a b))
    (Fleq:FreelistEq (strip m) (strip m') (Mem.freelist m)),
    Mem.freelist m = Mem.freelist m'->
    Mem.nextblockid m = Mem.nextblockid m'->
    Mem.storev a m b c = Some m1 ->
    exists m'1, Mem.storev a m' b c = Some m'1 /\ LPost (strip m1)(strip m'1)(FMemOpFP.storev_fp a b)(Mem.freelist m) /\ Mem.freelist m'1 = Mem.freelist m1 /\ Mem.nextblockid m'1 = Mem.nextblockid m1.
Proof.
  intros.
  eapply LPre_mem_storev_LPost with(Fleq:=Fleq) in H1;eauto.
  Hsimpl.
  enough(combine (strip m') (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m (strip m') Fleq) = m').
  Esimpl;eauto. rewrite <- H5;auto.

  pose proof combine_refl m'.
  rewrite H5.
  erewrite combine_equiv2;eauto.
Qed.  
  
Lemma unchanged_perm_cmp:
  forall m m' b i,
    unchanged_perm (belongsto (FP.cmps (FMemOpFP.weak_valid_pointer_fp m b i)))(strip m)(strip m')->
    Mem.valid_pointer m b i = Mem.valid_pointer m' b i.
Proof.
  unfold FMemOpFP.weak_valid_pointer_fp;intros.
  unfold Mem.valid_pointer in *.
  destruct Mem.perm_dec,Mem.perm_dec;auto;simpl in *;eapply H in p;eauto;try contradiction; unfold belongsto;Locs.unfolds; unfold FMemOpFP.range_locset;destruct Values.eq_block;auto;destruct zle,zlt;auto;try omega.
Qed.
Lemma unchanged_perm_cmp2:
  forall m m' b i,
    unchanged_perm (belongsto  (FP.cmps (FMemOpFP.weak_valid_pointer_fp m b i)))(strip m)(strip m')->
    Mem.valid_pointer m b i = false ->
    Mem.valid_pointer m b (i-1) = Mem.valid_pointer m' b (i-1).
Proof.
  unfold FMemOpFP.weak_valid_pointer_fp;intros.
  unfold Mem.valid_pointer in *.
  destruct H as [_ ?].
  destruct Mem.perm_dec,Mem.perm_dec,Mem.perm_dec;simpl in *;try congruence.
  eapply H in p;eauto.
  unfold GMem.perm,strip in p. simpl in p.
  contradiction.

  unfold belongsto,FMemOpFP.range_locset;Locs.unfolds.
  destruct Values.eq_block;try congruence.
  destruct zle,zlt;try omega;auto.

  contradict n0.
  eapply H in p;eauto.

  unfold belongsto,FMemOpFP.range_locset;Locs.unfolds.
  destruct Values.eq_block;try congruence.
  destruct zle,zlt;try omega;auto.
Qed.  
Lemma unchanged_perm_cmp_valid_pointer:
   forall m m' b i,
     unchanged_perm (belongsto (FP.cmps (FMemOpFP.weak_valid_pointer_fp m b i)))(strip m)(strip m')->
     (Mem.valid_pointer m b i|| Mem.valid_pointer m b (i - 1)) =   (Mem.valid_pointer m' b i|| Mem.valid_pointer m' b (i - 1)).
Proof.
  intros. eapply unchanged_perm_cmp in H as ?.
  rewrite H0.
  destruct (Mem.valid_pointer m' b i) eqn:?;auto;simpl.
  eapply unchanged_perm_cmp2 in H0;eauto.
Qed.
Lemma unchanged_perm_range_locset_1_valid_pointer:
  forall m m' b i,
    unchanged_perm (belongsto (FMemOpFP.range_locset b i 1))(strip m)(strip m')->
    Mem.valid_pointer m b i = Mem.valid_pointer m' b i.
Proof.
  unfold Mem.valid_pointer, FMemOpFP.range_locset.
  destruct 1 as [_ ?].
  destruct Mem.perm_dec,Mem.perm_dec;auto.
  contradict n. eapply H;eauto.
  unfold belongsto;Locs.unfolds. destruct Values.eq_block;auto.
  destruct zle,zlt;try omega;auto.
  contradict n. eapply H;eauto.
  unfold belongsto;Locs.unfolds. destruct Values.eq_block;auto.
  destruct zle,zlt;try omega;auto.
Qed.
Lemma union_refl_eq:  forall l, Locs.union l l = l.  intros;eapply Locs.locs_eq. eapply Locs.union_refl. Defined.
Lemma unchanged_perm_split:
  forall l1 l2 m m',
    unchanged_perm (belongsto (Locs.union l1 l2)) m m'->
    unchanged_perm (belongsto l1) m m' /\ unchanged_perm (belongsto l2) m m'.
Proof.
  intros.
  split.
  all: eapply unchanged_perm_implies;try apply H;unfold belongsto;Locs.unfolds;intros;auto with bool.
Qed.
Lemma cmps_union:
  forall fp1 fp2,
    FP.cmps (FP.union fp1 fp2) = Locs.union (FP.cmps fp1)(FP.cmps fp2).
Proof.  destruct fp1,fp2;unfold FP.union;simpl;auto. Qed.
Ltac cmpu_bool_destruct_int_fp:=
  try destruct Integers.Int.eq eqn:?;try apply Locs.union_refl;eauto;
  try destruct Values.eq_block eqn:?;try apply Locs.union_refl;eauto;
  try destruct Values.Val.cmp_different_blocks eqn:?;try apply Locs.union_refl;eauto;
  try unfold FMemOpFP.weak_valid_pointer_fp ;try unfold FMemOpFP.valid_pointer_fp;eauto;try destruct Mem.valid_pointer eqn:?;try apply Locs.union_refl;eauto.
Ltac cmpu_bool_destruct_b_fp:=
  try destruct Values.eq_block;try apply Locs.union_refl;
  try unfold FMemOpFP.weak_valid_pointer_fp;try unfold FMemOpFP.valid_pointer_fp;
  try destruct Mem.valid_pointer eqn:?;try apply Locs.union_refl;auto.
Lemma MemPre_cmpu_valid_pointer_ceq:
  forall m m' i j,
    MemPre (strip m)(strip m')(Cop_fp.cmpu_bool_fp_total m Integers.Ceq i j)->
    Values.Val.cmpu_bool (Mem.valid_pointer m) Integers.Ceq i j =  Values.Val.cmpu_bool (Mem.valid_pointer m') Integers.Ceq i j.
Proof.
  unfold compare_ints_fp.
  destruct 1 as [_ ? _];simpl in *.
  unfold Values.Val.cmpu_bool,Cop_fp.cmpu_bool_fp_total in *.
  ex_match2.

  all :try eapply unchanged_perm_cmp_valid_pointer in CmpMemPermExists;try  rewrite CmpMemPermExists in *; try match goal with H: true && ?a = true |- _ => destruct a eqn:?;try discriminate end.
  all :rewrite cmps_union in CmpMemPermExists.
  all : try do 2 erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx3;try rewrite Hx3 in Hx4;try discriminate.
  all : try apply unchanged_perm_split in CmpMemPermExists as [];auto.
  all : do 2 erewrite unchanged_perm_range_locset_1_valid_pointer with(m:=m)(m':=m') in Hx4;try rewrite Hx4 in Hx5;inv Hx5;eauto.
Qed.
Lemma MemPre_cmpu_valid_pointer_eq:
  forall m m' c i j,
    c = Integers.Clt \/ c = Integers.Ceq->
    MemPre (strip m)(strip m')(compare_ints_fp i j m)->
    Values.Val.cmpu_bool (Mem.valid_pointer m) c i j =  Values.Val.cmpu_bool (Mem.valid_pointer m') c i j.
Proof.
  unfold compare_ints_fp.
  destruct 1;subst;destruct 1 as [_ ? _];simpl in *;unfold Val.cmpu_bool,Cop_fp.cmpu_bool_fp_total in *;ex_match2.
  
  do 2 erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx3;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.

  do 2 erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx3;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.

  
  erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx5;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.

  erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx5;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.

  erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx5;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.

  erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx5;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.
  do 2 erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx3;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.

  do 2 erewrite unchanged_perm_cmp_valid_pointer with(m:=m)(m':=m') in Hx3;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try apply Locs.union_incr;rewrite FP.union_comm_eq; apply Locs.union_incr.

  do 2 erewrite unchanged_perm_range_locset_1_valid_pointer with(m:=m)(m':=m') in Hx5;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try rewrite Locs.locs_union_emp;try apply Locs.union_incr;rewrite FP.union_comm_eq;try apply Locs.union_incr.

  do 2 erewrite unchanged_perm_range_locset_1_valid_pointer with(m:=m)(m':=m') in Hx5;eauto;try congruence;eapply unchanged_perm_implies;try apply CmpMemPermExists;eapply belongsto_subset;repeat rewrite union_refl_eq;try rewrite Locs.locs_union_emp;try apply Locs.union_incr;rewrite FP.union_comm_eq;try apply Locs.union_incr.


Qed.


Lemma range_locset_union:
  forall b o i1 i2,
    Z.lt 0 i2->
    Z.lt 0 i1->
    Locs.union (FMemOpFP.range_locset b o i1)(FMemOpFP.range_locset b (Z.add o i1) i2) =
    FMemOpFP.range_locset b o (Z.add i1 i2).
Proof.
  intros. apply Locs.locs_eq.
  Locs.unfolds.
  unfold FMemOpFP.range_locset.
  intros.
  destruct Values.eq_block;auto.
  subst.
  repeat destruct zle;repeat destruct zlt;auto;try omega.
Qed.

Lemma fp_union_refl_eq:
  forall fp,
    FP.union fp fp = fp.
Proof.
  destruct fp. unfold FP.union.
  simpl.
  f_equal;apply union_refl_eq.
Qed.

Lemma MemPre_mem_alloc_LPost:
  forall m m0 sz m' b(Memeq:MemPre (strip m) m0 (FMemOpFP.alloc_fp m 0 sz))(Fleq: FreelistEq (strip m) m0 (Mem.freelist m)),
    Mem.alloc m 0 sz = (m',b)->
    exists m1,
      Mem.alloc (combine m0 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq)) 0 sz = (m1,b) /\ FMemOpFP.alloc_fp m 0 sz = FMemOpFP.alloc_fp  (combine m0 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq)) 0 sz  /\ LPost (strip m')(strip m1)(FMemOpFP.alloc_fp m 0 sz)(Mem.freelist m).
Proof.
  intros. remember  (combine m0 (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq)) as fm.
  pose proof fmem_alloc_exists fm 0 sz.
  Hsimpl.
  gmem_unfolds.
  inv H;inv H0.
  Transparent Mem.alloc.
  Esimpl;unfold Mem.alloc;eauto.
  simpl.
  constructor;auto.
  {
    constructor;[constructor|];gmem_unfolds;rewrite Locs.emp_union_locs.
    intros. inv H. destruct peq;try congruence.
    split;auto.

    intros. inv H.
    destruct peq;try congruence.
    rewrite e. do 2 rewrite Maps.PMap.gss.
    split;intro;auto.

    intros.
    inv H.
    destruct peq;try congruence.
    rewrite e. do 2 rewrite Maps.PMap.gss. auto.
  }
  {
    unfold FreelistEq in *.
    intros.
    gmem_unfolds.
    eapply Fleq in H.
    split;intros;destruct H0;auto;apply H in H0;auto.
  }
Qed.

Lemma MemPre_range_perm_eq:
  forall m b ofs sz p,
    Mem.range_perm m b ofs sz Memperm.Cur p->
    forall m',
      MemPre (strip m)(strip m')(FMemOpFP.free_fp b ofs sz)->
      Mem.range_perm m' b ofs sz Memperm.Cur p.
Proof.
  unfold Mem.range_perm,FMemOpFP.free_fp;intros.
  specialize (H _ H1).
  destruct H0 as [_ _ ?]. simpl in *.
  unfold GMem.perm,strip in EffectPermEqPre.
  unfold Mem.perm in *.
  simpl in *.
  eapply EffectPermEqPre;eauto.

  unfold effects. simpl.
  rewrite Locs.emp_union_locs.
  unfold belongsto,FMemOpFP.range_locset;Locs.unfolds.
  ex_match2.
  destruct zle,zlt;auto;try omega.
Qed.
Lemma MemPre_dep_range_perm_eq:
  forall m m' fp b sz a p,
    MemPre (strip m)(strip m')fp->
    Locs.subset (FMemOpFP.range_locset b 0 sz)(depends fp) -> 
    Mem.range_perm m b 0 sz a p->
    Mem.range_perm m' b 0 sz a p.
Proof.
  unfold Mem.range_perm. destruct fp;simpl;intros.
  apply H1 in H2 as ?.
  Locs.unfolds.
  assert(FMemOpFP.range_locset b 0 sz b ofs = true).
  unfold FMemOpFP.range_locset. destruct Values.eq_block;auto. destruct zle,zlt;auto;omega.
  specialize (H0 _ _ H4).
  unfold depends in H0. simpl in H0.
  Locs.unfolds.
  assert(cmps b ofs = true \/ reads b ofs = true).
  destruct cmps,reads;auto;inv H0.
  destruct H5.
  destruct H as [_ ? _]. eapply CmpMemPermExists;eauto.
  destruct H as [? _ _]. eapply ReadMemEq;eauto.
Qed.
    
Lemma MemPre_eff_range_perm_eq:
  forall m m' fp b sz a p,
    MemPre (strip m)(strip m')fp->
    Locs.subset (FMemOpFP.range_locset b 0 sz)(effects fp) -> 
    Mem.range_perm m b 0 sz a p->
    Mem.range_perm m' b 0 sz a p.
Proof.
  destruct fp;simpl;intros.
  destruct H as [_ _ ?].
  unfold effects in *;simpl in *.
  unfold Mem.range_perm in *.
  intros.
  specialize (H1 _ H).
  eapply EffectPermEqPre;eauto.
  unfold belongsto,Locs.belongsto. erewrite <- H0;eauto.
  unfold FMemOpFP.range_locset. Locs.unfolds.
  destruct Values.eq_block;auto.
  destruct zle,zlt;auto;try omega.
Qed.

Lemma LPre_mem_free_LPost:
  forall m m0 b i sz m' (Memeq:MemPre (strip m) m0 (FMemOpFP.free_fp b i sz))(Fleq:FreelistEq(strip m) m0 (Mem.freelist m)),
    Mem.free m b i sz = Some m'->
    exists m0',
      Mem.free (combine m0 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq)) b i sz = Some m0' /\ LPost (strip m0')(strip m')(FMemOpFP.free_fp b i sz)(Mem.freelist m) /\ Mem.freelist m0' = Mem.freelist m' /\ Mem.nextblockid m0' = Mem.nextblockid m'.
Proof.
  Local Transparent  Mem.free.
  unfold Mem.free,FMemOpFP.free_fp;intros.
  ex_match. inv H. clear Hx.
  remember (combine m0 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq)) as m1.
  assert(strip m1 = m0).
  rewrite Heqm1. rewrite strip_combine. auto.
  rewrite <-H in *.
  eapply MemPre_range_perm_eq in r as r2;eauto.
  destruct Mem.range_perm_dec ;try congruence.

  eexists. split. eauto.
  simpl. Esimpl;eauto;try(rewrite Heqm1;auto;fail).
  constructor.
  {
    destruct Memeq.
    constructor;[constructor|]; unfold strip,Mem.unchecked_free,effects;simpl;gmem_unfolds;eauto;intros.
    rewrite Heqm1;simpl. rewrite Locs.emp_union_locs in H0.
    apply range_locset_belongsto in H0 as [].
    rewrite H0 in *;clear H0.
    rewrite Zplus_minus in H1.
    apply r in H1 as ?. apply r2 in H1 as ?.
    apply Mem.perm_valid_block in H0.
    apply Mem.perm_valid_block in H2.
    rewrite Heqm1 in H2. unfold Mem.valid_block in  *. simpl in H2.
    split;auto.

    rewrite Locs.emp_union_locs in H0. apply range_locset_belongsto in H0 as [].
    rewrite H0,Maps.PMap.gss,Maps.PMap.gss.
    destruct zle,zlt;try omega;simpl. split;auto.

    rewrite Locs.emp_union_locs in H0. apply range_locset_belongsto in H0 as [].
    rewrite H0,Maps.PMap.gss in H1.
    destruct zle,zlt;try omega;simpl in H1. contradiction.
  }
  {
    rewrite Heqm1.
    unfold strip,Mem.unchecked_free,FreelistEq in *;gmem_unfolds; simpl in *.
    intros.
    eapply Fleq in H0;eauto.
    split;intro;apply H0;auto.
  }
Qed.

Lemma LPre_mem_free_LPost2:
  forall m m0 b i sz m' (Memeq:MemPre (strip m) (strip m0) (FMemOpFP.free_fp b i sz))(Fleq:FreelistEq(strip m) (strip m0) (Mem.freelist m)),
    Mem.free m b i sz = Some m'->
    exists m0',
      Mem.free m0 b i sz = Some m0' /\ LPost (strip m0')(strip m')(FMemOpFP.free_fp b i sz)(Mem.freelist m).
Proof.
  Local Transparent  Mem.free.
  unfold Mem.free,FMemOpFP.free_fp;intros.
  ex_match. inv H. clear Hx.
  eapply MemPre_range_perm_eq in r as r2;eauto.
  destruct Mem.range_perm_dec ;try congruence.

  eexists. split. eauto.
  simpl. Esimpl;eauto;try(rewrite Heqm1;auto;fail).
  constructor.
  {
    destruct Memeq.
    constructor;[constructor|]; unfold strip,Mem.unchecked_free,effects;simpl;gmem_unfolds;eauto;intros.
    rewrite Locs.emp_union_locs in *.
    apply range_locset_belongsto in H as [].
    rewrite H in *;clear H.
    rewrite Zplus_minus in H0.
    apply r in H0 as ?. apply r2 in H0 as ?.
    apply Mem.perm_valid_block in H.
    apply Mem.perm_valid_block in H1.
    unfold Mem.valid_block in  *. 
    split;auto.

    rewrite Locs.emp_union_locs in H. apply range_locset_belongsto in H as [].
    rewrite H,Maps.PMap.gss,Maps.PMap.gss.
    destruct zle,zlt;try omega;simpl. split;auto.

    rewrite Locs.emp_union_locs in H. apply range_locset_belongsto in H as [].
    rewrite H,Maps.PMap.gss in H0.
    destruct zle,zlt;try omega;simpl in H0. contradiction.
  }
  {
    unfold strip,Mem.unchecked_free,FreelistEq in *;gmem_unfolds; simpl in *.
    intros.
    eapply Fleq in H;eauto.
    split;intro;apply H;auto.
  }
Qed.

Lemma cmpu_bool_fp_effemp0:
  forall m c v i,
    Locs.eq (effects (of_optfp (Cop_fp.cmpu_bool_fp m c v i))) Locs.emp.
Proof.
  unfold Cop_fp.cmpu_bool_fp.
  intros.
  destruct v,i;simpl;unfold FP.emp,effects;simpl;try apply Locs.union_refl;destruct Archi.ptr64;simpl;try apply Locs.union_refl.
  cmpu_bool_destruct_int_fp.
  cmpu_bool_destruct_int_fp.
  cmpu_bool_destruct_b_fp;simpl;destruct ( Mem.valid_pointer m b0 (Integers.Ptrofs.unsigned i));simpl;try rewrite Locs.emp_union_locs;try apply Locs.union_refl; try destruct Values.Val.cmp_different_blocks;try apply Locs.union_refl.
Qed.

Lemma cmpu_bool_fp_effemp:
  forall m c v i,
    Locs.eq (effects (Cop_fp.cmpu_bool_fp_total m c v i)) Locs.emp.
Proof.
  unfold Cop_fp.cmpu_bool_fp.
  intros.
  destruct v,i;simpl;unfold FP.emp,effects;simpl;try apply Locs.union_refl;destruct Archi.ptr64;simpl;try apply Locs.union_refl.
  cmpu_bool_destruct_int_fp.
  cmpu_bool_destruct_int_fp.
  cmpu_bool_destruct_b_fp;simpl;destruct ( Mem.valid_pointer m b0 (Integers.Ptrofs.unsigned i));simpl;try rewrite Locs.emp_union_locs;try apply Locs.union_refl; try destruct Values.Val.cmp_different_blocks;try apply Locs.union_refl.
Qed.
Lemma LPre_weak_valid_pointer_fp_eq2:
  forall m m' c v (Memeq:MemPre (strip m) (strip m') (FMemOpFP.weak_valid_pointer_fp m c v))(Fleq:FreelistEq (strip m) (strip m') (Mem.freelist m)),
    FMemOpFP.weak_valid_pointer_fp m' c v = FMemOpFP.weak_valid_pointer_fp m c v.
Proof.
  unfold FMemOpFP.weak_valid_pointer_fp.
  intros.
  ex_match2.
  all :erewrite unchanged_perm_cmp,Hx0 in Hx;inv Hx.
  all :destruct Memeq;auto; unfold FMemOpFP.weak_valid_pointer_fp;rewrite H0; auto.
Qed.
Lemma LPre_weak_valid_pointer_fp_eq:
  forall m m' c v (Memeq:MemPre (strip m) m' (FMemOpFP.weak_valid_pointer_fp m c v))(Fleq:FreelistEq (strip m) m' (Mem.freelist m)),
    FMemOpFP.weak_valid_pointer_fp (combine m' (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)) c v = FMemOpFP.weak_valid_pointer_fp m c v.
Proof.
  unfold FMemOpFP.weak_valid_pointer_fp.
  intros.
  ex_match2.
  all :erewrite unchanged_perm_cmp,Hx0 in Hx;inv Hx.
  all :rewrite strip_combine.
  all :destruct Memeq;auto; unfold FMemOpFP.weak_valid_pointer_fp;rewrite H0; auto.
Qed.
Lemma range_locset_expend1_subset:
  forall b i ,
    Locs.subset (FMemOpFP.range_locset b i 1)(FMemOpFP.range_locset b (i - 1)2).
Proof.
  unfold FMemOpFP.range_locset.
  Locs.unfolds.
  intros.
  ex_match2.
  subst.
  destruct zle,zlt,zle,zlt;auto;try omega.
Qed.
Lemma locs_subset_union:
  forall l l1 l2,
    Locs.subset l l1 \/ Locs.subset l l2->
    Locs.subset l (Locs.union l1 l2 ).
Proof.
  Locs.unfolds.
  intros.
  destruct H;eapply H in H0;eauto;rewrite H0;auto with bool.
Qed.
Ltac solv_locs:=
  match goal with
  | H:?q |- ?q => assumption
  | H:_|- Locs.subset ?a ?a => apply Locs.subset_refl
  | H:_|- Locs.subset _ (Locs.union _ _) => apply locs_subset_union;try (left;solv_locs;fail);try(right;solv_locs;fail)
  | H:_|- Locs.subset (FMemOpFP.range_locset ?b ?i 1)(FMemOpFP.range_locset ?b (?i - 1) 2) => eapply range_locset_expend1_subset ;eauto
  end.
Lemma MemPre_split:
  forall m m' fp1 fp2,
    MemPre m m' (FP.union fp1 fp2)->
    MemPre m m' fp1 /\ MemPre m m' fp2.
Proof. split;eapply MemPre_subset;eauto;[|rewrite FP.union_comm_eq];apply FP.union_subset. Qed.
Lemma LPre_cmpu_bool_fp_total_eq:
  forall m m' c v i (Memeq:MemPre (strip m) m' (Cop_fp.cmpu_bool_fp_total m c v i))(Fleq:FreelistEq (strip m) m' (Mem.freelist m)),
    Cop_fp.cmpu_bool_fp_total(combine m' (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)) c v  i = Cop_fp.cmpu_bool_fp_total m c v i.
Proof.
  intros.
  unfold Cop_fp.cmpu_bool_fp_total in *.
  ex_match2.
  all : unfold FMemOpFP.weak_valid_pointer_fp.
  
  1 , 2 :ex_match2;try erewrite unchanged_perm_cmp,Hx5 in Hx4;inv Hx4;try rewrite strip_combine; try (inversion Memeq;auto; rewrite LPre_weak_valid_pointer_fp_eq;auto;apply unchanged_perm_comm;auto).
  apply MemPre_split in Memeq as [[ _ eq1 _][_ eq2 _]];subst.
  
  erewrite unchanged_perm_cmp with(m:=m)(m':=(combine m' (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq))).
  
  destruct (Mem.valid_pointer
        (combine m' (Mem.freelist m) (Mem.nextblockid m)
                 (FreelistEq_mem_fl_wd m m' Fleq)) b0 (Integers.Ptrofs.unsigned i0));eauto;erewrite unchanged_perm_cmp with(m:=m)(m':=(combine m' (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)));ex_match2.

  all: rewrite strip_combine;eauto.
Qed.

Lemma LPre_cmpu_bool_fp_eq:
  forall m m' c v i (Memeq:MemPre (strip m) m' (of_optfp (Cop_fp.cmpu_bool_fp m c v i)))(Fleq:FreelistEq (strip m) m' (Mem.freelist m)),
    Cop_fp.cmpu_bool_fp(combine m' (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)) c v  i = Cop_fp.cmpu_bool_fp m c v i.
Proof.
  intros.
  unfold Cop_fp.cmpu_bool_fp in *.
  destruct v,i;auto;simpl;destruct Archi.ptr64;auto.
  cmpu_bool_destruct_int_fp;try(erewrite unchanged_perm_cmp,Heqb1;auto;rewrite strip_combine;destruct Memeq;auto).
  cmpu_bool_destruct_int_fp;try(erewrite unchanged_perm_cmp,Heqb1;auto;rewrite strip_combine;destruct Memeq;auto).
  cmpu_bool_destruct_b_fp;simpl;subst;destruct ( Mem.valid_pointer (combine m' (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)) b0 (Integers.Ptrofs.unsigned i)) eqn:?;auto;try(erewrite unchanged_perm_cmp,Heqb1;eauto;[erewrite unchanged_perm_cmp,Heqb;eauto|];try(rewrite strip_combine;eapply MemPre_subset in Memeq as [];eauto;try(apply FP.union_subset);try(rewrite FP.union_comm_eq;apply FP.union_subset))).
Qed.
(*
Lemma fmem_eq_MemPre:
  forall m m' fp,
    fmem_eq m m'->
    MemPre (strip m)(strip m') fp.
Proof.
  destruct 1.
  Hsimpl.
  destruct H.
  constructor.
  apply unchanged_content_equiv.
  constructor;intros;auto.
  unfold GMem.perm;unfold strip;simpl.
  erewrite eq_access_eq_perm;eauto. split;auto.
  symmetry. eapply eq_contents;eauto.
  
  constructor. unfold unchanged_validity;auto.
  unfold GMem.eq_perm,GMem.perm;unfold strip;simpl;intros.
  erewrite eq_access_eq_perm;eauto. split;auto.
  intros.  unfold GMem.perm;unfold strip;simpl.
  erewrite eq_access_eq_perm;eauto. split;auto.
Qed.  

  *)