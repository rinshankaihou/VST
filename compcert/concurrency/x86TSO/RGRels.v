(** This file defines the type of [I], [R], [G], and some properties of them *)
Require Import Coqlib Maps Values GlobDefs GMemory TSOMem Footprint FPLemmas MemAux.

(** The type of [I] *)
Definition stInv : Type := gmem -> tsomem -> Prop.
(** The type of [R], [G] *)
Definition stRel : Type := gmem -> tsomem -> gmem -> tsomem -> Prop.
Definition Sta (I: stInv) (R: stRel) : Prop :=
  forall gm tm gm' tm',
    I gm tm ->
    R gm tm gm' tm' ->
    I gm' tm'.
Definition Implies (G: stRel) (R: stRel) : Prop :=
  forall gm tm gm' tm',
    G gm tm gm' tm' ->
    R gm tm gm' tm'.
Definition Implies' (I : stInv) (G: stRel) (R: stRel) : Prop :=
  forall gm tm gm' tm',
    I gm tm -> G gm tm gm' tm' ->
    R gm tm gm' tm'.

(* unbuffer guarantee ? .. *)
Definition G_ub : stRel :=
  fun gm tm gm' tm' =>
    gm = gm' /\ (exists t, unbuffer tm t = Some tm').

Lemma unbuffer_G_ub:
  forall gm tm t tm',
    unbuffer tm t = Some tm' ->
    G_ub gm tm gm tm'.
Proof.
  intros.
  unfold G_ub.
  eauto.
Qed.

Definition UBSta (I: stInv) : Prop :=
  forall gm tm gm' tm',
    I gm tm ->
    G_ub gm tm gm' tm' ->
    I gm tm'.

Definition UBImplies (I: stInv) (R: stRel) : Prop :=
  forall gm tm gm' tm',
    I gm tm ->
    G_ub gm tm gm' tm' ->
    R gm tm gm' tm'.


Definition rel_tm_gm_vb (M : gmem) (tm : tsomem) (fl : freelist) (t : tid) :=
  forall n b gm, get_block fl n = b ->
            apply_buffer (tso_buffers tm t) (memory tm) = Some gm ->
            In b (GMem.validblocks gm) <-> In b (GMem.validblocks M).

Definition tm_alloc_not_fl (tm : tsomem) (fl : freelist) (t : tid) :=
  forall t' blk n lo hi,
    t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
    blk <> get_block fl n.

(** [obj_mem] is a proposition to judge whether an location belongs to 
object memory. Location in object memory only has max permission. This definition 
corresponds to [objM] defined in Figure 20 on page 20 
in submission #115 supplement text *)  
Definition obj_mem (m: gmem) (b: block) (ofs: Z) : Prop :=
  (PMap.get b (GMem.mem_access m)) ofs Memperm.Max <> None /\
  (PMap.get b (GMem.mem_access m)) ofs Memperm.Cur = None.

(** [client_mem] is a proposition to judge whether an location belongs to 
client memory. *)
Definition client_mem (m: gmem) (b: block) (ofs: Z) : Prop :=
  (GMem.mem_access m) !! b ofs Memperm.Cur <> None /\
  (GMem.mem_access m) !! b ofs Memperm.Max <> None.

Definition unused_mem (m: gmem) (b: block) (ofs: Z) : Prop :=
  (GMem.mem_access m) !! b ofs Memperm.Max = None.

(** We define [eq_on_loc] to describle the memory relation between the location 
in gmem of high-level x86SC program and the same one in gmem of low-level x86TSO 
program after applying thread buffer *)
Record eq_on_loc (b: block) (ofs: Z) (m tm: gmem) : Prop :=
  {
    (* [valid_block] equality *)
    eq_loc_validity:
      GMem.valid_block m b <-> GMem.valid_block tm b;
    (* [memory permission] equality *)
    eq_loc_perm:
      forall k, (GMem.mem_access m) !! b ofs k = (GMem.mem_access tm) !! b ofs k;
    (* [memory content] equality *)
    eq_loc_content:
      ZMap.get ofs ((GMem.mem_contents m) !! b) =
      ZMap.get ofs ((GMem.mem_contents tm) !! b);
  }.


(* sep object client block *)
Definition sep_obj_client_block (sm: gmem) : Prop :=
  forall b ofs1 ofs2,
    obj_mem sm b ofs1 ->
    client_mem sm b ofs2 ->
    False.

Inductive obj_fp (gm gm': gmem) (fp: FP.t) : Prop :=
| obj_emp_fp:
    fp = FP.emp ->
    obj_fp gm gm' fp
| obj_valid_block_fp:
    forall (H_object_valid_block_fp: forall b ofs,
          Locs.belongsto (FP.locs fp) b ofs ->
          obj_mem gm b ofs \/ exists ofs', obj_mem gm b ofs'),
      obj_fp gm gm' fp
| obj_alloc_fp:
    forall (H_object_alloc_fp: forall b ofs,
          Locs.belongsto (FP.locs fp) b ofs ->
          ~ GMem.valid_block gm b /\
          GMem.valid_block gm' b /\
          (forall ofs', obj_mem gm' b ofs' \/ unused_mem gm' b ofs')),
      obj_fp gm gm' fp.

Inductive client_fp (gm gm': gmem) (fp: FP.t) : Prop :=
| client_emp_fp:
    fp = FP.emp ->
    client_fp gm gm' fp
| client_valid_block_fp:
    forall (H_client_valid_block_fp: forall b ofs,
          Locs.belongsto (FP.locs fp) b ofs ->
          client_mem gm b ofs \/ exists ofs', client_mem gm b ofs' ),
      client_fp gm gm' fp
| client_alloc_fp:
    forall (H_client_alloc_fp: forall b ofs,
          Locs.belongsto (FP.locs fp) b ofs ->
          ~ GMem.valid_block gm b /\
          GMem.valid_block gm' b /\
          (forall ofs', client_mem gm' b ofs' \/ unused_mem gm' b ofs')),
      client_fp gm gm' fp.

Inductive client_fp' (gm: gmem) (fp: FP.t) : Prop :=
| client_emp_fp' : fp = FP.emp -> client_fp' gm fp
| client_valid_block_fp' :
    forall (H_client_valid_block_fp: forall b ofs,
          Locs.belongsto (FP.locs fp) b ofs ->
          client_mem gm b ofs \/ exists ofs', client_mem gm b ofs'),
    client_fp' gm fp
| client_alloc_fp' :
    (forall (b : block) (ofs : Z), Locs.belongsto (FP.locs fp) b ofs -> ~ GMem.valid_block gm b) ->
    client_fp' gm fp.

Lemma client_fp_client_fp':
  forall gm gm' fp, client_fp gm gm' fp -> client_fp' gm fp.
Proof.
  clear. intros. inv H.
  eapply client_emp_fp'; auto.
  eapply client_valid_block_fp'; auto.
  eapply client_alloc_fp'. intros. apply H_client_alloc_fp in H. intuition.
Qed.

Lemma obj_mem_valid:
  forall sm b ofs, obj_mem sm b ofs -> GMem.valid_block sm b.
Proof.
  clear. intros. inv H.
  destruct (in_dec peq b (GMem.validblocks sm)); auto.
  eapply GMem.invalid_noaccess in n. rewrite n in H0. contradiction.
Qed.

Lemma client_mem_valid:
  forall sm b ofs, client_mem sm b ofs -> GMem.valid_block sm b.
Proof.
  unfold client_mem. intros. 
  destruct (in_dec peq b (GMem.validblocks sm)); auto.
  eapply GMem.invalid_noaccess in n. rewrite n in H. intuition.
Qed.  

Lemma unused_mem_client_mem_excluded:
  forall sm b ofs,
    unused_mem sm b ofs ->
    client_mem sm b ofs ->
    False.
Proof. unfold unused_mem, client_mem. intros. intuition. Qed.

Lemma unused_mem_object_mem_excluded:
  forall sm b ofs,
    unused_mem sm b ofs ->
    obj_mem sm b ofs ->
    False.
Proof. unfold unused_mem, obj_mem. intros. intuition. Qed.

Lemma valid_unused_mem_forward:
  forall sm sm' b ofs,
    GMem.valid_block sm b ->
    GMem.forward sm sm' ->
    unused_mem sm b ofs ->
    unused_mem sm' b ofs.
Proof.
  unfold unused_mem. intros.
  destruct ((GMem.mem_access sm') !! b ofs Memperm.Max) eqn:A; simpl; auto.
  eapply GMem.alloc_forward in H0; eauto.
  rewrite H1 in H0. inv H0.
  unfold Memperm.perm_order'. rewrite A. apply Memperm.perm_any_N.
Qed.
  
Lemma obj_mem_client_mem_excluded:
  forall sm sm' b ofs,
    GMem.forward sm sm' ->
    obj_mem sm b ofs ->
    client_mem sm' b ofs ->
    False.
Proof.
  clear. intros. exploit obj_mem_valid; eauto. intro. inv H0; inv H1.
  eapply GMem.alloc_forward in H2; eauto. rewrite H4 in H2. auto.
  instantiate (1:=Memperm.Nonempty).
  destruct ((GMem.mem_access sm') !! b ofs Memperm.Cur); simpl; auto.
  apply Memperm.perm_any_N.  
Qed.

Lemma fp_conflict_locs_conflict:
  forall fp1 fp2,
    FP.conflict' fp1 fp2 ->
    exists b ofs,
      Locs.belongsto (FP.locs fp1) b ofs /\
      Locs.belongsto (FP.locs fp2) b ofs.
Proof.
  clear.
  destruct fp1, fp2; intro; inv H; Locs.unfolds; simpl in *;
    unfold FP.locs, FP.ge_cmps, FP.ge_reads, FP.ge_writes in *;
    simpl in *; destruct H0 as (b & ofs & ?); red_boolean_true;
      Locs.unfolds; exists b, ofs; split; auto; red_boolean_true.
Qed.

Lemma smile_emp_fp:
  forall fp, FP.smile fp FP.emp.
Proof.
  clear. intro. 
  constructor; simpl; unfold Locs.smile;
    repeat rewrite Locs.locs_intersect_emp;
    repeat rewrite Locs.locs_intersect_emp_sym;
    auto using Locs.eq_refl.
Qed.

Lemma forward_client_mem':
  forall sm1 sm2 b ofs,
    GMem.forward sm1 sm2 ->
    GMem.valid_block sm1 b ->
    client_mem sm2 b ofs ->
    client_mem sm1 b ofs.
Proof.
  unfold client_mem. intros. destruct H1 as [A B].
  split.
  destruct ((GMem.mem_access sm2) !! b ofs Memperm.Cur) eqn:C; try contradiction.
  exploit GMem.alloc_forward. eauto. eauto. rewrite C. apply Memperm.perm_any_N.
  destruct ((GMem.mem_access sm1) !! b ofs Memperm.Cur) eqn:C'; try contradiction.
  intros; intro; discriminate.
  destruct ((GMem.mem_access sm2) !! b ofs Memperm.Max) eqn:C; try contradiction.
  exploit GMem.alloc_forward. eauto. eauto. rewrite C. apply Memperm.perm_any_N.
  destruct ((GMem.mem_access sm1) !! b ofs Memperm.Max) eqn:C'; try contradiction.
  intros; intro; discriminate.
Qed.
    
Lemma sep_obj_client_block_excluded:
  forall sm1 sm2 b ofs1 ofs2,
    sep_obj_client_block sm1 ->
    GMem.forward sm1 sm2 ->
    obj_mem sm1 b ofs1 ->
    client_mem sm2 b ofs2 ->
    False.
Proof.
  intros sm1 sm2 b ofs1 ofs2 Hsep Hforward Hobj Hclt.
  exploit obj_mem_valid. eauto. intro.
  exploit forward_client_mem'; eauto.
Qed.
  
Lemma obj_fp_forward_client_fp'_smile:
  forall sm1 fp1 sm2 sm3 fp3,
    sep_obj_client_block sm1 ->
    obj_fp sm1 sm2 fp1 ->
    GMem.forward sm1 sm2 ->
    GMem.forward sm2 sm3 ->
    client_fp' sm3 fp3 ->
    FP.smile fp1 fp3.
Proof.
  clear. intros sm1 fp1 sm2 sm3 fp3 Hsep H H0 H1 H2.
  inv H; inv H2; auto using smile_emp_fp, fpsmile_sym;
    apply FP.smile_conflict_compat; intro C;
      apply FP.conflict'_conflict_equiv, fp_conflict_locs_conflict in C;
      destruct C as (b & ofs & C1 & C2).

  apply H_object_valid_block_fp in C1; destruct C1 as [C1|[ofs' C1]];
    apply H_client_valid_block_fp in C2; destruct C2 as [C2|[ofs'' C2]].
  eapply obj_mem_client_mem_excluded; [eapply GMem.forward_trans; [exact H0| exact H1]| eauto | eauto].
  eapply sep_obj_client_block_excluded. eauto. eapply GMem.forward_trans; eauto. eauto. eauto.
  eapply sep_obj_client_block_excluded. eauto. eapply GMem.forward_trans; eauto. eauto. eauto.
  eapply sep_obj_client_block_excluded. eauto. eapply GMem.forward_trans; eauto. eauto. eauto.
  
  eapply H. eauto. eapply GMem.dom_forward. eapply GMem.forward_trans. exact H0. exact H1.
  eapply H_object_valid_block_fp in C1. destruct C1 as [C1|[ofs' C1]]; eapply obj_mem_valid; eauto.

  apply H_client_valid_block_fp in C2; destruct C2 as [C2|[ofs'' C2]];
    apply H_object_alloc_fp in C1; destruct C1 as [Hfresh [Hvalid [C1|C1]]].
  eapply obj_mem_client_mem_excluded; eauto.
  eapply unused_mem_client_mem_excluded. eapply valid_unused_mem_forward. eauto. eauto. eauto. auto.
  eapply obj_mem_client_mem_excluded; eauto.
  eapply unused_mem_client_mem_excluded. eapply valid_unused_mem_forward. eauto. eauto. eauto. auto.

  eapply H. eauto. eapply GMem.dom_forward. exact H1.
  eapply H_object_alloc_fp in C1. destruct C1 as (Hfresh & Hvalid & [Hobj|Hunused]); auto.

  Unshelve. eauto.
Qed.

Lemma client_mem_obj_mem_excluded:
  forall sm1 sm2,
    (forall b ofs, obj_mem sm1 b ofs <-> obj_mem sm2 b ofs) ->
    (forall b ofs, client_mem sm1 b ofs -> obj_mem sm2 b ofs -> False).
Proof.
  clear. intros. apply H in H1. inv H0; inv H1; congruence.
Qed.

Lemma adjacent_client_fp_obj_fp_smile:
  forall sm1 fp1 sm2 fp2 sm3,
    sep_obj_client_block sm1 ->
    client_fp sm1 sm2 fp1 ->
    GMem.forward sm1 sm2 ->
    (forall b ofs, obj_mem sm1 b ofs <-> obj_mem sm2 b ofs) ->
    obj_fp sm2 sm3 fp2 ->
    FP.smile fp1 fp2.
Proof.
  clear. intros sm1 fp1 sm2 fp2 sm3 Hsep Hclient Hforward Hobjeq Hobj.
  inv Hobj; inv Hclient; auto using smile_emp_fp, fpsmile_sym;
    apply FP.smile_conflict_compat; intro C;
      apply FP.conflict'_conflict_equiv, fp_conflict_locs_conflict in C;
      destruct C as (b & ofs & C1 & C2).

  apply H_client_valid_block_fp in C1; destruct C1 as [C1|[ofs' C1]];
    apply H_object_valid_block_fp in C2; destruct C2 as [C2|[ofs'' C2]];
      eauto using client_mem_obj_mem_excluded.
  rewrite <- Hobjeq in C2. eauto.
  rewrite <- Hobjeq in C2. eauto.
  rewrite <- Hobjeq in C2. eauto.
  
  apply H_client_alloc_fp in C1; apply H_object_valid_block_fp in C2.
  destruct C2 as [C2|[ofs' C2]]; destruct C1 as [Hfresh [Hvalid [Hclient|Hunused]]].
  eapply obj_mem_client_mem_excluded. auto using GMem.forward_refl. eauto. eauto.
  eapply unused_mem_object_mem_excluded; eauto.
  eapply obj_mem_client_mem_excluded. auto using GMem.forward_refl. eauto. eauto.
  eapply unused_mem_object_mem_excluded; eauto.

  apply H_client_valid_block_fp in C1; apply H_object_alloc_fp in C2.
  destruct C1 as [C1|[ofs' C1]]; destruct C2 as [Hfresh [Hvalid _]].
  exploit client_mem_valid; eauto. intros. apply Hfresh. eapply GMem.dom_forward; eauto.
  exploit client_mem_valid; eauto. intros. apply Hfresh. eapply GMem.dom_forward; eauto.
  
  apply H_object_alloc_fp in C2. apply H_client_alloc_fp in C1. intuition.
Qed.