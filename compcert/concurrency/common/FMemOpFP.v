Require Import Coqlib Integers Values AST Blockset Footprint FMemory MemAux Injections LDSimDefs.


(** ** relations on footprints *)
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

Inductive LocMapped (f: meminj) sls tb tofs : Prop :=
  Loc_Mapped: forall b ofs delta,
    Locs.belongsto sls b ofs ->
    f b = Some (tb, delta) ->
    tofs = ofs + delta ->
    LocMapped f sls tb tofs.

Inductive LocsMapped (f: meminj) (sls tls: Locs.t) : Prop :=
  Locs_Mapped :
    (forall tb tofs, Locs.belongsto tls tb tofs ->
                LocMapped f sls tb tofs) ->
    LocsMapped f sls tls.

Lemma emp_locs_mapped:
  forall f sls, LocsMapped f sls Locs.emp.
Proof.
  constructor. intros. inversion H.
Qed.

Record fp_mapped (f: meminj) (fp tfp: FP.t) : Prop :=
  {
    cmps_mapped: LocsMapped f (FP.cmps fp) (FP.cmps tfp);
    reads_mapped: LocsMapped f (FP.reads fp) (FP.reads tfp);
    writes_mapped: LocsMapped f (FP.writes fp) (FP.writes tfp);
    frees_mapped: LocsMapped f (FP.frees fp) (FP.frees tfp);
  }.

Lemma emp_fp_mapped:
  forall f fp, fp_mapped f fp empfp.
Proof.
  intros. constructor; apply emp_locs_mapped.
Qed.

(** Lemmas about fp mapped *)
Lemma locs_mapped_union_s:
  forall f sls tls,
    LocsMapped f sls tls ->
    forall sls',
      LocsMapped f (Locs.union sls sls') tls.
Proof.
  clear; intros. inv H.
  constructor; intros. apply H0 in H. inv H.
  econstructor; eauto with locs.
  unfold Locs.belongsto, Locs.union in *. rewrite H1. auto.
Qed.
  
Lemma fp_mapped_union_s:
  forall f fp1 tfp1 fp2,
    fp_mapped f fp1 tfp1 ->
    fp_mapped f (FP.union fp1 fp2) tfp1.
Proof.
  clear. intros. inv H. unfold FP.union.
  constructor; simpl; apply locs_mapped_union_s; auto.
Qed.

Lemma locs_mapped_union_t:
  forall f sls tls1 tls2,
    LocsMapped f sls tls1 ->
    LocsMapped f sls tls2 ->
    LocsMapped f sls (Locs.union tls1 tls2).
Proof.
  clear; intros. inv H; inv H0.
  econstructor. intros.
  unfold Locs.belongsto, Locs.union in *. apply orb_true_iff in H0.
  destruct H0; [apply H1 in H0|apply H in H0]; auto.
Qed.

Lemma fp_mapped_union_t:
  forall f fp tfp1 tfp2,
    fp_mapped f fp tfp1 ->
    fp_mapped f fp tfp2 ->
    fp_mapped f fp (FP.union tfp1 tfp2).
Proof.
  clear; intros. unfold FP.union.
  inv H; inv H0. constructor; simpl; apply locs_mapped_union_t; auto.
Qed.

Lemma fp_mapped_union:
  forall f fp1 tfp1 fp2 tfp2,
    fp_mapped f fp1 tfp1 ->
    fp_mapped f fp2 tfp2 ->
    fp_mapped f (FP.union fp1 fp2) (FP.union tfp1 tfp2).
Proof.
  clear; intros.
  apply fp_mapped_union_t; [|rewrite FP.union_comm_eq];
    apply fp_mapped_union_s; eauto.
Qed.

Lemma inject_incr_locs_mapped:
  forall f ls tls,
    LocsMapped f ls tls ->
    forall f',
      inject_incr f f' ->
      LocsMapped f' ls tls.
Proof.
  clear. intros.
  inv H. constructor. intros. apply H1 in H.
  inv H. econstructor; eauto.
Qed.

Lemma inject_incr_fp_mapped:
  forall f fp tfp,
    fp_mapped f fp tfp ->
    forall f',
      inject_incr f f' ->
      fp_mapped f' fp tfp.
Proof.
  clear. intros.
  inv H. constructor; eapply inject_incr_locs_mapped; eauto.
Qed.

Lemma fp_mapped_fpG:
  forall mu j m tm fp tfp
    (wd_mu: Bset.inject_weak' (inj mu) (SharedSrc mu) (SharedTgt mu))
    (INJMU: forall b, Bset.belongsto (SharedSrc mu) b ->
                 (Bset.inj_to_meminj (inj mu) b) = j b)
    (MEMINJ: Mem.inject j m tm),
    fpG (Mem.freelist m) (SharedSrc mu) fp ->
    fp_mapped j fp tfp ->
    fpG (Mem.freelist tm) (SharedTgt mu) tfp.
Proof.
  intros until 3. intros Hfp MAPPED.
  inv MAPPED. destruct fp, tfp; simpl in *.
  inv wd_mu. 
  unfold fpG, FP.blocks, FP.locs, Locs.blocks, Locs.union, Bset.belongsto, Locs.belongsto
    in *; simpl in *.
  intros tb [tofs Htfp].
  repeat rewrite orb_true_iff in Htfp.
  destruct Htfp as [Htfp|[Htfp|[Htfp|Htfp]]];
    [inv cmps_mapped0
    |inv reads_mapped0
    |inv writes_mapped0
    |inv frees_mapped0];
    specialize (H tb tofs Htfp); inv H;
      assert (Htmp: exists ofs, cmps b ofs || (reads b ofs || (writes b ofs || frees b ofs)) = true)
      by (exists ofs; rewrite H0; repeat rewrite orb_true_r; auto);
      specialize (Hfp b Htmp); clear Htmp;

        (destruct Hfp as [Hfp|Hfp];
         [left; apply INJMU in Hfp; rewrite <- Hfp in H1;
          unfold Bset.inj_to_meminj in H1; apply inj_range' with (b:=b);
          (destruct (inj mu _); inv H1; auto) 
         |right; exploit Mem.mi_freelist; eauto]).
Qed.

Lemma fp_mapped_LfpG:
  forall mu j m tm fp tfp
    (wd_mu: Bset.inject_weak' (inj mu) (SharedSrc mu) (SharedTgt mu))
(*    (GENVDOM: forall b : positive,
        Plt b bound ->
        exists tb : block, j b = Some (tb, 0) /\ Plt tb tbound)*)
    (GENVRANGE: forall (b1 b2 : block) (delta : Z),
        j b1 = Some (b2, delta) ->
        Bset.belongsto (SharedTgt mu) b2 ->
        Bset.belongsto (SharedSrc mu) b1)
    (INJMU: forall b, Bset.belongsto (SharedSrc mu) b ->
                 (Bset.inj_to_meminj (inj mu) b) = j b)
    (MEMINJ: Mem.inject j m tm)
    (NOOVERLAPT: no_overlap (Mem.freelist tm) (SharedTgt mu))
  ,
    HfpG (Mem.freelist m) mu fp ->
    fp_mapped j fp tfp ->
    LfpG (Mem.freelist tm) mu fp tfp.
Proof.
  intros until 5. intros Hfp MAPPED.
  inv Hfp.
  assert (HtfpG: fpG (Mem.freelist tm) (SharedTgt mu) tfp) by (eapply fp_mapped_fpG; eauto).
  inv wd_mu.
  
  constructor; auto.
  inv MAPPED. destruct fp, tfp; simpl in *.
  constructor; simpl in *;
  [inv cmps_mapped0|
   inv reads_mapped0|
   inv writes_mapped0|
   inv frees_mapped0].
  
  constructor; intros tb tofs SHARED BELONGSTO; specialize (H0 _ _ BELONGSTO); inv H0.
  destruct (H b). generalize H1; clear. exists ofs; cbv; rewrite H1; auto.
  exists b. rewrite <- INJMU in H2; auto. cbv in H2. 
  match goal with H: match ?x with _ => _ end = _ |- _ => destruct x eqn:INJ; inv H end.
  rewrite Z.add_0_r. split; auto.
  exfalso. exploit Mem.mi_freelist; eauto. intros. inv H3. eapply NOOVERLAPT; eauto. 

  constructor; intros tb tofs SHARED BELONGSTO; specialize (H0 _ _ BELONGSTO); inv H0.
  destruct (H b). generalize H1; clear.
  exists ofs; cbv; rewrite H1; repeat match goal with |- context[if ?x then true else true] => destruct x; auto end.
  exists b. rewrite <- INJMU in H2; auto. cbv in H2. 
  match goal with H: match ?x with _ => _ end = _ |- _ => destruct x eqn:INJ; inv H end.
  rewrite Z.add_0_r. split; auto.
  exfalso. exploit Mem.mi_freelist; eauto. intros. inv H3. eapply NOOVERLAPT; eauto.

  constructor; intros tb tofs SHARED BELONGSTO; specialize (H0 _ _ BELONGSTO); inv H0.
  destruct (H b). generalize H1; clear.
  exists ofs; cbv; rewrite H1; repeat match goal with |- context[if ?x then true else true] => destruct x; auto end.
  exists b. rewrite <- INJMU in H2; auto. cbv in H2. 
  match goal with H: match ?x with _ => _ end = _ |- _ => destruct x eqn:INJ; inv H end.
  rewrite Z.add_0_r. split; auto.
  exfalso. exploit Mem.mi_freelist; eauto. intros. inv H3. eapply NOOVERLAPT; eauto.

  constructor; intros tb tofs SHARED BELONGSTO; specialize (H0 _ _ BELONGSTO); inv H0.
  destruct (H b). generalize H1; clear.
  exists ofs; cbv; rewrite H1; repeat match goal with |- context[if ?x then true else true] => destruct x; auto end.
  exists b. rewrite <- INJMU in H2; auto. cbv in H2. 
  match goal with H: match ?x with _ => _ end = _ |- _ => destruct x eqn:INJ; inv H end.
  rewrite Z.add_0_r. split; auto.
  exfalso. exploit Mem.mi_freelist; eauto. intros. inv H3. eapply NOOVERLAPT; eauto.
Qed.


(** * Footprints of memory operations *)
(** We define footprints for the following memory interfaces:
    - [alloc]
    - [free]
    - [load]
    - [store]
    - [loadv]
    - [storev]
    - [loadbytes]
    - [storebytes]
    - [free_list]
    - [drop_perm]
    - [valid_pointer]
    - [weak_valid_Pointer]


 *)

Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation FP := FP.Build_t.

(** [TODO] move to LDSimDefs *)
Lemma emp_loc_match:
  forall mu ls, LocMatch mu ls empls.
Proof. intros. constructor. intros. inv H0. Qed.


Definition range_locset (b: block) (ofs: Z) (size: Z) : locset :=
  fun b' ofs' =>
    if (eq_block b b')
    then zle ofs ofs' && zlt ofs' (ofs + size)
    else false.

Lemma range_locset_loc:
  forall b ofs size b' ofs',
    Locs.belongsto (range_locset b ofs size) b' ofs' <->
    b' = b /\ ofs' >= ofs /\ ofs' < ofs + size.
Proof.
  split; unfold range_locset, Locs.belongsto; intros. 
  - destruct (eq_block b b'); [subst | discriminate].
    split; [auto|]. 
    rewrite andb_true_iff in H; destruct H. 
    split. destruct Z_le_gt_dec. Lia.lia. inversion H.
    destruct Z_lt_dec. auto. inversion H0.
  - destruct (eq_block b b');
      try destruct Z_le_gt_dec; 
      try destruct Z_lt_dec; auto; try Lia.lia.
Qed.

Lemma range_locset_inj_fp_mapped:
  forall f b tb delta ofs size,
    f b = Some (tb, delta) ->
    LocsMapped f (range_locset b ofs size) (range_locset tb (ofs + delta) size).
Proof.
  constructor; intros.
  unfold Locs.belongsto, range_locset in *.
  destruct eq_block; inv H0.
  apply Loc_Mapped with b (tofs-delta) delta; [|auto|Lia.lia].
  unfold Locs.belongsto. destruct eq_block; [|congruence].
  repeat destruct zle, zlt; auto; Lia.lia.
Qed.

Local Hint Resolve range_locset_loc range_locset_inj_fp_mapped.


(** ** ALLOC *)
(** The footprint for allocation is wierd. Since it requires the 
    highest priority which is called "frees".... *)
Definition uncheck_alloc_fp (b: block) (lo hi: Z) : footprint :=
  FP empls empls empls (fun b' _ => if peq b b' then true else false).

Definition alloc_fp (m: mem) (lo hi: Z) : footprint :=
  uncheck_alloc_fp (Mem.nextblock m) lo hi.

Lemma alloc_fp_loc:
  forall m lo hi b ofs,
    Locs.belongsto (FP.frees (alloc_fp m lo hi)) b ofs <->
    b = (Mem.nextblock m).
Proof.
  unfold alloc_fp, uncheck_alloc_fp; simpl; intros.
  Locs.unfolds. destruct peq; subst; try tauto.
  split; intro; congruence.
Qed.

Lemma alloc_parallel_inj_fp_mapped:
  forall f m tm lo hi delta,
    f (Mem.nextblock m) = Some (Mem.nextblock tm, delta) ->
    fp_mapped f (alloc_fp m lo hi)
              (alloc_fp tm (lo+delta) (hi+delta)).
Proof.
  unfold alloc_fp; intros.
  constructor; simpl; try apply emp_locs_mapped.
  constructor; intros; Locs.unfolds.
  destruct peq; subst.
  econstructor; eauto. Locs.unfolds. destruct peq; congruence.
  instantiate (1:= tofs - delta). Lia.lia.
  discriminate.
Qed.

Lemma alloc_LfpG:
  forall mu tm lo hi fp,
    no_overlap (Mem.freelist tm) (SharedTgt mu) ->
    LfpG (Mem.freelist tm) mu fp (alloc_fp tm lo hi).
Proof.
  intros. constructor.
  constructor; try (unfold alloc_fp, uncheck_alloc_fp; simpl; apply emp_loc_match; fail).
  constructor. intros. apply alloc_fp_loc in H1. inv H1.
  exfalso; eapply H; eauto.
  unfold fpG. 
  unfold FP.blocks, FP.locs, Locs.union, alloc_fp, uncheck_alloc_fp, range_locset; simpl.
  unfold Locs.blocks, Bset.belongsto, Locs.belongsto. right. inv H0.
  destruct eq_block; [|congruence].
  subst b. eexists. unfold Mem.nextblock, get_block. eauto.
Qed.

Local Hint Resolve alloc_fp_loc alloc_parallel_inj_fp_mapped. (* alloc_LfpG. *)
  

(** ** FREE *)
Definition free_fp (b: block) (lo hi: Z) : footprint :=
  FP empls empls empls (range_locset b lo (hi - lo)).

Lemma free_fp_loc:
  forall b lo hi b' ofs',
    Locs.belongsto (FP.frees (free_fp b lo hi)) b' ofs' <->
    b' = b /\ ofs' >= lo /\ ofs' < hi.
Proof.
  unfold free_fp. simpl. intros. rewrite range_locset_loc. rewrite Zplus_minus. tauto.
Qed.

Local Hint Resolve free_fp_loc.


(** ** LOAD *)
Definition load_fp (chunk: memory_chunk) (b: block) (ofs: Z) : footprint :=
  FP empls (range_locset b ofs (size_chunk chunk)) empls empls.

Lemma load_fp_loc:
  forall chunk b ofs b' ofs',
    Locs.belongsto (FP.reads (load_fp chunk b ofs)) b' ofs' <->
    b' = b /\ ofs' >= ofs /\ ofs' < ofs + size_chunk chunk.
Proof.
  unfold load_fp. simpl. intros. rewrite range_locset_loc. tauto.
Qed.

Local Hint Resolve load_fp_loc.


(** ** STORE *)
Definition store_fp (chunk: memory_chunk) (b: block) (ofs: Z) : footprint :=
  FP empls empls (range_locset b ofs (size_chunk chunk)) empls.

Lemma store_fp_loc:
  forall chunk b ofs b' ofs',
    Locs.belongsto (FP.writes (store_fp chunk b ofs)) b' ofs' <->
    b' = b /\ ofs' >= ofs /\ ofs' < ofs + size_chunk chunk.
Proof.
  unfold store_fp. simpl. intros. apply range_locset_loc.
Qed.

Lemma store_inj_fp_mapped:
  forall f m tm chunk b ofs v m' tb delta,
    Mem.inject f m tm ->
    Mem.store chunk m b ofs v = Some m' ->
    f b = Some (tb, delta) ->
    fp_mapped f (store_fp chunk b ofs)
              (store_fp chunk tb (ofs + delta)).
Proof.
  unfold store_fp. intros until delta. intros MEMINJ STORE INJ.
  constructor; simpl; try apply emp_locs_mapped.
  constructor. intros. apply range_locset_loc in H. inv H.
  apply Loc_Mapped with b (tofs-delta) delta; [|auto|Lia.lia].
  rewrite range_locset_loc. intuition.
Qed.
  
Local Hint Resolve store_fp_loc store_inj_fp_mapped.


(** ** LOADV *)
Definition loadv_fp (chunk: memory_chunk) (addr: val) : footprint :=
  match addr with
  | Vptr b ofs => load_fp chunk b (Ptrofs.unsigned ofs)
  | _ => empfp
  end.

Lemma loadv_fp_loc:
  forall chunk b ofs b' ofs',
    Locs.belongsto (FP.reads (loadv_fp chunk (Vptr b ofs))) b' ofs' <->
    b' = b /\ ofs' >= Ptrofs.unsigned ofs /\ ofs' < Ptrofs.unsigned ofs + size_chunk chunk.
Proof. unfold loadv_fp. auto. Qed.

Lemma loadv_inj_fp_mapped:
  forall f m tm chunk b ofs v tb delta,
    Mem.inject f m tm ->
    Mem.loadv chunk m (Vptr b ofs) = Some v ->
    f b = Some (tb, delta) ->
    fp_mapped f (loadv_fp chunk (Vptr b ofs))
              (loadv_fp chunk (Vptr tb (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  unfold loadv_fp; intros.
  constructor; simpl; try apply emp_locs_mapped.
  constructor. intros. rewrite range_locset_loc in H2. inv H2.
  eapply Loc_Mapped with b (tofs-delta) delta; [|eauto|Lia.lia].
  exploit Mem.load_valid_access; eauto. intro.
  exploit Mem.mi_representable; [eauto|eauto|eauto with mem |]. intro.
  unfold Ptrofs.add in *. do 2 rewrite Ptrofs.unsigned_repr in H4; auto. 
  apply range_locset_loc. intuition.
  destruct ofs; simpl in *. Lia.lia.
  rewrite Ptrofs.unsigned_repr; [tauto|]. destruct ofs; simpl in *. Lia.lia.
  rewrite Ptrofs.unsigned_repr; [tauto|]. destruct ofs; simpl in *. Lia.lia.
Qed.

Local Hint Resolve loadv_fp_loc.


(** ** STOREV *)
Definition storev_fp (chunk: memory_chunk) (addr: val) : footprint :=
  match addr with
  | Vptr b ofs => store_fp chunk b (Ptrofs.unsigned ofs)
  | _ => empfp
  end.

Lemma storev_fp_loc:
  forall chunk b ofs b' ofs',
    Locs.belongsto (FP.writes (storev_fp chunk (Vptr b ofs))) b' ofs' <->
    b' = b /\ ofs' >= Ptrofs.unsigned ofs /\ ofs' < Ptrofs.unsigned ofs + size_chunk chunk.
Proof. unfold storev_fp. auto. Qed.

Lemma storev_inj_fp_mapped:
  forall f m tm chunk b ofs v m' tb delta,
    Mem.inject f m tm ->
    Mem.storev chunk m (Vptr b ofs) v = Some m' ->
    f b = Some (tb, delta) ->
    fp_mapped f (storev_fp chunk (Vptr b ofs))
              (storev_fp chunk (Vptr tb (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  unfold storev_fp; intros.
  constructor; simpl; try apply emp_locs_mapped.
  constructor. intros. rewrite range_locset_loc in H2. inv H2.
  apply Loc_Mapped with b (tofs-delta) delta; [|auto|Lia.lia].
  exploit Mem.store_valid_access_3; eauto. intro.
  exploit Mem.mi_representable; [eauto|eauto|eauto with mem |]. intro.
  unfold Ptrofs.add in *. do 2 rewrite Ptrofs.unsigned_repr in H4; auto. 
  apply range_locset_loc. intuition.
  destruct ofs; simpl in *. Lia.lia.
  rewrite Ptrofs.unsigned_repr; [tauto|]. destruct ofs; simpl in *. Lia.lia.
  rewrite Ptrofs.unsigned_repr; [tauto|]. destruct ofs; simpl in *. Lia.lia.
Qed.

Local Hint Resolve storev_fp_loc storev_inj_fp_mapped.

(** ** LOADBYTES *)
Definition loadbytes_fp (b: block) (ofs n: Z) : footprint :=
  FP empls (range_locset b ofs n) empls empls.

Lemma loadbytes_fp_loc:
  forall b ofs n b' ofs',
    Locs.belongsto (FP.reads (loadbytes_fp b ofs n)) b' ofs' <->
    b' = b /\ ofs' >= ofs /\ ofs' < ofs + n.
Proof. apply range_locset_loc. Qed.

Lemma loadbytes_inj_fp_mapped:
  forall f m tm b ofs n bytes tb delta,
    Mem.inject f m tm ->
    Mem.loadbytes m b (Ptrofs.unsigned ofs) n = Some bytes ->
    f b = Some (tb, delta) ->
    fp_mapped f (loadbytes_fp b (Ptrofs.unsigned ofs) n)
              (loadbytes_fp
                 tb (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) n).
Proof.
  intros until delta. intros MEMINJ LOADBYTES INJ.
  unfold loadbytes_fp. 
  constructor; simpl; try apply emp_locs_mapped.
  constructor. intros.
  apply range_locset_loc in H. inv H.
  apply Loc_Mapped with b (tofs-delta) delta; [|auto|Lia.lia].
  apply range_locset_loc.
  destruct (zlt 0 n).
  exploit Mem.loadbytes_range_perm; eauto. instantiate (1:= Ptrofs.unsigned ofs). Lia.lia. intro.
  exploit Mem.mi_representable; [eauto|eauto|eauto with mem |]. intro.
  unfold Ptrofs.add in H1.
  do 2 rewrite Ptrofs.unsigned_repr in H1; auto; try rewrite Ptrofs.unsigned_repr; destruct ofs; simpl in *; try Lia.lia. 
  intuition.
Qed.

Local Hint Resolve loadbytes_fp_loc loadbytes_inj_fp_mapped.


(** ** STOREBYTES *)
Definition storebytes_fp (b: block) (ofs n: Z) : footprint :=
  FP empls empls (range_locset b ofs n) empls.

Lemma storebytes_fp_loc:
  forall b ofs n b' ofs',
    Locs.belongsto (FP.writes (storebytes_fp b ofs n)) b' ofs' <->
    b' = b /\ ofs' >= ofs /\ ofs' < ofs + n.
Proof. unfold storebytes_fp. simpl. intros. apply range_locset_loc. Qed.

Lemma storebytes_inj_fp_mapped:
  forall f m tm b ofs bytes m' tb delta,
    Mem.inject f m tm ->
    Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
    f b = Some (tb, delta) ->
    fp_mapped f (storebytes_fp b (Ptrofs.unsigned ofs) (Z.of_nat (length bytes)))
              (storebytes_fp
                 tb (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) (Z.of_nat (length bytes))).
Proof.
  intros until delta. intros MEMINJ STOREBYTES INJ.
  unfold storebytes_fp. 
  constructor; simpl; try apply emp_locs_mapped.
  constructor. intros.
  rewrite range_locset_loc in H. inv H.
  apply Loc_Mapped with b (tofs-delta) delta; [|auto|Lia.lia].
  destruct H1. destruct bytes. simpl in *. Lia.lia.
  exploit Mem.storebytes_range_perm; eauto. instantiate (1:= Ptrofs.unsigned ofs). 
  simpl. clear. pose proof (Zgt_pos_0 (Pos.of_succ_nat (length bytes))). Lia.lia. intro.
  exploit Mem.mi_representable; [eauto|eauto|eauto with mem |]. intro.
  unfold Ptrofs.add in *.
  destruct ofs; simpl in *.
  apply range_locset_loc. 
  do 2 rewrite Ptrofs.unsigned_repr in H0; auto; try rewrite Ptrofs.unsigned_repr; try Lia.lia.
  do 2 rewrite Ptrofs.unsigned_repr in H; auto; try rewrite Ptrofs.unsigned_repr; try Lia.lia.
Qed.

Local Hint Resolve storebytes_fp_loc storebytes_inj_fp_mapped.


(** ** FREE_LIST *)
Fixpoint free_list_fp (bl: list (block * Z * Z)) : footprint :=
  match bl with
  | nil => empfp
  | (b,lo,hi) :: bl =>
    FP.union (free_fp b lo hi) (free_list_fp bl)
  end.

Lemma free_list_fp_loc:
  forall bl b ofs,
    Locs.belongsto (FP.frees (free_list_fp bl)) b ofs <->
    exists lo hi, In (b,lo,hi) bl /\ lo <= ofs /\ ofs < hi.
Proof.
  induction bl; simpl.
  intuition. destruct H as (_&_&H&_). contradiction.
  intros. destruct a as ((b0, lo0), hi0).
  pose proof (range_locset_loc b0 lo0 (hi0 - lo0) b ofs) as H.
  unfold FP.union, free_fp, Locs.union, Locs.belongsto in *. simpl in *.
  rewrite orb_true_iff. rewrite IHbl, H. clear IHbl H.
  split; intros.
  - destruct H ; [exists lo0, hi0| destruct H as (lo'&hi'&H_in&H_ofs); eauto].
    destruct H; subst. split; [auto|Lia.lia].
  - destruct H as (lo' & hi' & [H|H] & Hofs & Hofs');
      [left; inv H; split; [auto|Lia.lia]
      |right; eauto].
Qed.

Lemma free_list_fp_frees:
  forall bl, free_list_fp bl =
        FP.Build_t Locs.emp Locs.emp Locs.emp
                   (FP.frees (free_list_fp bl)).
Proof.
  clear. intros.
  unfold free_list_fp.
  induction bl. unfold empfp; auto.
  destruct a as [[p hi] lo]. rewrite IHbl.
  unfold free_fp, FP.union; simpl.
  eexists; f_equal.
Qed.

Local Hint Resolve free_list_fp_loc free_list_fp_frees.
    
(** ** DROP *)
(** Is drop used in step relations? 
    It seems drop is only used in constructing initial memory. *)

(** ** VALID_POINTER *)
Definition valid_pointer_fp (b: block) (ofs: Z) : footprint :=
  FP (range_locset b ofs 1) empls empls empls.

Lemma valid_pointer_fp_loc:
  forall b ofs b' ofs',
    Locs.belongsto (FP.cmps (valid_pointer_fp b ofs)) b' ofs' <->
    b = b' /\ ofs = ofs'.
Proof.
  unfold valid_pointer_fp. simpl. intros. rewrite range_locset_loc.
  split; intros; (split; [intuition | Lia.lia]).
Qed.

Lemma valid_pointer_inj_fp_mapped:
  forall f m tm b ofs tb delta,
    Mem.inject f m tm ->
    Mem.valid_pointer m b (Ptrofs.unsigned ofs) = true ->
    f b = Some (tb, delta) ->
    fp_mapped f (valid_pointer_fp b (Ptrofs.unsigned ofs))
              (valid_pointer_fp tb (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  unfold valid_pointer_fp; intros.
  assert (DELTA: 0 <= delta <= Ptrofs.max_unsigned).
  { exploit Mem.valid_pointer_inject_no_overflow; eauto.
    exploit Mem.mi_representable; [eauto|eauto| |]. instantiate (1:=ofs).
    rewrite Mem.valid_pointer_nonempty_perm in H0. eauto with mem.
    intros. destruct ofs. simpl in *. Lia.lia. }
  assert (TOFS: 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned).
  { exploit Mem.valid_pointer_inject_no_overflow; eauto.
    exploit Mem.mi_representable; [eauto|eauto| |]. instantiate (1:=ofs).
    rewrite Mem.valid_pointer_nonempty_perm in H0. eauto with mem.
    intros. destruct ofs. simpl in *. Lia.lia. }
  unfold Ptrofs.add. do 2 rewrite Ptrofs.unsigned_repr; auto.
  constructor; simpl; try apply emp_locs_mapped.
  constructor. intros. apply range_locset_loc in H2. inv H2. 
  apply Loc_Mapped with b (tofs - delta) delta; [|auto|Lia.lia].
  rewrite range_locset_loc. intuition.
Qed.


  
Definition weak_valid_pointer_fp (m: mem) (b: block) (ofs: Z) : footprint :=
  if Mem.valid_pointer m b ofs
  then valid_pointer_fp b ofs
  else FP (range_locset b (ofs - 1) 2) empls empls empls.

Lemma weak_valid_pointer_fp_loc:
  forall m b ofs b' ofs',
    Locs.belongsto (FP.cmps (weak_valid_pointer_fp m b ofs)) b' ofs' <->
    b = b' /\
    ((Mem.valid_pointer m b ofs = true
      /\ ofs' = ofs)
     \/
     (Mem.valid_pointer m b ofs = false
      /\ (ofs' = ofs \/ ofs' = ofs - 1))).
Proof.
  unfold weak_valid_pointer_fp. intros.
  destruct (Mem.valid_pointer m b ofs); simpl; rewrite range_locset_loc.
  split; intros.
  split; [intuition|left; split; [auto|try Lia.lia]].
  split; [intuition|destruct H as [H [H'|H']]; intuition].
  split; intros.
  split; [intuition|right; split; [auto|try Lia.lia]].
  split; [intuition|destruct H as [H [H'|H']]; intuition].
Qed.

Lemma weak_valid_inj_fp_mapped:
  forall f m tm b ofs tb delta,
    Mem.inject f m tm ->
    Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = true ->
    f b = Some (tb, delta) ->
    fp_mapped f (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
              (weak_valid_pointer_fp tm tb (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  unfold Mem.weak_valid_pointer, weak_valid_pointer_fp; intros.
  assert (DELTA: 0 <= delta <= Ptrofs.max_unsigned).
  { exploit Mem.weak_valid_pointer_inject_no_overflow; eauto.
    exploit Mem.mi_representable; [eauto|eauto| |]. instantiate (1:=ofs).
    rewrite orb_true_iff, 2 Mem.valid_pointer_nonempty_perm in H0.
    destruct H0; [left|right]; eauto with mem.
    intros. destruct ofs. simpl in *. Lia.lia. }
  assert (TOFS: 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned).
  { exploit Mem.weak_valid_pointer_inject_no_overflow; eauto.
    exploit Mem.mi_representable; [eauto|eauto| |]. instantiate (1:=ofs).
    rewrite orb_true_iff, 2 Mem.valid_pointer_nonempty_perm in H0.
    destruct H0; [left|right]; eauto with mem.
    intros. destruct ofs. simpl in *. Lia.lia. }

  unfold Ptrofs.add. do 2 rewrite Ptrofs.unsigned_repr; auto.
  destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs)) eqn:VALID.
  * exploit Mem.valid_pointer_inject; eauto. intro.
    rewrite H2. constructor; simpl; try apply emp_locs_mapped.
    constructor. intros. apply range_locset_loc in H3. inv H3. 
    apply Loc_Mapped with b (tofs - delta) delta; [|auto|Lia.lia].
    rewrite range_locset_loc. intuition.
  * rewrite orb_true_iff in H0. destruct H0; [discriminate|].
    destruct (Mem.valid_pointer tm tb _).
    ** constructor; simpl; try apply emp_locs_mapped.
       constructor. intros. apply range_locset_loc in H2. inv H2.
       apply Loc_Mapped with b (tofs - delta) delta; [|auto|Lia.lia].
       rewrite range_locset_loc. intuition.
    ** constructor; simpl; try apply emp_locs_mapped.
       constructor. intros. apply range_locset_loc in H2. inv H2.
       apply Loc_Mapped with b (tofs - delta) delta; [|auto|Lia.lia].
       rewrite range_locset_loc. intuition.
Qed.

Lemma weak_valid_inj_valid_fp_mapped:
  forall f m tm b ofs tb delta,
    Mem.inject f m tm ->
    Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = true ->
    f b = Some (tb, delta) ->
    fp_mapped f (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
              (valid_pointer_fp tb (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  unfold Mem.weak_valid_pointer, weak_valid_pointer_fp; intros.
  destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs)) eqn:VALID.
  eapply valid_pointer_inj_fp_mapped; eauto.
  unfold valid_pointer_fp.

  assert (DELTA: 0 <= delta <= Ptrofs.max_unsigned).
  { rewrite orb_true_iff in H0.
    destruct H0; try discriminate.
    exploit Mem.weak_valid_pointer_inject_no_overflow; eauto.
    unfold Mem.weak_valid_pointer. erewrite H0, orb_true_r. auto.
    exploit Mem.mi_representable; [eauto|eauto| |]. instantiate (1:=ofs).
    rewrite Mem.valid_pointer_nonempty_perm in H0. eauto with mem.
    intros. destruct ofs. simpl in *. Lia.lia. }
  assert (TOFS: 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned).
  { rewrite orb_true_iff in H0.
    destruct H0; try discriminate.
    exploit Mem.weak_valid_pointer_inject_no_overflow; eauto.
    unfold Mem.weak_valid_pointer. erewrite H0, orb_true_r. auto.
    exploit Mem.mi_representable; [eauto|eauto| |]. instantiate (1:=ofs).
    rewrite Mem.valid_pointer_nonempty_perm in H0. eauto with mem.
    intros. destruct ofs. simpl in *. Lia.lia. }
  
  constructor; simpl; try apply emp_locs_mapped.
  constructor. intros. apply range_locset_loc in H2. inv H2. 
  apply Loc_Mapped with b (tofs - delta) delta; [|auto|Lia.lia].
  rewrite range_locset_loc. unfold Ptrofs.add in H4. rewrite 2 Ptrofs.unsigned_repr in H4; auto. intuition.
  rewrite Ptrofs.unsigned_repr; auto.
Qed.

Lemma valid_inj_weak_valid_fp_mapped:
  forall f m tm b ofs tb delta,
    Mem.inject f m tm ->
    Mem.valid_pointer m b (Ptrofs.unsigned ofs) = true ->
    f b = Some (tb, delta) ->
    fp_mapped f (valid_pointer_fp b (Ptrofs.unsigned ofs))
              (weak_valid_pointer_fp tm tb (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  unfold weak_valid_pointer_fp. intros.
  exploit Mem.valid_pointer_inject; eauto. intro.
  exploit Mem.valid_pointer_inject_no_overflow; eauto. intro.
  exploit Mem.mi_representable; eauto. rewrite Mem.valid_pointer_nonempty_perm in H0. eauto with mem. intro.
  unfold Ptrofs.add at 1. rewrite 2 Ptrofs.unsigned_repr at 1; auto.
  rewrite H2. eapply valid_pointer_inj_fp_mapped; eauto.
  destruct ofs. simpl in *. Lia.lia.
Qed.