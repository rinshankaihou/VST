Require Import Coqlib Values Footprint FMemory.

(** ** Here we define freshblocks function for FMemory *)
Fixpoint diff {A: Type} (eq_dec: forall x y: A, {x = y} + {x <> y}) (l l' : list A) : list A :=
  match l with
  | nil => l'
  | v :: l => diff eq_dec l (remove eq_dec v l')
  end.

Lemma remove_subset :
  forall A eq_dec (x x': A) l,
    In x' (remove eq_dec x l) ->
    In x' l.
Proof.
  induction l; simpl. auto.
  destruct eq_dec. auto.
  simpl. destruct 1; auto.
Qed.

Lemma remove_In':
  forall A eq_dec (x x': A) l,
    In x' l ->
    x' <> x ->
    In x' (remove eq_dec x l).
Proof.
  induction l; simpl; auto.
  intros. 
  destruct eq_dec, H; subst; simpl; try congruence; auto.
Qed.
  
Lemma diff_spec:
  forall A eq_dec l l' x,
    In x (@diff A eq_dec l l') <->
    ~ In x l /\ In x l' .
Proof.
  induction l; simpl. tauto.
  intros. rewrite IHl. clear IHl.
  split.
  - intros [LEFT RIGHT].
    split; [intro | eapply remove_subset; eauto ].
    destruct H; [subst | congruence].
    eapply remove_In; eauto.
  - intros [LEFT RIGHT].
    split; [intro; apply LEFT; auto | ].
    destruct (eq_dec a x); subst.
    exfalso; apply LEFT; auto.
    apply remove_In'; auto.
Qed.

Definition fresh_blocks_func (m m': mem) : list block :=
  diff eq_block (Mem.validblocks m) (Mem.validblocks m').

Inductive fresh_blocks (m m': mem) : list block -> Prop :=
  Fresh_blocks :
    forall bl, (forall b, In b bl <-> ~ Mem.valid_block m b /\ Mem.valid_block m' b) ->
          fresh_blocks m m' bl.

Theorem fresh_blocks_func_spec1:
  forall m m' bl,
    fresh_blocks_func m m' = bl ->
    fresh_blocks m m' bl.
Proof.
  unfold fresh_blocks_func; intros.
  constructor; unfold Mem.valid_block. destruct m, m'; subst; simpl.
  apply diff_spec.
Qed.

Theorem fresh_blocks_func_spec2:
  forall m m' b bl,
    ~ Mem.valid_block m b /\ Mem.valid_block m' b ->
    fresh_blocks_func m m' = bl ->
    In b bl.
Proof.
  unfold fresh_blocks_func, Mem.valid_block. destruct m, m'; subst; simpl; clear.
  intros; subst. apply diff_spec; auto.
Qed.

Theorem fresh_blocks_func_spec3:
  forall m m' b,
    In b (fresh_blocks_func m m') ->
    ~ Mem.valid_block m b /\ Mem.valid_block m' b.
Proof.
  unfold fresh_blocks_func, Mem.valid_block.
  destruct m, m'; subst; simpl; clear.
  intros. apply diff_spec in H; auto.
Qed.

(** ** Here the [step2] relation is replaced with [Fstep2] *)
(** To adapt the original CompCert proof, we define [star] relation for [Fstep2] *)
(** Move to another file *)
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

Inductive star {genv state: Type} (step: genv -> state -> mem -> footprint -> state -> mem -> Prop)
          (ge : genv) : state -> mem -> footprint -> state -> mem -> Prop :=
| star_refl : forall s m, star step ge s m empfp s m
| star_step : forall s1 m1 fp1 s2 m2 fp2 s3 m3,
    step ge s1 m1 fp1 s2 m2 ->
    star step ge s2 m2 fp2 s3 m3 ->
    star step ge s1 m1 (FP.union fp1 fp2) s3 m3.

Lemma star_one {genv state: Type} (step: genv -> state -> mem -> footprint -> state -> mem -> Prop) :
  forall ge s1 m1 fp m2 s2, step ge s1 m1 fp s2 m2 -> star step ge s1 m1 fp s2 m2.
Proof.
  intros. rewrite <- (FP.fp_union_emp fp). eapply star_step; eauto. apply star_refl. 
Qed.

Lemma star_trans {genv state: Type} (step: genv -> state -> mem -> footprint -> state -> mem -> Prop) :
  forall ge s1 m1 fp1 s2 m2, star step ge s1 m1 fp1 s2 m2 ->
  forall fp2 s3 m3 fp, star step ge s2 m2 fp2 s3 m3 -> fp = FP.union fp1 fp2 -> star step ge s1 m1 fp s3 m3.
Proof.
  induction 1; intros; subst fp.
  rewrite FP.emp_union_fp. auto.
  rewrite <- FP.fp_union_assoc.
  eapply star_step; eauto. 
Qed.

Lemma star_left {genv state: Type} (step: genv -> state -> mem -> footprint -> state -> mem -> Prop) :
  forall ge s1 m1 fp1 s2 m2 fp2 s3 m3 fp,
  step ge s1 m1 fp1 s2 m2 -> star step ge s2 m2 fp2 s3 m3 -> fp = FP.union fp1 fp2 ->
  star step ge s1 m1 fp s3 m3.
Proof.
  intros. subst. eapply star_step; eauto.
Qed.

Lemma star_right {genv state: Type} (step: genv -> state -> mem -> footprint -> state -> mem -> Prop) :
  forall ge s1 m1 fp1 s2 m2 fp2 s3 m3 fp,
  star step ge s1 m1 fp1 s2 m2 -> step ge s2 m2 fp2 s3 m3 -> fp = FP.union fp1 fp2 ->
  star step ge s1 m1 fp s3 m3.
Proof.
  intros. subst. eapply star_trans; eauto.
  rewrite <- (FP.fp_union_emp fp2).
  eapply star_step; eauto. constructor.
Qed.