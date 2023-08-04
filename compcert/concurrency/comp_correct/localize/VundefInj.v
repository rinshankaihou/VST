Require Import Coqlib Values Memory.

(** injection from Vundef to pointer values are undesirable for footprint preservation,
    because [cmpu] on pointer values generates cmp footprint, while [cmpu] on Vundefs 
    has no footprint. *)

(** specific requirements on Vundef injected values *)
Definition not_ptr (v: val) : Prop :=
  match v with
  | Vptr _ _ => False
  | _ => True
  end.

Definition local_ptr (Local: block -> Prop) (v: val) : Prop :=
  match v with
  | Vptr b _ => Local b
  | _ => True
  end.

Lemma not_ptr_implies_local:
  forall v Local, not_ptr v -> local_ptr Local v.
Proof. destruct v; simpl; intros; tauto. Qed.



(** restricting [Val.inject] *)
Definition val_inj_undef_spec (v v': val) (spec: val -> Prop) : Prop :=
  match v with
  | Vundef => spec v'
  | _ => True
  end.

Definition val_inj_undef_spec' (v v': val) (spec: val -> Prop) : Prop :=
  v = Vundef -> spec v'.

Lemma val_inj_undef_spec_eq:
  forall v v' spec, val_inj_undef_spec v v' spec <-> val_inj_undef_spec' v v' spec.
Proof. destruct v; simpl; cbv; intros; firstorder; discriminate. Qed.
  
Lemma val_inj_undef_spec_implies:
  forall v v' (spec1 spec2: val -> Prop),
    (spec1 v' -> spec2 v') ->
    val_inj_undef_spec v v' spec1 ->
    val_inj_undef_spec v v' spec2.
Proof. unfold val_inj_undef_spec; intros; destruct v; auto. Qed.

Inductive vl_inj_undef_spec : list val -> list val -> (val -> Prop) -> Prop :=
| inject_undef_nil: forall spec, vl_inj_undef_spec nil nil spec
| inject_undef_cons: forall v v' spec vl vl', val_inj_undef_spec v v' spec ->
                                         vl_inj_undef_spec vl vl' spec ->
                                         vl_inj_undef_spec (v::vl) (v'::vl') spec.

Lemma vl_inj_undef_spec_implies:
  forall (spec1 spec2: val -> Prop),
    (forall v, spec1 v -> spec2 v) ->
    forall vl vl', vl_inj_undef_spec vl vl' spec1 ->
              vl_inj_undef_spec vl vl' spec2.
Proof.
  induction vl.
  intros; inv H0. constructor.
  intros. inv H0. constructor; auto. eapply val_inj_undef_spec_implies; try eassumption; auto.
Qed.


Definition val_inj_undef_not_ptr (v v': val) := val_inj_undef_spec v v' not_ptr.
Definition val_inj_undef_local_ptr (Local: block -> Prop) (v v': val) := val_inj_undef_spec v v' (local_ptr Local).

Definition vl_inj_undef_not_ptr (vl vl': list val) := vl_inj_undef_spec vl vl' not_ptr.
Definition vl_inj_undef_local_ptr (Local: block -> Prop) (vl vl': list val) := vl_inj_undef_spec vl vl' (local_ptr Local).

Lemma Vundef_inj_not_ptr_implies_local:
  forall Local v v',
    val_inj_undef_not_ptr v v' ->
    val_inj_undef_local_ptr Local v v'.
Proof.
  unfold val_inj_undef_not_ptr, val_inj_undef_local_ptr; intros.
  eapply val_inj_undef_spec_implies in H; eauto. apply not_ptr_implies_local.
Qed.

Lemma Vundef_inj_list_not_ptr_implies_local:
  forall Local vl vl',
    vl_inj_undef_not_ptr vl vl' ->
    vl_inj_undef_local_ptr Local vl vl'.
Proof.
  unfold vl_inj_undef_not_ptr, vl_inj_undef_local_ptr; intros.
  eapply vl_inj_undef_spec_implies in H; eauto. intros; apply not_ptr_implies_local; auto.
Qed.
    

(** restricting [memval_inject] *)
(* specify images of Vundef fragments and uninitialized contents Undef *)
Definition memval_inject_undef_spec (mv mv': memval) (spec: val -> Prop) : Prop :=
  match mv, mv' with
  | Undef, Fragment v _ _ => spec v
  | Fragment Vundef _ _, Fragment v _ _ => spec v
  | _, _ => True
  end.

Lemma memval_inject_undef_spec_implies:
  forall (spec1 spec2: val -> Prop),
    (forall v, spec1 v -> spec2 v) ->
    forall mv mv',
      memval_inject_undef_spec mv mv' spec1 ->
      memval_inject_undef_spec mv mv' spec2.
Proof. unfold memval_inject_undef_spec; destruct mv; auto; destruct mv'; auto; destruct v; auto. Qed.
  
Definition memval_inject_undef_not_ptr (mv mv': memval) : Prop := memval_inject_undef_spec mv mv' (not_ptr).
Definition memval_inject_undef_local (Local: block -> Prop) (mv mv': memval) : Prop :=
  memval_inject_undef_spec mv mv' (local_ptr Local).

Lemma Undef_inj_not_ptr_implies_local:
  forall mv mv',
    memval_inject_undef_not_ptr mv mv' ->
    forall Local, memval_inject_undef_local Local mv mv'.
Proof.
  unfold memval_inject_undef_not_ptr, memval_inject_undef_local; intros.
  eapply memval_inject_undef_spec_implies. intros; eapply not_ptr_implies_local; eauto. auto.
Qed.

(** TODO: properties about memval_inject? *)

Lemma memval_inject_undef_not_ptr_bytes:
  forall n, memval_inject_undef_not_ptr (Byte n) (Byte n).
Proof. cbn; auto. Qed.

Lemma memval_inject_undef_not_ptr_frag:
  forall v1 v2 q n,
    val_inj_undef_not_ptr v1 v2 ->
    memval_inject_undef_not_ptr (Fragment v1 q n) (Fragment v2 q n).
Proof. cbn; auto. Qed.

Lemma memval_inject_undef_local_ptr_frag:
  forall Local v1 v2 q n,
    val_inj_undef_local_ptr Local v1 v2 ->
    memval_inject_undef_local Local (Fragment v1 q n) (Fragment v2 q n).
Proof. cbn; auto. Qed.

(* do not hold *)
(*
Lemma proj_value_inject_undef_not_ptr:
  forall spec vl1 vl2 f q,
    list_forall2 (memval_inject f) vl1 vl2 ->
    list_forall2 (fun l1 l2 => memval_inject_undef_spec l1 l2 spec) vl1 vl2 ->
    val_inj_undef_spec (proj_value q vl1) (proj_value q vl2) spec \/ (proj_value q vl2 = Vundef).
Proof.
  intros. inversion H0; subst. simpl; auto.
  inv H. unfold proj_value.
  inv H6; cbn; auto.
  
  destruct (check_value (size_quantity_nat q) v1 q (Fragment v1 q0 n :: al)) eqn:? .
  destruct (Val.eq v1 Vundef) eqn:C; [subst; cbn|destruct v1; inversion C];
    destruct (check_value (size_quantity_nat q) v2 q (Fragment v2 q0 n :: bl)); cbn; auto.
  destruct (check_value (size_quantity_nat q) v2 q (Fragment v2 q0 n :: bl)) eqn:?; cbn; auto.
  unfold check_value in Heqb, Heqb0. destruct (size_quantity_nat q) eqn:?; [discriminate|].
  destruct Val.eq; [destruct Val.eq;[|discriminate]|congruence]; simpl in Heqb, Heqb0. clear e e0.
  destruct quantity_eq;[|try discriminate].
  destruct (Nat.eqb_spec n0 n); [|discriminate].
  simpl in Heqb, Heqb0. fold check_value in Heqb, Heqb0.
  
  
  

  destruct Heqb. rewrite H3. cbn. auto.
  
  constructor; auto. constructor; auto.



  Focus 2.
  destruct b1; simpl; auto. 
  destruct (check_value (size_quantity_nat q) v q (Fragment v q0 n :: bl)) eqn:?; simpl in H1; cbn; auto.
  
Qed.
  
           
  
    exploit check_value_inject. ; eauto
    clear H1. unfold check_value in H3.
    generalize vl vl' H3 H H0 H2. clear.
    induction n; simpl. intros. inv H; congruence.
    intros. destruct vl. congruence.
    inv H. inv H0. destruct m; try (inv H3; fail).
    destruct (Val.eq Vundef v); try (inv H3; fail).
    destruct quantity_eq; try (inv H3; fail).
    destruct (n=? n0)%nat; try (inv H3; fail).
    exploit IHn; try eassumption; clear IHn. auto.
    subst. inv H5. 
    
    auto.
    inv H5.
    destruct 
    destruct m; try (inv H3; fail).
    
    induction n. destruct vl, vl'; auto. inversion H.
    
    
    
    
  
  
  
  simpl in H1. auto.
  destruct (Val.eq a1 
  induction vl1. cbn. inversion 1; simpl; auto.
  destruct vl2; inversion 1. subst. inversion 1. subst.
  exploit IHvl1; eauto.
  destruct a; simpl in *; destruct m; auto;
    repeat match goal with |- context[match ?x with _ => _ end] => destruct x eqn:?; simpl; auto end.
  inversion H3. destruct v; cbn; auto. destruct v; inv H3; auto; inv H2; cbn; auto.
  
  cut (check_value (size_quantity_nat q) (Vptr b2 (Integers.Ptrofs.add i (Integers.Ptrofs.repr delta))) q
                   (Fragment (Vptr b2 (Integers.Ptrofs.add i (Integers.Ptrofs.repr delta))) q1 n0 :: vl2) = false).
  congruence.
  assert (q = q1).
  { unfold check_value in Heqb0.
    destruct q; simpl in Heqb0;
      destruct quantity_eq; auto; try (simpl in Heqb0;
                                       repeat rewrite andb_false_r in Heqb0;
                                       repeat rewrite andb_false_l in Heqb0; discriminate). }
  subst q1. clear Heqb0.
  generalize Heqb.
  generalize dependent H0.
  generalize dependent H.
  generalize (Integers.Ptrofs.add i (Integers.Ptrofs.repr delta)); clear. intros.
  rewrite <- Heqb. unfold check_value. destruct q; simpl; repeat rewrite <- andb_assoc.
  do 2 destruct Val.eq; try congruence; simpl.
  destruct quantity_eq; try congruence; simpl.
  do 4 (destruct n0; auto). simpl.
  inversion H; subst.
  destruct vl2; inv H6; auto.
  destruct 
  match goal with
  | |- ?x && _ = _ =>
    let Hx := fresh in 
    destruct x eqn:Hx; [simpl|inversion Hx]
  end.
  
  
  
  

  
  Lemma check_value_frag_ptr_
  destruct q.
  simpl in Heqb0.
  unfold check_value in *; simpl in *.

  repeat 
    match goal with
    | H: ?x = ?x |- _ => clear H
    | H: True |- _ => clear H
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H; destruct H
(*    | H: match ?x with _ => _ end = true |- _ =>
      destruct x eqn:?; try (inv H; fail)
               
    | H: ?x && ?y = false |- _ =>
      destruct x eqn:?; try congruence *) 
    end.
  subst. 
  
  clear H6.
*)  


  
(** restricting [Mem.mem_inj] *)
