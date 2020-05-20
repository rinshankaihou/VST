Require Import VST.floyd.proofauto.
Require Import VST.progs.binary_heap_model.
Require Import VST.progs.binary_heap.
Require Import RelationClasses.
(* Require Import VST.floyd.sublist. *)

Set Nested Proofs Allowed.

(* Versions in Z... *)

Definition Zexchange {A : Type} (L : list A) (i j : Z) : list A :=
  exchange L (Z.to_nat i) (Z.to_nat j).

Lemma Zlength_Zexchange {A : Type} : forall (L : list A) i j,
  Zlength (Zexchange L i j) = Zlength L.
Proof.
  intros. unfold Zexchange. do 2 rewrite Zlength_correct. rewrite exchange_length. trivial.
Qed.

Lemma Zlength_one: forall A (a : A),
  Zlength [a] = 1.
Proof. reflexivity. Qed.

Lemma Znth_nth_error {A} `{Ia : Inhabitant A} : forall (L : list A) (i : Z),
  0 <= i < Zlength L ->
  nth_error L (Z.to_nat i) = Some (Znth i L).
Proof.
  intros. rewrite <- nth_Znth; trivial.
  apply nth_error_nth.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma nth_error_Znth {A} `{Ia : Inhabitant A}: forall (L1 L2 : list A) i j,
  0 <= i < Zlength L1 ->
  0 <= j < Zlength L2 ->
  nth_error L1 (Z.to_nat i) = nth_error L2 (Z.to_nat j) <->
  Znth i L1 = Znth j L2.
Proof.
  intros.
  assert (Z.to_nat i < length L1 /\ Z.to_nat j < length L2)%nat. {
    generalize (Zlength_length _ L1 (Zlength L1)); intro.
    generalize (Zlength_length _ L2 (Zlength L2)); intro.
    destruct H1. apply Zlength_nonneg.
    destruct H2. apply Zlength_nonneg.
    rewrite (H1 eq_refl). rewrite (H2 eq_refl). lia. }
  repeat rewrite <- nth_Znth; trivial.
  generalize (nth_error_nth A Ia); intros.
  split; intros. do 2 (rewrite H2 in H3; try lia). inversion H3. congruence.
  rewrite H2. rewrite H2. congruence. lia. lia.
Qed.

Lemma Znth_Zexchange : forall {A} `{Ia : Inhabitant A} (L : list A) i j,
  0 <= i < Zlength L ->
  0 <= j < Zlength L ->
  Znth i (Zexchange L i j) = Znth j L.
Proof.
  intros.
  apply nth_error_Znth; auto. rewrite Zlength_Zexchange. trivial.
  generalize (Zlength_length _ L (Zlength L)). intro.
  apply nth_error_exchange; lia.
Qed.

Lemma Znth_Zexchange' : forall {A} `{Ia : Inhabitant A} (L : list A) i j,
  0 <= i < Zlength L ->
  0 <= j < Zlength L ->
  Znth j (Zexchange L i j) = Znth i L.
Proof.
  intros.
  apply nth_error_Znth; auto. rewrite Zlength_Zexchange. trivial.
  generalize (Zlength_length _ L (Zlength L)). intro.
  apply nth_error_exchange'; lia.
Qed.

Lemma Znth_Zexchange'' : forall {A} `{Ia : Inhabitant A} (L : list A) k i j,
  0 <= i < Zlength L ->
  0 <= j < Zlength L ->
  k <> i -> k <> j ->
  Znth k (Zexchange L i j) = Znth k L.
Proof.
  intros.
  assert (k < 0 \/ 0 <= k < Zlength L \/ Zlength L <= k) by lia.
  destruct H3 as [? | [? | ?]].
  repeat rewrite Znth_underflow; trivial.
  2: repeat rewrite Znth_overflow; try rewrite Zlength_Zexchange; trivial; lia.
  apply nth_error_Znth; auto. rewrite Zlength_Zexchange. trivial.
  apply nth_error_exchange''.
  intro. apply H1. apply Z2Nat.inj; lia.
  intro. apply H2. apply Z2Nat.inj; lia.
Qed.

Lemma Zexchange_eq: forall A (L : list A) i,
  Zexchange L i i = L.
Proof. unfold Zexchange. intros. apply exchange_eq. Qed.

Lemma upd_Znth_overwrite:
  forall {A} (l : list A) i a b,
    0 <= i < Zlength l ->
    upd_Znth i (upd_Znth i l a) b = upd_Znth i l b.
Proof.
  intros.
  rewrite upd_Znth_unfold by now rewrite upd_Znth_Zlength.
  rewrite upd_Znth_Zlength; trivial.
  repeat rewrite upd_Znth_unfold by trivial.
  rewrite sublist0_app1.
  2: rewrite Zlength_sublist; lia.
  rewrite sublist_sublist00 by lia.
  f_equal. f_equal.
  rewrite app_assoc.
  rewrite sublist_app2.
  2: { rewrite Zlength_app, Zlength_sublist by lia.
       unfold Zlength. simpl. lia.
  }
  rewrite Zlength_app, Zlength_sublist by lia.
  unfold Zlength at 1; simpl.
  rewrite sublist_same; trivial.
  - lia.
  - unfold Zlength at 2; simpl.
    rewrite Zlength_sublist by lia. lia.
Qed.

Lemma upd_Znth_same_Znth:
  forall {A} `{Ia : Inhabitant A} (l: list A) i,
    0 <= i < Zlength l ->
    upd_Znth i l (Znth i l) = l.
Proof.
  intros. rewrite upd_Znth_unfold by trivial.
  rewrite <- sublist_len_1 by trivial.
  repeat rewrite <- sublist_split.
  apply sublist_same; trivial.
  all: lia.
Qed.

Lemma exchange_eq_nil: forall A (L : list A) i j,
  exchange L i j = [] ->
  L = [].
Proof. unfold exchange. intros A L i j. case nth_error; auto. case nth_error; auto.
  destruct L. trivial. destruct j, i; simpl; discriminate.
Qed.

Lemma nth_error_eq: forall A (L1 L2 : list A),
  (forall i, nth_error L1 i = nth_error L2 i) ->
  L1 = L2.
Proof.
  induction L1. destruct L2; auto; intros. specialize (H 0%nat); discriminate.
  destruct L2. intro. specialize (H 0%nat); discriminate. intros.
  f_equal. specialize (H 0%nat). inversion H. trivial.
  apply IHL1. intro. specialize (H (S i)). apply H.
Qed.

Lemma Zexchange_head_foot: forall A (head : A) body foot,
  Zexchange ((head :: body) ++ [foot]) 0 (Zlength (head :: body)) = ((foot :: body) ++ [head]).
Proof.
  intros.
  apply nth_error_eq. intro i'. unfold Zexchange. simpl Z.to_nat. case (eq_nat_dec i' 0); intro.
  + subst i'. 
    rewrite nth_error_exchange; simpl. 2: lia.
    rewrite app_comm_cons. rewrite ZtoNat_Zlength.
    rewrite nth_error_app2. simpl. rewrite Nat.sub_diag. trivial. lia.
    rewrite ZtoNat_Zlength. rewrite app_length. simpl. lia.
  + case (eq_nat_dec i' (Z.to_nat (Zlength (head :: body)))); intro.
    - subst i'.
      rewrite nth_error_exchange'; simpl. 2: lia.
      rewrite app_comm_cons. rewrite ZtoNat_Zlength.
      rewrite nth_error_app2. simpl. rewrite Nat.sub_diag. trivial. simpl. lia.
      rewrite ZtoNat_Zlength. rewrite app_length. simpl. lia.
    - rewrite nth_error_exchange''; auto.
      destruct i'. contradiction. simpl. rewrite ZtoNat_Zlength in n0. simpl in n0.
      assert (i' < (length body) \/ i' >= length (body ++ [foot]))%nat. { rewrite app_length. simpl. lia. }
      destruct H. repeat rewrite nth_error_app1; auto.
      assert (i' >= length (body ++ [head]))%nat. { rewrite app_length in *. simpl in *. lia. }
      apply nth_error_None in H. apply nth_error_None in H0. congruence.
Qed.

Lemma Permutation_Zlength: forall A (L1 : list A) L2,
  Permutation L1 L2 ->
  Zlength L1 = Zlength L2.
Proof.
  intros. apply Permutation_length in H. do 2 rewrite Zlength_correct. congruence.
Qed.


(* Relation on heap items. *)
Definition heap_item : Type := (int * int)%type.
Definition cmp (a b : heap_item) : bool :=
  negb (Int.lt (fst b) (fst a)).
Definition cmp_rel (a b : heap_item) : Prop :=
  cmp a b = true.
Lemma cmp_dec: forall a a', {cmp_rel a a'} + {~cmp_rel a a'}.
Proof.
  intros [? ?] [? ?]. unfold cmp_rel, cmp. simpl. case (Int.lt i1 i); simpl; auto.
Qed. 
Instance cmp_po: PreOrder cmp_rel.
Proof.
  constructor. intros [? ?]. red. unfold cmp. simpl. case_eq (Int.lt i i); auto; intro. exfalso.
  apply lt_inv in H. lia.
  intros [? ?] [? ?] [? ?]. unfold cmp_rel, cmp. simpl. 
  case_eq (Int.lt i3 i); auto.
  case_eq (Int.lt i1 i); auto.
  case_eq (Int.lt i3 i1); auto. simpl.
  intros ? ? ?. exfalso.
  apply lt_inv in H1.
  apply lt_false_inv in H.
  apply lt_false_inv in H0.
  lia.
Qed.
Lemma cmp_linear: forall a b,
  cmp_rel a b \/ cmp_rel b a.
Proof.
  intros [? ?] [? ?]. unfold cmp_rel, cmp; simpl.
  case_eq (Int.lt i1 i); auto. intro. 
  right.
  case_eq (Int.lt i i1); auto. intro. exfalso. 
  apply lt_inv in H. apply lt_inv in H0.
  lia.
Qed.

(* Not sure if it's a great idea to expose the capacity inside the abstraction boundary. *)
Definition heap : Type := (nat * list heap_item)%type.
Instance heap_inhabitant : Inhabitant heap := (O, []).
Definition heap_capacity (h : heap) : Z := Z.of_nat (fst h).
Definition heap_items (h : heap) : list heap_item := snd h.
Definition heap_size (h : heap) : Z := Zlength (heap_items h).

(*
Definition heap_permutation (h1 h2 : heap) : Prop :=
  heap_capacity h1 = heap_capacity h2 /\ Permutation (heap_items h1) (heap_items h2).
*)

Definition heap_ordered := binary_heap_model.heapOrdered heap_item cmp_rel.
Definition weak_heap_ordered_bottom_up (L : list heap_item) (x : Z) := 
  binary_heap_model.weak_heapOrdered2 heap_item cmp_rel L (Z.to_nat x).
Definition weak_heap_ordered_top_down (L : list heap_item) (x : Z) := 
  binary_heap_model.weak_heapOrdered heap_item cmp_rel L (Z.to_nat x).
Definition swim := binary_heap_model.swim heap_item cmp_rel cmp_dec.
Definition sink L i := binary_heap_model.sink heap_item cmp_rel cmp_dec (L,i).
(* Definition insert := binary_heap_model.insert heap_item cmp_rel cmp_dec. *)
(* Definition remove_min := binary_heap_model.remove_min heap_item cmp_rel cmp_dec. *)
Definition Zleft_child i  := Z.of_nat (binary_heap_model.left_child  (Z.to_nat i)).
Lemma Zleft_child_unfold: forall i,
  0 <= i ->
  Zleft_child i = (2 * i) + 1.
Proof.
  unfold Zleft_child, binary_heap_model.left_child. intros.
  do 2 rewrite Nat2Z.inj_add. rewrite Z2Nat.id; lia.
Qed.
Definition Zright_child i := Z.of_nat (binary_heap_model.right_child (Z.to_nat i)).
Lemma Zright_child_unfold: forall i,
  Zright_child i = Zleft_child i + 1.
Proof.
  unfold Zright_child, Zleft_child, binary_heap_model.right_child. intros.
  rewrite Nat2Z.inj_add. trivial.
Qed.
Definition Zparent (i : Z) : Z := Z.of_nat (parent (Z.to_nat i)).
Lemma Zparent_unfold: forall i,
  0 < i ->
  Zparent i = (i - 1) / 2.
Proof.
  unfold Zparent, parent. intros.
  rewrite Nat.div2_div, div_Zdiv; auto.
  rewrite Nat2Z.inj_sub. rewrite Z2Nat.id; lia.
  lia.
Qed.
Lemma Zparent_0:
  Zparent 0 = 0.
Proof. reflexivity. Qed.
Lemma Zparent_repr: forall i,
  0 < i <= Int.max_unsigned ->
  Int.repr (Zparent i) = Int.divu (Int.repr (i - 1)) (Int.repr 2).
Proof.
  intros. unfold Int.divu. repeat rewrite Int.unsigned_repr.
  2,3: rep_lia. rewrite Zparent_unfold. trivial. lia.
Qed.

(* This may get bundled elsewhere at some point. *)
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.

Definition t_item := Tstruct _structItem noattr.
Definition t_pq := Tstruct _structPQ noattr.

Definition heap_item_rep (i : heap_item) : reptype t_item :=
  (Vint (fst i), Vint (snd i)).

Definition hitem (i : heap_item) : val -> mpred :=
  data_at Tsh t_item (heap_item_rep i).

Definition harray (contents : list heap_item) : val -> mpred :=
  data_at Tsh (tarray t_item (Zlength contents)) (map heap_item_rep contents).

Lemma harray_emp: forall arr,
  harray [] arr |-- emp.
Proof.
  unfold harray. intros. rewrite data_at_isptr. entailer. rewrite data_at_zero_array_eq; auto.
Qed.

Lemma fold_harray': forall L i arr,
  i = Zlength L ->
  data_at Tsh (tarray t_item i) (map heap_item_rep L) arr = harray L arr.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma fold_harray: forall L arr,
  data_at Tsh (tarray t_item (Zlength L)) (map heap_item_rep L) arr = harray L arr.
Proof. reflexivity. Qed.

Lemma harray_split: forall L1 L2 ptr,
  harray (L1 ++ L2) ptr = 
  ((harray L1 ptr) * 
   (harray L2 (field_address0 (tarray t_item (Zlength (L1 ++ L2))) [ArraySubsc (Zlength L1)] ptr)))%logic.
Proof.
  intros. unfold harray.
  rewrite map_app.
  erewrite split2_data_at_Tarray_app.
  2: rewrite Zlength_map; reflexivity. 2: rewrite Zlength_app, Zlength_map; lia.
  rewrite Zlength_app.
  replace (Zlength L1 + Zlength L2 - Zlength L1) with (Zlength L2) by lia.
  trivial.
Qed.

Definition valid_pq (pq : val) (h: heap): mpred :=
  EX arr : val, EX junk: list heap_item,
    (!! heap_ordered (heap_items h)) && (!! (Zlength ((heap_items h) ++ junk) = heap_capacity h)) &&
    (data_at Tsh t_pq (Vint (Int.repr (heap_capacity h)), (Vint (Int.repr (heap_size h)), arr)) pq *
       harray ((heap_items h) ++ junk) arr).

Definition exch_spec :=
  DECLARE _exch WITH i : Z, j : Z, arr: val, arr_contents: list heap_item
  PRE [tuint, tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents; 0 <= j < Zlength arr_contents)
    PARAMS (Vint (Int.repr i); Vint (Int.repr j); arr)
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    PROP ()
    LOCAL ()
    SEP (harray (Zexchange arr_contents i j) arr).

Definition less_spec :=
  DECLARE _less WITH i : Z, j : Z, arr: val, arr_contents: list heap_item
  PRE [tuint, tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents; 0 <= j < Zlength arr_contents)
    PARAMS (Vint (Int.repr i); Vint (Int.repr j); arr)
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Val.of_bool (cmp (Znth i arr_contents) (Znth j arr_contents))))
    SEP (harray arr_contents arr).

Definition swim_spec :=
  DECLARE _swim WITH i : Z, arr: val, arr_contents: list heap_item
  PRE [tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents;
          weak_heap_ordered_bottom_up arr_contents i)
    PARAMS (Vint (Int.repr i); arr)
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    EX arr_contents' : list (int * int),
      PROP (heap_ordered arr_contents'; Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (harray arr_contents' arr).

Definition size_spec := 
  DECLARE _size WITH pq : val, h : heap
  PRE [tptr t_pq]
    PROP ()
    PARAMS (pq)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (heap_size h))))
    SEP (valid_pq pq h).

Definition capacity_spec := 
  DECLARE _capacity WITH pq : val, h : heap
  PRE [tptr t_pq]
    PROP ()
    PARAMS (pq)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (heap_capacity h))))
    SEP (valid_pq pq h).

Definition remove_min_nc_spec :=
  DECLARE _remove_min_nc WITH pq : val, h : heap, i : val, iv : heap_item
  PRE [tptr t_pq, tptr t_item]
    PROP (heap_size h > 0)
    PARAMS (pq; i)
    GLOBALS ()
    SEP (valid_pq pq h; hitem iv i)
  POST [tvoid]
  EX h', EX iv' : heap_item,
    PROP (heap_capacity h = heap_capacity h';
          Permutation (heap_items h) (iv' :: heap_items h');
          Forall (cmp_rel iv') (heap_items h'))
    LOCAL ()
    SEP (valid_pq pq h'; hitem iv' i).

Definition insert_nc_spec :=
  DECLARE _insert_nc WITH pq : val, h : heap, i : val, iv : heap_item
  PRE [tptr t_pq, tptr t_item]
    PROP (heap_size h < heap_capacity h)
    PARAMS (pq; i)
    GLOBALS ()
    SEP (valid_pq pq h; hitem iv i)
  POST [tvoid]
  EX h',
    PROP (heap_capacity h = heap_capacity h';
          Permutation (iv :: heap_items h) (heap_items h'))
    LOCAL ()
    SEP (valid_pq pq h'; hitem iv i).

Definition sink_spec :=
  DECLARE _sink WITH i : Z, arr: val, arr_contents: list heap_item, first_available : Z
  PRE [tuint, tptr t_item, tuint]
    PROP (0 <= i <= Zlength arr_contents; 
          first_available = Zlength arr_contents;
          (2 * first_available) <= Int.max_unsigned; (* i = fa - 1 -> (2 * i + 1) = 2 * fa - 1, must be representable *)
          weak_heap_ordered_top_down arr_contents i)
    PARAMS (Vint (Int.repr i); arr; Vint (Int.repr first_available))
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    EX arr_contents' : list heap_item,
      PROP (heap_ordered arr_contents' /\ Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (harray arr_contents' arr).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ exch_spec ; less_spec ; swim_spec ; sink_spec ; 
                                   remove_min_nc_spec ; insert_nc_spec ; 
                                   size_spec ; capacity_spec ]).

Axiom admit: forall (P: Prop), P.


Lemma slow_qed : 
forall (arr : val)
   (first_available : Z)
   (Delta : tycontext)
  (i' : Z)
  (arr_contents' : list heap_item)
  (H7 : ENTAIL Delta,
     PROP ( )
     LOCAL (temp _j (Vint (Int.repr (Zleft_child i')));
     temp _k (Vint (Int.repr i')); temp _arr arr;
     temp _first_available (Vint (Int.repr first_available)))
     SEP (harray arr_contents' arr)
     |-- local
           (liftx
              (eq
                 (if
                   Int.ltu (Int.add (Int.repr (Zleft_child i')) (Int.repr 1))
                     (Int.repr first_available)
                  then Vtrue
                  else Vfalse))
              (liftx
                 (force_val2
                    (both_int
                       (fun n1 n2 : int => Some (Val.of_bool (Int.ltu n1 n2)))
                       sem_cast_pointer sem_cast_pointer))
                 (liftx
                    (force_val2
                       (both_int
                          (fun n1 n2 : int => Some (Vint (Int.add n1 n2)))
                          sem_cast_pointer sem_cast_pointer)) 
                    (eval_id _j) (liftx (Vint (Int.repr 1))))
                 (eval_id _first_available)))),
True.
Proof.
intros.
match type of H7 with _ |-- ?A => replace A with (@TT (environ->mpred) _) in H7 by apply admit end.
auto.
Qed.



Lemma body_sink: semax_body Vprog Gprog f_sink sink_spec.
Proof.
  start_function.
  assert (Hc : i = Zlength arr_contents \/ 0 <= i < Zlength arr_contents) by lia. destruct Hc as [Hc | Hc].
* (* Special case: oob sink, used when removing the last element of the heap. *)
  forward_while ( PROP () LOCAL (temp _k (Vint (Int.repr i)); temp _first_available (Vint (Int.repr first_available))) SEP (harray arr_contents arr) ).
  entailer!. entailer. lia.
  forward.
  Exists arr_contents. entailer!.
  eapply weak_heapOrdered_oob. 2: apply H2. rewrite Zlength_correct. lia.
* (* Main line *)
(* 0.08 to here *)
  forward_loop (EX i' : Z, EX arr_contents' : list heap_item, 
                 PROP (0 <= i' < Zlength arr_contents; 
                       sink arr_contents (Z.to_nat i) = sink arr_contents' (Z.to_nat i'))
                 LOCAL (temp _k (Vint (Int.repr i')); temp _arr arr; temp _first_available (Vint (Int.repr first_available)))
                 SEP (harray arr_contents' arr)).
  Exists i arr_contents. entailer!.
  Intros i' arr_contents'.
  assert (Zlength arr_contents = Zlength arr_contents'). { unfold sink in H4. 
    pose proof (sink_permutation _ cmp_rel cmp_dec arr_contents (Z.to_nat i)).
    pose proof (sink_permutation _ cmp_rel cmp_dec arr_contents' (Z.to_nat i')).
    apply Permutation_Zlength in H5. apply Permutation_Zlength in H6. congruence. }
  forward_if (Zleft_child i' < first_available).
    { forward. entailer!. rewrite Zleft_child_unfold; lia. }
    { forward. (* Prove postcondition *)
      Exists arr_contents'. entailer!. unfold sink at 2 in H4.
      rewrite <- Zleft_child_unfold in H6 by lia.
      unfold Zleft_child in H6. rewrite H5 in H6. rewrite Zlength_correct in H6.
      erewrite sink_done in H4. 2: apply Znth_nth_error; lia.
      rewrite <- H4. { split. 
      * apply sink_hO. apply cmp_po. apply cmp_linear. apply H2. 
      * apply sink_permutation. }
      intros. assert (left_child (Z.to_nat i') < length arr_contents')%nat by (apply nth_error_Some; congruence).
      lia.
      intros. assert (right_child (Z.to_nat i') < length arr_contents')%nat by (apply nth_error_Some; congruence).
      unfold right_child in H7. lia. }
  forward.
(* 0.22 to here *)
  rewrite mul_repr, add_repr. rewrite <- Zleft_child_unfold by lia.

  check_Delta; check_POSTCONDITION;
  repeat (apply -> seq_assoc; abbreviate_semax);
  repeat apply -> semax_seq_skip.
apply semax_seq with (EX b : bool, PROP (if b then Zright_child i' <  first_available /\  cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents')
                                      else Zright_child i' >= first_available \/ ~cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents') )
                           LOCAL (temp _t'1 (Val.of_bool b); temp _k (Vint (Int.repr i')); temp _j (Vint (Int.repr (Zleft_child i'))); temp _arr arr; temp _first_available (Vint (Int.repr first_available))) 
                           SEP (harray arr_contents' arr)).

  check_Delta; check_POSTCONDITION.
 repeat apply -> semax_seq_skip;
 repeat (apply seq_assoc1; try apply -> semax_seq_skip).

match goal with
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sifthenelse ?e ?c1 ?c2) _ =>
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R e v HRE;
    simpl in v;

    apply (semax_ifthenelse_PQR' _ v);
idtac end.
 reflexivity.



 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end.
 match goal with
 | |- ?P |-- _ =>
    match type of P with
    | ?T => unify T (environ->mpred); clean_up_stackframe; go_lower
    | _ => clear_Delta; pull_out_props
    end
 | |- _ => fail "The entailer tactic works only on entailments   _ |-- _ "
 end.

 saturate_local.


    repeat simplify_float2int;
    gather_prop.

    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true).

   repeat erewrite unfold_reptype_elim in * by (apply JMeq_refl; reflexivity).

   simpl_compare.

   simpl_denote_tc.
apply prop_right.
clearbody Delta.
clear - H7.
2,3,4,5: apply admit.
subst v.
unfold eval_expr in H7.
simpl eval_binop in H7.
match type of H7 with _ |-- ?A => set (j:=A) in H7 end.
clearbody j.
set (c := andp _ _) in *.
clearbody c.
clear - H7.
(* UNCOMMENT THIS LINE TO HAVE Qed BLOW UP IN Coq 8.11.1 
    replace c with j in H7 by apply admit.  *)
auto.
Qed.