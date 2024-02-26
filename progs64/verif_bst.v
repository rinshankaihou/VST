(* Do not edit this file, it was generated automatically *)
Require Import VST.floyd.proofauto VST.floyd.compat.
Require Import VST.progs64.bst.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.

Section TREES.
Variable V : Type.
Variable default: V.

Definition key := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.

Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint delete (x: key) (s: tree) : tree :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else pushdown_left a b
 end.

End TREES.
Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Fixpoint tree_rep (t: tree val) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.

Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.

(* TODO: seems not useful *)
Lemma treebox_rep_spec: forall (t: tree val) (b: val),
  treebox_rep t b ⊣⊢
  EX p: val, 
  match t with
  | E => !!(p=nullval) && data_at Tsh (tptr t_struct_tree) p b
  | T l x v r => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      data_at Tsh (tptr t_struct_tree) p b *
      spacer Tsh (sizeof tint) (sizeof size_t) p *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
      field_at Tsh t_struct_tree [StructField _value] v p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.
Proof.
  intros.
  unfold treebox_rep at 1.
  f_equiv; intros p.
  destruct t; simpl.
  + apply pred_ext; entailer!!.
  + unfold treebox_rep.
    apply pred_ext; entailer!!.
    - Intros pa pb.
      Exists pa pb.
      unfold_data_at (data_at _ _ _ p).
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
    - Intros pa pb.
      Exists pa pb.
      unfold_data_at (data_at _ _ _ p).
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
Qed.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ tint]
     PROP (4 <= n <= Int.max_unsigned)
     PARAMS (Vint (Int.repr n))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     RETURN (v)
     SEP (memory_block Tsh n v).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ tptr tvoid , tint]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() PARAMS(p; Vint (Int.repr n))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () RETURN ( ) SEP ().

Definition treebox_new_spec :=
 DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
       PROP() PARAMS() SEP ()
  POST [ tptr (tptr t_struct_tree) ]
    EX v:val,
    PROP()
    RETURN(v)
    SEP (data_at Tsh (tptr t_struct_tree) nullval v).

Definition insert_spec :=
 DECLARE _insert
  WITH b: val, x: Z, v: val, t: tree val
  PRE  [ tptr (tptr t_struct_tree), tint, tptr Tvoid ]
    PROP( Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
    PARAMS(b; Vint (Int.repr x); v)
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    RETURN( )
    SEP (treebox_rep (insert x v t) b).

Definition lookup_spec :=
 DECLARE _lookup
  WITH b: val, x: Z, v: val, t: tree val
  PRE  [ tptr (tptr t_struct_tree), tint  ]
    PROP( Int.min_signed <= x <= Int.max_signed)
    PARAMS(b; Vint (Int.repr x))
    SEP (treebox_rep t b)
  POST [ tptr Tvoid ]
    PROP()
    RETURN(lookup nullval x t)
    SEP (treebox_rep t b).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH ta: tree val, x: Z, vx: val, tb: tree val, y: Z, vy: val, tc: tree val, b: val, l: val, pa: val, r: val
  PRE  [ tptr (tptr (Tstruct _tree noattr)),
        tptr (Tstruct _tree noattr),
        tptr (Tstruct _tree noattr)]
    PROP(Int.min_signed <= x <= Int.max_signed; is_pointer_or_null vx)
    PARAMS(b; l; r)
    SEP (data_at Tsh (tptr t_struct_tree) l b;
         data_at Tsh t_struct_tree (Vint (Int.repr x), (vx, (pa, r))) l;
         tree_rep ta pa;
         tree_rep (T tb y vy tc) r)
  POST [ Tvoid ] 
    EX pc: val,
    PROP(Int.min_signed <= y <= Int.max_signed; is_pointer_or_null vy)
    RETURN( )
    SEP (data_at Tsh (tptr t_struct_tree) r b;
         data_at Tsh t_struct_tree (Vint (Int.repr y), (vy, (l, pc))) r;
         tree_rep (T ta x vx tb) l;
         tree_rep tc pc).

Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH ta: tree val, x: Z, v: val, tb: tree val, b: val, p: val
  PRE  [ tptr (tptr (Tstruct _tree noattr))]
    PROP(Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) v)
    PARAMS(b)
    SEP (data_at Tsh (tptr t_struct_tree) p b;
         spacer Tsh (sizeof tint) (sizeof size_t) p;
         field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p;
         field_at Tsh t_struct_tree [StructField _value] v p;
         treebox_rep ta (field_address t_struct_tree [StructField _left] p);
         treebox_rep tb (field_address t_struct_tree [StructField _right] p))
  POST [ Tvoid ] 
    PROP()
    RETURN( )
    SEP (treebox_rep (pushdown_left ta tb) b).

Definition delete_spec :=
 DECLARE _delete
  WITH b: val, x: Z, t: tree val
  PRE  [ tptr (tptr t_struct_tree), tint]
    PROP( Int.min_signed <= x <= Int.max_signed)
    PARAMS(b; Vint (Int.repr x))
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    RETURN( )
    SEP (treebox_rep (delete x t) b).

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH t: tree val, p: val
  PRE  [ tptr t_struct_tree ]
       PROP() PARAMS (p) SEP (tree_rep t p)
  POST [ Tvoid ]
    PROP()
    RETURN()
    SEP (emp).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH t: tree val, b: val
  PRE  [ tptr (tptr t_struct_tree) ]
       PROP() PARAMS(b) SEP (treebox_rep t b)
  POST [ Tvoid ]
    PROP()
    RETURN()
    SEP (emp).

Definition Gprog : funspecs :=
    ltac:(with_library prog [
    mallocN_spec; freeN_spec; treebox_new_spec;
    tree_free_spec; treebox_free_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec
  ]).

Lemma tree_rep_saturate_local:
   forall t p, tree_rep t p |-- !! is_pointer_or_null p.
Proof.
destruct t; simpl; intros.
entailer!!.
Intros pa pb. entailer!.
Qed.

#[export] Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; Intros; try Intros pa pb; subst; auto with valid_pointer.
Qed.
#[export] Hint Resolve tree_rep_valid_pointer: valid_pointer.

Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree) [] b.
Proof.
intros.
unfold treebox_rep.
Intros p.
entailer!.
Qed.

#[export] Hint Resolve treebox_rep_saturate_local: saturate_local.

Definition insert_inv (b0: val) (t0: tree val) (x: Z) (v: val): assert :=
  EX b: val, EX t: tree val,
  PROP()
  LOCAL(temp _t b; temp _x (Vint (Int.repr x));   temp _value v)
  SEP(treebox_rep t b;  (treebox_rep (insert x v t) b -* treebox_rep (insert x v t0) b0)).

Lemma tree_rep_nullval: forall t,
  tree_rep t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer!! |].
  simpl tree_rep.
  Intros pa pb. entailer!.
Qed.

#[export] Hint Resolve tree_rep_nullval: saturate_local.

Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- treebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!!.
Qed.

Lemma bst_left_entail: forall (t1 t1' t2: tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t1 (field_address t_struct_tree [StructField _left] p) *
       (treebox_rep t1'
         (field_address t_struct_tree [StructField _left] p) -*
        treebox_rep (T t1' k v t2) b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.

  iIntros "(? & ? & ? & ? & ? & ?) Hleft".
  clear p1.
  unfold treebox_rep.
  iExists p.
  simpl.
  iDestruct "Hleft" as (p1) "(? & ?)".
  iFrame.
  iSplit; first done.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  iFrame.
Qed.

Lemma bst_right_entail: forall (t1 t2 t2': tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t2 (field_address t_struct_tree [StructField _right] p) *
       (treebox_rep t2'
         (field_address t_struct_tree [StructField _right] p) -*
        treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.

  iIntros "(? & ? & ? & ? & ? & ?) Hright".
  clear p2.
  unfold treebox_rep.
  iExists p.
  simpl.
  iDestruct "Hright" as (p2) "(? & ?)".
  iFrame.
  iSplit; first done.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  iFrame.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply Z.ltb_lt; lia)
                          | rewrite if_falseb by (apply Z.ltb_ge; lia)].

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ _ (insert_inv b t x v) (insert_inv b t x v) )].
  * (* Precondition *)
    unfold insert_inv.
    Exists b t. entailer.
    iIntros "$ $".
  * (* Loop body *)
    unfold insert_inv at 1.
    Intros b1 t1.
    forward. (* Sskip *)
    forward. (* p = *t; *)
    forward_if.
    + (* then clause *)
      subst p.
      Time forward_call (sizeof t_struct_tree).
      Intros p'.
      rewrite memory_block_data_at_ by auto.
      forward. (* p->key=x; *)
      simpl.
      forward. (* p->value=value; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)
      assert_PROP (t1= (@E _)) by entailer!.
      subst t1. simpl tree_rep. rewrite !prop_true_andp by auto.
      forward. (* *t = p; *)
      forward. (* return; *)
      iIntros "(? & H)"; iApply "H".
      by iApply treebox_rep_leaf.
    + (* else clause *)
      destruct t1.
        { simpl tree_rep. Intros. contradiction. }
      simpl tree_rep.
      Intros pa pb. clear H1.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _left] p) t1_1.
        entailer!. simpl.
        simpl_compb.
        sep_apply (bst_left_entail t1_1 (insert x v t1_1)).
        iIntros "(($ & H1) & Ht) ?".
        iApply "Ht"; iApply "H1"; done.
      - (* Inner if, second branch:  k<x *)
        forward. (* t=&p->right *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _right] p) t1_2.
        entailer!. simpl.
        simpl_compb; simpl_compb.
        sep_apply (bst_right_entail t1_1 t1_2 (insert x v t1_2)).
        iIntros "(($ & H1) & Ht) ?".
        iApply "Ht"; iApply "H1"; done.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by lia.
        subst x.  clear H H1 H3.
        forward. (* p->value=value *)
        forward. (* return *) simpl.
        (* TODO: SIMPLY THIS LINE *)
        simpl_compb.
        simpl_compb.
        iIntros "(? & H)"; iApply "H"; iStopProof.
        unfold treebox_rep. Exists p.
        simpl tree_rep. Exists pa pb. entailer!!.
  * (* After the loop *)
    forward.
    auto.
Qed.

Definition lookup_inv (b0 p0: val) (t0: tree val) (x: Z): assert :=
  EX p: val, EX t: tree val, 
  PROP(lookup nullval x t = lookup nullval x t0) 
  LOCAL(temp _p p; temp _x (Vint (Int.repr x)))
  SEP(tree_rep t p;  (tree_rep t p -* tree_rep t0 p0)).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  forward. (* p=*t; *)
  apply (semax_post_ret1 nil
          (data_at Tsh (tptr t_struct_tree) p b :: tree_rep t p :: nil)).
  1: intro HH; inversion HH.
  1: unfold treebox_rep; Exists p; entailer!!.
  apply semax_frame''.
  forward_while (lookup_inv b p t x).
  * (* precondition implies loop invariant *)
    Exists p t. entailer!.
    auto.
  * (* type-check loop condition *)
    entailer!.
  * (* loop body preserves invariant *)
    destruct t0; unfold tree_rep at 1; fold tree_rep. Intros; contradiction.
    Intros pa pb. unfold tptr in H2.
    forward.
    forward_if; [ | forward_if ].
    + (* then clause: x<y *)
      forward. (* p=p<-left *)
      Exists (pa,t0_1). unfold fst,snd.
      entailer!!.
      - rewrite <- H0; simpl.
        simpl_compb; auto.
      - iIntros "(? & ? & H) ?"; iApply "H"; iStopProof.
        simpl. Exists pa pb; entailer!.
    + (* else-then clause: y<x *)
      forward. (* p=p<-right *)
      Exists (pb,t0_2). unfold fst,snd.
      entailer!!.
      - rewrite <- H0; simpl.
        simpl_compb; simpl_compb; auto.
      - iIntros "(? & ? & H) ?"; iApply "H"; iStopProof.
        simpl. Exists pa pb; entailer!.
    + (* else-else clause: x=y *)
      assert (x=k) by lia. subst x. clear H H3 H4.
      forward. (* v=p->value *)
      forward. (* return v; *) simpl.
      entailer!!.
      - rewrite <- H0. simpl.
        simpl_compb; simpl_compb; auto.
      - iIntros "(? & ? & ? & H)"; iApply "H"; iStopProof.
        Exists pa pb; entailer!!.
  * (* after the loop *)
    forward. (* return NULL; *)
    entailer!.
    iIntros "(? & H)"; iApply "H"; done.
Qed.

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  simpl.
  Intros pb pc.
  forward. (* mid=r->left *)
  forward. (* l->right=mid *)
  forward. (* r->left=l *)
  forward. (* _l = r *)
  Exists pc.
  entailer!!.
  simpl.
  Exists pa pb.
  entailer!!.
Qed.

Definition pushdown_left_inv (b_res: val) (t_res: tree val): assert :=
  EX b: val, EX ta: tree val, EX x: Z, EX v: val, EX tb: tree val,
  PROP  () 
  LOCAL (temp _t b)
  SEP   (treebox_rep (T ta x v tb) b;
         (treebox_rep (pushdown_left ta tb) b -* treebox_rep t_res b_res)).

Lemma cancel_emp_spacer:
  forall sh x y p, x=y ->
    emp |-- spacer sh x y p.
Proof.
intros.
subst.
unfold spacer.
rewrite Z.sub_diag. simpl. auto.
Qed.

Lemma cancel_spacer_emp:
  forall sh x y p, x=y -> 
    spacer sh x y p |-- emp.
Proof.
intros.
subst.
unfold spacer.
rewrite Z.sub_diag. simpl. auto.
Qed.

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ _ (pushdown_left_inv b (pushdown_left ta tb))
                         (pushdown_left_inv b (pushdown_left ta tb)))].
  + (* Precondition *)
    unfold pushdown_left_inv.
    Exists b ta x v tb.
    entailer!!.
    rewrite (treebox_rep_spec (T ta x v tb)).
    Exists p.
    entailer!!.
    auto.
  + (* Loop body *)
    unfold pushdown_left_inv.
    clear x v H H0.
    Intros b0 ta0 x vx tbc0.
    unfold treebox_rep at 1.
    Intros p0.
    forward. (* skip *)
    forward. (* p = *t; *)
    simpl tree_rep.
    Intros pa pbc.
    forward. (* q = p->right *)
    forward_if.
    - subst.
      assert_PROP (tbc0 = (@E _)) by entailer!.
      subst.
      forward. (* q=p->left *)
      forward. (* *t=q *)
      Time forward_call (p0, sizeof t_struct_tree). (* freeN(p, sizeof ( *p )); *)
      {
        entailer!.
        rewrite memory_block_data_at_ by auto.
        cancel.
      }
      forward. (* return *)
      simpl.
      iIntros "(? & H)"; iApply "H"; iStopProof.
      unfold treebox_rep; Exists pa.
      entailer!!.
    - destruct tbc0 as [| tb0 y vy tc0].
        { simpl tree_rep. Intros; contradiction. }
      Time forward_call (ta0, x, vx, tb0, y, vy, tc0, b0, p0, pa, pbc). (* turn_left(t, p, q); *)
      Intros pc.
      forward. (* t = &q->left; *)
      Exists (field_address t_struct_tree [StructField _left] pbc) ta0 x vx tb0.
      (* TODO entailer: not to simply too much in entailer? *)
      Opaque tree_rep. entailer!. Transparent tree_rep.
      sep_apply (bst_left_entail (T ta0 x vx tb0) (pushdown_left ta0 tb0)).
      iIntros "(($ & H1) & Ht) ?".
      iApply "Ht"; iApply "H1"; done.
  + forward. (* Sskip *)
    auto.
Qed.

Definition delete_inv (b0: val) (t0: tree val) (x: Z): assert :=
  EX b: val, EX t: tree val,
  PROP()
  LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
  SEP(treebox_rep t b;  (treebox_rep (delete x t) b -* treebox_rep (delete x t0) b0)).

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ _ (delete_inv b t x) (delete_inv b t x) )].
  * (* Precondition *)
    unfold delete_inv.
    Exists b t. entailer.
    iIntros "$ $".
  * (* Loop body *)
    unfold delete_inv.
    Intros b1 t1.
    forward. (* Sskip *)
    unfold treebox_rep at 1. Intros p1.
    forward. (* p = *t; *)
    forward_if.
    + (* then clause *)
      subst p1.
      assert_PROP (t1= (@E _)) by entailer!.
      subst t1. simpl tree_rep. rewrite !prop_true_andp by auto.
      forward. (* return; *)
      unfold treebox_rep at 1.
      iIntros "(? & H)"; iApply "H"; iStopProof.
      Exists nullval.
      simpl tree_rep.
      entailer!!.
    + (* else clause *)
      destruct t1.
        { simpl tree_rep.  Intros; contradiction. }
      simpl tree_rep.
      Intros pa pb. clear H0.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold delete_inv.
        Exists (field_address t_struct_tree [StructField _left] p1) t1_1.
        entailer!. simpl.
        simpl_compb.
        sep_apply (bst_left_entail t1_1 (delete x t1_1)).
        iIntros "(($ & H1) & Ht) ?"; iApply "Ht"; iApply "H1"; done.
      - (* Inner if, second branch:  k<x *)
        forward. (* t=&p->right *)
        unfold delete_inv.
        Exists (field_address t_struct_tree [StructField _right] p1) t1_2.
        entailer!. simpl.
        simpl_compb; simpl_compb.
        sep_apply (bst_right_entail t1_1 t1_2 (delete x t1_2)).
        iIntros "(($ & H1) & Ht) ?"; iApply "Ht"; iApply "H1"; done.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by lia.
        subst x.
        unfold_data_at (data_at _ _ _ p1).
        gather_SEP (field_at _ _ [StructField _left] _ _)
                        (tree_rep _ pa).

        replace_SEP 0 (treebox_rep t1_1 (field_address t_struct_tree [StructField _left] p1)).
        {
          unfold treebox_rep; entailer!.
          Exists pa.
          rewrite field_at_data_at. simpl.
          entailer!.
        }
        gather_SEP (field_at _ _ [StructField _right] _ _)
                        (tree_rep _ pb).
        replace_SEP 0 (treebox_rep t1_2 (field_address t_struct_tree [StructField _right] p1)).
        {
          unfold treebox_rep; entailer!!.
          Exists pb.
          rewrite field_at_data_at.
          entailer!!.
        }
        Time forward_call (t1_1, k, v, t1_2, b1, p1);
                    [entailer! .. | ].
        forward. (* return *)
        simpl.
        simpl_compb.
        simpl_compb.
        iIntros "(? & H)"; iApply "H"; done.
  * (* After the loop *)
    forward. auto.
Qed.

Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  Time forward_call (sizeof (tptr t_struct_tree)).
  Intros p.
  rewrite memory_block_data_at_ by auto.
  forward.
  forward.
  Exists p. entailer!!.
Qed.

Lemma body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function.
  forward_if.
  + destruct t; simpl tree_rep.
      1: Intros. contradiction.
    Intros pa pb.
    forward.
    forward.
    Time forward_call (p, sizeof t_struct_tree).
    {
      entailer!.
      rewrite memory_block_data_at_ by auto.
      cancel.
    }
    Time forward_call (t1,pa).
    Time forward_call (t2,pb).
    entailer!!.
  + forward.
    subst.
    unfold tree_rep; entailer!.
Qed.

Lemma body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold treebox_rep.
  Intros p.
  forward.
  Time forward_call (t,p).
  simpl.
  Time forward_call (b, sizeof (tptr t_struct_tree)).
  saturate_local.
  rewrite memory_block_data_at_ by auto; cancel.
  forward.
Qed.

Module Abstractions.
(* Demonstration of data abstraction via funspec_sub. *)


(* Definitions of [combine] and [Abs] taken from 
   Verified Functional Algorithms (Software Foundations Volume 3),
   chapter SearchTree *)
Section TREE_ABS.

Definition total_map (A:Type) := key -> A.
Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A:Type} (m : total_map A)
                    (x : key) (v : A) :=
  fun x' => if x =? x' then v else m x'.


Definition combine {A} (pivot: key) (m1 m2: total_map A) : total_map A :=
  fun x : key => if zlt x pivot  then m1 x else m2 x.

Inductive Abs:  tree val -> total_map val -> Prop :=
| Abs_E: Abs E (t_empty nullval)
| Abs_T: forall a b l k v r,
      Abs l a ->
      Abs r b ->
      Abs (T l k v r)  (t_update (combine k a b) k v).

Theorem insert_relate:
 forall k v t cts,
    Abs t cts ->
    Abs (insert k v t) (t_update cts k v).
Admitted.  (* This is an exercise in Verified Functional Algorithms *)

Theorem lookup_relate:
  forall k t cts ,
    Abs t cts -> lookup nullval k t =  cts k.
Admitted.  (* This is an exercise in Verified Functional Algorithms *)


Definition tmap_rep (m: total_map val) (p: val) : mpred :=
   EX t: tree val, !! Abs t m && treebox_rep t p.

Lemma tmap_rep_isptr m p: tmap_rep m p |-- !!(isptr p) && tmap_rep m p.
Proof. entailer.
unfold tmap_rep. Intros t. entailer!.
Qed.

Definition abs_insert_spec :=
 DECLARE _insert
  WITH b: val, x: Z, v: val, m: total_map val
  PRE  [ tptr (tptr t_struct_tree), tint, tptr Tvoid ]
    PROP( Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
    PARAMS (b; Vint (Int.repr x); v)
    SEP (tmap_rep m b)
  POST [ Tvoid ] 
    PROP()
    RETURN()
    SEP (tmap_rep (t_update m x v) b).

Definition abs_treebox_new_spec :=
 DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
       PROP() PARAMS() SEP ()
  POST [ tptr (tptr t_struct_tree) ]
    EX v:val,
    PROP()
    RETURN(v)
    SEP (tmap_rep (t_empty nullval) v).

Definition abs_treebox_free_spec :=
 DECLARE _treebox_free
  WITH m: total_map val, p: val
  PRE  [ tptr (tptr t_struct_tree) ]
       PROP() PARAMS(p) SEP (tmap_rep m p)
  POST [ Tvoid ]
    PROP()
    RETURN()
    SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Lemma subsume_insert:
 funspec_sub (snd insert_spec) (snd abs_insert_spec).
Proof.
do_funspec_sub. destruct w as [[[b x] v] m]. simpl.
rewrite <- fupd_intro.
monPred.unseal. Intros.
destruct args. inv H1.
destruct args. inv H1.
destruct args. inv H1.
destruct args; inv H1. simpl in *.
unfold env_set, eval_id in *. simpl in *. subst. 
unfold tmap_rep.
Intros t.
Exists (b, x, v, t) (emp : mpred). simpl.
entailer!!.
intros. Exists (insert x v t).
entailer!!. apply insert_relate; trivial.
Qed.

Lemma subsume_treebox_new:
 funspec_sub (snd treebox_new_spec) (snd abs_treebox_new_spec).
Proof.
do_funspec_sub.
rewrite <- fupd_intro.
monPred.unseal. Intros.
Exists tt (emp : mpred). entailer!!.
intros tau ? ?. Exists (eval_id ret_temp tau). entailer!!.
unfold tmap_rep.
Exists (empty_tree val).
unfold treebox_rep.
Exists nullval.
entailer!!.
constructor.
simpl. entailer!!. 
Qed.

Lemma subsume_treebox_free:
 funspec_sub (snd treebox_free_spec) (snd abs_treebox_free_spec).
Proof.
do_funspec_sub. destruct w as [m p]. clear H.
rewrite <- fupd_intro.
simpl; monPred.unseal. Intros.
subst.
unfold env_set, eval_id in *. simpl in *. 
unfold tmap_rep.
Intros t.
Exists (t,p) (emp : mpred). simpl. entailer!!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
rename a into gv.
assert_PROP (isptr (gv ___stringlit_1)) by entailer!.
assert_PROP (isptr (gv ___stringlit_2)) by entailer!.
assert_PROP (isptr (gv ___stringlit_3)) by entailer!.
assert_PROP (isptr (gv ___stringlit_4)) by entailer!.
freeze [0;1;2;3] FR1.
forward_call subsume_treebox_new tt.
Intros p. 
sep_apply tmap_rep_isptr; Intros. 
forward_call subsume_insert (p, 3, gv ___stringlit_1, t_empty nullval).
forward_call subsume_insert (p, 1, gv ___stringlit_2, (t_update (t_empty nullval) 3 (gv ___stringlit_1))).
forward_call subsume_insert (p, 4, gv ___stringlit_3, (t_update
             (t_update (t_empty nullval) 3
                (gv ___stringlit_1)) 1 (gv ___stringlit_2))).
forward_call subsume_insert (p, 1, gv ___stringlit_4, 
           (t_update
             (t_update
                (t_update (t_empty nullval) 3
                   (gv ___stringlit_1)) 1
                (gv ___stringlit_2)) 4 (gv ___stringlit_3))).
forward_call subsume_treebox_free ((t_update
             (t_update
                (t_update
                   (t_update (t_empty nullval) 3
                      (gv ___stringlit_1)) 1
                   (gv ___stringlit_2)) 4
                (gv ___stringlit_3)) 1 (gv ___stringlit_4)), p).
forward.
Qed.

End TREE_ABS.
End Abstractions.
