Require Import Coqlib Memperm Memtype Memory.

Inductive eq_perm_kind: Memperm.perm_kind -> perm_kind -> Prop :=
  eq_max: eq_perm_kind Memperm.Max Max
| eq_cur: eq_perm_kind Memperm.Cur Cur.

Inductive eq_permission: Memperm.permission -> permission -> Prop :=
  eq_freeable: eq_permission Memperm.Freeable Freeable
| eq_writable: eq_permission Memperm.Writable Writable
| eq_readable: eq_permission Memperm.Readable Readable
| eq_nonempty: eq_permission Memperm.Nonempty Nonempty.

Definition perm_kind_convert (K: perm_kind) : Memperm.perm_kind :=
  match K with
  | Max => Memperm.Max
  | Cur => Memperm.Cur
  end.

Definition perm_kind_convert' (K: Memperm.perm_kind) : perm_kind :=
  match K with
  | Memperm.Max => Max
  | Memperm.Cur => Cur
  end.

Definition permission_convert (P: permission) : Memperm.permission :=
  match P with
  | Freeable => Memperm.Freeable
  | Writable => Memperm.Writable
  | Readable => Memperm.Readable
  | Nonempty => Memperm.Nonempty
  end.

Definition permission_convert' (P: Memperm.permission) : permission :=
  match P with
  | Memperm.Freeable => Freeable 
  | Memperm.Writable => Writable
  | Memperm.Readable => Readable
  | Memperm.Nonempty => Nonempty
  end.

Lemma perm_order''_equiv_1:
  forall p1 p2,
    Memperm.perm_order'' p1 p2 ->
    Mem.perm_order'' (option_map permission_convert' p1)
                     (option_map permission_convert' p2).
Proof.
  intros. destruct p1, p2; inv H; cbv; auto.
  destruct p0; constructor.
  destruct p0; constructor.
  constructor.
  destruct p; constructor.
Qed.

Lemma perm_order_convert'_eq:
  forall p1 p2,
    Memperm.perm_order p1 p2 <->
    perm_order (permission_convert' p1) (permission_convert' p2).
Proof.
  intros. split; intros; [destruct p1|destruct p1,p2]; inv H; try constructor.
Qed.

Lemma eq_perm_kind_convert:
  forall K K',
    eq_perm_kind K' K ->
    perm_kind_convert K = K'.
Proof. intros. destruct K; inv H; auto. Qed.

Lemma eq_permission_convert':
  forall P P',
    eq_permission P' P ->
    permission_convert' P' = P.
Proof. intros. destruct P; inv H; auto. Qed.

Lemma perm_kind_convert_eq:
  forall k, eq_perm_kind (perm_kind_convert k) k.
Proof. intros k. destruct k; simpl; constructor. Qed.

Lemma permission_convert_eq:
  forall p, eq_permission (permission_convert p) p.
Proof. intros p. destruct p; simpl; constructor. Qed.
