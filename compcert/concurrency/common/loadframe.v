(* This file is adapted from [load_frame.v] of Compositional CompCert ,
   for marshalling arguments in/out memory. 
   
   In addition to the original definitions related to [store_args],
   we define corresponding footprints of operations reading/writing arguments.
*)

Require Import Coqlib Integers Values AST Memory.


Require Import Footprint MemOpFP val_casted.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.


Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)          (**r pointer to argument frame *)
      (args: list val)     (**r initial program arguments *)
      (tys: list typ)      (**r initial argument types *)
      (sigres: option typ), (**r optional return type *)
      load_frame.

Require Mach.

Definition store_stack := Mach.store_stack.
Definition load_stack := Mach.load_stack.


Definition load_stack_fp (sp: val) (ty: typ) (ofs: ptrofs) : footprint :=
  loadv_fp (chunk_of_type ty) (Val.offset_ptr sp ofs).

Definition store_stack_fp (sp: val) (ty: typ) (ofs: ptrofs) : footprint :=
  storev_fp (chunk_of_type ty) (Val.offset_ptr sp ofs).




(** Note: Tlong has to be 8 aligned... *)

(** ofs : byte offset *)
Fixpoint store_args_rec (m: mem) (sp: val) (ofs: Z) (args: list val) (tys: list typ) 
  : option mem :=
  match args,tys with
  | nil, nil => Some m
  | a::args',ty::tys' =>
    match ty, a with
    | Tlong, Vlong n =>
      match store_stack m sp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs + 4)) (Vint (Int64.hiword n)) with
      | Some m' =>
        match store_stack m' sp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)) (Vint (Int64.loword n)) with
        | Some m'' => store_args_rec m'' sp (ofs + typesize ty) args' tys'
        | Non => None
        end
      | None => None
      end
    | Tlong, _ => None
    | _, _ =>
      match store_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)) a with
      | None => None
      | Some m' => store_args_rec m' sp (ofs + typesize ty) args' tys'
      end
    end
  | _,_ => None
  end.


Fixpoint args_bytes_rec args tys : option Z :=
  match tys, args with
  | nil, nil => Some 0
  | ty'::tys',a'::args' =>
    if val_has_type_func a' ty'
    then match args_bytes_rec args' tys' with
         | Some z => Some (AST.typesize ty' + z)
         | None => None
         end
    else None
  | _, _ => None
  end.

Fixpoint args_len_rec args tys : option Z :=
  match tys, args with
  | nil, nil => Some 0
  | ty'::tys',a'::args' =>
    if val_has_type_func a' ty'
    then match args_len_rec args' tys' with
         | Some z => Some (Locations.typesize ty' + z)
         | None => None
         end
    else None
  | _, _ => None
  end.

Lemma typesize_agree:
  forall t, (Locations.typesize t) * 4 = typesize t.
Proof. intros. destruct t; simpl; auto. Qed.

Lemma args_bytes_length:
  forall args tys z,
    args_bytes_rec args tys = Some z ->
    (4 | z) /\
    args_len_rec args tys = Some (z / 4).
Proof.
  induction args; intros; destruct tys; inv H.
  split; [apply Z.divide_0_r|auto].
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ =>
           destruct x eqn:?; inv H
         end.
  apply IHargs in Heqo. destruct Heqo.
  assert (4 | typesize t) by
      (destruct t; simpl; try replace 8 with (4 * 2) by Lia.lia; try apply Z.divide_mul_l; try apply Z.divide_refl).
  split; [apply Z.divide_add_r; auto|].
  simpl. rewrite Heqb. rewrite H0. f_equal.
  rewrite <- typesize_agree, Z_div_plus_full_l; auto. Lia.lia.
Qed.

Lemma args_length_bytes:
  forall args tys z,
    args_len_rec args tys = Some z ->
    args_bytes_rec args tys = Some (4 * z).
Proof.
  induction args; intros; destruct tys; inv H; auto.
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ =>
           destruct x eqn:?; inv H
         end.
  apply IHargs in Heqo.
  rewrite Z.mul_add_distr_l, Z.mul_comm, typesize_agree.
  simpl. rewrite Heqo, Heqb. auto.
Qed.

Lemma args_len_rec_non_neg:
  forall args tyl z,
    args_len_rec args tyl = Some z ->
    z >= 0.
Proof.
  clear; induction args; simpl; intros.
  destruct tyl; inv H. Lia.lia.
  destruct tyl; inv H. destruct val_has_type_func; inv H1. destruct args_len_rec eqn:H; inv H0.
  apply IHargs in H. 
  unfold Locations.typesize; destruct t; try Lia.lia.
Qed.

Lemma args_len_rec_exists:
  forall args0 tyl0,
    wd_args args0 tyl0 = true ->
    exists z, args_len_rec args0 tyl0 = Some z.
Proof.
  clear. induction args0; unfold wd_args; intros ?; repeat rewrite andb_true_iff.
  intuition. destruct tyl0; simpl; eauto. inversion H.
  intuition. destruct tyl0; simpl. inversion H. simpl in H.
  rewrite andb_true_iff in H. destruct H. rewrite H. clear H.
  unfold wd_args in IHargs0. specialize (IHargs0 tyl0). rewrite H0 in IHargs0. clear H0.
  assert (vals_defined args0 = true) by (destruct a; auto; discriminate).
  rewrite H in IHargs0; clear H.
  destruct zlt. exploit IHargs0; auto. intros (z & Hz). rewrite Hz. eauto.
  generalize g H1; clear. intros. exfalso.
  destruct zlt; inv H1. rewrite Zlength_cons in l. Lia.lia.
Qed.

Lemma args_len_rec_bound:
  forall args0 tyl0 z,
    args_len_rec args0 tyl0 = Some z ->
    z <= (2 * Zlength args0).
Proof.
  clear. induction args0; intros.
  simpl in H. destruct tyl0; inv H. simpl. Lia.lia.
  simpl in H. destruct tyl0; inv H. destruct val_has_type_func; inv H1.
  destruct args_len_rec eqn:C; inv H0. apply IHargs0 in C; clear IHargs0.
  rewrite Zlength_cons. destruct t; unfold Locations.typesize; try Lia.lia.
Qed.

Lemma store_args_rec_exists:
  forall tyl0 args0 z m sp0 ofs,
    args_len_rec args0 tyl0 = Some z ->
    vals_defined args0 = true ->
    (4 | ofs) ->
    0 <= ofs ->
    ofs + 4 * z < Ptrofs.max_unsigned ->
    Mem.range_perm m sp0 ofs (ofs + 4 * z) Cur Writable ->
    exists m', store_args_rec m (Vptr sp0 Ptrofs.zero) ofs args0 tyl0 = Some m'.
Proof.
  clear. induction tyl0; intros.
  destruct args0; inv H. simpl. eauto.
  destruct args0; inv H.

  destruct val_has_type_func eqn:?; inv H6.
  destruct args_len_rec eqn:?; inv H5.
  pose proof (args_len_rec_non_neg _ _ _ Heqo) as ZGE0.
  apply val_has_type_funcP in Heqb.

  simpl; unfold store_stack, Mach.store_stack, Mem.storev.
  destruct a; simpl.
  { edestruct (Mem.valid_access_store m Mint32 sp0 ofs v).
    unfold Mem.valid_access. simpl. split; auto. intros ? ?; apply H4; unfold Locations.typesize; try Lia.lia.
    eapply IHtyl0 in Heqo. destruct Heqo. exists x0.
    rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr. rewrite e, H; auto. unfold Locations.typesize in *. Lia.lia.
    destruct v; auto; inv H0.
    apply Z.divide_add_r; auto. apply Z.divide_refl. Lia.lia. unfold Locations.typesize in *. Lia.lia.
    replace (ofs + 4 * (Locations.typesize Tint + z0)) with (ofs + 4 + 4 * z0) in H4 by (unfold Locations.typesize; Lia.lia).
    intros ofs' RANGE. eapply Mem.perm_store_1, H4; eauto. Lia.lia. }
  { edestruct (Mem.valid_access_store m Mfloat64 sp0 ofs v).
    unfold Mem.valid_access. simpl. split; auto. intros ? ?; apply H4; unfold Locations.typesize; try Lia.lia.
    eapply IHtyl0 in Heqo. destruct Heqo. exists x0.
    rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr. rewrite e, H; auto. unfold Locations.typesize in *. Lia.lia.
    destruct v; auto; inv H0.
    apply Z.divide_add_r; auto. replace 8 with (4 * 2) by Lia.lia. apply Z.divide_mul_l, Z.divide_refl.
    Lia.lia. unfold Locations.typesize in *. Lia.lia.
    replace (ofs + 4 * (Locations.typesize Tfloat + z0)) with (ofs + 8 + 4 * z0) in H3 by (unfold Locations.typesize; Lia.lia).
    intros ofs' RANGE. eapply Mem.perm_store_1, H4; eauto. unfold Locations.typesize. Lia.lia. }
  { destruct v; inv Heqb. inv H0.
    edestruct (Mem.valid_access_store m Mint32 sp0 (ofs + 4) (Vint (Int64.hiword i))).
    unfold Mem.valid_access. simpl. split; auto. intros ? ?; apply H4; unfold Locations.typesize; try Lia.lia.
    apply Z.divide_add_r; auto. apply Z.divide_refl.
    edestruct (Mem.valid_access_store x Mint32 sp0 ofs (Vint (Int64.loword i))).
    unfold Mem.valid_access. simpl. split; auto.
    intros ? ?; eapply Mem.perm_store_1, H4; eauto; unfold Locations.typesize; try Lia.lia.
    eapply IHtyl0 in Heqo. destruct Heqo. exists x1. 
    repeat rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr. rewrite e, e0; eauto.
    unfold Locations.typesize in *. Lia.lia.
    unfold Locations.typesize in *. Lia.lia.
    auto.
    apply Z.divide_add_r; auto. replace 8 with (4 * 2) by Lia.lia. apply Z.divide_mul_l, Z.divide_refl.
    Lia.lia. unfold Locations.typesize in *; Lia.lia. 
    replace (ofs + 4 * (Locations.typesize Tlong + z0)) with (ofs + 8 + 4 * z0) in H4 by (unfold Locations.typesize; Lia.lia).
    intros ofs' RANGE. eapply Mem.perm_store_1, Mem.perm_store_1, H4; eauto. Lia.lia. }
  { edestruct (Mem.valid_access_store m Mfloat32 sp0 ofs v).
    unfold Mem.valid_access. simpl. split; auto. intros ? ?; apply H4; unfold Locations.typesize; try Lia.lia.
    eapply IHtyl0 in Heqo. destruct Heqo. exists x0.
    rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr. rewrite e, H; auto. unfold Locations.typesize in *. Lia.lia.
    destruct v; inv Heqb. inv H0. auto.
    apply Z.divide_add_r; auto. apply Z.divide_refl. Lia.lia. unfold Locations.typesize in *. Lia.lia.
    replace (ofs + 4 * (Locations.typesize Tsingle + z0)) with (ofs + 4 + 4 * z0) in H4 by (unfold Locations.typesize; Lia.lia).
    intros ofs' RANGE. eapply Mem.perm_store_1, H4; eauto. Lia.lia. }
  { edestruct (Mem.valid_access_store m Many32 sp0 ofs v).
    unfold Mem.valid_access. simpl. split; auto. intros ? ?; apply H4; unfold Locations.typesize; try Lia.lia.
    eapply IHtyl0 in Heqo. destruct Heqo. exists x0.
    rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr. rewrite e, H; auto. unfold Locations.typesize in *. Lia.lia.
    destruct v; inv Heqb; inv H0; auto.
    apply Z.divide_add_r; auto. apply Z.divide_refl. Lia.lia. unfold Locations.typesize in *. Lia.lia.
    replace (ofs + 4 * (Locations.typesize Tint + z0)) with (ofs + 4 + 4 * z0) in H3 by (unfold Locations.typesize; Lia.lia).
    intros ofs' RANGE. eapply Mem.perm_store_1, H4; eauto. unfold Locations.typesize; Lia.lia. }
  { edestruct (Mem.valid_access_store m Many64 sp0 ofs v).
    unfold Mem.valid_access. simpl. split; auto. intros ? ?; apply H4; unfold Locations.typesize; try Lia.lia.
    eapply IHtyl0 in Heqo. destruct Heqo. exists x0.
    rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr. rewrite e, H; auto. unfold Locations.typesize in *. Lia.lia.
    destruct v; inv Heqb; inv H0; auto.
    apply Z.divide_add_r; auto. replace 8 with (4 * 2) by Lia.lia. apply Z.divide_mul_l, Z.divide_refl.
    Lia.lia. unfold Locations.typesize in *. Lia.lia.
    replace (ofs + 4 * (Locations.typesize Tany64 + z0)) with (ofs + 8 + 4 * z0) in H3 by (unfold Locations.typesize; Lia.lia).
    intros ofs' RANGE. eapply Mem.perm_store_1, H4; eauto. unfold Locations.typesize; Lia.lia. }
Qed.

Lemma args_len_rec_inject:
  forall j args args' tyl z,
    Val.inject_list j args args' ->
    vals_defined args = true ->
    args_len_rec args tyl = Some z ->
    args_len_rec args' tyl = Some z.
Proof.
  clear. induction args; intros. inv H. auto.
  inv H. inv H1. inv H0. destruct tyl as [|ty' tys'];[discriminate|destruct (val_has_type_func a ty') eqn:?; try discriminate].
  simpl. inv H4; destruct ty'; cbv in Heqb; try discriminate; simpl;
           (destruct args_len_rec eqn:?; try discriminate; inv H1;
            eapply IHargs in Heqo; eauto; rewrite Heqo; auto).
Qed.

Fixpoint tyl_length (tyl: list typ) : Z :=
  match tyl with
  | nil => 0
  | ty' :: tyl' =>
    Locations.typesize ty' + (tyl_length tyl')
  end.

Fixpoint tyl_bytes (tyl: list typ) : Z :=
  match tyl with
  | nil => 0
  | ty'::tyl' =>
    AST.typesize ty' + (tyl_bytes tyl')
  end.

Lemma tyl_length_agree:
  forall tyl, (tyl_length tyl) * 4 = tyl_bytes tyl.
Proof.
  induction tyl; auto.
  unfold tyl_length. rewrite Z.mul_add_distr_r. fold tyl_length. rewrite IHtyl.
  rewrite typesize_agree; auto.
Qed.

Lemma tyl_length_size_arguments_32:
  forall tyl, Conventions1.size_arguments_32 tyl 0 = tyl_length tyl.
Proof.
  clear. induction tyl; auto. simpl. rewrite <- IHtyl. 
  generalize tyl (Locations.typesize a). clear. induction tyl.
  intros. simpl. Lia.lia.
  simpl. intros. rewrite (IHtyl (Locations.typesize a)). rewrite (IHtyl (z + Locations.typesize a)). Lia.lia.
Qed.
            
Lemma tyl_bytes_app:
  forall tyl tyl',
    tyl_bytes (tyl ++ tyl') = tyl_bytes tyl + tyl_bytes tyl'.
Proof.
  clear. induction tyl; simpl; intros; auto. rewrite IHtyl. Lia.lia.
Qed.
Lemma tyl_bytes_non_neg:
  forall tyl, tyl_bytes tyl >= 0.
Proof.
  clear. induction tyl as[|ty tyl]; simpl; [| pose proof (AST.typesize_pos ty)]; Lia.lia.
Qed.



Definition store_arg m sp ofs ty' a' :=
  store_args_rec m sp ofs a' ty'.

Definition store_args m sp args tys := store_args_rec m (Vptr sp Ptrofs.zero) 0 args tys.

Lemma store_args_exists:
  forall tyl0 args0 z m m' sp0,
    wd_args args0 tyl0 = true ->
    args_len_rec args0 tyl0 = Some z ->
    Mem.alloc m 0 (4 * z) = (m', sp0) ->
    exists m'', store_args m' sp0 args0 tyl0 = Some m''.
Proof.
  clear.
  unfold wd_args. intros. exploit store_args_rec_exists; eauto.
  repeat rewrite andb_true_iff in H. destruct vals_defined; intuition.
  apply Z.divide_0_r. Lia.lia.
  repeat rewrite andb_true_iff in H. intuition.
  destruct zlt; inv H3.
  pose proof (args_len_rec_bound _ _ _ H0).
  assert (Int.max_unsigned = Ptrofs.max_unsigned).
  { clear. reflexivity. }
  Lia.lia.
  intros ? ?. eapply Mem.perm_alloc_2 in H1; eauto. eapply Mem.perm_implies; eauto. constructor.
Qed.

Lemma store_args_rec_unchanged_on:
  forall sp args tyl z m m',
    store_args_rec m (Vptr sp Ptrofs.zero) z args tyl = Some m' ->
    Mem.unchanged_on (fun b _ => b <> sp) m m'.
Proof.
  clear. induction args; simpl; intros.
  destruct tyl; inv H. eapply Mem.unchanged_on_refl.
  destruct tyl; inv H. 
  destruct t;
    repeat match goal with
           | H : match ?x with _ => _ end = _ |- _ =>
             destruct x eqn:?; inv H;
               unfold store_stack, Mach.store_stack, Mem.storev in *; simpl in *
           | H : Mem.store _ _ sp _ _ = _ |- _ =>
             eapply (Mem.store_unchanged_on (fun b _ => b <> sp)) in H; eauto
           | H: Mem.unchanged_on ?P ?x ?y |- Mem.unchanged_on ?P ?x ?z =>
             apply Mem.unchanged_on_trans with y; eauto
           end.
Qed.

Lemma store_args_unchanged_on:
  forall m sp args tyl m',
    store_args m sp args tyl = Some m' ->
    Mem.unchanged_on (fun b _ => b <> sp) m m'.
Proof.
  clear. intros. eapply store_args_rec_unchanged_on; eauto.
Qed.


Fixpoint store_args_rec_fp (sp: block) (ofs: Z) (tys: list typ) : footprint :=
  let vsp := Vptr sp Ptrofs.zero in
  match tys with
  | nil => empfp
  | ty::tys' =>
    match ty with
    | Tlong =>
      FP.union (FP.union (store_stack_fp vsp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)))
                         (store_stack_fp vsp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs + 4))))
               (store_args_rec_fp sp (ofs + typesize ty) tys')
    | _ =>
      FP.union (store_stack_fp vsp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs))) 
               (store_args_rec_fp sp (ofs + typesize ty) tys')
    end
  end.

Definition store_args_fp sp tyl := store_args_rec_fp sp 0 tyl.

Ltac red_ptr :=
  match goal with
  | H: context[Ptrofs.add Ptrofs.zero _] |- _ => rewrite Ptrofs.add_zero_l in H
  | |- context[Ptrofs.add Ptrofs.zero _] => rewrite Ptrofs.add_zero_l
  | |- context[Ptrofs.unsigned (Ptrofs.repr _)] =>
    try (rewrite Ptrofs.unsigned_repr; [| unfold Ptrofs.max_unsigned; try Lia.lia; fail])
  | H: context[Ptrofs.unsigned (Ptrofs.repr _)] |- _ =>
    try (rewrite Ptrofs.unsigned_repr in H;[| unfold Ptrofs.max_unsigned; try Lia.lia; fail])
  end.
Ltac red_triv :=
  match goal with
  | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?; try (inv H; fail)
  | H: match ?x with _ => _ end |- _ => destruct x eqn:?; try (congruence; fail)
  end.
Ltac Cintro :=
  match goal with
  | |- not ?x => intro
  end.

(** store_args -> unchanged on ... *)
Lemma store_stack_unchanged_on:
  forall m sp ty ofs v m',
    store_stack m (Vptr sp Ptrofs.zero) ty ofs v = Some m' ->
    Mem.unchanged_on
      (fun b i => ~ (b = sp /\ (Ptrofs.unsigned ofs <= i < Ptrofs.unsigned ofs + AST.typesize ty))) m m'.
Proof.
  unfold store_stack, Mach.store_stack. intros until m'; simpl.
  rewrite Ptrofs.add_zero_l. generalize (Ptrofs.unsigned ofs). clear.
  intros. eapply Mem.store_unchanged_on; eauto.
  intros. intro. apply H1. split; auto. destruct ty; simpl in *; auto.
Qed.

  
Lemma store_args_rec_unchanged_on_weak:
  forall m sp ofs args tyl m',
    0 <= ofs ->
    ofs + (4 * (2 * Zlength args)) < Ptrofs.modulus ->
    store_args_rec m (Vptr sp Ptrofs.zero) ofs args tyl = Some m' ->
    Mem.unchanged_on
      (fun b i => if eq_block b sp then i < (Ptrofs.unsigned (Ptrofs.repr ofs)) else True) m m'.
Proof.
  intros until tyl. generalize m sp ofs args. clear. induction tyl; intros.
  unfold store_args_rec in H0. destruct args; inv H1.
  apply Mem.unchanged_on_refl.
  destruct args. inversion H1. simpl in H1. 
  assert (0 < typesize a <= 8) by (destruct a; simpl; Lia.lia).
  assert (Zlength args >= 0) by (rewrite Zlength_correct; Lia.lia).
  assert (4 * (2 * Zlength args) >= 0) by Lia.lia.
  assert (typesize a <= 4 * (2 * Zlength (v :: args))).
  { rewrite Zlength_cons, <- Zmult_succ_r_reverse, Z.mul_add_distr_l. Lia.lia. }
  rewrite Zlength_cons, <- Zmult_succ_r_reverse, Z.mul_add_distr_l in H0.
  repeat red_triv; 
    repeat match goal with
           | H: store_stack _ _ _ _ _ = Some _ |- _ => apply store_stack_unchanged_on in H; red_ptr
           | H: store_args_rec _ _ _ _ _ = _ |- _ => eapply IHtyl in H; try Lia.lia
           end;
    try (eapply (Mem.unchanged_on_trans _ m m0 m');
         eapply Mem.unchanged_on_implies; simpl; eauto; intros; simpl; try intros [? ?]; red_ptr; red_triv; Lia.lia; fail).

  eapply (Mem.unchanged_on_trans _ m m1 m');
    [eapply (Mem.unchanged_on_trans _ m m0 m1)|];
    eapply Mem.unchanged_on_implies; simpl; eauto; intros; simpl; try intros [? ?]; red_ptr; red_triv; Lia.lia.
Qed.


(** agreements between args and stack contents *)
Fixpoint agree_args_contains_aux m sp0 ofs args tys : Prop :=
  let vsp := Vptr sp0 Ptrofs.zero in
  match tys, args with
  | nil, nil => True
  | ty :: tys', a :: args' =>
    match ty, a with
    | Tlong , Vlong n =>
      load_stack m vsp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs + 4)) = Some (Vint (Int64.hiword n)) 
      /\ load_stack m vsp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)) = Some (Vint (Int64.loword n))
      /\ agree_args_contains_aux m sp0 (ofs + typesize ty) args' tys'
    | Tlong, _ => False
    | _ , _ =>
      load_stack m vsp ty (Ptrofs.repr ofs) = Some a 
      /\ agree_args_contains_aux m sp0 (ofs + typesize ty) args' tys'
    end
  | _, _ => False
  end.

Definition agree_args_contains m sp0 args tys : Prop := agree_args_contains_aux m sp0 0 args tys.



Lemma store_args_rec_agree_args_contains_aux:
  forall tyl m sp ofs args m',
    wd_args args tyl = true ->
    0 <= ofs ->
    ofs + (4 * (2 * Zlength args)) < Ptrofs.modulus ->
    store_args_rec m (Vptr sp Ptrofs.zero) ofs args tyl = Some m' ->
    agree_args_contains_aux m' sp ofs args tyl.
Proof.
  induction tyl as [|ty tyl']; intros.
  destruct args; simpl in *; [trivial|congruence].
  destruct args as [|v args']. simpl in *. congruence.
  rewrite Zlength_cons, <- Zmult_succ_r_reverse, Z.mul_add_distr_l in H1.
  assert (0 < typesize ty <= 8) by (destruct ty; simpl; Lia.lia).
  assert (Zlength args' >= 0) by (rewrite Zlength_correct; Lia.lia).
  assert (4 * (2 * Zlength args') >= 0) by Lia.lia.
  assert (typesize ty + 4 * (2 * Zlength args') <= 4 * (2 * (Zlength args' + 1))).
  { rewrite Z.mul_add_distr_l. Lia.lia. }
  replace (4 * 2) with 8 in * by Lia.lia.
  repeat match goal with
         | H: context[4 * (2 * ?x)] |- _ =>
           replace (4 * (2 * x)) with (8 * x) in H by Lia.lia
         | H: context[_ * (_ + _)] |- _ =>
           rewrite Z.mul_add_distr_l in H
         | H: context[?x + (?y + ?z)] |- _ =>
           rewrite Z.add_assoc in H
         end.
  assert (wd_args args' tyl' = true).
  { unfold wd_args in *. repeat rewrite andb_true_iff in H.
    destruct H. destruct H. simpl in H. rewrite andb_true_iff in H. destruct H.
    assert (vals_defined args' = true) by (destruct v; inv H8; auto).
    rewrite H9, H10. rewrite andb_true_l. 
    generalize H7. clear. rewrite Zlength_cons. intros H.
    apply zlt_true. destruct zlt; [Lia.lia| inv H]. }
  assert (Val.has_type v ty /\ v <> Vundef) as [? ?].
  { unfold wd_args in *. repeat rewrite andb_true_iff in H.
    destruct H. destruct H. simpl in H. rewrite andb_true_iff in H. destruct H.
    apply val_has_type_funcP in H. split; auto.
    intro. subst v. inversion H9. }
  simpl in H2 |- *.
  destruct ty; repeat red_triv; repeat red_ptr;
    match goal with
    | H: store_args_rec _ _ _ _ _ = Some _ |- _ =>
      exploit store_args_rec_unchanged_on_weak; try eexact H; try Lia.lia; eauto;
      eapply IHtyl' in H; try Lia.lia; auto
    end;
    repeat split; auto; unfold load_stack, Mach.load_stack, Mem.loadv; simpl; repeat red_ptr;
      try (eapply Mem.load_unchanged_on; eauto;
           [simpl; intros; destruct eq_block; auto; Lia.lia
           |eapply Mem.load_store_same in Heqo; simpl in Heqo; repeat red_ptr; rewrite Heqo; destruct v; inv H8; auto; fail 
           ]; fail).

  exploit store_stack_unchanged_on; try eexact Heqo0. intros.
  eapply Mem.load_unchanged_on; eauto; [simpl; intros; destruct eq_block; auto; Lia.lia|]. clear H10.
  eapply Mem.load_unchanged_on; eauto. simpl; intros; Cintro. repeat red_ptr. Lia.lia. clear H11.
  eapply Mem.load_store_same in Heqo; simpl in Heqo; repeat red_ptr. rewrite Heqo; destruct v; inv H8; auto.
  
  eapply Mem.load_unchanged_on; eauto; [simpl; intros; destruct eq_block; auto; Lia.lia|].   
  eapply Mem.load_store_same in Heqo0; simpl in Heqo0; repeat red_ptr. rewrite Heqo0; destruct v; inv H8; auto.
Qed.
  
Lemma agree_args_contains_aux_invariant:
  forall tys m sp ofs args m',
  agree_args_contains_aux m sp ofs args tys -> 
  Mem.unchanged_on (fun b ofs => b=sp) m m' ->
  agree_args_contains_aux m' sp ofs args tys.
Proof.
induction tys. destruct args; simpl; auto.
intros m'; destruct args; simpl; auto.
intros m''.
destruct a; try (intros (LOAD0 & AGREE) UNCHG;
                 split;
                 [eapply Mem.load_unchanged_on; eauto; simpl; auto|eauto]).
destruct v; try (intro C; inv C; fail).
intros (LOAD1 & LOAD2 & AGREE) UNCHG.
split; [|split;[|eauto]]; eapply Mem.load_unchanged_on; eauto; simpl; auto.
Qed.



(** FMem version of store_args *)
Require Import FMemory.
Definition store_stack_fmem (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) : option mem :=
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

Fixpoint store_args_rec_fmem (m: mem) (sp: val) (ofs: Z) (args: list val) (tys: list typ) 
  : option mem :=
  match args,tys with
  | nil, nil => Some m
  | a::args',ty::tys' =>
    match ty, a with
    | Tlong, Vlong n =>
      match store_stack_fmem m sp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs + 4)) (Vint (Int64.hiword n)) with
      | Some m' =>
        match store_stack_fmem m' sp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)) (Vint (Int64.loword n)) with
        | Some m'' => store_args_rec_fmem m'' sp (ofs + typesize ty) args' tys'
        | Non => None
        end
      | None => None
      end
    | Tlong, _ => None
    | _, _ =>
      match store_stack_fmem m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)) a with
      | None => None
      | Some m' => store_args_rec_fmem m' sp (ofs + typesize ty) args' tys'
      end
    end
  | _,_ => None
  end.

Definition store_args_fmem (m: mem) (sp: block) (args: list val) (tys: list typ) : option mem :=
  store_args_rec_fmem m (Vptr sp Ptrofs.zero) 0 args tys.
