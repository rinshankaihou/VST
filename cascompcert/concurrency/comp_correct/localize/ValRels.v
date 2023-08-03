Require Import Coqlib Maps Integers Values Memdata AST Globalenvs.
Require Import Blockset Footprint FMemOpFP GMemory MemAux CUAST LDSimDefs Localize MemInterpolant val_casted FMemPerm.
Require Import Lia.


Inductive val_related (j: Bset.inj) : val -> val -> Prop :=
| rel_vundef: val_related j Vundef Vundef
| rel_int: forall i, val_related j (Vint i) (Vint i)
| rel_long : forall i, val_related j (Vlong i) (Vlong i)
| rel_float : forall f, val_related j (Vfloat f) (Vfloat f)
| rel_single : forall f, val_related j (Vsingle f) (Vsingle f)
| rel_ptr : forall b b' ofs, j b = Some b' -> val_related j (Vptr b ofs) (Vptr b' ofs).

Lemma val_related_incr:
  forall j j',
    inject_incr (Bset.inj_to_meminj j) (Bset.inj_to_meminj j') ->
    (forall v v', val_related j v v' -> val_related j' v v').
Proof. intros. inv H0; econstructor. eapply inject_incr_bset_inj_incr; eauto. Qed.

Lemma val_related_val_inject_strict:
  forall j v v',
    val_related j v v' <->
    val_inject_strict (Bset.inj_to_meminj j) v v'.
Proof.
  destruct v, v'; try (split; intro C; inv C; constructor; fail). split; intros H; inv H; unfold Bset.inj_to_meminj in *.
  econstructor. rewrite H1. eauto. auto using Ptrofs.add_zero.
  destruct (j b) eqn:? ; inv H3. rewrite Ptrofs.add_zero. constructor. auto.
Qed.

(** memval *)
Inductive memval_related (j: Bset.inj) : memval -> memval -> Prop :=
| rel_undef: memval_related j Undef Undef
| rel_byte: forall b, memval_related j (Byte b) (Byte b)
| rel_frag: forall v v' q n, val_related j v v' -> memval_related j (Fragment v q n) (Fragment v' q n).
               
Lemma memval_related_memval_inject_strict:
  forall j mv mv',
    memval_related j mv mv' <-> memval_inject_strict (Bset.inj_to_meminj j) mv mv'.
Proof.
  destruct mv, mv'; try (split; intro C; inv C; constructor; fail).
  split; intros H; inv H; unfold Bset.inj_to_meminj in *.
  inv H1; repeat econstructor; eauto. rewrite H; eauto. auto using Ptrofs.add_zero.
  inv H1; repeat constructor; auto. destruct (j b1) eqn:?;[|discriminate].
  inv H. rewrite Ptrofs.add_zero. constructor; auto.
Qed.

Lemma inj_value_pointer:
  forall j b b' ofs bl ,
    Bset.inj_inject j ->
    j b = Some b' ->
    list_forall2 (memval_related j) bl (inj_value (if Archi.ptr64 then Q64 else Q32) (Vptr b' ofs)) ->
    bl = inj_value (if Archi.ptr64 then Q64 else Q32) (Vptr b ofs).
Proof.
  intros until 2.
  generalize (if Archi.ptr64 then Q64 else Q32). intro q.
  unfold inj_value. generalize (size_quantity_nat q). intros n.
  revert bl. induction n; simpl; intros; inv H1.
  auto.
  f_equal; auto. inv H5. inv H3. f_equal. f_equal.
  eapply H; eauto.
Qed.

(** args *)
Lemma G_arg_exists_arg_related:
  forall v Shared j,
    G_arg Shared v ->
    Bset.inject j Shared Shared ->
    exists v', val_related j v v'.
Proof.
  destruct v; try (eexists; econstructor; fail). intros.
  inv H0. exploit inj_dom. simpl in H. eauto. intros [b' INJ].
  exists (Vptr b' i). constructor. auto.
Qed.

Lemma G_arg_exists_arg_related':
  forall v' Shared j,
    G_arg Shared v' ->
    Bset.inject j Shared Shared ->
    exists v, val_related j v v'.
Proof.
  destruct v'; try (eexists; econstructor; fail). intros.
  inv H0. inv inj_weak. exploit inj_range. simpl in H. eauto. intros [b0 INJ].
  exists (Vptr b0 i). constructor. auto.
Qed.

Lemma G_args_exists_args_related:
  forall vl Shared j,
    G_args Shared vl ->
    Bset.inject j Shared Shared ->
    exists vl', list_forall2 (val_related j) vl vl'.
Proof.
  induction vl; eauto. exists nil. constructor.
  intros. inv H. apply IHvl with Shared j in H4; auto. destruct H4.
  exploit G_arg_exists_arg_related; eauto. intros [a' REL]. exists (a' :: x). constructor; auto.
Qed.

Lemma G_args_exists_args_related':
  forall vl' Shared j,
    G_args Shared vl' ->
    Bset.inject j Shared Shared ->
    exists vl, list_forall2 (val_related j) vl vl'.
Proof.
  induction vl'; eauto. exists nil. constructor.
  intros. inv H. apply IHvl' with Shared j in H4; auto. destruct H4.
  exploit G_arg_exists_arg_related'; eauto. intros [a0 REL]. exists (a0 :: x). constructor; auto.
Qed.

(** operation in Val *)
Definition uop_val_related (uop: val -> val) : Prop :=
  forall j v v', val_related j v v' -> val_related j (uop v) (uop v').
Ltac solvuop := intros until v'; intros A; inv A; constructor; auto.
Definition uop_option_val_related (uop: val -> option val) : Prop :=
  forall j v v', val_related j v v' -> option_rel (val_related j) (uop v) (uop v').
Ltac solvuopopt := intros until v'; intros A; inv A; simpl; repeat econstructor; eauto;
                   try match goal with |- context[option_map _ ?x] => destruct x; repeat constructor; auto end.
Definition binop_val_related (bop: val -> val -> val) : Prop :=
  forall j v1 v1' v2 v2',
    Bset.inj_inject j ->
    val_related j v1 v1' ->
    val_related j v2 v2' ->
    val_related j (bop v1 v2) (bop v1' v2').
Ltac solvbinop := intros until v2'; intros INJECT A B; inv A; inv B; simpl;
                  repeat match goal with |- context[match ?x with _ => _ end] => destruct x end;
                  try constructor; try congruence; auto;
                  try (exfalso; match goal with H: ~ _ |- _ => apply H; subst; eapply INJECT; eauto end; fail).

Lemma offset_ptr_val_related: forall ofs, uop_val_related (fun v => Val.offset_ptr v ofs). Proof. solvuop. Qed.
Lemma add_val_related: binop_val_related Val.add. Proof. solvbinop. Qed.
Lemma addl_val_related: binop_val_related Val.addl. Proof. solvbinop. Qed.
Lemma mul_val_related: binop_val_related Val.mul. Proof. solvbinop. Qed.
Lemma mull_val_related: binop_val_related Val.mull. Proof. solvbinop. Qed.
Lemma zero_ext_related: forall z, uop_val_related (Val.zero_ext z). Proof. solvuop. Qed.
Lemma sign_ext_related: forall z, uop_val_related (Val.sign_ext z). Proof. solvuop. Qed.
Lemma longofintu_related: uop_val_related Val.longofintu. Proof. solvuop. Qed.
Lemma longofint_related: uop_val_related Val.longofint. Proof. solvuop. Qed.
Lemma loword_related: uop_val_related Val.loword. Proof. solvuop. Qed.
Lemma singleoffloat_related: uop_val_related Val.singleoffloat. Proof. solvuop. Qed.
Lemma floatofsingle_related: uop_val_related Val.floatofsingle. Proof. solvuop. Qed.
Lemma intoffloat_related: uop_option_val_related Val.intoffloat. Proof. solvuopopt. Qed.
Lemma floatofint_related: uop_option_val_related Val.floatofint. Proof. solvuopopt. Qed.
Lemma intofsingle_related: uop_option_val_related Val.intofsingle. Proof. solvuopopt. Qed.
Lemma longoffloat_related: uop_option_val_related Val.longoffloat. Proof. solvuopopt. Qed.
Lemma floatoflong_related: uop_option_val_related Val.floatoflong. Proof. solvuopopt. Qed.
Lemma longofsingle_related: uop_option_val_related Val.longofsingle. Proof. solvuopopt. Qed.
Lemma singleoflong_related: uop_option_val_related Val.singleoflong. Proof. solvuopopt. Qed.
Lemma singleofint_related: uop_option_val_related Val.singleofint. Proof. solvuopopt. Qed.
Lemma neg_related: uop_val_related Val.neg. Proof. solvuop. Qed.
Lemma negl_related: uop_val_related Val.negl. Proof. solvuop. Qed.
Lemma sub_related: binop_val_related Val.sub. Proof. solvbinop. Qed.
Lemma subl_related: binop_val_related Val.subl. Proof. solvbinop. Qed.
Lemma mulhs_related: binop_val_related Val.mulhs. Proof. solvbinop. Qed.
Lemma mulhu_related: binop_val_related Val.mulhu. Proof. solvbinop. Qed.
Lemma shr_related: binop_val_related Val.shr. Proof. solvbinop. Qed.
Lemma shrl_related: binop_val_related Val.shrl. Proof. solvbinop. Qed.
Lemma and_related: binop_val_related Val.and. Proof. solvbinop. Qed.
Lemma andl_related: binop_val_related Val.andl. Proof. solvbinop. Qed.
Lemma or_related: binop_val_related Val.or. Proof. solvbinop. Qed.
Lemma orl_related: binop_val_related Val.orl. Proof. solvbinop. Qed.
Lemma xor_related: binop_val_related Val.xor. Proof. solvbinop. Qed.
Lemma xorl_related: binop_val_related Val.xorl. Proof. solvbinop. Qed.
Lemma notint_related: uop_val_related Val.notint. Proof. solvuop. Qed.
Lemma notl_related: uop_val_related Val.notl. Proof. solvuop. Qed.
Lemma shl_related: binop_val_related Val.shl. Proof. solvbinop. Qed.
Lemma shll_related: binop_val_related Val.shll. Proof. solvbinop. Qed.
Lemma shru_related: binop_val_related Val.shru. Proof. solvbinop. Qed.
Lemma shrlu_related: binop_val_related Val.shrlu. Proof. solvbinop. Qed.
Lemma ror_related: binop_val_related Val.ror. Proof. solvbinop. Qed.
Lemma rorl_related: binop_val_related Val.rorl. Proof. solvbinop. Qed.
Lemma addf_related: binop_val_related Val.addf. Proof. solvbinop. Qed.
Lemma subf_related: binop_val_related Val.subf. Proof. solvbinop. Qed.
Lemma mulf_related: binop_val_related Val.mulf. Proof. solvbinop. Qed.
Lemma divf_related: binop_val_related Val.divf. Proof. solvbinop. Qed.
Lemma absf_related: uop_val_related Val.absf. Proof. solvuop. Qed.
Lemma addfs_related: binop_val_related Val.addfs. Proof. solvbinop. Qed.
Lemma subfs_related: binop_val_related Val.subfs. Proof. solvbinop. Qed.
Lemma mulfs_related: binop_val_related Val.mulfs. Proof. solvbinop. Qed.
Lemma divfs_related: binop_val_related Val.divfs. Proof. solvbinop. Qed.
Lemma absfs_related: uop_val_related Val.absfs. Proof. solvuop. Qed.
Lemma mullhs_related: binop_val_related Val.mullhs. Proof. solvbinop. Qed.
Lemma mullhu_related: binop_val_related Val.mullhu. Proof. solvbinop. Qed.
Lemma negf_related: uop_val_related Val.negf. Proof. solvuop. Qed.
Lemma negfs_related: uop_val_related Val.negfs. Proof. solvuop. Qed.
Lemma longofwors_related: binop_val_related Val.longofwords. Proof. solvbinop. Qed.
Lemma of_bool_related: forall j b, val_related j (Val.of_bool b) (Val.of_bool b).
Proof. intros. destruct b; cbv; auto using rel_int. Qed.

Lemma of_optbool_related: forall j ob ob', option_rel eq ob ob' -> val_related j (Val.of_optbool ob) (Val.of_optbool ob').
Proof. intros. inv H; simpl; try constructor. destruct y; constructor. Qed.

Lemma maketotal_related: forall j ov ov', option_rel (val_related j) ov ov' -> val_related j (Val.maketotal ov) (Val.maketotal ov').
Proof. intros. inv H. constructor. inv H0; simpl; constructor; auto. Qed.

Hint Resolve offset_ptr_val_related add_val_related addl_val_related mul_val_related mull_val_related
      zero_ext_related sign_ext_related longofintu_related longofint_related loword_related singleoffloat_related
      floatofsingle_related intoffloat_related floatofint_related intofsingle_related
      longoffloat_related floatoflong_related longofsingle_related singleoflong_related
      singleofint_related negl_related neg_related sub_related subl_related mulhs_related mulhu_related
      shrl_related shr_related and_related andl_related or_related orl_related xor_related xorl_related
      notint_related notl_related notl_related shl_related shll_related shru_related shrlu_related
      ror_related rorl_related addf_related subf_related mulf_related divf_related absf_related
      addfs_related subfs_related mulfs_related divfs_related absfs_related
      mullhs_related mullhu_related negf_related negfs_related
      of_bool_related of_optbool_related maketotal_related
      rel_vundef rel_int rel_long rel_float rel_single rel_ptr.


(** Mem ops *)
Lemma mem_rel_range_perm:
  forall j bound fl fm m,
    mem_related j bound fl (FMemory.strip fm) m ->
    forall b b' ofs size K K' p p',
      construct_inj j bound fl b = Some b' ->
      eq_perm_kind K' K ->
      eq_permission p' p ->
      Memory.Mem.range_perm m b ofs size K p <->
      FMemory.Mem.range_perm fm b' ofs size K' p'.
Proof.
  intros. inv H. destruct fm; simpl in *. unfold FMemory.strip in *. simpl in *.
  split; intros; intros ofs' RANGE; specialize (H ofs' RANGE);
    unfold GMem.perm, FMemory.Mem.perm in *; simpl in *; eapply mem_related_mem_perm_eq; eauto.
Qed.

Lemma mem_rel_valid_access:
  forall j bound fl fm m,
    mem_related j bound fl (FMemory.strip fm) m ->
    forall b b' chunk ofs p p', construct_inj j bound fl b = Some b' ->
                           eq_permission p' p ->
                           Memory.Mem.valid_access m chunk b ofs p <->
                           FMemory.Mem.valid_access fm chunk b' ofs p'.
Proof.
  intros. unfold Memory.Mem.valid_access, FMemory.Mem.valid_access; simpl.
  exploit mem_rel_range_perm; eauto. Focus 2. intro. rewrite H2. firstorder. constructor.
Qed.

Lemma related_proj_bytes:
  forall j mvl mvl',
    list_forall2 (memval_related j) mvl mvl' ->
    proj_bytes mvl = proj_bytes mvl'.
Proof. induction mvl; intros; inv H; auto. simpl. inv H2; auto. erewrite IHmvl; eauto. Qed.

Lemma related_check_value:
  forall j mvl mvl' v v',
    Bset.inj_inject j ->
    list_forall2 (memval_related j) mvl mvl' ->
    val_related j v v' ->
    forall n q, check_value n v q mvl = check_value n v' q mvl'.
Proof.
  induction 2; intros; destruct n; simpl in *; auto.
  inv H0; auto. rewrite IHlist_forall2; auto.
  inv H2; inv H3; auto.
  do 2 destruct Val.eq; auto.
  inversion e. subst. rewrite H0 in H2; inv H2. contradiction.
  inversion e. subst. exploit H. exact H0. exact H2. intro; subst. contradiction.
Qed.

Lemma related_proj_value:
  forall j mvl mvl' q,
    Bset.inj_inject j ->
    list_forall2 (memval_related j) mvl mvl' ->
    val_related j (proj_value q mvl) (proj_value q mvl').
Proof.
  intros. unfold proj_value.
  inversion H0; auto.
  inv H1; auto.
  erewrite related_check_value; eauto.
  destruct check_value; auto.
Qed.

Lemma load_result_related:
  forall j v v' chunk,
    val_related j v v' ->
    val_related j (Val.load_result chunk v) (Val.load_result chunk v').
Proof. intros. unfold Val.load_result; inv H; destruct chunk; simpl; constructor; auto. Qed.

Lemma decode_val_related:
  forall j mvl mvl' chunk,
    Bset.inj_inject j ->
    list_forall2 (memval_related j) mvl mvl' ->
    val_related j (decode_val chunk mvl) (decode_val chunk mvl').
Proof.
  intros. unfold decode_val. exploit related_proj_bytes; eauto. intro A. rewrite A.
  destruct (proj_bytes mvl'). destruct chunk; constructor.
  destruct chunk; try constructor.
  destruct Archi.ptr64; try constructor.
  1-3: exploit related_proj_value; eauto; intros; eauto using load_result_related.
Qed.

Lemma encode_val_related:
  forall j v v' chunk,
    Bset.inj_inject j ->
    val_related j v v' ->
    list_forall2 (memval_related j) (encode_val chunk v) (encode_val chunk v').
Proof.
  intros. unfold encode_val.
  inv H0; destruct chunk; simpl; repeat constructor; auto.
Qed.
  
Lemma mem_rel_getN:
  forall j bound fl m m' b b' size base,
    mem_related j bound fl (FMemory.strip m') m ->
    Memory.Mem.range_perm m b base (base + (Z.of_nat size)) Memtype.Cur Memtype.Readable ->
    construct_inj j bound fl b = Some b' ->
    list_forall2 (memval_related (construct_inj j bound fl))
                 (Memory.Mem.getN size base (Memory.Mem.mem_contents m) !! b)
                 (FMemory.Mem.getN size base (FMemory.Mem.mem_contents m') !! b').
Proof.
  intros until 1. revert base. induction size. simpl. constructor.
  simpl. constructor. rewrite memval_related_memval_inject_strict.
  exploit mem_related_mem_val_inject; eauto.
  apply Memory.Mem.perm_cur_max. apply H0. rewrite Zpos_P_of_succ_nat. omega.
  apply IHsize; auto. intros z RANGE. apply H0. rewrite Zpos_P_of_succ_nat. omega.
Qed.

Lemma setN_memval_related:
  forall j v v' content content' ofs chunk z,
    Bset.inj_inject j ->
    val_related j v v' ->
    memval_inject_strict
      (Bset.inj_to_meminj j) (ZMap.get ofs content) (ZMap.get ofs content') ->
    memval_inject_strict
      (Bset.inj_to_meminj j)
      (ZMap.get ofs (Memory.Mem.setN (encode_val chunk v) z content))
      (ZMap.get ofs (FMemory.Mem.setN (encode_val chunk v') z content')).
Proof.
  intros until 2. exploit encode_val_related. eauto. eauto. 
  clear H0. instantiate (1:= chunk).
  generalize (encode_val chunk v) (encode_val chunk v'). clear v v' chunk.
  intros bl bl' REL MVREL. revert z content content' MVREL.
  induction REL; intros; simpl. auto.
  apply IHREL. clear IHREL.
  destruct (zeq ofs z). subst. do 2 rewrite ZMap.gss.
  inv H0; constructor. inv H1; try constructor.
  econstructor. unfold Bset.inj_to_meminj. rewrite H0. eauto.
  rewrite Ptrofs.add_zero. auto.
  do 2 (rewrite ZMap.gso; auto).
Qed.

Lemma load_related:
  forall j bound fl m m' b b' z chunk
    (NOREP: norep fl),
    mem_related j bound fl (FMemory.strip m') m ->
    construct_inj j bound fl b = Some b' ->
    option_rel (val_related (construct_inj j bound fl))
               (Memory.Mem.load chunk m b z) (FMemory.Mem.load chunk m' b' z).
Proof.
  intros. 
  destruct (Memory.Mem.valid_access_dec m chunk b z Memtype.Readable).
  exploit Memory.Mem.valid_access_load; eauto. intros [v1 LOAD]. rewrite LOAD.
  exploit mem_rel_valid_access; eauto. eapply eq_readable. intro. apply H1 in v.
  exploit FMemory.Mem.valid_access_load; eauto. intros [v2 LOAD']. rewrite LOAD'.
  constructor. apply Memory.Mem.load_result in LOAD; apply FMemory.Mem.load_result in LOAD'; subst.
  unfold Memory.Mem.valid_access, FMemory.Mem.valid_access in *; simpl in *.
  revert v H H0 H1. rewrite Memdata.size_chunk_conv. 
  generalize z (Memdata.size_chunk_nat chunk) NOREP. clear. intros base size. intros.
  exploit mem_rel_getN; eauto. rewrite <- H1 in v. destruct v. eauto. intro MEMVALREL.
  apply decode_val_related; auto.
  apply construct_inj_injective; inv H; auto.
  intros ? ? ? ? . eapply mem_related_freelist_disjoint.
  unfold get_block. rewrite H. auto.
  assert (~ FMemory.Mem.valid_access m' chunk b' z Memperm.Readable).
  { intro. apply n. destruct H1. split; auto. rewrite <- mem_rel_range_perm in H1; eauto; try constructor. }
  destruct (Memory.Mem.load) eqn:LOAD. apply Memory.Mem.load_valid_access in LOAD. congruence.
  destruct (FMemory.Mem.load) eqn:LOAD'. apply FMemory.Mem.load_valid_access in LOAD'. congruence.
  constructor.
Qed.
  
Lemma loadv_related:
  forall j bound fl m m' v v' chunk (NOREP: norep fl),
    mem_related j bound fl (FMemory.strip m') m ->
    val_related (construct_inj j bound fl) v v' ->
    option_rel (val_related (construct_inj j bound fl))
               (Memory.Mem.loadv chunk m v) (FMemory.Mem.loadv chunk m' v').
Proof.
  intros. inv H0; simpl; try constructor.
  apply load_related; auto.
Qed.

Lemma loadbytes_related:
  forall j bound fl m m' b b' base size,
    size >= 0 ->
    mem_related j bound fl (FMemory.strip m') m ->
    Memory.Mem.range_perm m b base (base + size) Memtype.Cur Memtype.Readable ->
    construct_inj j bound fl b = Some b' ->
    option_rel (list_forall2 (memval_related (construct_inj j bound fl)))
               (Memory.Mem.loadbytes m b base size)
               (FMemory.Mem.loadbytes m' b' base size).
Proof.
  intros. exploit Memory.Mem.range_perm_loadbytes; eauto.
  intros [bl LOADBYTES]. rewrite LOADBYTES.
  exploit FMemory.Mem.range_perm_loadbytes; eauto.
  eapply mem_rel_range_perm; eauto; try constructor.
  intros [bl' LOADBYTES']. rewrite LOADBYTES'. constructor.
  Transparent Memory.Mem.loadbytes FMemory.Mem.loadbytes.
  unfold Memory.Mem.loadbytes, FMemory.Mem.loadbytes in *.
  do 2 match goal with H:context[if ?x then _ else _] |- _ => destruct x; inv H end.
  apply mem_rel_getN; auto. rewrite nat_of_Z_eq; auto. 
Qed.
  
Lemma store_related:
  forall j bound fl m1 m1' b b' z v v' chunk (NOREP: norep fl),
    mem_related j bound fl (FMemory.strip m1') m1 ->
    construct_inj j bound fl b = Some b' ->
    val_related (construct_inj j bound fl) v v' ->
    option_rel (fun m2 m2' => mem_related j bound fl (FMemory.strip m2') m2)
               (Memory.Mem.store chunk m1 b z v) (FMemory.Mem.store chunk m1' b' z v').
Proof.
  intros.
  assert (INJECTIVE: Bset.inj_inject (construct_inj j bound fl)).
  { apply construct_inj_injective; inv H; auto.
    intros ? ? ? ? . eapply mem_related_freelist_disjoint.
    unfold get_block. rewrite H; eauto. }
  Transparent FMemory.Mem.store Memory.Mem.store.
  unfold FMemory.Mem.store, Memory.Mem.store.
  destruct (Memory.Mem.valid_access_dec m1 chunk b z Memtype.Writable) as [VA|VA];
    destruct (FMemory.Mem.valid_access_dec m1' chunk b' z Memperm.Writable) as [VA'|VA'];
    try constructor.
  { unfold FMemory.strip in *; simpl in *.
    constructor; inv H; auto; simpl.
    intros. destruct (peq b b0), (peq b' b'0); subst.
    do 2 rewrite PMap.gss. eapply mem_related_mem_val_inject in H2; eauto.
    simpl in *. apply setN_memval_related; auto.
    exfalso. apply n. congruence.
    exfalso. apply n. eapply INJECTIVE; eauto.
    do 2 (rewrite PMap.gso; auto). }
  exfalso. apply VA'. eapply mem_rel_valid_access; eauto. constructor.
  exfalso. apply VA. eapply mem_rel_valid_access; eauto. constructor.
Qed.

Lemma storev_related:
  forall j bound fl m1 m1' addr addr' v v' chunk (NOREP: norep fl),
    mem_related j bound fl (FMemory.strip m1') m1 ->
    val_related (construct_inj j bound fl) addr addr' ->
    val_related (construct_inj j bound fl) v v' ->
    option_rel (fun m2 m2' => mem_related j bound fl (FMemory.strip m2') m2)
               (Memory.Mem.storev chunk m1 addr v) (FMemory.Mem.storev chunk m1' addr' v').
Proof.
  intros. inv H0; simpl; try constructor.
  apply store_related; auto.
Qed.

Lemma alloc_result_related:
forall j bound fl m1 m1' lo hi m2 stk m2' stk',
    fl = FMemory.Mem.freelist m1' ->
    mem_related j bound fl (FMemory.strip m1') m1 ->
    Memory.Mem.alloc m1 lo hi = (m2, stk) ->
    FMemory.Mem.alloc m1' lo hi = (m2', stk') ->
    (construct_inj j bound fl) stk = Some stk'.
Proof.
  intros until stk'; intros FL MEMREL ALLOC ALLOC'.
  apply Memory.Mem.alloc_result in ALLOC;
    apply FMemory.Mem.alloc_result in ALLOC'.
  unfold Memory.Mem.nextblock.
  assert (~ Plt stk bound). inv MEMREL. intro. apply mem_related_shared_valid_local in H. apply Plt_ne in H. auto.
  destruct (Nat.eq_dec (Pos.to_nat stk - Pos.to_nat bound) (FMemory.Mem.nextblockid m1'))%nat; auto.
  unfold construct_inj. destruct plt;[contradiction|]. subst; unfold FMemory.Mem.nextblock. f_equal. auto.
  assert (construct_inj j bound fl stk = Some (get_block fl (Pos.to_nat stk - Pos.to_nat bound)%nat)).
  { unfold construct_inj. destruct plt;[contradiction|]. subst; unfold FMemory.Mem.nextblock. auto. }
  apply Nat.lt_gt_cases in n. exfalso. destruct n.
  (* LT *)
  assert (~ Memory.Mem.valid_block m1 stk).
  { subst. unfold Memory.Mem.valid_block. intro. apply Plt_ne in H2; auto. }
  assert (FMemory.Mem.valid_block m1' (get_block fl (Pos.to_nat stk - Pos.to_nat bound))).
  { eapply FMemory.Mem.valid_wd; eauto. subst. auto. }
  exploit mem_related_valid_block; eauto. intro. rewrite H4 in H2. exfalso. eauto.
  (* GT *)
  assert (FMemory.Mem.valid_block m1' (get_block fl (FMemory.Mem.nextblockid m1'))).
  { assert (exists b, Ple bound b /\ Plt b stk /\ (Pos.to_nat b - Pos.to_nat bound = FMemory.Mem.nextblockid m1'))%nat.
    { remember (FMemory.Mem.nextblockid m1') as N. remember (Pos.to_nat stk) as STK. remember (Pos.to_nat bound) as B.
      exists (Pos.of_nat (STK - (STK - B - N))).
      assert (N + B > 0)%nat. assert (0 < B)%nat. subst. apply Pos2Nat.is_pos. omega.
      assert (STK - (STK - B - N) = N + B)%nat. generalize H1; clear. intros. omega.
      rewrite H3. rewrite Nat2Pos.id; [|revert H2; clear; intro; omega].
      split;[|split;[|clear; omega]].
      rewrite <- (Pos2Nat.id bound), <- HeqB. clear.
      unfold Ple. 
      revert B. induction N; intros. simpl. lia.
      destruct B. simpl. lia.
      remember (S B) as B'.
      rewrite plus_Sn_m, Nat2Pos.inj_succ. specialize (IHN B'). lia. lia.
      rewrite <- (Pos2Nat.id stk), <- HeqSTK. assert (N + B < STK)%nat by (revert H1; clear; intro; omega).
      revert H2 H4. clear. generalize (N + B)%nat. clear. unfold Plt.
      intros. apply Pos2Nat.inj_lt. repeat rewrite Nat2Pos.id; auto; lia.
    }      
    destruct H2 as [b [BOUND [LTSTK NEXT]]]. rewrite <- NEXT in H1|-* .
    assert (construct_inj j bound fl b = Some (get_block fl (Pos.to_nat b - Pos.to_nat bound))).
    { unfold construct_inj. destruct plt; auto.
      exploit Plt_Ple_trans. exact p. exact BOUND. intro C. apply Plt_ne in C. contradiction. }
    exploit mem_related_valid_block; eauto. unfold FMemory.strip, GMem.valid_block. simpl. intro. apply H3.
    subst. auto.
  }
  eapply FMemory.Mem.valid_wd in H2; subst; eauto. omega.
Qed.
  
Lemma alloc_related:
  forall j bound fl m1 m1' lo hi m2 stk m2' stk' (NOREP: norep fl),
    fl = FMemory.Mem.freelist m1' ->
    mem_related j bound fl (FMemory.strip m1') m1 ->
    Memory.Mem.alloc m1 lo hi = (m2, stk) ->
    FMemory.Mem.alloc m1' lo hi = (m2', stk') ->
    mem_related j bound fl (FMemory.strip m2') m2.
Proof.
  intros until stk'; intros ? FL MEMREL ALLOC ALLOC'.
  exploit alloc_result_related; eauto. intro.
  Transparent Memory.Mem.alloc FMemory.Mem.alloc.
  unfold Memory.Mem.alloc, FMemory.Mem.alloc in *.
  inv ALLOC. inv ALLOC'. unfold FMemory.strip; simpl.
  inv MEMREL; constructor; simpl in *; auto.
  (* valid *)
  unfold Memory.Mem.valid_block, GMem.valid_block in *; simpl in *. intros.
  destruct (peq b (Memory.Mem.nextblock m1)).
  subst. split; intro. left. congruence. eauto with coqlib.
  split; intro. right. eapply mem_related_valid_block; eauto.
  unfold Plt in *. lia.
  destruct H1. subst. exfalso. apply n. eapply construct_inj_injective; eauto.
  intros ? ? ? ? . eapply mem_related_freelist_disjoint. unfold get_block; rewrite H1. eauto.
  apply Plt_trans with (Memory.Mem.nextblock m1); auto with coqlib.
  eapply mem_related_valid_block; eauto.
  (* shared valid *)
  unfold Memory.Mem.valid_block in *; simpl in *. intros. unfold Plt in *.
  apply Pos.lt_trans  with (Memory.Mem.nextblock m1); auto. lia.
  (* shared_valid' *)
  unfold GMem.valid_block in *; simpl in *. intros. right. auto.
  (* perm *)
  unfold GMem.perm, Memory.Mem.perm in *; simpl in *.
  intros. exploit mem_related_mem_perm_eq; eauto. instantiate (1:= ofs); intro.
  destruct (peq b (Memory.Mem.nextblock m1)). subst.
  rewrite H in H0. inv H0. repeat rewrite PMap.gss.
  destruct (zle lo ofs && zlt ofs hi).
  split; intro; inv H2; constructor.
  split; intro C; inv C.
  repeat rewrite PMap.gso; auto. intro. apply n. subst.
  eapply construct_inj_injective; eauto.
  intros ? ? ? ? . eapply mem_related_freelist_disjoint. unfold get_block; rewrite H4. eauto.
  (* memval *)
  intros.
  destruct (peq b (Memory.Mem.nextblock m1)); subst.
  rewrite H in H0. inv H0. repeat rewrite PMap.gss. repeat rewrite ZMap.gi. constructor.
  repeat rewrite  PMap.gso; auto. apply mem_related_mem_val_inject; auto.
  unfold Memory.Mem.perm in *; simpl in *.
  rewrite PMap.gso in H1; auto.
  intro; apply n; subst. eapply construct_inj_injective; eauto.
  intros ? ? ? ? . eapply mem_related_freelist_disjoint. unfold get_block; rewrite H2. eauto.
Qed.

Lemma free_related:
  forall j bound fl m1 m1' b b' lo hi,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) -> 
    mem_related j bound fl (FMemory.strip m1') m1 ->
    construct_inj j bound fl b = Some b' ->
    option_rel (fun m2 m2' => mem_related j bound fl (FMemory.strip m2') m2)
               (Memory.Mem.free m1 b lo hi)
               (FMemory.Mem.free m1' b' lo hi).
Proof.
  intros until hi. intros NOREP NOOVERLAP INJECT MEMREL INJ.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT) as INJECTIVE.
  destruct (Memory.Mem.free m1 b lo hi) as [m2|] eqn:FREE;
    destruct (FMemory.Mem.free m1' b' lo hi) as [m2'|] eqn:FREE'; try constructor.
  pose proof FREE as FREEE0. apply Memory.Mem.free_result in FREE; apply FMemory.Mem.free_result in FREE'.
  unfold Memory.Mem.unchecked_free, FMemory.Mem.unchecked_free in *; subst. unfold FMemory.strip. simpl.
  inv MEMREL; constructor; eauto; simpl.
  { (* perm *)
    unfold GMem.perm, Memory.Mem.perm, Memperm.perm_order', Memory.Mem.perm_order' in *; simpl.
    intros. exploit mem_related_mem_perm_eq; eauto. instantiate (1:= ofs). intro.
    destruct (peq b0 b).
    subst. rewrite INJ in H. inv H. repeat rewrite PMap.gss.
    generalize H0 H1 H2 INJECTIVE; clear; intros PERMKIND PERM PERMEQ.
    inv PERMKIND; inv PERM; match goal with |- context[if ?x then _ else _] => destruct x end; try tauto.
    repeat rewrite PMap.gso; auto. intro. apply n. eapply INJECTIVE; subst; eauto. }
  { (* content *)
    intros. eapply mem_related_mem_val_inject; eauto.
    generalize H0; clear. unfold Memory.Mem.perm; simpl.
    destruct (peq b b0). subst. rewrite PMap.gss. destruct (_ && _); auto. intro C. inversion C.
    rewrite PMap.gso; auto. }
  apply Memory.Mem.free_range_perm in FREE.
  exploit mem_rel_range_perm; eauto; try (intro A; apply A in FREE); try constructor.
  apply FMemory.Mem.range_perm_free in FREE. rewrite FREE' in FREE. inversion FREE. discriminate.
  apply FMemory.Mem.free_range_perm in FREE'.
  exploit mem_rel_range_perm; eauto; try (intro A; apply A in FREE'); try constructor.
  apply Memory.Mem.range_perm_free in FREE'. rewrite FREE in FREE'. inversion FREE'. discriminate.
Qed.

Lemma valid_pointer_related:
  forall j bound fl m m' b b' ofs,
    mem_related j bound fl (FMemory.strip m') m ->
    construct_inj j bound fl b = Some b' ->
    Memory.Mem.valid_pointer m b ofs = FMemory.Mem.valid_pointer m' b' ofs.
Proof.
  intros. unfold Memory.Mem.valid_pointer, FMemory.Mem.valid_pointer.
  unfold Memory.Mem.perm_dec, FMemory.Mem.perm_dec.
  destruct Memory.Mem.perm_order'_dec.
  fold (Memory.Mem.perm m b ofs Memtype.Cur Memtype.Nonempty) in p. simpl in *.
  erewrite <- mem_related_mem_perm_eq in p; eauto; try constructor.
  unfold GMem.perm, FMemory.strip in p. simpl in *. destruct FMemory.Mem.perm_order'_dec; auto; exfalso; eauto.
  fold (Memory.Mem.perm m b ofs Memtype.Cur Memtype.Nonempty) in n. simpl in *.
  erewrite <- mem_related_mem_perm_eq in n; eauto; try constructor.
  unfold GMem.perm, FMemory.strip in n. simpl in *. destruct FMemory.Mem.perm_order'_dec; auto; exfalso; eauto.
Qed.

Lemma cmpu_bool_related:
  forall j bound fl m m' v1 v2 v1' v2' c,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) -> 
    mem_related j bound fl (FMemory.strip m') m ->
    val_related (construct_inj j bound fl) v1 v1' ->
    val_related (construct_inj j bound fl) v2 v2' ->
    option_rel eq (Val.cmpu_bool (Memory.Mem.valid_pointer m) c v1 v2)
               (Val.cmpu_bool (FMemory.Mem.valid_pointer m') c v1' v2').
Proof.
  intros. pose proof (construct_inj_injective _ _ _ H H0 H1).
  inv H3; inv H4; simpl; try destruct Archi.ptr64; try constructor; auto;
      repeat erewrite valid_pointer_related; eauto;
        repeat match goal with |- context[match ?x with _ => _ end] => destruct x eqn:?Hx end;
        try congruence; destruct c; simpl; try constructor; auto;
          subst; exfalso; eauto.
Qed.

Lemma cmplu_bool_related:
  forall j valid_pointer v1 v1' v2 v2' c,
    val_related j v1 v1' ->
    val_related j v2 v2' ->
    option_rel eq (Val.cmplu_bool valid_pointer c v1 v2)
               (Val.cmplu_bool valid_pointer c v1' v2').
Proof. intros. inv H; inv H0; destruct c; simpl; constructor; auto. Qed.


Hint Resolve  alloc_related alloc_result_related free_related.
