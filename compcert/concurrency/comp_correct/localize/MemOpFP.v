Require Import Coqlib Integers Values AST Blockset Footprint.
Require Import FMemOpFP.

Require Import Memory.



(** ** relations on footprints *)
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation FP := FP.Build_t.

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
    - [eval_builtin_args_fp]
 *)

Local Hint Resolve range_locset_loc range_locset_inj_fp_mapped.

(** ** ALLOC *)
(** The footprint for allocation is wierd. Since it requires the 
    highest priority which is called "frees".... *)

Definition alloc_fp (m: mem) (lo hi: Z) : footprint :=
  uncheck_alloc_fp m.(Mem.nextblock) lo hi.

Lemma alloc_fp_loc:
  forall m lo hi b ofs,
    Locs.belongsto (FP.frees (alloc_fp m lo hi)) b ofs <->
    b = m.(Mem.nextblock).
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
  econstructor; intros. Locs.unfolds.
  destruct peq; subst.
  econstructor; eauto; Locs.unfolds.
  destruct peq; congruence.
  instantiate (1:= tofs - delta); Lia.lia.
  congruence.
Qed.
  
Local Hint Resolve alloc_fp_loc alloc_parallel_inj_fp_mapped.
(** ** FREE *)
Notation free_fp := free_fp.
Notation free_fp_loc := free_fp_loc.
Local Hint Resolve free_fp_loc.

(** ** STORE *)
Notation store_fp := store_fp.
Notation store_fp_loc := store_fp_loc.
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
Notation loadv_fp := loadv_fp.
Notation loadv_fp_loc := loadv_fp_loc.
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

Local Hint Resolve loadv_fp_loc loadv_inj_fp_mapped.

(** ** STOREV *)
Notation storev_fp := storev_fp.
Notation storev_fp_loc := storev_fp_loc.
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
Notation loadbytes_fp := loadbytes_fp.
Notation loadbytes_fp_loc := loadbytes_fp_loc.
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
  Lia.lia.
Qed.

Local Hint Resolve loadbytes_fp_loc loadbytes_inj_fp_mapped.


(** ** STOREBYTES *)
Notation storebytes_fp := storebytes_fp.
Notation storebytes_fp_loc := storebytes_fp_loc.
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
  intuition.
Qed.

Local Hint Resolve storebytes_fp_loc storebytes_inj_fp_mapped.

(** ** FREE_LIST *)
Notation free_list_fp := free_list_fp.
Notation free_list_fp_loc := free_list_fp_loc.
Notation free_list_fp_frees := free_list_fp_frees.
Local Hint Resolve free_list_fp_loc free_list_fp_frees.
    
(** ** DROP *)
(** Is drop used in step relations? 
    It seems drop is only used in constructing initial memory. *)

(** ** VALID_POINTER *)
Notation valid_pointer_fp := valid_pointer_fp.
Notation valid_pointer_fp_loc := valid_pointer_fp_loc.

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


Lemma weak_valid_pointer_extend_subset:
  forall m m' b ofs,
    Mem.extends m m' ->
    FP.subset (weak_valid_pointer_fp m' b (Ptrofs.unsigned ofs))
              (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs)).
Proof.
  clear. intros. inv H. inv mext_inj. unfold inject_id in mi_perm.
  unfold weak_valid_pointer_fp, valid_pointer_fp. unfold Mem.valid_pointer.
  destruct (Mem.perm_dec m), (Mem.perm_dec m'); simpl; try apply FP.subset_refl.
  simpl. eapply mi_perm in p; eauto. rewrite Z.add_0_r in p. contradiction.
  constructor; simpl; try apply Locs.subset_emp. clear.
  Locs.unfolds. unfold FMemOpFP.range_locset. intros.
  destruct eq_block; [|discriminate].
  destruct zle, zlt; try discriminate. destruct zle, zlt; try Lia.lia; auto.
Qed.

(** ** Builtin Args *)
Require Import Globalenvs Events.
Inductive eval_builtin_arg_fp {A: Type} (ge: Senv.t) (e: A -> val) (sp: val) : AST.builtin_arg A -> footprint -> Prop :=
| eval_BA_fp : forall x, eval_builtin_arg_fp ge e sp (BA x) empfp
| eval_BA_int_fp: forall n, eval_builtin_arg_fp ge e sp (BA_int n) empfp
| eval_BA_long_fp: forall n, eval_builtin_arg_fp ge e sp (BA_long n) empfp
| eval_BA_float_fp: forall n, eval_builtin_arg_fp ge e sp (BA_float n) empfp
| eval_BA_single_fp: forall n, eval_builtin_arg_fp ge e sp (BA_single n) empfp
| eval_BA_loadstack_fp: forall chunk ofs,
    eval_builtin_arg_fp ge e sp (BA_loadstack chunk ofs) (loadv_fp chunk (Val.offset_ptr sp ofs))
| eval_BA_addrstack: forall ofs, eval_builtin_arg_fp ge e sp (BA_addrstack ofs) empfp
| eval_BA_loadglobal: forall chunk id ofs,
    eval_builtin_arg_fp ge e sp (BA_loadglobal chunk id ofs) (loadv_fp chunk (Senv.symbol_address ge id ofs))
| eval_BA_addrglobal: forall id ofs, eval_builtin_arg_fp ge e sp (BA_addrglobal id ofs) empfp
| eval_BA_splitlong: forall hi lo fp1 fp2 fp,
    eval_builtin_arg_fp ge e sp hi fp1 ->
    eval_builtin_arg_fp ge e sp lo fp2 ->
    FP.union fp1 fp2 = fp ->
    eval_builtin_arg_fp ge e sp (BA_splitlong hi lo) fp.

Inductive eval_builtin_args_fp {A: Type} (ge: Senv.t) (e: A -> val) (sp: val) :
  list (AST.builtin_arg A) -> footprint -> Prop :=
| eval_BAs_nil: eval_builtin_args_fp ge e sp nil empfp
| eval_BAs_cons: forall a al fp1 fp2 fp,
    eval_builtin_arg_fp ge e sp a fp1 ->
    eval_builtin_args_fp ge e sp al fp2 ->
    fp = FP.union fp1 fp2 ->
    eval_builtin_args_fp ge e sp (a :: al) fp.

Section EVAL_BUILTIN_ARG_PRESERVED.
Variables A F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable e: A -> val.
Variable sp: val.
Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.
Lemma eval_builtin_arg_fp_preserved:
  forall a fp, eval_builtin_arg_fp ge1 e sp a fp -> eval_builtin_arg_fp ge2 e sp a fp.
Proof.
  assert (EQ: forall id ofs, Senv.symbol_address ge2 id ofs = Senv.symbol_address ge1 id ofs).
  { unfold Senv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; try constructor. rewrite <- EQ. constructor.
  econstructor; eauto.
Qed.
Lemma eval_builtin_args_fp_preserved:
  forall al fp, eval_builtin_args_fp ge1 e sp al fp -> eval_builtin_args_fp ge2 e sp al fp.
Proof.
  induction 1; econstructor; eauto. eapply eval_builtin_arg_fp_preserved; eauto.
Qed.
End EVAL_BUILTIN_ARG_PRESERVED.

Section EVAL_BUILTIN_ARG_LESSDEF.
Variable A: Type.
Variable ge: Senv.t.
Variables e1 e2: A -> val.
Variable sp: val.
Lemma eval_builtin_arg_fp_lessdef:
  forall a fp, eval_builtin_arg_fp ge e1 sp a fp ->
          eval_builtin_arg_fp ge e2 sp a fp.
Proof. induction 1; econstructor; eauto. Qed.
Lemma eval_builtin_args_fp_lessdef:
  forall al fp, eval_builtin_args_fp ge e1 sp al fp ->
           eval_builtin_args_fp ge e2 sp al fp.
Proof.
  induction 1; econstructor; eauto.
  eapply eval_builtin_arg_fp_lessdef; eauto.
Qed.
End EVAL_BUILTIN_ARG_LESSDEF.

