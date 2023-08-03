Require Import Coqlib Values Globalenvs
        Blockset Footprint GMemory Memory MemAux.

Require Import LDSimDefs LDSim LDSim_local.

Require Import Maps FiniteMaps.


Lemma ptrofs_add_0:
  forall ofs, Integers.Ptrofs.add ofs (Integers.Ptrofs.repr 0) = ofs.
Proof.
  intro. rewrite <- Integers.Ptrofs.unsigned_zero,
         Integers.Ptrofs.repr_unsigned, Integers.Ptrofs.add_zero. auto.
Qed.

Lemma inj_to_meminj_some:
  forall j b b' delta, Bset.inj_to_meminj j b = Some (b', delta) ->
                  j b = Some b' /\ delta = 0.
Proof. clear. unfold Bset.inj_to_meminj. intros. destruct (j b); inv H. auto. Qed.

Lemma eq_valid_eq_nextblock:
  forall m m',
    (forall b, Mem.valid_block m b <-> Mem.valid_block m' b) ->
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  intros. unfold Mem.valid_block in H.
  destruct (plt (Mem.nextblock m) (Mem.nextblock m')).
  specialize (H (Mem.nextblock m)). xomega.
  rewrite <- Pos.le_nlt, Pos.lt_eq_cases in n. destruct n; auto.
  specialize (H (Mem.nextblock m')). xomega.
Qed.

Lemma mem_access_default:
  forall m ofs K, fst (Mem.mem_access m) ofs K = None.
Proof.
  intros. exploit (pmap_finite_sound_c _ (Mem.mem_access m)).
  instantiate (1:= Pos.max (pmap_finite_c _ (Mem.mem_access m)) (Mem.nextblock m)).
  xomega. intro.
  rewrite <- H. exploit Mem.nextblock_noaccess; eauto. xomega.
Qed.


(** memval inject strict *)
Inductive val_inject_strict (mi: meminj) : val -> val -> Prop :=
  inject_int : forall i : Integers.Int.int, val_inject_strict mi (Vint i) (Vint i)
| inject_long : forall i : Integers.Int64.int, val_inject_strict mi (Vlong i) (Vlong i)
| inject_float : forall f : Floats.float, val_inject_strict mi (Vfloat f) (Vfloat f)
| inject_single : forall f : Floats.float32, val_inject_strict mi (Vsingle f) (Vsingle f)
| inject_ptr : forall (b1 : block) (ofs1 : Integers.Ptrofs.int) (b2 : block)
                 (ofs2 : Integers.Ptrofs.int) (delta : BinNums.Z),
    mi b1 = Some (b2, delta) ->
    ofs2 = Integers.Ptrofs.add ofs1 (Integers.Ptrofs.repr delta) ->
    val_inject_strict mi (Vptr b1 ofs1) (Vptr b2 ofs2)
| val_inject_undef : val_inject_strict mi Vundef Vundef.

Inductive memval_inject_strict (f: meminj) : memval -> memval -> Prop :=
  memval_inject_byte': forall n, memval_inject_strict f (Byte n) (Byte n)
| memval_inject_frag': forall v1 v2 q n, val_inject_strict f v1 v2 ->
                                    memval_inject_strict f (Fragment v1 q n) (Fragment v2 q n)
| memval_inject_undef': memval_inject_strict f Undef Undef.

Lemma memval_eq_inject_strict_eq:
  forall mi mv mv1 mv2,
    memval_inject_strict mi mv mv1 ->
    memval_inject_strict mi mv mv2 ->
    mv1 = mv2.
Proof.
  intros. destruct mv; inv H; inv H0; auto.
  destruct v; inv H5; inv H4; auto.
  rewrite H1 in H2. inv H2. auto.
Qed.

Lemma memval_eq_inject_strict_eq':
  forall j mv1 mv2 mv,
    Bset.inj_inject j ->
    memval_inject_strict (Bset.inj_to_meminj j) mv1 mv ->
    memval_inject_strict (Bset.inj_to_meminj j) mv2 mv ->
    mv1 = mv2.
Proof.
  intros. destruct mv; inv H0; inv H1; auto.
  destruct v; inv H4; inv H3; auto. unfold Bset.inj_to_meminj in *.
  destruct (j b1) eqn:?; inv H5. destruct (j b0) eqn:?; inv H4.
  eapply H in Heqo. rewrite Heqo; eauto. cut (ofs0 = ofs1). intros; subst; auto.
  rewrite <- Integers.Ptrofs.unsigned_zero in H6.
  rewrite Integers.Ptrofs.repr_unsigned in H6.
  do 2 rewrite Integers.Ptrofs.add_zero in H6. auto.
Qed.
        
(** Bset revert *)
Lemma finite_bset_inject_revert:
  forall j (bs bs': Bset.t) bound
    (FINITE: forall b, bs b -> Plt b bound),
    Bset.inject j bs bs' ->
    exists j', Bset.inject j' bs' bs /\ 
          (forall b b', j b = Some b' <-> j' b' = Some b).
Proof.
  intros j bs bs' bound FINITE INJECT.
  assert (REC: forall B, (B <= bound)%positive ->
                    exists j', (forall b b',(b < B)%positive -> j b = Some b' -> j' b' = Some b)
                          /\
                          (forall b b', j' b' = Some b -> j b = Some b')).
  { (* induction on B *)
    intros B; pattern B. apply Pos.peano_rect; intros.
    (* base *)
    exists (fun b => None). intros.
    split; intros. xomega. inv H0.
    (* inductive *)
    exploit H. xomega. intros (j'0 & JJ' & J'J). clear H.
    destruct (j p) as [p_img|] eqn:INJp.
    (* p in bs *)
    exists (fun b' => if peq b' p_img then Some p else j'0 b').
    split; intros.
    (* J -> J' *)
    destruct peq; subst.
    (*  b = p *)
    inv INJECT. inv inj_weak. exploit (inj_injective b p); eauto. intro. subst; auto.
    (*  b <> p *)
    exploit JJ'; eauto.
    destruct (peq b p). exfalso. apply n. subst. rewrite H1 in INJp. inv INJp; auto.
    xomega.
    (* J' <- J *)
    destruct peq. inv H. auto. eauto.
    (* p not in bs *)
    exists j'0. split; auto. intros. destruct (peq b p). subst. rewrite INJp in H1; inv H1.
    apply JJ'; auto. xomega.
  }
  exploit (REC bound). xomega. intros (j' & Hj'1 & Hj'2).
  exists j'. split.
  inv INJECT. inv inj_weak.
  constructor; intros. constructor; intros.
  apply Hj'2 in H. eapply inj_range'; eauto.
  apply inj_dom in H. destruct H as [b H]. exists b. apply Hj'1; auto. apply inj_dom' in H. apply FINITE; auto.
  apply Hj'2 in H. eapply inj_dom'. eauto.
  apply Hj'2 in H. apply Hj'2 in H0. rewrite H in H0. inv H0; auto.
  destruct (inj_range _ H) as [b' H']. exists b'. apply Hj'1; auto. apply FINITE; auto. eapply inj_dom'. eauto.
  
  split; intros. destruct (plt b bound). apply Hj'1; auto. 
  inv INJECT. eapply Bset.inj_dom' in H; eauto. apply FINITE in H. contradiction.
  apply Hj'2. auto.
Qed.


Lemma bset_inject_revert:
  forall j bound,
    let bs := (fun b => Plt b bound) in
    Bset.inject j bs bs ->
    exists j', Bset.inject j' bs bs /\ 
          (forall b b', j b = Some b' <-> j' b' = Some b).
Proof.
  intros until bs. intro INJECT.
  assert (REC: forall B, (B <= bound)%positive ->
                    exists j', (forall b b',(b < B)%positive -> j b = Some b' -> j' b' = Some b)
                          /\
                          (forall b b', j' b' = Some b -> j b = Some b')).
  { (* induction on B *)
    intros B; pattern B. apply Pos.peano_rect; intros.
    (* base *)
    exists (fun b => None). intros.
    split; intros. xomega. inv H0.
    (* inductive *)
    exploit (Bset.inj_dom _ _ _ INJECT p). subst bs. unfold Bset.belongsto. xomega.
    intros (p_img & INJ_p).
    exploit H. xomega. intros (j'_0 & Hj'_0).
    exists (fun b => if peq b p_img then Some p else j'_0 b).
    split; intros.
    destruct (peq b p).
    (*  b = p *)
    subst. rewrite INJ_p in H2. inv H2. destruct peq; [auto|contradiction].
    (*  b <> p *)
    assert (j b = Some p_img <-> False).
    { split; [intro C | contradiction]. inv INJECT.
      pose proof (Bset.inj_injective _ _ _ inj_weak _ _ _ INJ_p C). subst b. contradiction. }
    destruct peq; subst. apply H3 in H2. contradiction.
    destruct Hj'_0. apply H4. xomega. auto.

    destruct peq; subst. inv H1. auto.
    destruct Hj'_0. apply H3. auto.
  }
  exploit (REC bound). xomega. intros (j' & Hj'1 & Hj'2).
  exists j'. split.
  inv INJECT. inv inj_weak.
  constructor; intros. constructor; intros.
  apply Hj'2 in H. eapply inj_range'; eauto.
  apply inj_dom in H. destruct H as [b H]. exists b. apply Hj'1; auto. apply inj_dom' in H.
  unfold Bset.belongsto in H. subst bs. xomega.
  apply Hj'2 in H. eapply inj_dom'. eauto.
  apply Hj'2 in H. apply Hj'2 in H0. rewrite H in H0. inv H0; auto.
  destruct (inj_range _ H) as [b' H']. exists b'. apply Hj'1; auto. eapply inj_dom'. eauto.
  
  split; intros. destruct (plt b bound). apply Hj'1; auto. 
  inv INJECT. eapply Bset.inj_dom' in H; eauto. subst bs. unfold Bset.belongsto in H.
  contradiction. apply Hj'2. auto.
Qed.





(** Construct memval mapping for each block *)

Lemma memval_inject_strict_revert:
  forall j j',
    (forall b b', j b = Some b' <-> j' b' = Some b) ->
    forall v v',
      memval_inject_strict (Bset.inj_to_meminj j) v v' ->
      memval_inject_strict (Bset.inj_to_meminj j') v' v.
Proof.
  intros.
  destruct v, v'; inv H0; constructor.
  inv H2; try constructor. unfold Bset.inj_to_meminj in H0.
  destruct (j b1) eqn:? . inv H0.
  assert (ofs1 = Integers.Ptrofs.add ofs1 (Integers.Ptrofs.repr 0)).
  { rewrite <- Integers.Ptrofs.unsigned_zero,
    Integers.Ptrofs.repr_unsigned, Integers.Ptrofs.add_zero. auto. }
  rewrite <- H0. rewrite H0 at 2. econstructor; eauto. rewrite H in Heqo.
  cbv. rewrite Heqo. auto. inv H0.
Qed.

(* construct injected value: pointer to unmapped block injected to Vundef. *)
Definition inject_value (j: Bset.inj) (v: val) : val :=
  match v with
  | Vptr b ofs =>
    match j b with
    | Some b' => Vptr b' ofs
    | None => Vundef
    end
  | _ => v
  end.

Lemma inject_value_func_wd:
  forall (j: Bset.inj) v,
    G_arg (fun b => if j b then True else False) v ->
    val_inject_strict (Bset.inj_to_meminj j) v (inject_value j v) .
Proof.
  intros. cbv in H. destruct v; simpl; try constructor.
  destruct (j b) eqn: Jb; [clear H|contradiction].
  econstructor. unfold Bset.inj_to_meminj. rewrite Jb. eauto.
  rewrite <- Integers.Ptrofs.unsigned_zero,
  Integers.Ptrofs.repr_unsigned, Integers.Ptrofs.add_zero. auto.
Qed.

Definition inject_memval (j: Bset.inj) (mv: memval) : memval :=
  match mv with
  | Undef => Undef
  | Byte n => Byte n
  | Fragment v q n => Fragment (inject_value j v) q n
  end.

Definition G_memval (bs: Bset.t) (mv: memval) : Prop :=
  match mv with
  | Fragment v _ _ => G_arg bs v
  | _ => True
  end.

Lemma inject_memval_func_wd:
  forall (j: Bset.inj) mv,
    G_memval (fun b => if j b then True else False) mv ->
    memval_inject_strict (Bset.inj_to_meminj j) mv (inject_memval j mv).
Proof.
  intros. cbv in H. destruct mv; simpl; try constructor.
  eapply inject_value_func_wd; eauto.
Qed.

Definition inject_zmap_memval (j: Bset.inj) (m: ZMap.t memval) (z: Z) : memval :=
  (inject_memval j (ZMap.get z m)).

Program Definition inject_zmap_memval_c (j: Bset.inj) (m: ZMap.t memval) :=
  @zmap_construct_c memval (fun z => inject_zmap_memval j m z)
                    (fst (zmap_finite_c memval m)) (snd (zmap_finite_c memval m))
                    (inject_memval j (fst m)) _.
Next Obligation.
  unfold inject_zmap_memval.
  exploit (zmap_finite_sound_c memval m).
  instantiate (2:= (fst (zmap_finite_c memval m))).
  instantiate (1:= (snd (zmap_finite_c memval m))).
  2: eauto. auto. intros. rewrite <- H0. auto.
Qed.


(** Construct mem content *)
(* for those blocks within bound and mapped by j, 
       update the original_content with j^-1(update_content) *)
Definition inject_content (j j': Bset.inj) (bound: block)
           (original_content update_content: PMap.t (ZMap.t memval))
           (b: block) : ZMap.t memval :=
  if plt b bound 
  then
    match j b with
    | Some b' => proj1_sig (inject_zmap_memval_c j' (update_content!!b'))
    | _ => original_content!!b
    end
  else
    original_content!!b
.

Program Definition inject_content_c (j j': Bset.inj) (bound: block)
        (original_content update_content: PMap.t (ZMap.t memval)) :=
  pmap_construct_c
    _ (fun b => inject_content j j' bound original_content update_content b)
    (Pos.max (pmap_finite_c _ original_content) bound)
    (fst original_content) _.
Next Obligation.
  unfold inject_content. destruct plt. xomega.
  exploit pmap_finite_sound_c; eauto. xomega.
Qed.




(** Construct mem access *)
(* update m2 with m1' *)
Definition update_access_func (j: Bset.inj) (bound: block)
           (m2 m1': PMap.t (Z -> perm_kind -> option permission))
           (b: block) : Z -> perm_kind -> option permission :=
  if plt b bound then
    match j b with
    | Some b' => m1' !! b'
    | None => m2 !! b
    end
  else m2 !! b.

Program Definition update_access_c (j: Bset.inj) (bound: block)
        (m2 m1' : PMap.t (Z -> perm_kind -> option permission)) :=
  pmap_construct_c _ (update_access_func j bound m2 m1')
                   (Pos.max (pmap_finite_c _ m2) bound) (fst m2) _.
Next Obligation.
  unfold update_access_func. destruct plt; [|exploit pmap_finite_sound_c; eauto]; xomega.
Qed.

Program Definition update_memory (j21 j12: Bset.inj) (bound: block)
        (m2 m1': Mem.mem) : Mem.mem :=
  Mem.mkmem (proj1_sig (inject_content_c j21 j12 bound (Mem.mem_contents m2) (Mem.mem_contents m1')))
            (proj1_sig (update_access_c j21 bound (Mem.mem_access m2) (Mem.mem_access m1')))
            (Pos.max (Mem.nextblock m2) bound)
            _ _ _.
Next Obligation.
  pose proof (proj2_sig (update_access_c j21 bound (Mem.mem_access m2) (Mem.mem_access m1'))).
  simpl in H. destruct H. rewrite H0. clear H H0.
  unfold update_access_func. 
  destruct (j21 b) eqn:?; destruct plt; apply Mem.access_max.
Qed.
Next Obligation.
  pose proof (proj2_sig (update_access_c j21 bound (Mem.mem_access m2) (Mem.mem_access m1'))).
  simpl in H0. destruct H0. rewrite H1. unfold update_access_func.
  destruct plt;[xomega|]. apply Mem.nextblock_noaccess; xomega.
Qed.
Next Obligation.
  pose proof (proj2_sig (inject_content_c j21 j12 bound (Mem.mem_contents m2) (Mem.mem_contents m1'))).
  simpl in H; destruct H. rewrite H0.
  unfold inject_content. destruct (j21 b); destruct plt; try apply Mem.contents_default.
  destruct (proj2_sig (inject_zmap_memval_c j12 (Mem.mem_contents m1') !! b0)).
  rewrite H1. rewrite Mem.contents_default. auto.
Qed.








