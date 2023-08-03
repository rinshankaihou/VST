Require Import Coqlib Values Globalenvs
        Blockset Footprint GMemory Memory MemAux FMemPerm
        InteractionSemantics IS_local.

Require Import LDSimDefs LDSim LDSim_local.
Require Import Maps FiniteMaps MemInterpolant LDSimDefs_local.

(** * Lifting lemams *)
(** This file contains lifting lemmas for reusing CompCert proof on compiler correctness.
    The main idea is to map [GMemory] to CompCert [Memory],
    and prove simulation over CompCert [Memory] implies simulation over [GMemory]. 
 *)
(** The main result is [Theorem localize] *)

Definition dom (B: block) : list block :=
  map (Pos.of_nat) (seq 1 (Pos.to_nat B - 1))%nat.

Lemma dom_spec_rec: forall B, dom (Pos.succ B) = (dom B) ++ B :: nil.
Proof.
  intro. unfold dom. rewrite Pos2Nat.inj_succ. pose proof (Pos2Nat.is_pos B) as POS.
  remember (Pos.to_nat B) as N.
  assert (B = Pos.of_nat N). subst. rewrite Pos2Nat.id; auto. rewrite H. clear B HeqN H.
  assert (forall s, 0 < N -> seq s (S N - 1) = seq s (N - 1) ++ (s + (N - 1)) :: nil)%nat.
  { clear. induction N. intros. omega.
    destruct N; simpl in *. intro. rewrite Nat.add_0_r. auto.
    intros. rewrite (IHN (S s));[|omega]. simpl. repeat f_equal; omega. }
  rewrite H; auto. rewrite map_app. replace (1 + (N - 1))%nat with N by omega. simpl. auto.
Qed.

Lemma dom_length: forall B, length (dom B) = (Pos.to_nat B - 1)%nat.
Proof. intro. unfold dom. rewrite map_length, seq_length; auto. Qed.

Lemma dom_correct: forall B b, Plt b B <-> In b (dom B).
Proof.
  intros. split; intros.
  unfold dom. rewrite <- (Pos2Nat.id b). apply in_map. auto.
  apply in_seq. pose proof (Pos2Nat.is_pos b); pose proof (Pos2Nat.is_pos B).
  rewrite Nat.add_sub_assoc, minus_plus; try split; try omega. apply Pos2Nat.inj_lt; auto.
  unfold dom in H. apply in_map_iff in H. destruct H as [x [Hb IN]].
  apply in_seq in IN. pose proof (Pos2Nat.is_pos B). rewrite Nat.add_sub_assoc, minus_plus in IN; try omega.
  assert (Pos.to_nat b = x). rewrite <- Hb. apply Nat2Pos.id. omega. rewrite <- H0 in IN. destruct IN as [_ IN].
  destruct (plt b B); auto. apply Pos2Nat.inj_lt in IN. congruence.
Qed.

Lemma dom_norep: forall B, NoDup (dom B).
Proof.
  apply positive_Peano_ind. cbv. constructor.
  intros. rewrite dom_spec_rec. rewrite NoDup_nth_error in H. apply NoDup_nth_error.
  rewrite dom_length in H. rewrite app_length. simpl. intros.
  destruct (Nat.eq_dec i (length (dom x))), (Nat.eq_dec j (length (dom x))); try omega.
  (* i = B, j < B *)
  rewrite nth_error_app2 in H1; try omega. rewrite e, Nat.sub_diag in H1. simpl in H1.
  assert (j < length (dom x ++ x :: nil))%nat. apply nth_error_Some. intro. congruence.
  rewrite app_length in H2. simpl in H2. rewrite nth_error_app1 in H1; try omega.
  symmetry in H1. apply nth_error_in in H1. apply dom_correct, Plt_ne in H1. contradiction.
  (* i < B, j = B *)
  rewrite nth_error_app2 with (n:=j) in H1; try omega. rewrite e, Nat.sub_diag in H1. simpl in H1.
  assert (i < length (dom x ++ x :: nil))%nat. apply nth_error_Some. intro. congruence.
  rewrite app_length in H2. simpl in H2. rewrite nth_error_app1 in H1; try omega.
  apply nth_error_in in H1. apply dom_correct, Plt_ne in H1. contradiction.
  (* i < B, j < B *)
  rewrite nth_error_app1 in H1; try omega.
  assert (nth_error (dom x ++ x :: nil) j <> None). intro. rewrite H2 in H1. apply nth_error_None in H1. omega.
  apply nth_error_Some in H2. rewrite app_length in H2. simpl in H2.
  rewrite nth_error_app1 in H1; try omega.
  apply H; auto. rewrite dom_length in H0, n. omega.
Qed.

Definition range j B : list (option block) :=
  map j (dom B).

Fixpoint leftout (dom: list block) (range: list (option block)): list block :=
  match range with
  | nil => dom
  | None :: range' => leftout dom range'
  | Some b :: range' => leftout (remove peq b dom) range'
  end.

Lemma leftout_nil: forall R, leftout nil R = nil. Proof. induction R; auto. destruct a; auto. Qed.
  
Lemma leftout_cons:
  forall d R D, leftout (d :: D) R = (leftout (d::nil) R) ++ leftout D R.
Proof. induction R; auto. simpl. destruct a; auto. destruct peq; auto. rewrite leftout_nil. auto. Qed.

Lemma leftout_correct: forall R D b, In b (leftout D R) -> In b D /\ ~ In (Some b) R.
Proof.
  induction R; auto; simpl; intros. destruct a as [a|].
  apply IHR in H. destruct H. destruct (peq a b). subst. exfalso. eapply remove_In. eauto.
  split. generalize H. clear. induction D; simpl; auto. destruct peq; auto. simpl. intros [|]; auto.
  intros [|]. inv H1. contradiction. auto.
  apply IHR in H. destruct H. split; auto. intros [|]; congruence.
Qed.

Lemma not_in_remove:
  forall D b, ~ In b D -> remove peq b D = D.
Proof. induction D; auto. simpl. intros. destruct peq. exfalso; apply H; auto. f_equal; auto. Qed.

Lemma nodup_remove_one:
  forall D b,
    NoDup D ->
    (length (remove peq b D) >= length D - 1)%nat /\
    NoDup (remove peq b D).
Proof.
  induction D; intros. simpl. auto.
  simpl. destruct peq. inv H. rewrite not_in_remove; auto. split; [omega|auto].
  inv H. apply IHD with b in H3. simpl. destruct H3. split;[omega|constructor; auto].
  intro. apply H2. generalize n H1; clear. intro H. induction D; auto. simpl. destruct peq. auto.
  simpl. intros [?|?]; auto.
Qed.

Lemma leftout_length:
  forall R D, NoDup D -> (length (leftout D R) >= length D - length R)%nat.
Proof.
  induction R; simpl; intros. omega.
  destruct a as [a|]; auto.
  apply nodup_remove_one with (b:=a) in H. destruct H. apply IHR in H0. unfold block in *; omega.
  apply IHR in H. omega.
Qed.

Lemma leftout_length_none:
  forall R1 R2 D, (length (leftout D (R1 ++ None :: R2)) = length (leftout D (R1 ++ R2)))%nat.
Proof. induction R1; auto. intros. simpl. destruct a as [a|]; auto. Qed.
  
Lemma domain_extension:
  forall j BOUND,
    (forall b b', j b = Some b' -> Plt b BOUND) ->
    forall b, Plt b BOUND -> j b = None ->
         exists b', (forall b, j b <> Some b') /\ Plt b' BOUND.
Proof.
  intros j B DOMBOUND b BOUND NOTINDOM.
  assert (forall b ob, j b = ob -> In ob (range j B)). 
  intros. destruct ob. rewrite <- H. apply in_map with (x := b0). apply dom_correct; eauto.
  rewrite <- NOTINDOM. apply in_map with (x := b). apply dom_correct; eauto.
  assert (In None (range j B)).
  unfold block. rewrite <- NOTINDOM. apply in_map with (x := b). apply dom_correct; eauto.
  exploit in_split; eauto. intros [R1 [R2 RANGE]].
  assert (length (leftout (dom B) (range j B)) > 0)%nat.
  rewrite RANGE. rewrite leftout_length_none. pose proof (leftout_length (R1 ++ R2) (dom B) (dom_norep B)).
  assert (length (dom B) = length (range j B)). unfold range. rewrite map_length; auto.
  rewrite H2, RANGE in H1. repeat rewrite app_length in H1. simpl in H1. omega.
  assert (exists b', In b' (leftout (dom B) (range j B))). destruct (leftout (dom B) (range j B)); simpl; eauto. inv H1.
  destruct H2. exists x. apply leftout_correct in H2. destruct H2. apply dom_correct in H2. split; auto.
  intros. intro. apply H in H4. contradiction.
Qed.

Lemma inj_extension:
  forall j BOUND
    (DOMRANGE: forall b b', j b = Some b' -> Plt b BOUND /\ Plt b' BOUND)
    (INJECTIVE: forall b1 b2 b', j b1 = Some b' -> j b2 = Some b' -> b1 = b2),
  exists j', inject_incr (Bset.inj_to_meminj j) (Bset.inj_to_meminj j') /\
        Bset.inject j' (fun b => Plt b BOUND) (fun b => Plt b BOUND).
Proof.
  clear. intros.
  assert (REC:forall B, Ple B BOUND ->
                   exists j',
                     (forall b b', j' b = Some b' -> Plt b BOUND /\ Plt b' BOUND) /\
                     (forall b1 b2 b', j' b1 = Some b' -> j' b2 = Some b' -> b1 = b2) /\
                     (forall b, Plt b B -> exists b', j' b = Some b') /\
                     inject_incr (Bset.inj_to_meminj j)
                                 (Bset.inj_to_meminj j')).
  { intro B. pattern B. apply positive_Peano_ind.
    (* base *)
    intro. exists j. do 2 (split; [auto|]). split. intros. destruct b; inv H0. apply inject_incr_refl.
    (* inductive *)
    intros. clear B. rename x into B.
    assert (Ple B BOUND). eapply Ple_trans; eauto with coqlib. apply H in H1. clear H.
    destruct H1 as (j' & DOMRANGE' & INJECTIVE' & TOTALB & INCR').
    destruct (j' B) eqn:HB.
    (* already in dom *)
    exists j'. split; auto. split; auto. split. intro. destruct (peq b B). intros. subst. eauto.
    intro. assert (Plt b B). apply Plt_succ_inv in H. destruct H; congruence. auto. auto.
    (* not in dom *)
    assert (exists B', (forall b, j' b <> Some B') /\ Plt B' BOUND) as [B' [Hfresh Hrange]].
    { 
      eapply domain_extension; eauto. intros; edestruct DOMRANGE'; eauto.
      apply Pos.le_succ_l; auto. }
    exists (fun b => if peq b B then Some B' else j' b).
    split. intros. destruct peq; subst; auto. inv H.
    split; auto. unfold Plt, Ple in *. apply Pos.le_succ_l; auto.
    split. intros. destruct (peq b1 B); destruct (peq b2 B); subst; auto.
    inv H. apply Hfresh in H1. contradiction.
    inv H1. apply Hfresh in H. contradiction. eapply INJECTIVE'; eauto.
    split. intros. apply Plt_succ_inv in H; destruct H.
    destruct peq; auto. subst. apply Plt_ne in H. contradiction.
    destruct peq; eauto. congruence.
    apply inject_incr_trans with (Bset.inj_to_meminj j'); auto.
    intros b b' delta. unfold Bset.inj_to_meminj. destruct peq; subst.
    rewrite HB. discriminate. auto.
  }
  exploit (REC BOUND). eauto with coqlib. intros (j' & DOMRANGE' & INJECTIVE' & DOMTOTAL & INCR).
  exists j'. split; auto.
  constructor; auto. constructor; auto.
  intros. edestruct DOMRANGE'; eauto.
  assert (RANGE': forall b b', j' b = Some b' -> Plt b' BOUND) by (intros; edestruct DOMRANGE'; eauto).
  revert RANGE' INJECTIVE' DOMTOTAL; clear. revert j'. unfold Bset.belongsto.
  pattern BOUND. apply positive_Peano_ind.
  intros. destruct b'; inv H. clear.
  intros B; intros. exploit DOMTOTAL. apply Plt_succ. intros [B' HBB'].
  remember (fun b => if plt b B
                  then match j' b with
                       | Some b' => if peq b' B then Some B' else Some b'
                       | None => None
                       end
                  else None) as aj.
  assert (A1: forall b b', aj b = Some b' -> Plt b' B).
  { subst. intros b b'0. destruct plt; [|discriminate]. destruct (j' b) eqn:?; [|discriminate].
    destruct peq. subst. intro C. inv C. destruct (peq b'0 B); subst.
    assert (b = B) by (eapply INJECTIVE'; eauto). subst. apply Plt_ne in p. contradiction.
    apply RANGE', Plt_succ_inv in HBB'. destruct HBB'; congruence.
    intro C; inv C.  apply RANGE' in Heqo. apply Plt_succ_inv in Heqo. destruct Heqo; congruence. }
  assert (A2: forall b1 b2 b', aj b1 = Some b' -> aj b2 = Some b' -> b1 = b2).
  { intros b1 b2 b''. rewrite Heqaj. destruct (plt b1 B);[|discriminate].  destruct (plt b2 B); [|discriminate].
    destruct (j' b1) eqn:Hb1; [|discriminate]. destruct (j' b2) eqn:Hb2; [|discriminate].
    destruct (peq p1 B); destruct (peq p2 B); subst; intros C1 C2; inv C1; inv C2; eauto.
    exploit INJECTIVE'. exact HBB'. exact Hb2. intro. subst. apply Plt_ne in p0. congruence.
    exploit INJECTIVE'. exact HBB'. exact Hb1. intro. subst. apply Plt_ne in p. congruence.
  }
  assert (A3: forall b, Plt b B -> exists b', aj b = Some b').
  { intros b Hb. rewrite Heqaj. destruct plt;[|contradiction].
    exploit (DOMTOTAL b). apply Plt_trans with B; eauto with coqlib. intros [b'' Hb''].
    rewrite Hb''. destruct peq; eauto. }
  specialize (H aj A1 A2 A3).
  assert (forall b b', aj b = Some b' -> j' b = Some b' \/ (j' b = Some B /\ j' B = Some b')).
  { clear H A1 A2 A3. intros. subst. destruct plt; [|discriminate].
    assert (Plt b (Pos.succ B)) by (apply Plt_trans with B; eauto with coqlib).
    destruct (j' b) eqn:A; [|apply DOMTOTAL in H1; destruct H1; congruence].
    destruct peq; subst. inv H. auto. auto. }
  destruct (peq b' B).
  { destruct (peq B' B). exists B. subst. auto.
    assert (exists b0, Plt b0 B /\ j' b0 = Some B).
    { apply Classical_Prop.NNPP. intro.
      assert (C:forall b, ~ Plt b B \/ j' b <> Some B).
      { intros. destruct (plt b B); [right|left; auto]. intro. apply H2. eauto. }
      clear H2. exploit (H B'). apply RANGE' in HBB'.
      apply Plt_succ_inv in HBB'; destruct HBB';[auto|try congruence].
      intros [b0 AJ]. pose proof AJ as AJ'. apply H1 in AJ. destruct AJ.
      exploit INJECTIVE'. exact HBB'. exact H2. intro. subst b0.
      subst aj. destruct (plt B B). eapply Plt_ne; eauto. discriminate.
      specialize (C b0). destruct C as [C | C]. apply C.
      subst aj. destruct plt; auto; discriminate. destruct H2. congruence.
    }
    destruct H2 as [? [_ ?]]. subst. eauto. }
  apply Plt_succ_inv in H0. destruct H0;[|congruence]. apply H in H0. destruct H0.
  apply H1 in H0. destruct H0 as [H0| [_ H0]]; eauto.

  intros. edestruct DOMRANGE'; eauto.
Qed.


(** relate GMem and Mem *)
(** Mem --[j, bound, fl]--> GMem *)
(*
       bound
  |------|-----------...
  |  |   |  \
  |  j   |   \
  |  |   |    \
  |------|  |--------fl---------..
 *)

Definition construct_inj (j: Bset.inj) (bound: block) (fl: freelist) : Bset.inj :=
  fun b =>
    if plt b bound
    then j b
    else Some (get_block fl ((Pos.to_nat b) - (Pos.to_nat bound))%nat).

Lemma construct_inj_total:
  forall j bound fl,
    Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound) ->
    (forall b, exists b', construct_inj j bound fl b = Some b').
Proof.
  intros. unfold construct_inj.
  destruct plt. exploit Bset.inj_dom; eauto. eauto.
Qed.

Lemma construct_inj_injective:
  forall j bound fl,
    norep fl ->
    no_overlap fl (fun b => Plt b bound) ->
    Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound) ->
    Bset.inj_inject (construct_inj j bound fl).
Proof.
  clear; intros.
  intros b1 b2 b'.
  unfold construct_inj. destruct plt; destruct plt; intros; eauto.
  inv H1. inv inj_weak. eauto.
  inv H3. exploit H0; eauto. eapply Bset.inj_range' in H2; eauto. inv H1; eauto. tauto.
  inv H2. exploit H0; eauto. eapply Bset.inj_range' in H3; eauto. inv H1; eauto. tauto.
  inv H2; inv H3. inv H. destruct (peq b1 b2); auto.
  unfold get_block in H4. exfalso; eapply H2. 2: eauto. xomega.
Qed.
        
Lemma construct_inj_incr:
  forall j bound fl,
    (forall b b', j b = Some b' -> Plt b bound) ->
    inject_incr (Bset.inj_to_meminj j) (Bset.inj_to_meminj (construct_inj j bound fl)).
Proof.
  intros. unfold construct_inj. intros b b' delta.
  unfold Bset.inj_to_meminj. destruct (j b) eqn:?;[|discriminate].
  apply H in Heqo. intro. inv H0. destruct plt; auto. contradiction.
Qed.

(** construct access *)
Definition inject_access (j: Bset.inj) (bound: block)
           (original_access: PMap.t (Z -> perm_kind -> option permission))
           (update_access: PMap.t (Z -> Memperm.perm_kind -> option Memperm.permission))
           (b : block) : Z -> perm_kind -> option permission :=
  if plt b bound then
    match j b with
    | Some b' =>
      fun z K =>
        option_map permission_convert' (update_access!!b' z (perm_kind_convert K))
    | None =>
      original_access!!b
    end
  else
    original_access !! b. 

Program Definition inject_access_c (j j': Bset.inj) (bound: block)
        (original_access: PMap.t (Z -> perm_kind -> option permission))
        (update_access: PMap.t (Z -> Memperm.perm_kind -> option Memperm.permission)) :=
  pmap_construct_c _ (inject_access j bound original_access update_access)
                   (Pos.max (pmap_finite_c _ original_access) bound)
                   (fst original_access) _.
Next Obligation.
  unfold inject_access. destruct plt; [|exploit pmap_finite_sound_c; eauto]; xomega.
Qed.



Record mem_related (j: Bset.inj) (bound: block) (fl: freelist)
       (gm: gmem) (m: mem) : Prop :=
  {
    mem_related_inj_j:
      Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound);
    mem_related_freelist_disjoint:
      forall n, ~ Plt (get_block fl n) bound;
    mem_related_valid_block:
      forall b b',
        construct_inj j bound fl b = Some b' ->
        Mem.valid_block m b <-> GMem.valid_block gm b';
    mem_related_shared_valid_local:
      forall b, Plt b bound -> Mem.valid_block m b;
    mem_related_shared_valid_global:
      forall b, Plt b bound -> GMem.valid_block gm b;
    mem_related_mem_perm_eq:
      forall b b' ofs K K' P P',
        construct_inj j bound fl b = Some b' ->
        eq_perm_kind K' K ->
        eq_permission P' P ->
        GMem.perm gm b' ofs K' P' <-> Mem.perm m b ofs K P;
    mem_related_mem_val_inject:
      forall b b' ofs,
        construct_inj j bound fl b = Some b' ->
        Mem.perm m b ofs Max Readable ->
        memval_inject_strict (Bset.inj_to_meminj (construct_inj j bound fl))
                             (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)))
                             (Maps.ZMap.get ofs (Maps.PMap.get b' (GMem.mem_contents gm)));
  }.

Ltac constr_inj_total b fl MEMREL :=
  exploit (construct_inj_total _ _ fl (mem_related_inj_j _ _ _ _ _ MEMREL)); eauto;
  try (inv MEMREL; eauto; fail);
  instantiate (1:=b);
  let b' := fresh b in
  intros (b' & INJb).

Lemma mem_related_inj_dom_1:
  forall j bound fl gm m,
    mem_related j bound fl gm m->
    forall b, Plt b bound -> exists b', j b = Some b' /\ Plt b' bound.
Proof.
  intros. exploit mem_related_inj_j; eauto. intros.
  inv H1. exploit inj_dom; eauto. intros [b' Jb].
  exists b'. split; auto. exploit Bset.inj_range'; eauto.
Qed.
                             
Lemma mem_related_inj_dom_2:
  forall j bound fl gm m,
    mem_related j bound fl gm m ->
    forall b b', j b = Some b' -> Plt b bound.
Proof.
  intros. exploit mem_related_inj_j; eauto. intros.
  inv H1. exploit Bset.inj_dom'; eauto.
Qed.

Lemma mem_related_inj_range_1:
  forall j bound fl gm m,
    mem_related j bound fl gm m ->
    forall b', Plt b' bound -> exists b, j b = Some b' /\ Plt b bound.
Proof.
  intros. exploit mem_related_inj_j; eauto. intros.
  inv H1. exploit Bset.inj_range; eauto. intros [b Jb].
  exists b. split; auto. exploit Bset.inj_dom'; eauto.
Qed.

Lemma  mem_related_inj_range_2:
  forall j bound fl gm m,
    mem_related j bound fl gm m ->
    forall b b', j b = Some b' -> Plt b' bound.
Proof.
  intros. exploit mem_related_inj_j; eauto. intros.
  inv H1. exploit Bset.inj_range'; eauto.
Qed.
                  
Lemma mem_related_inj_injective:
  forall j bound fl gm m,
    mem_related j bound fl gm m -> 
    Bset.inj_inject j.
Proof.
  intros. exploit mem_related_inj_j; eauto. intros.
  unfold Bset.inj_inject. intros.
  inv H0. inv inj_weak. eauto.
Qed.

Lemma mem_related_inj_construct_inj:
  forall j bound fl m m' b b',
    mem_related j bound fl m m' ->
    j b = Some b' ->
    construct_inj j bound fl b = Some b'.
Proof.
  unfold construct_inj; intros; destruct plt; auto. exfalso; apply n.
  inv H. inv mem_related_inj_j0. inv inj_weak. unfold Bset.belongsto in *; eauto.
Qed.

Lemma construct_inj_compat_1:
  forall j bound fl b b',
    j b = Some b' ->
    (forall b1 b2, j b1 = Some b2 -> Plt b1 bound) ->
    construct_inj j bound fl b = Some b'.
Proof.
  intros. unfold construct_inj. destruct plt; auto.
  exfalso. apply n. eapply H0; eauto.
Qed.

Lemma mem_related_mem_val_shared:
  forall j bound fl gm m,
    mem_related j bound fl gm m ->
    forall b b' ofs,
      j b = Some b' ->
      Mem.perm m b ofs Max Readable ->
      memval_inject_strict (Bset.inj_to_meminj (construct_inj j bound fl))
                           (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)))
                           (Maps.ZMap.get ofs (Maps.PMap.get b' (GMem.mem_contents gm))).
Proof.
  intros. eapply construct_inj_compat_1 in H0; eauto.
  eapply mem_related_mem_val_inject; eauto.
  eapply mem_related_inj_dom_2; eauto.
Qed.

Lemma mem_related_unchg_freelist_unchg_local:
  forall j bound fl gm m gm' m',
    norep fl ->
    no_overlap fl (fun b => Plt b bound) ->
    mem_related j bound fl gm m ->
    unchg_freelist fl gm gm' ->
    mem_related j bound fl gm' m' ->
    LDefs.unchg_local (fun b => Plt b bound) m m'.
Proof.
  intros j bound fl gm m gm' m' NOREP NOOVERLAP H H0 H1. inv H0. constructor.
  (* valid *)
  assert (forall b, Mem.valid_block m b <-> Mem.valid_block m' b).
  { intros b. destruct (plt b bound).
    (* shared *)
    exploit mem_related_shared_valid_local; eauto. clear H1.
    exploit mem_related_shared_valid_local; eauto. clear H.
    intros. tauto.
    (* in freelist *)
    constr_inj_total b fl H.
    rewrite mem_related_valid_block; eauto.
    rewrite mem_related_valid_block; eauto.
    apply unchanged_on_validity; eauto. exact 0.
    unfold construct_inj in INJb. destruct plt; [xomega|]. inv INJb.
    unfold in_fl, get_block. eexists; eauto.
  }
  exploit eq_valid_eq_nextblock; eauto. intro. rewrite H2. xomega.
  (* perm eq *)
  unfold Bset.belongsto. intros.
  constr_inj_total b fl H.
  do 2 (rewrite <- mem_related_mem_perm_eq; eauto;
        try eapply perm_kind_convert_eq;
        try eapply permission_convert_eq).
  apply unchanged_on_perm. unfold construct_inj in INJb. destruct plt;[xomega|]. inv INJb.
  unfold in_fl, get_block; eauto.
  eapply mem_related_valid_block; eauto.
  (* content eq *)
  unfold Bset.belongsto. intros.
  constr_inj_total b fl H.
  assert (in_fl fl b0).
  { unfold construct_inj in INJb; destruct plt; [xomega|inv INJb].
    unfold in_fl, get_block; eauto. }
  eapply memval_eq_inject_strict_eq'.
  eapply construct_inj_injective; eauto. inv H. eauto.
  exploit mem_related_mem_val_inject; eauto.
  rewrite <- mem_related_mem_perm_eq; eauto; try (econstructor; fail).
  rewrite <- unchanged_on_perm; eauto. rewrite mem_related_mem_perm_eq; eauto; try (econstructor; fail).
  rewrite <- mem_related_valid_block; eauto. eapply Mem.perm_valid_block; eauto.
  rewrite unchanged_on_contents. clear H1. exploit mem_related_mem_val_inject; eauto.
  auto. rewrite mem_related_mem_perm_eq; eauto; constructor.
Qed.

Lemma mem_related_reach_closed:
  forall m m' j bound fl,
    mem_related j bound fl m m' ->
    MemClosures.reach_closed m (fun b => Plt b bound) <->
    MemClosures_local.reach_closed m' (fun b => Plt b bound).
Proof.
  clear. split; intros.
  - destruct H0 as [RC UNDEF VUNDEF]; constructor; intros.
    * clear UNDEF VUNDEF. inv H0. induction H1. auto.
      exploit (mem_related_inj_dom_1); eauto. intros [b'0 [INJ0 CLOSED0]].
      exploit (mem_related_mem_val_shared); eauto. 
      intro VAL_INJ0. inv VAL_INJ0; try congruence.
      destruct v1; try congruence. inv H5.
      rewrite H2 in H3. inv H3.
      assert (MemClosures.reach' m (fun b => Plt b bound) nil b'0).
      { econstructor. eauto. }
      assert (MemClosures.reachable m (fun b => Plt b bound) b2).
      { econstructor. eapply MemClosures.reach_cons. eauto.
        erewrite mem_related_mem_perm_eq; eauto. eapply construct_inj_compat_1; eauto.
        eapply mem_related_inj_dom_2; eauto. constructor. constructor. eauto. }
      unfold Bset.belongsto in *.
      exploit mem_related_inj_range_1; eauto. intros [b_0 [INJ2 CLOSED2]].
      unfold Bset.inj_to_meminj, construct_inj in H8.
      destruct plt in H8. auto. inv H8.
      exploit mem_related_freelist_disjoint; eauto. contradiction.
    * clear RC VUNDEF. intro.
      exploit Bset.inj_dom; eauto. inv H; eauto.
      intros (b0 & INJ).
      exploit construct_inj_compat_1; eauto. intros.
      eapply Bset.inj_dom' in H3;[|apply mem_related_inj_j in H; inv H; eauto]. eauto.
      instantiate (1:= fl).
      intro. exploit (mem_related_mem_val_inject); eauto. rewrite H2. intro. inv H4.
      eapply (UNDEF b0); eauto. eapply Bset.inj_range'; try exact INJ. apply mem_related_inj_j in H; inv H; eauto.
      eapply mem_related_mem_perm_eq; eauto. constructor. constructor.
    * clear RC UNDEF. intro.
      exploit Bset.inj_dom; eauto. inv H; eauto.
      intros (b0 & INJ).
      exploit construct_inj_compat_1; eauto. intros.
      eapply Bset.inj_dom' in H3;[|apply mem_related_inj_j in H; inv H; eauto]. eauto.
      instantiate (1:= fl).
      intro. exploit (mem_related_mem_val_inject); eauto. rewrite H2. intro. inv H4. inv H6.
      eapply (VUNDEF b0); eauto. eapply Bset.inj_range'; try exact INJ. apply mem_related_inj_j in H; inv H; eauto.
      eapply mem_related_mem_perm_eq; eauto. constructor. constructor.
  - destruct H0 as [RC UNDEF VUNDEF]; constructor; intros.
    * clear UNDEF VUNDEF. inv H0. induction H1; auto.
      exploit (mem_related_inj_range_1); eauto. intros [b'0 [INJ0 CLOSED0']].
      exploit (mem_related_mem_val_shared); eauto.       
      eapply mem_related_mem_perm_eq; eauto. unfold construct_inj.
      destruct plt; [auto|xomega]. constructor. constructor.
      intro VAL_INJ0. inv VAL_INJ0; try congruence.
      destruct v1; inv H5; try congruence.
      rewrite H2 in H4. inv H4.
      assert (MemClosures_local.reach' m' (fun b => Plt b bound) nil b'0).
      { econstructor; eauto. }
      assert (MemClosures_local.reachable m' (fun b => Plt b bound) b0).
      { econstructor. eapply MemClosures_local.reach_cons. eauto.
        erewrite <- mem_related_mem_perm_eq; eauto. eapply construct_inj_compat_1; eauto.
        eapply mem_related_inj_dom_2; eauto. constructor. constructor. eauto. }
      apply RC in H5.
      exploit mem_related_inj_dom_1; eauto. intros [b_0 [INJ2 CLOSED2]].
      exploit mem_related_inj_dom_2; eauto. intros CLOSED0.
      unfold Bset.inj_to_meminj, construct_inj in H8.
      destruct plt in H8. rewrite INJ2 in H8. inv H8. eapply mem_related_inj_range_2; eauto.
      contradiction.
    * clear RC VUNDEF. intro.
      exploit Bset.inj_range; eauto. inv H. inv mem_related_inj_j0; eauto.
      intros (b0 & INJ).
      exploit construct_inj_compat_1; eauto. intros.
      eapply Bset.inj_dom' in H3;[|apply mem_related_inj_j in H; inv H; eauto]. eauto.
      instantiate (1:= fl).
      intro. eapply mem_related_mem_perm_eq in H1; eauto. 
      exploit (mem_related_mem_val_inject); eauto.
      rewrite H2. intro. inv H4.
      eapply (UNDEF b0); eauto. eapply Bset.inj_dom'; try exact INJ. apply mem_related_inj_j in H; inv H; eauto.
      constructor. constructor.
    * clear RC UNDEF. intro.
      exploit Bset.inj_range; eauto. inv H. inv mem_related_inj_j0; eauto.
      intros (b0 & INJ).
      exploit construct_inj_compat_1; eauto. intros.
      eapply Bset.inj_dom' in H3;[|apply mem_related_inj_j in H; inv H; eauto]. eauto.
      instantiate (1:= fl).
      intro. eapply mem_related_mem_perm_eq in H1; eauto. 
      exploit (mem_related_mem_val_inject); eauto.
      rewrite H2. intro. inv H4. inv H7.
      eapply (VUNDEF b0); eauto. eapply Bset.inj_dom'; try exact INJ. apply mem_related_inj_j in H; inv H; eauto.
      constructor. constructor.
Qed.

Definition arg_related (j: Bset.inj) (v v': val) : Prop :=
  val_inject_strict (Bset.inj_to_meminj j) v v'.

Lemma arg_related_G_arg_1:
  forall bj bs bs' v v' (INJDOM: forall b b', bj b = Some b' -> Bset.belongsto bs b),
    G_arg bs' v' -> arg_related bj v v' -> G_arg bs v.
Proof.
  clear. intros. inv H0; try constructor.
  unfold Bset.inj_to_meminj in H1. destruct (bj b1) eqn:?; try congruence.
  inv H1. apply INJDOM in Heqo. auto.
  inv H.
Qed.

Lemma arg_related_G_arg_2:
  forall bj bs bs' v v' (INJRANGE: forall b b', bj b = Some b' -> Bset.belongsto bs' b'),
    G_arg bs v -> arg_related bj v v' -> G_arg bs' v'.
Proof.
  clear. intros. inv H0; try constructor.
  unfold Bset.inj_to_meminj in H1. destruct (bj b1) eqn:?; try congruence.
  inv H1. apply INJRANGE in Heqo. auto.
  inv H.
Qed.

Definition oarg_related: Bset.inj -> option val -> option val -> Prop :=
  fun bj oarg1 oarg2 =>
    match oarg1, oarg2 with
    | Some arg1, Some arg2 =>
      arg_related bj arg1 arg2
    | None, None => True
    | _, _ => False
    end.

Definition args_related (bj: Bset.inj) (vl vl': list val) : Prop :=
  list_forall2 (arg_related bj) vl vl'.

Lemma args_related_G_args_1:
  forall j bs bs' args args'
    (INJDOM: forall b b', j b = Some b' -> Bset.belongsto bs b),
    G_args bs' args' -> args_related j args args' -> G_args bs args.
Proof.
  clear. intros until args.
  induction args; intros; inv H0.
  constructor; auto.
  inv H. constructor. eapply arg_related_G_arg_1; eauto. eapply IHargs; eauto.
Qed.

Lemma args_related_G_args_2:
  forall j bs bs' args args'
    (INJRANGE: forall b b', j b = Some b' -> Bset.belongsto bs' b'),
    G_args bs args -> args_related j args args' -> G_args bs' args'.
Proof.
  clear. intros until args.
  induction args; intros; inv H0.
  constructor; auto.
  inv H. constructor. eapply arg_related_G_arg_2; eauto. eapply IHargs; eauto.
Qed.

Inductive Loclocalize (j: Bset.inj) (ls ls_local: Locs.t) : Prop :=
  Loc_localize:
    (forall b b', j b = Some b' ->
             forall ofs, Locs.belongsto ls b' ofs <-> Locs.belongsto ls_local b ofs)
    -> Loclocalize j ls ls_local.

Record FPlocalize (j: Bset.inj) (fp fp_local: FP.t) : Prop :=
  {
    cmp_localize: Loclocalize j (FP.cmps fp) (FP.cmps fp_local);
    read_localize: Loclocalize j (FP.reads fp) (FP.reads fp_local);
    write_localize: Loclocalize j (FP.writes fp) (FP.writes fp_local);
    free_localize: Loclocalize j (FP.frees fp) (FP.frees fp_local);
  }.

(* FPlocalize emp *)
Lemma FPlocalize_emp:
  forall j, FPlocalize j FP.emp FP.emp.
Proof.
  clear. intro. constructor; constructor; intros; simpl in *; split; auto.
Qed.

(** FPlocalize union *)
Lemma Loclocalize_union:
  forall j l1 l1' l2 l2',
    Loclocalize j l1 l1' ->
    Loclocalize j l2 l2' ->
    Loclocalize j (Locs.union l1 l2) (Locs.union l1' l2').
Proof.
  clear. intros. inv H; inv H0. constructor. intros.
  specialize (H b b' H0 ofs). specialize (H1 b b' H0 ofs).
  Locs.unfolds. split; intros; red_boolean_true.
  rewrite H1 in H3. red_boolean_true.
  rewrite H in H3. red_boolean_true.
  rewrite <- H1 in H3. red_boolean_true.
  rewrite <- H in H3. red_boolean_true.
Qed.
Lemma FPlocalize_union:
  forall j fp1 fp2 fp1' fp2',
    FPlocalize j fp1 fp1' ->
    FPlocalize j fp2 fp2' ->
    FPlocalize j (FP.union fp1 fp2) (FP.union fp1' fp2').
Proof.
  clear. intros.
  inv H; inv H0. constructor; simpl; apply Loclocalize_union; auto.
Qed.


(* sge -> global; tge -> local; j: local -> global *)
Record ge_match_strict {F1 V1 F2 V2: Type} (j: Bset.inj)
       (sge: Genv.t (F1) (V1)) (tge: Genv.t (F2) (V2)) : Prop :=
  {
    ge_match_strict_next:
      Genv.genv_next sge = Genv.genv_next tge;
    ge_match_strict_dom:
      (forall b gd, (Genv.genv_defs tge) ! b = Some gd -> exists b', j b = Some b') /\
      (forall b' gd', (Genv.genv_defs sge) ! b' = Some gd' -> exists b, j b = Some b');
    ge_match_strict_inj_injective:
      forall b1 b2 b', j b1 = Some b' -> j b2 = Some b' -> b1 = b2;
    ge_match_strict_senv:
      forall id,
        inj_oblock j (Senv.find_symbol tge id) (Senv.find_symbol sge id);
    ge_match_strict_defs:
      forall b b',
        j b = Some b' -> option_rel globdef_match (Genv.genv_defs sge) ! b' (Genv.genv_defs tge) ! b;
    ge_match_strict_public:
      forall id, In id (Genv.genv_public sge) <-> In id (Genv.genv_public tge);
  }.

Lemma inject_incr_bset_inj_incr:
  forall j j',
    inject_incr (Bset.inj_to_meminj j) (Bset.inj_to_meminj j') ->
    (forall b b', j b = Some b' -> j' b = Some b').
Proof.
  unfold Bset.inj_to_meminj. intros. exploit H. rewrite H0. eauto.
  destruct (j' b). intros. inv H1. auto. discriminate.
Qed.
  
Lemma ge_match_strict_incr:
  forall j j' (INJECTIVE': forall b1 b2 b', j' b1 = Some b' -> j' b2 = Some b' -> b1 = b2),
    inject_incr (Bset.inj_to_meminj j) (Bset.inj_to_meminj j') ->
    forall F1 V1 F2 V2 (sge: Genv.t F1 V1) (tge: Genv.t F2 V2),
      ge_match_strict j sge tge ->
      ge_match_strict j' sge tge.
Proof.
  intros. destruct H0 as [H1 [H2 H2'] INJECTIVE H3 H4]. constructor; auto; simpl in *.
  split; intros b gd H'; [specialize (H2 b gd H')|specialize (H2' b gd H')].
  destruct H2. exists x. eapply inject_incr_bset_inj_incr; eauto.
  destruct H2'. exists x. eapply inject_incr_bset_inj_incr; eauto.
  intros. specialize (H3 id). inv H3; constructor. eapply inject_incr_bset_inj_incr; eauto.
  intros. specialize (H4 b b'). 
  destruct ((Genv.genv_defs sge) ! b') eqn:Hb'; destruct ((Genv.genv_defs tge) ! b) eqn:Hb; try constructor.
  apply H2' in Hb'. destruct Hb'. pose proof H5. eapply inject_incr_bset_inj_incr in H5; eauto.
  exploit (INJECTIVE' x b); eauto. intro; subst. clear H5. specialize (H4 H6). inv H4. auto.
  apply H2' in Hb'. destruct Hb'. pose proof H5. eapply inject_incr_bset_inj_incr in H5; eauto.
  exploit (INJECTIVE' x b); eauto. intro; subst. clear H5. specialize (H4 H6). inv H4.
  apply H2 in Hb. destruct Hb. pose proof H5. eapply inject_incr_bset_inj_incr in H5; eauto.
  rewrite H0 in H5; inv H5. apply H4 in H6. inv H6.
Qed.

(* 
   |-----------------|
     /\
     || j21
   |-----------------|
     /\
     || j22 (which should be flat_inj on shared blocks)
     \/
   |-----------------|
     || j23
     \/ 
   |-----------------|
 *)


(** Localize Mapping *)
Section LangLocalize.
  Context {L: Language}
          {sem: sem_local}
          (bj: Bset.inj)
          (ge: Genv.t (InteractionSemantics.F L) (InteractionSemantics.V L))
          (ge_local: Genv.t (F sem) (V sem))
          (Ge: InteractionSemantics.G L)
          (Ge_local: G sem)
          (match_state: Bset.inj -> freelist -> InteractionSemantics.core L -> gmem -> core sem -> mem -> Prop)
  .
  
  (* We require Shared to be blocks less than ge.next *)  
  Local Notation Bound := (Genv.genv_next ge).
  Local Notation Shared := (fun b:block => Plt b Bound).

  
  Record LocalizeSim
    : Prop :=
    {
      (* Localizing ge would result in a strictly matching ge_local,
         i.e. ge.next = ge_local.next, and every (ident, def) pair matches,
         and (ident, block) pairs matchs w.r.t. bj *)
      (* need bj well defined on (fun b => Plt b Bound) *)
      localize_ge: ge_match_strict bj ge ge_local /\
                   Bset.inject bj (fun b => Plt b (Genv.genv_next ge_local)) (fun b => Plt b (Genv.genv_next ge));


      localize_freelist_norep:
        forall fl c m lc lm,
          match_state bj fl c m lc lm ->
          norep fl;

      localize_freelist_no_overlap:
        forall fl c m lc lm,
          match_state bj fl c m lc lm ->
          no_overlap fl Shared;
      
      (* matching state implies memories are related w.r.t. Shared, bj, and fl *)
      localize_mem:
        forall fl c m lc lm,
          match_state bj fl c m lc lm ->
          mem_related bj (Genv.genv_next ge) fl m lm;
      
      localize_init:
        forall id args c,
          G_args Shared args ->
          init_core L Ge id args = Some c ->
          exists args_local lc,
            args_related bj args_local args /\
            init_core_local sem Ge_local id args_local = Some lc /\
            (forall m fl,
                init_gmem L ge m ->
                norep fl ->
                no_overlap fl (valid_block_bset m) ->
                MemClosures.reach_closed m Shared ->
                exists lm,
                  init_mem sem ge_local lm /\
                  mem_related bj (Genv.genv_next ge) fl m lm /\
                  match_state bj fl c m lc lm)
      ;
      
      localize_lockstep:
        forall fl c lc m lm fp c' m',
          match_state bj fl c m lc lm ->
          step L Ge fl c m fp c' m' ->
          fpG fl Shared fp ->
          exists lfp lc' lm',
            step_local sem Ge_local lc lm lfp lc' lm' /\
            FPlocalize (construct_inj bj (Genv.genv_next ge) fl) fp lfp /\
            match_state bj fl c' m' lc' lm'
      ;

      localize_at_external:
        forall fl c lc m lm f sg args,
          match_state bj fl c m lc lm ->
          at_external L Ge c = Some (f, sg, args) ->
          G_args Shared args ->
          exists args_local,
            at_external_local sem Ge_local lc = Some (f, sg, args_local) /\
            args_related bj args_local args
      ;

      localize_after_external:
        forall fl c lc m lm ores c' lores,
          match_state bj fl c m lc lm ->
          (* G_oarg Shared ores -> *)
          oarg_related bj lores ores ->
          after_external L c ores = Some c' ->
          exists lc',
            after_external_local sem lc lores = Some lc' /\
            match_state bj fl c' m lc' lm
      ;

      localize_rely:
        forall fl c lc m lm,
          match_state bj fl c m lc lm ->
          (forall m' lm',
              unchg_freelist fl m m' ->
              mem_related bj (Genv.genv_next ge) fl m' lm' ->
              match_state bj fl c m' lc lm')
      ;
      
      localize_halt:
        forall fl c lc m lm res,
          match_state bj fl c m lc lm ->
          halt L c = Some res ->
          G_arg Shared res ->
          exists lres,
            halt_local sem lc = Some lres /\
            arg_related bj lres res 
      ;
              
            
    }.

End LangLocalize.


Inductive LangLocalize (comp_unit: Type) (wdcu: comp_unit -> Prop): Language -> sem_local -> Prop :=
  LangLocalize_intro:
    forall F V G core f1 f2 f3 f4 f5 f6 f7 f8 f1' f2' f3' f4' f5' f6' f7', 
      (forall (cu: comp_unit) (Hwdcu: wdcu cu) (ge: Genv.t F V) (Ge: G),
          init_genv (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8) cu ge Ge ->
          exists bj_ident ge_local Ge_local match_state,
            init_genv_local (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7')
                            cu ge_local Ge_local /\
            ge_match_strict bj_ident ge ge_local /\
            (forall b b', bj_ident b = Some b' -> exists gd, Genv.find_def ge_local b = Some gd) /\
            (forall bj,
                inject_incr (Bset.inj_to_meminj bj_ident) (Bset.inj_to_meminj bj) ->
                Bset.inject bj (fun b => Plt b (Genv.genv_next ge_local)) (fun b => Plt b (Genv.genv_next ge)) ->
                @LocalizeSim
                  (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8)
                  (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7')
                  bj ge ge_local Ge Ge_local match_state))
      ->
      LangLocalize comp_unit wdcu (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8)
                   (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7').

Lemma localize_localizesim:
  forall F V G comp_unit wdcu core f1 f2 f3 f4 f5 f6 f7 f8 f1' f2' f3' f4' f5' f6' f7', 
      let L := (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8) in
      let L' := (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7') in
      LangLocalize comp_unit wdcu L L' ->
      (forall cu (Hwdcu: wdcu cu) ge Ge,
          f7 cu ge Ge ->
          exists bj_ident ge_local Ge_local match_state,
            f1' cu ge_local Ge_local /\
            ge_match_strict bj_ident ge ge_local /\
            (forall b b', bj_ident b = Some b' -> exists gd, Genv.find_def ge_local b = Some gd) /\
            (forall bj,
                inject_incr (Bset.inj_to_meminj bj_ident) (Bset.inj_to_meminj bj) ->
                Bset.inject bj (fun b => Plt b (Genv.genv_next ge_local)) (fun b => Plt b (Genv.genv_next ge)) ->
                @LocalizeSim L L' bj ge ge_local Ge Ge_local match_state)).
Proof.
  intros; simpl in *. inversion H. subst.
  repeat match goal with
         | H: existT ?x ?y ?a = existT ?x ?y ?b |- _ =>
           apply Eqdep.EqdepTheory.inj_pair2 in H
         | H: ?x = ?x |- _ => clear H
         end.
  subst. auto.
Qed.




(** Lift Mapping *)
Section LangLift.
  Context {L: Language}
          {sem: sem_local}
          (bj: Bset.inj)
          (ge_local: Genv.t (F sem) (V sem))
          (ge: Genv.t (InteractionSemantics.F L) (InteractionSemantics.V L))
          (Ge_local: G sem)
          (Ge: InteractionSemantics.G L)
          (match_state: Bset.inj -> freelist -> InteractionSemantics.core L -> gmem -> core sem -> mem -> Prop)
  .

  Local Notation Shared := (fun b:block => Plt b (Genv.genv_next ge)).
  
  Record LiftSim
    : Prop :=
    {
      lift_ge: ge_match_strict bj ge ge_local /\
               Bset.inject bj (fun b => Plt b (Genv.genv_next ge_local)) (fun b => Plt b (Genv.genv_next ge));

      lift_freelist_norep:
        forall fl c m lc lm,
          match_state bj fl c m lc lm ->
          norep fl;
      
      lift_freelist_no_overlap:
        forall fl c m lc lm,
          match_state bj fl c m lc lm ->
          no_overlap fl Shared;
      
      lift_mem:
        forall fl c m lc lm,
          match_state bj fl c m lc lm ->
          mem_related bj (Genv.genv_next ge) fl m lm;

      lift_init:
        forall args,
          G_args Shared args ->
          exists args_local,
            args_related bj args_local args /\
            (forall id lc,
                init_core_local sem Ge_local id args_local = Some lc ->
                exists c, init_core L Ge id args = Some c /\
                     (forall m fl,
                         init_gmem L ge m ->
                         norep fl ->
                         no_overlap fl (valid_block_bset m) ->
                         MemClosures.reach_closed m Shared ->
                         exists lm,
                           init_mem sem ge_local lm /\
                           mem_related bj (Genv.genv_next ge) fl m lm /\
                           match_state bj fl c m lc lm
                     )
            )
      ;
      
      lift_lockstep:
        forall fl c lc m lm lfp lc' lm',
          match_state bj fl c m lc lm ->
          step_local sem Ge_local lc lm lfp lc' lm' ->
          exists fp c' m',
            step L Ge fl c m fp c' m' /\
            FPlocalize (construct_inj bj (Genv.genv_next ge) fl) fp lfp /\
            fpG fl Shared fp /\
            match_state bj fl c' m' lc' lm'
      ;

      lift_at_external:
        forall fl c lc m lm f sg args_local,
          match_state bj fl c m lc lm ->
          at_external_local sem Ge_local lc = Some (f, sg, args_local) ->
          G_args Shared args_local -> 
          exists args,
            at_external L Ge c = Some (f, sg, args) /\
            args_related bj args_local args
      ;

      lift_after_external:
        forall fl c lc m lm ores lc' lores,
          match_state bj fl c m lc lm ->
          (* G_oarg Shared ores -> *)
          oarg_related bj lores ores ->
          after_external_local sem lc lores = Some lc' ->          
          exists c',
            after_external L c ores = Some c' /\
            match_state bj fl c' m lc' lm
      ;

      lift_rely:
        forall fl c lc m lm,
          match_state bj fl c m lc lm ->
          (forall m' lm',
              unchg_freelist fl m m' ->
              mem_related bj (Genv.genv_next ge) fl m' lm' ->
              match_state bj fl c m' lc lm')
      ;
      
      lift_halt:
        forall fl c lc m lm lres,
          match_state bj fl c m lc lm ->
          halt_local sem lc = Some lres ->
          G_arg Shared lres ->
          exists res,
            halt L c = Some res /\
            arg_related bj lres res 
      ;
              
    }.

End LangLift.

Inductive LangLift (comp_unit: Type) (wdcu: comp_unit -> Prop): Language -> sem_local -> Prop :=
  LangLift_intro :
    forall F V G core f1 f2 f3 f4 f5 f6 f7 f8 f1' f2' f3' f4' f5' f6' f7',
      (forall cu (Hwdcu: wdcu cu) ge Ge,
          init_genv (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8) cu ge Ge ->
          exists bj_ident ge_local Ge_local match_state,
            init_genv_local (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7')
                            cu ge_local Ge_local /\
            ge_match_strict bj_ident ge ge_local /\
            (forall b b', bj_ident b = Some b' -> exists gd, Genv.find_def ge_local b = Some gd) /\
            (forall bj,
                inject_incr (Bset.inj_to_meminj bj_ident) (Bset.inj_to_meminj bj) ->
                Bset.inject bj (fun b => Plt b (Genv.genv_next ge_local)) (fun b => Plt b (Genv.genv_next ge)) ->
                @LiftSim (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8)
                         (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7')
                         bj ge_local ge Ge_local Ge match_state))
      ->
      LangLift comp_unit wdcu (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8)
               (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7').

Lemma lift_liftsim:
  forall F V G comp_unit wdcu core f1 f2 f3 f4 f5 f6 f7 f8 f1' f2' f3' f4' f5' f6' f7',
    LangLift comp_unit wdcu (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8)
             (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7') ->
    (forall cu (Hwdcu: wdcu cu) ge Ge,
        init_genv (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8) cu ge Ge ->
        exists bj_ident ge_local Ge_local match_state,
          init_genv_local (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7')
                          cu ge_local Ge_local /\
          ge_match_strict bj_ident ge ge_local/\
          (forall b b', bj_ident b = Some b' -> exists gd, Genv.find_def ge_local b = Some gd) /\
          (forall bj,
              inject_incr (Bset.inj_to_meminj bj_ident) (Bset.inj_to_meminj bj) ->
              Bset.inject bj (fun b => Plt b (Genv.genv_next ge_local)) (fun b => Plt b (Genv.genv_next ge)) ->
              @LiftSim (Build_Language F V G comp_unit core f1 f2 f3 f4 f5 f6 f7 f8)
                       (Build_sem_local F V G comp_unit core f1' f2' f3' f4' f5' f6' f7')
                       bj ge_local ge Ge_local Ge match_state)).
Proof.
  intros; simpl in *. inversion H. subst.
  repeat match goal with
         | H: existT ?x ?y ?a = existT ?x ?y ?b |- _ =>
           apply Eqdep.EqdepTheory.inj_pair2 in H
         | H: ?x = ?x |- _ => clear H
         end.
  subst. auto.
Qed.
  
(*
Definition LangLift (L: Language) (sem: @sem_local L) : Prop :=
  forall cu ge Ge,
    init_genv L cu ge Ge ->
    exists bj ge_local Ge_local match_state,
      init_genv_local sem cu ge_local Ge_local /\
      @LiftSim L sem bj ge_local ge Ge_local Ge match_state.
 *)

Lemma lift_lockstep_plus:
  forall L sem bj ge_local ge Ge_local Ge match_state,
    @LiftSim L sem bj ge_local ge Ge_local Ge match_state ->
    forall fl c lc m lm lfp lc' lm',
      match_state bj fl c m lc lm ->
      plus (step_local sem Ge_local) lc lm lfp lc' lm' ->
      exists fp c' m',
        InteractionSemantics.plus (step L Ge fl) c m fp c' m' /\
        FPlocalize (construct_inj bj (Genv.genv_next ge) fl) fp lfp /\
        fpG fl (fun b => Plt b (Genv.genv_next ge)) fp /\
        match_state bj fl c' m' lc' lm'.
Proof.
  intros until match_state. intros LIFT.
  intros until lm'. intros MATCH PLUS.
  pose proof (lift_lockstep _ _ _ _ _ _ LIFT) as LIFT'.
  generalize dependent MATCH.
  generalize dependent m. generalize dependent c.
  induction PLUS; intros.
  
  eapply LIFT' in H; eauto.
  destruct H as (fp0 & c'0 & m'0 & STEP' & FPINJ & FPG & MATCH').
  exists fp0, c'0, m'0.
  split; auto. econstructor; eauto.

  eapply LIFT' in H; eauto.
  destruct H as (fp0 & c'0 & m'0 & STEP' & FPINJ & FPG & MATCH').
  eapply IHPLUS in MATCH'; eauto.
  destruct MATCH' as (fp0' & c''0 & m''0 & STEP'' & FPINJ' & FPG' & MATCH'').
  exists (FP.union fp0 fp0'), c''0, m''0.
  split.
  eapply InteractionSemantics.plus_cons; eauto.
  split. eapply FPlocalize_union; eauto.
  split; auto. eapply fpG_union; eauto.
Qed.


    
Inductive Inj_lift: Bset.inj -> Bset.inj -> Injections.Mu -> Injections.Mu -> Prop :=
| InjLift: forall j21 j23 mu lmu
             (BSETEQ21: Injections.SharedSrc lmu = Injections.SharedSrc mu)
             (INJ21: Bset.inject j21 (Injections.SharedSrc lmu) (Injections.SharedSrc mu))
             (BSETEQ23: Injections.SharedTgt lmu = Injections.SharedTgt mu)
             (INJ23: Bset.inject j23 (Injections.SharedTgt lmu) (Injections.SharedTgt mu))
             (Consist1:
                forall b1 b3, Injections.inj mu b1 = Some b3 ->
                         exists b2 b2',
                           j21 b2 = Some b1 
                           /\ Injections.inj lmu b2 = Some b2'
                           /\ j23 b2' = Some b3)
             (Consist2:
                forall b2 b2', Injections.inj lmu b2 = Some b2' ->
                          exists b1 b3,
                            j21 b2 = Some b1
                            /\ j23 b2' = Some b3
                            /\ Injections.inj mu b1 = Some b3),
    Inj_lift j21 j23 mu lmu.
                      

Lemma Inj_lift_inject:
  forall j21 j23 mu lmu,
    Inj_lift j21 j23 mu lmu ->
    Bset.inject (Injections.inj lmu) (Injections.SharedSrc lmu) (Injections.SharedTgt lmu) ->
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu).
Proof.
  intros. inv H.
  constructor.
  * constructor.
    ** intros. exploit Consist1; eauto. intros (b2 & b2' & J21 & J22 & J23).
       inv INJ21. inv inj_weak. eapply inj_range'; eauto.
    ** intros. inv INJ23. inv H0. inv INJ21.
       exploit (Bset.inj_range _ _ _ inj_weak); eauto. intros (b2' & J23).
       exploit (Bset.inj_dom' _ _ _ inj_weak); eauto. intro.
       exploit (Bset.inj_range _ _ _ inj_weak0); eauto. intros (b2 & J22).
       exploit (Bset.inj_dom' _ _ _ inj_weak0); eauto. intro.
       exploit inj_dom1; eauto. intros (b & J21).
       exists b. exploit Consist2; eauto. intros (b1 & b3 & J21' & J23' & ?).
       rewrite J23 in J23'. rewrite J21 in J21'. inv J21'. inv J23'. auto.
    ** intros. exploit Consist1; eauto. intros (b2 & b2' & J21 & J22 & J23).
       inv INJ23. exploit (Bset.inj_range' _ _ _ inj_weak); eauto.
    ** intros. destruct (Consist1 _ _ H) as (b1' & b1'' & J21 & J22 & J23).
       destruct (Consist1 _ _ H1) as (b2' & b2'' & J21' & J22' & J23').
       assert (b1'' = b2'').
       { inv INJ23. eapply Bset.inj_injective in inj_weak; eauto. }
       assert (b1' = b2').
       { inv H0. eapply Bset.inj_injective in inj_weak; eauto. }
       subst. rewrite J21 in J21'. inv J21'. auto.
  * intros. inv INJ21. inv H0. inv INJ23.
    exploit (Bset.inj_range _ _ _ inj_weak); eauto. intros (b2 & J21).
    exploit (Bset.inj_dom' _ _ _ inj_weak); eauto. intro.
    eapply inj_dom0 in H0. destruct H0 as [b2' J22].
    exploit Consist2; eauto. intros (b1 & b3 & J21' & J23' & ?).
    exists b3. rewrite J21 in J21'. inv J21'. auto.
Qed.

Lemma Inj_lift_inject':
  forall j21 j23 mu lmu,
    Inj_lift j21 j23 mu lmu ->
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    Bset.inject (Injections.inj lmu) (Injections.SharedSrc lmu) (Injections.SharedTgt lmu).
Proof.
  intros. inv H.
  constructor.
  * constructor.
    ** intros. exploit Consist2; eauto. intros (b1 & b3 & J21 & J23 & J13).
       inv INJ21. inv inj_weak. eapply inj_dom'; eauto.
    ** intros.
       eapply Bset.inj_dom in H; eauto. destruct H as (b3 & J23). pose proof J23 as J23'.
       eapply Bset.inj_range' in J23; [|inv INJ23; eauto].
       eapply Bset.inj_range in J23; [|inv H0; eauto]. destruct J23 as [b1 J13].
       eapply Consist1 in J13. destruct J13 as (b2 & b2' & J21 & J22 & J23'').
       exploit Bset.inj_injective. inv INJ23; eauto. eexact J23'. eexact J23''. intro; subst.
       eauto.
    ** intros. exploit Consist2; eauto. intros (b1 & b3 & J21 & J23 & J13).
       inv INJ23. exploit (Bset.inj_dom' _ _ _ inj_weak); eauto.
    ** intros b2 b2' b H H1.
       destruct (Consist2 _ _ H) as (b1 & b3 & J21 & J23 & J13).
       destruct (Consist2 _ _ H1) as (b1' & b3' & J21' & J23' & J13').
       rewrite J23 in J23'. inv J23'.
       exploit Bset.inj_injective. inv H0; eauto. eexact J13. eexact J13'. intro; subst.
       exploit Bset.inj_injective. inv INJ21; eauto. eexact J21. eexact J21'. auto.
  * intros. eapply (Bset.inj_dom j21) in H; eauto. destruct H as [b1 J21].
    exploit (Bset.inj_range'); eauto. inv INJ21; eauto. intro Hb1.
    eapply Bset.inj_dom in Hb1; eauto. destruct Hb1 as [b3 J13].
    eapply Consist1 in J13. destruct J13 as (b2 & b2' & J21' & J22 & J23).
    exploit Bset.inj_injective. inv INJ21; eauto. eexact J21. eexact J21'. intro; subst.
    eauto.
Qed.

Lemma Inj_lift_SharedSrc:
  forall j21 j23 mu lmu,
    Inj_lift j21 j23 mu lmu ->
    forall b, Injections.SharedSrc mu b <-> Injections.SharedSrc lmu b.
Proof.
  intros. inv H. rewrite BSETEQ21. tauto.
Qed.

Lemma Inj_lift_SharedTgt:
  forall j21 j23 mu lmu,
    Inj_lift j21 j23 mu lmu ->
    forall b, Injections.SharedTgt mu b <-> Injections.SharedTgt lmu b.
Proof.
  intros. inv H. rewrite BSETEQ23. tauto.
Qed.

Lemma Inj_lift_j21_dom:
  forall j21 j23 mu lmu,
    Inj_lift j21 j23 mu lmu ->
    (forall b b', j21 b = Some b' -> Injections.SharedSrc lmu b).
Proof.
  intros. inv H. inv INJ21. inv inj_weak. eapply inj_dom'; eauto.
Qed.

Lemma memval_inject_strict_memval_inject:
  forall j21 j23 mu lmu v1 v1' v2' v2,
    Inj_lift j21 j23 mu lmu ->
    memval_inject_strict (Bset.inj_to_meminj j21) v1' v1 ->
    memval_inject (Bset.inj_to_meminj (Injections.inj lmu)) v1' v2' ->
    memval_inject_strict (Bset.inj_to_meminj j23) v2' v2 ->
    memval_inject (Bset.inj_to_meminj (Injections.inj mu)) v1 v2.
Proof.
  intros.
  destruct v1; inv H0; inv H1; inv H2; try constructor.
  destruct v; inv H5; inv H7; inv H6; try constructor.
  unfold Bset.inj_to_meminj in *.
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?; inv H end.
  inv H. apply Consist2 in Heqo0. destruct Heqo0 as (b3' & b4' & J21 & J23 & INJ).
  rewrite J21 in Heqo1. inv Heqo1. rewrite J23 in Heqo. inv Heqo.
  econstructor. rewrite INJ. eauto. auto.
Qed.

Lemma memval_inject_strict_memval_inject':
  forall j21 j23 mu lmu v1 v1' v2' v2,
    Inj_lift j21 j23 mu lmu ->
    memval_inject_strict (Bset.inj_to_meminj j21) v1' v1 ->
    memval_inject (Bset.inj_to_meminj (Injections.inj mu)) v1 v2 ->
    memval_inject_strict (Bset.inj_to_meminj j23) v2' v2 ->
    memval_inject (Bset.inj_to_meminj (Injections.inj lmu)) v1' v2'.
Proof.
  intros.
  destruct v1; inv H0; inv H1; inv H2; try constructor.
  destruct v; inv H5; inv H7; inv H3; try constructor.
  unfold Bset.inj_to_meminj in *.
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?; inv H end.
  inv H. apply Consist1 in Heqo0. destruct Heqo0 as (b3' & b4' & J21 & INJ & J23 ).
  assert (b1 = b3').
  { inv INJ21. inv inj_weak. eapply inj_injective; eauto. }
  assert (b0= b4').
  { inv INJ23. inv inj_weak. eapply inj_injective; eauto. }
  subst. econstructor. rewrite INJ. eauto. generalize H7; clear. intro.
  
  repeat rewrite ptrofs_add_0 in *. auto.
Qed.



Lemma Loclocalize_LocMatch:
  forall j21 j23 j21incr j23incr mu lmu ls lls lls' ls',
    Inj_lift j21 j23 mu lmu ->
    Bset.inject (Injections.inj lmu) (Injections.SharedSrc lmu) (Injections.SharedTgt lmu) ->
    inject_incr (Bset.inj_to_meminj j21) (Bset.inj_to_meminj j21incr) ->
    inject_incr (Bset.inj_to_meminj j23) (Bset.inj_to_meminj j23incr) ->
    Loclocalize j21incr ls lls ->
    Injections.LocMatch lmu lls lls' ->
    Loclocalize j23incr ls' lls' ->
    Injections.LocMatch mu ls ls'.
Proof.
  intros j21 j23 j21incr j23incr mu lmu ls lls lls' ls'
         INJLIFT INJLMU INCR21 INCR23 LOCALIZE21 LOCMATCH LOCALIZE23.
  constructor. intros b' ofs ? ?.
  assert (exists lb', j23 lb' = Some b' /\ Locs.belongsto lls' lb' ofs /\
                 Bset.belongsto (Injections.SharedTgt lmu) lb').
  { inv INJLIFT. inv INJ23. exploit Bset.inj_range; eauto. intros (lb' & J23).
    exploit inject_incr_bset_inj_incr; try exact J23; eauto. intro J23'.
    exists lb'. split. auto. inv LOCALIZE23. split. eapply H1; eauto.
    exploit Bset.inj_dom'; eauto. }
  destruct H1 as (lb' & J23 & LLoc' & LShared'). clear H H0.
  assert (exists lb, (Injections.inj lmu) lb = Some lb' /\ Locs.belongsto lls lb ofs /\
                Bset.belongsto (Injections.SharedSrc lmu) lb).
  { inv LOCMATCH. exploit H; eauto. intros (lb & LShared & LLoc).
    exploit inject_incr_bset_inj_incr; try exact J21; eauto. intro J21'.
    exists lb. split. auto. split. auto. inv INJLMU. exploit Bset.inj_dom'; eauto. }
  destruct H as (lb & J22 & LLoc & LShared). clear LShared' LLoc'.
  assert (exists b, j21 lb = Some b /\ Locs.belongsto ls b ofs /\
               Bset.belongsto (Injections.SharedSrc mu) b).
  { inv INJLIFT. clear INJ23. exploit Bset.inj_dom; eauto. intros (b & J21).
    exploit inject_incr_bset_inj_incr; try exact J21; eauto. intro J21'.
    exists b. split. auto. inv LOCALIZE21. split. eapply H; eauto.
    inv INJ21. exploit Bset.inj_range'; eauto. }
  destruct H as (b & J21 & Loc & Shared).
  exists b. split; auto. inv INJLIFT. exploit Consist2; eauto.
  intros (b1 & b3 & J21' & J23' & ?).
  rewrite J21 in J21'. rewrite J23 in J23'. inv J21'. inv J23'. auto.
Qed.

Lemma FPlocalize_FPMatch:
  forall j21 j23 j21incr j23incr mu lmu,
    Inj_lift j21 j23 mu lmu ->
    Bset.inject (Injections.inj lmu) (Injections.SharedSrc lmu) (Injections.SharedTgt lmu) ->
    inject_incr (Bset.inj_to_meminj j21) (Bset.inj_to_meminj j21incr) ->
    inject_incr (Bset.inj_to_meminj j23) (Bset.inj_to_meminj j23incr) ->
    forall fp lfp lfp' fp',
      FPlocalize j21incr fp lfp ->
      FPlocalize j23incr fp' lfp' ->
      Injections.FPMatch' lmu lfp lfp' ->
      Injections.FPMatch' mu fp fp'.
Proof.
  intros j21 j23 j21incr j23incr mu lmu INJLIFT INJLMU INCR21 INCR23
         fp lfp lfp' fp' LOCALIZE21 LOCALIZE23 MATCH.
  inv LOCALIZE23. 
  constructor; eapply Loclocalize_LocMatch; try eassumption;
    inv MATCH; try eassumption;
      inv LOCALIZE21; FP.unfolds_thrshd; repeat apply Loclocalize_union; auto.
Qed.


Lemma ge_localize:
  forall sl tl ssem tsem sG tG sge tge
    j21 j23 mu mu_local sG_local tG_local sge_local tge_local
    R12 R32,
    Inj_lift j21 j23 mu mu_local ->
    (** DONE: modify the interface of LDSim.ge_init_inj 
              LDSim.ge_init_inj mu sge tge 
              to include relation between Shared and ge.genv_next
     *)
    ge_init_inj mu sge tge ->
    @LocalizeSim sl ssem j21 sge sge_local sG sG_local R12 ->
    @LiftSim tl tsem j23 tge_local tge tG_local tG R32 ->
    ge_init_inj mu_local sge_local tge_local.
Proof.
  clear. intros.
  constructor.
  { eapply localize_ge in H1. destruct H1 as [H1 _]. eapply lift_ge in H2.
    inv H. inv H1. rewrite BSETEQ21, <- ge_match_strict_next0. inv H0. auto. }
  { eapply localize_ge in H1. destruct H1 as [H1 _]. eapply lift_ge in H2. destruct H2 as [H2 _].
    inv H. inv H2. rewrite BSETEQ23, <- ge_match_strict_next0. inv H0; auto. }
  { eapply Inj_lift_inject'; eauto. inv H0. auto. }
  { intros. eapply localize_ge in H1. eapply lift_ge in H2.
    destruct H1 as [H1 H1']. destruct H2 as [H2 H2'].
    eapply ge_match_strict_senv in H1. instantiate (1:= id) in H1.
    eapply ge_match_strict_senv in H2. instantiate (1:= id) in H2.
    eapply senv_injected in H0. instantiate (1:= id) in H0.
    generalize H H0 H1 H2; clear. intros.
    unfold Senv.find_symbol. simpl.
    inv H0; inv H1; inv H2; try constructor; try congruence.
    inv H. apply Consist1 in H6.
    rewrite <- H3 in H7. inv H7. rewrite <- H5 in H9. inv H9.
    destruct H6 as (b2 & b2' & INJ21' & INJ22 & INJ23').
    exploit Bset.inj_injective. inv INJ21; eauto. exact H8. exact INJ21'. intro; subst.
    exploit Bset.inj_injective. inv INJ23; eauto. exact H10. exact INJ23'. intro; subst.
    auto. }
Qed.

Lemma local_ldsim_SharedSrc:
  forall ssem tsem I I_order sG tG sge tge R ,
    @local_ldsim_properties ssem tsem I I_order sG tG sge tge R ->
    forall Beta i mu fpS fpT sconfig tconfig,
      R Beta i mu fpS fpT sconfig tconfig ->
      (forall b, Injections.SharedSrc mu b <-> Plt b (Genv.genv_next sge)).
Proof.
  intros.
  inv H. apply match_mu_ge in H0. inv H0. rewrite mu_shared_src. tauto.
Qed.

Lemma local_ldsim_SharedTgt:
  forall ssem tsem I I_order sG tG sge tge R ,
    @local_ldsim_properties ssem tsem I I_order sG tG sge tge R ->
    forall Beta i mu fpS fpT sconfig tconfig,
      R Beta i mu fpS fpT sconfig tconfig ->
      (forall b, Injections.SharedTgt mu b <-> Plt b (Genv.genv_next tge)).
Proof.
  intros. inv H. apply match_mu_ge in H0. inv H0. rewrite mu_shared_tgt. tauto.
Qed.

Lemma arg_rel_strict_lift:
  forall mu lmu j21 j23 argS argT argS' argT',
    Inj_lift j21 j23 mu lmu ->
    arg_rel (Injections.inj mu) argS argT ->
    args_related j21 argS' argS ->
    args_related j23 argT' argT ->
    arg_rel (Injections.inj lmu) argS' argT'.
Proof.
  intros mu lmu j21 j23 argS argT argS' argT' LIFT REL13.
  generalize dependent argS'.
  generalize dependent argT'.
  induction REL13; intros argT' argS' REL21 REL23.
  inv REL21; inv REL23. constructor.
  inv REL21. inv REL23.
  constructor.
  (* by val_inject_strict... *)
  inv H3; inv H5; inv H; try constructor.
  unfold Bset.inj_to_meminj in *.
  destruct (j21 b1) eqn:J21; try discriminate; inv H0.
  destruct (j23 b0) eqn:J23; try discriminate; inv H1.
  destruct (Injections.inj mu b2) eqn:J13; try discriminate; inv H7.
  repeat rewrite Integers.Ptrofs.add_zero in H9. subst.
  inv LIFT. apply Consist1 in J13. destruct J13 as (b1' & b0' & J21' & J22 & J23').
  exploit Bset.inj_injective. inv INJ21; eauto. exact J21. exact J21'. intro; subst.
  exploit Bset.inj_injective. inv INJ23; eauto. exact J23. exact J23'. intro; subst.
  econstructor. rewrite J22; eauto. rewrite Integers.Ptrofs.add_zero; auto.
  apply IHREL13; auto.
Qed.
  

Lemma ores_rel_strict_lift:
  forall mu lmu j21 j23 ores ores',
    Inj_lift j21 j23 mu lmu ->
    G_oarg (Injections.SharedSrc mu) ores ->
    ores_rel (Injections.inj mu) ores ores' ->
    exists ores_local ores_local',
      oarg_related j21 ores_local ores /\
      ores_rel (Injections.inj lmu) ores_local ores_local' /\
      oarg_related j23 ores_local' ores'.
Proof.
  intros mu lmu j21 j23 ores ores' INJLIFT GRES ORESREL.
  destruct ores eqn:Hores; destruct ores' eqn:Hores'; inversion ORESREL;
    match goal with
    | H1: ores = ?x, H2: ores' = ?y |- _ =>
      try (exists x, y; subst; repeat split; try constructor; fail)
    end.
  
  destruct (Injections.inj mu b1) eqn:H';
    unfold Bset.inj_to_meminj in H; rewrite H' in H; inv H; auto.
  inv INJLIFT. exploit (Consist1 b1 b2). auto.
  intros (b1' & b2' & J21 & J22 & J23).
  exists (Some (Vptr b1' ofs1)), (Some (Vptr b2' ofs1)).
  split.
  econstructor. cbv. rewrite J21. eauto.
  rewrite <- Integers.Ptrofs.unsigned_zero,
  Integers.Ptrofs.repr_unsigned, Integers.Ptrofs.add_zero. auto.
  split.
  econstructor. unfold Bset.inj_to_meminj. rewrite J22. eauto.
  rewrite <- Integers.Ptrofs.unsigned_zero,
  Integers.Ptrofs.repr_unsigned, Integers.Ptrofs.add_zero. auto.
  econstructor. unfold Bset.inj_to_meminj. rewrite J23. eauto. auto.
  subst.  contradiction.
Qed.



(** Memory interpolant for HLRELY *)
Program Definition inject_memory (j j': Bset.inj) (bound: block)
        (gm: gmem) (m: mem)
        (REV: forall b b', j b = Some b' <-> j' b' = Some b)
        (SHARED_VALID: forall b b', j b = Some b' -> Plt b (Mem.nextblock m))
  : mem :=
  Mem.mkmem (proj1_sig (inject_content_c j j' bound (Mem.mem_contents m) (GMem.mem_contents gm)))
            (proj1_sig (inject_access_c j j' bound (Mem.mem_access m) (GMem.mem_access gm)))
            (Mem.nextblock m) _ _ _.
Next Obligation.
  pose proof (proj2_sig (inject_access_c j j' bound (Mem.mem_access m) (GMem.mem_access gm))).
  simpl in H. destruct H. rewrite H0. clear H H0.
  unfold inject_access. 
  destruct (j b) eqn:Jb. destruct plt.
  apply perm_order''_equiv_1. simpl. apply GMem.access_max.
  apply Mem.access_max. destruct plt; apply Mem.access_max. 
Qed.
Next Obligation.
  pose proof (proj2_sig (inject_access_c j j' bound (Mem.mem_access m) (GMem.mem_access gm))).      
  destruct H0. rewrite H1. clear H0 H1. unfold inject_access.
  destruct (j b) eqn:Jb. exploit SHARED_VALID; eauto. intro. contradiction.
  destruct plt; exploit (Mem.nextblock_noaccess); eauto.
Qed.
Next Obligation.
  pose proof (proj2_sig (inject_content_c j j' bound (Mem.mem_contents m) (GMem.mem_contents gm))).
  destruct H. rewrite H0. unfold inject_content. 
  destruct (j b); destruct plt; try apply Mem.contents_default.
  destruct (proj2_sig (inject_zmap_memval_c j' (GMem.mem_contents gm) !! b0)).
  rewrite H1. unfold inject_memval. rewrite GMem.contents_default. auto.
Qed.

Lemma mem_inj_localize:
  forall j21 j23 bound fl fl' mu lmu m lm lm' m',
    Inj_lift j21 j23 mu lmu ->
    mem_related j21 bound fl m lm ->
    mem_related j23 bound fl' m' lm' ->
    GMem.mem_inj (Bset.inj_to_meminj (Injections.inj mu)) m m' ->
    Mem.mem_inj (Bset.inj_to_meminj (Injections.inj lmu)) lm lm'.
Proof.
  intros j21 j23 bound fl fl' mu lmu m lm lm' m' H H0 H1 H2.
  
  constructor; intros; exploit inj_to_meminj_some; eauto; intros [INJ Hdelta]; subst.
  destruct H. apply Consist2 in INJ. destruct INJ as (b1' & b2' & J21 & J23 & INJ').
  exploit mem_related_inj_construct_inj; eauto. intro.
  exploit (mem_related_inj_construct_inj j21); eauto. intro.
  rewrite <- mem_related_mem_perm_eq; eauto;
    try apply perm_kind_convert_eq; try apply permission_convert_eq.
  rewrite <- mem_related_mem_perm_eq in H4; eauto;
    try apply perm_kind_convert_eq; try apply permission_convert_eq.
  inv H2. eapply mi_perm; eauto. unfold Bset.inj_to_meminj. rewrite INJ'. auto.

  apply Z.divide_0_r.

  destruct H. apply Consist2 in INJ. destruct INJ as (b1' & b2' & J21 & J23 & INJ').
  exploit (mem_related_inj_construct_inj j21); eauto. intro.
  pose proof H4. rewrite <- (mem_related_mem_perm_eq j21) in H4; eauto; try constructor.
  exploit GMem.mi_memval; eauto. unfold Bset.inj_to_meminj. rewrite INJ'. eauto. intro.
  

  (* rule out the case when source content is Undef, or Fragment Vundef..
         in which case we cannot relate source and target contents.
   *)
  assert (ZMap.get ofs (GMem.mem_contents m) !! b1' = Undef \/
          ZMap.get ofs (GMem.mem_contents m) !! b1' <> Undef) as [Triv|Nontriv].
  { clear. destruct (ZMap.get ofs (GMem.mem_contents m) !! b1'); auto; right; intro C; inv C. }
  rewrite Triv in *. exploit (mem_related_mem_val_shared j21); eauto. intro.
  rewrite Triv in *. inv H7. constructor.

  assert ((exists q n, ZMap.get ofs (GMem.mem_contents m) !! b1' = Fragment Vundef q n) \/
          (forall q n, ZMap.get ofs (GMem.mem_contents m) !! b1' <> Fragment Vundef q n))
    as [(q&n&Triv)|Nontriv'].
  { clear.
    destruct (ZMap.get ofs (GMem.mem_contents m) !! b1');
      try (right; intros ? ? C; inv C; fail).
    destruct v; try (right; intros ? ? C; inv C; fail).
    left. eauto. }
  exploit (mem_related_mem_val_shared j21); eauto. intro.
  rewrite Triv in *; clear Triv Nontriv. inv H7. inv H10. clear H8.
  inv H6. clear H8.
  exploit (mem_related_mem_val_shared j23); eauto.
  exploit GMem.mi_perm; eauto. unfold Bset.inj_to_meminj; rewrite INJ'. eauto.
  intro. rewrite (mem_related_mem_perm_eq j23) in H6; eauto.
  eapply mem_related_inj_construct_inj; eauto. constructor. constructor.
  rewrite <- H11. intro. inv H6. constructor. constructor.

  (* contents are related by mu *)
  eapply memval_inject_strict_memval_inject'; eauto.
  econstructor; eauto.
  
  exploit (mem_related_mem_val_shared j21); eauto.
  pose proof (mem_related_freelist_disjoint _ _ _ _ _ H0) as FLDISJ.
  exploit (Bset.inj_weak). inv H0. apply mem_related_inj_j0. 
  generalize H6 Consist1 FLDISJ. clear. intros GMI Consist1 FLDISJ INJ MI.
  inv GMI; try (rewrite <- H0 in MI; inv MI; constructor; fail).
  rewrite <- H in *. inv MI. constructor. 
  inv H4; try constructor. econstructor; eauto. rewrite <- H3. inv H1.
  unfold Bset.inj_to_meminj, construct_inj in *; destruct plt; auto.
  destruct (Injections.inj mu b2) eqn:?; inv H6.
  destruct (Consist1 _ _ Heqo) as (b2'0 & b4' & J21 & INJ' & J23).
  exploit Bset.inj_range'; eauto. unfold Bset.belongsto; intro.
  inv H3. exfalso; eapply FLDISJ; eauto.

  exploit (mem_related_mem_val_shared j23); eauto.
  eapply GMem.mi_perm in H4; eauto; unfold Bset.inj_to_meminj; try rewrite INJ'; eauto.
  rewrite <- mem_related_mem_perm_eq; eauto. eapply mem_related_inj_construct_inj; eauto.
  constructor. constructor.
  pose proof (mem_related_freelist_disjoint _ _ _ _ _ H1) as FLDISJ.
  exploit (Bset.inj_weak). inv H1. apply mem_related_inj_j0. 
  generalize Nontriv Nontriv' H6 Consist1 FLDISJ. clear.
  intros Nontriv Nontriv' GMI Consist1 FLDISJ INJ MI.
  rewrite Z.add_0_r in *.
  inv GMI; try (try rewrite <- H in MI; try rewrite <- H0 in MI; inv MI; constructor; fail).
  rewrite <- H0 in *. inv MI. constructor. 
  inv H4; try constructor. econstructor; eauto. rewrite <- H3. inv H1. 
  unfold Bset.inj_to_meminj, construct_inj in *; destruct plt; auto.
  destruct (Injections.inj mu b3) eqn:?; inv H7.
  destruct (Consist1 _ _ Heqo) as (b2'0 & b4' & J21 & INJ' & J23).
  exploit Bset.inj_range'; eauto. unfold Bset.belongsto; intro.
  inv H3. exfalso; eapply FLDISJ; eauto.
  congruence.
  rewrite <- H0 in Nontriv. contradiction.      
Qed.

Lemma mem_inj_localize':
  forall j21 j23 bound fl fl' mu lmu m lm lm' m',
    Inj_lift j21 j23 mu lmu ->
    mem_related j21 bound fl m lm ->
    mem_related j23 bound fl' m' lm' ->
    Mem.mem_inj (Bset.inj_to_meminj (Injections.inj lmu)) lm lm' ->
    GMem.mem_inj (Bset.inj_to_meminj (Injections.inj mu)) m m'.
Proof.
  intros j21 j23 bound fl fl' mu lmu m lm lm' m' H H0 H1 H2.
  
  constructor; intros; exploit inj_to_meminj_some; eauto; intros [INJ Hdelta]; subst.
  destruct H. apply Consist1 in INJ. destruct INJ as (b1' & b2' & J21 & INJ' & J23).
  exploit mem_related_inj_construct_inj; eauto. intro.
  exploit (mem_related_inj_construct_inj j21); eauto. intro.
  rewrite mem_related_mem_perm_eq; eauto.
  rewrite mem_related_mem_perm_eq in H4; eauto.
  inv H2. eapply mi_perm; eauto. unfold Bset.inj_to_meminj. rewrite INJ'. auto.
  instantiate (1:= perm_kind_convert' k). destruct k; constructor.
  instantiate (1:= permission_convert' p). destruct p; constructor.
  destruct k; constructor. destruct p; constructor.
  
  apply Z.divide_0_r.

  destruct H. apply Consist1 in INJ. destruct INJ as (b1' & b2' & J21 & INJ' & J23).
  exploit (mem_related_inj_construct_inj j21); eauto. intro.
  pose proof H4. rewrite (mem_related_mem_perm_eq j21) in H4; eauto; try constructor.
  exploit Mem.mi_memval; eauto. unfold Bset.inj_to_meminj. rewrite INJ'. eauto. intro.

  (* rule out the case when source content is Undef, or Fragment Vundef..
         in which case we cannot relate source and target contents.
   *)
  assert (ZMap.get ofs (Mem.mem_contents lm) !! b1' = Undef \/
          ZMap.get ofs (Mem.mem_contents lm) !! b1' <> Undef) as [Triv|Nontriv].
  { clear. destruct (ZMap.get ofs (Mem.mem_contents lm) !! b1'); auto; right; intro C; inv C. }
  rewrite Triv in *. exploit (mem_related_mem_val_shared j21); eauto. intro.
  rewrite Triv in *. inv H7. constructor.

  assert ((exists q n, ZMap.get ofs (Mem.mem_contents lm) !! b1' = Fragment Vundef q n) \/
          (forall q n, ZMap.get ofs (Mem.mem_contents lm) !! b1' <> Fragment Vundef q n))
    as [(q&n&Triv)|Nontriv'].
  { clear.
    destruct (ZMap.get ofs (Mem.mem_contents lm) !! b1');
      try (right; intros ? ? C; inv C; fail).
    destruct v; try (right; intros ? ? C; inv C; fail).
    left. eauto. }
  exploit (mem_related_mem_val_shared j21); eauto. intro.
  rewrite Triv in *; clear Triv Nontriv. inv H7. inv H9. inv H6.
  exploit (mem_related_mem_val_shared j23); eauto.
  exploit Mem.mi_perm; eauto. unfold Bset.inj_to_meminj; rewrite INJ'. eauto.
  intro. rewrite <- H11 in H6. inv H6. constructor. constructor.

  (* contents are related by mu *)
  eapply memval_inject_strict_memval_inject; eauto.
  econstructor; eauto.
  
  exploit (mem_related_mem_val_shared j21); eauto.
  pose proof (mem_related_freelist_disjoint _ _ _ _ _ H0) as FLDISJ.
  exploit (Bset.inj_weak). inv H0. apply mem_related_inj_j0. 
  generalize H6 Consist2 FLDISJ. clear. intros GMI Consist2 FLDISJ INJ MI.
  inv GMI; try (rewrite <- H0 in MI; inv MI; constructor; fail).
  rewrite <- H in *. inv MI. constructor. 
  inv H3; try constructor. econstructor; eauto. rewrite <- H2. inv H1.
  unfold Bset.inj_to_meminj, construct_inj in *. destruct plt; auto.
  destruct (Injections.inj lmu b0) eqn:?; inv H5.
  destruct (Consist2 _ _ Heqo) as (b2'0 & b4' & J21 & J23 & INJ') .
  exploit Bset.inj_dom'; eauto. unfold Bset.belongsto; intro. contradiction.

  exploit (mem_related_mem_val_shared j23); eauto.
  eapply Mem.mi_perm in H4; eauto; unfold Bset.inj_to_meminj; try rewrite INJ'; eauto. 
  pose proof (mem_related_freelist_disjoint _ _ _ _ _ H1) as FLDISJ.
  exploit (Bset.inj_weak). inv H1. apply mem_related_inj_j0. 
  generalize Nontriv Nontriv' H6 Consist2 FLDISJ. clear.
  intros Nontriv Nontriv' GMI Consist2 FLDISJ INJ MI.
  rewrite Z.add_0_r in *.
  inv GMI; try (try rewrite <- H in MI; try rewrite <- H0 in MI; inv MI; constructor; try congruence; fail).
  rewrite <- H0 in *; clear H0. inv MI. constructor. 
  inv H2; try constructor. econstructor; eauto. rewrite <- H0. inv H1; try congruence. clear H0. 
  unfold Bset.inj_to_meminj, construct_inj in *; destruct plt; auto. exfalso.
  destruct (Injections.inj lmu b3) eqn:?; inv H6.
  destruct (Consist2 _ _ Heqo) as (b2'0 & b4' & J21 & J23 & INJ').
  exploit Bset.inj_dom'; eauto. 
Qed.

(** TODO: move to ? *)
Lemma peq_by_plt:
  forall p p', (forall x, Plt x p <-> Plt x p') -> p = p'.
Proof.
  intros. unfold Plt in *. pose proof (Pos.lt_total p p').
  destruct H0 as [LT | [EQ|LT]]; auto.
  exfalso. apply H in LT. eapply Pos.lt_irrefl; eauto.
  exfalso. apply H in LT. eapply Pos.lt_irrefl; eauto.
Qed.

Lemma mem_related_Rely_LRely:
  forall j bound fl gm m gm' m',
    norep fl ->
    no_overlap fl (fun b => Plt b bound) ->
    mem_related j bound fl gm m ->
    Rely fl (fun b => Plt b bound) gm gm' ->
    mem_related j bound fl gm' m' ->
    LDefs.Rely (fun b => Plt b bound) m m'.
Proof.
  intros j bound fl gm m gm' m' NOREP NOOVERLAP MEMREL GRELY MEMREL'.
  inv GRELY. constructor.
  (** TODO: valid_block equiv -> nextblock eq ?????? *)
  { pose proof (mem_related_valid_block _ _ _ _ _ MEMREL).
    pose proof (mem_related_valid_block _ _ _ _ _ MEMREL').
    apply peq_by_plt. intro. unfold Mem.valid_block in *.
    exploit construct_inj_total. inv MEMREL; eauto.
    instantiate (1:= x). instantiate (1:= fl). intros [x' INJ].
    rewrite H3; eauto. rewrite H2; eauto.
    unfold construct_inj in INJ. destruct plt.
    eapply Bset.inj_range' in INJ;[|inv MEMREL; inv mem_related_inj_j0; eauto].
    split; intros; eapply mem_related_shared_valid_global; eauto.
    split; intros.
    eapply GMem.unchanged_on_validity; eauto. simpl.
    inv INJ. unfold in_fl, get_block. eauto.
    erewrite <- GMem.unchanged_on_validity; eauto. simpl.
    inv INJ. unfold in_fl, get_block. eauto. }
  eapply mem_related_unchg_freelist_unchg_local; eauto.
  eapply mem_related_reach_closed; eauto.
  Unshelve. exact 0. exact 0.
Qed.

Lemma Rely_mem_related_exists:
  forall j bound fl gm m gm',
    mem_related j bound fl gm m ->
    Rely fl (fun b => Plt b bound) gm gm' ->
    exists m', mem_related j bound fl gm' m'.
Proof.
  intros j bound fl gm m gm' MEMREL GRELY.
  exploit bset_inject_revert; eauto. inv MEMREL. eauto.
  intros (j' & INJ' & REV).
  assert (SHARED_VALID: forall b b', j b = Some b' -> Plt b (Mem.nextblock m)).
  { intros. exploit (mem_related_shared_valid_local); eauto.
    exploit mem_related_inj_j; eauto. intro. inv H0. exploit Bset.inj_dom'; eauto. }
  exists (inject_memory j j' bound gm' m REV SHARED_VALID).
  econstructor; try (inv MEMREL; auto; fail).
  (* valid block *)
  intros. exploit mem_related_valid_block; eauto. intros.
  unfold Mem.valid_block. unfold inject_memory. simpl. rewrite H0.
  inv GRELY. unfold construct_inj in H. destruct (plt b bound).
  eapply Bset.inj_range' in H; [|exploit mem_related_inj_j; eauto; intros [? _]; eauto].
  unfold Bset.belongsto in H. clear p.
  exploit mem_related_shared_valid_global; eauto. intro. split; [inv H1|]; auto.
  inv H. inv H2. rewrite <- unchanged_on_validity. inv MEMREL. tauto.
  exact 0. unfold get_block, in_fl. eauto.
  (* shared valid global *)
  intros. exploit mem_related_shared_valid_global; eauto; intros.
  inv GRELY. inv H1. auto.
  (* eq perm *)
  unfold inject_memory. 
  intros. unfold construct_inj in H. 
  unfold Mem.perm, Mem.perm_order'. simpl.      
  destruct (proj2_sig (inject_access_c j j' bound (Mem.mem_access m) (GMem.mem_access gm'))).
  rewrite (H3 b). unfold inject_access.
  destruct plt. rewrite H.
  (* * b < bound, shared eq to gm' *)
  erewrite eq_perm_kind_convert; eauto.
  erewrite <- (eq_permission_convert' P P'); eauto.
  unfold GMem.perm, Memperm.perm_order'.
  destruct ((GMem.mem_access gm')!!b' ofs K') eqn:? ; simpl.
  apply perm_order_convert'_eq. tauto.
  (* * b > bound, use unchg_local relate gm' and gm, then by related ... *)
  destruct (plt b (Mem.nextblock m)).
  (* * valid *)
  inv GRELY. inv H5. 
  erewrite <- unchanged_on_perm. rewrite mem_related_mem_perm_eq; eauto.
  unfold Mem.perm, Mem.perm_order'. instantiate (1:=b). tauto.
  unfold construct_inj. destruct plt; [xomega|auto].
  unfold in_fl, get_block in *. inv H. eauto.
  erewrite <- mem_related_valid_block; eauto.
  unfold construct_inj; destruct plt; [xomega|auto].
  (* * invalid *)
  exploit Mem.nextblock_noaccess; eauto. intro. rewrite H4.
  split; intro; [|contradiction]. apply n0.
  fold (Mem.valid_block m b). rewrite (mem_related_valid_block _ _ _ _ _ MEMREL b b').
  inv GRELY. inv H7. rewrite unchanged_on_validity.
  unfold GMem.valid_block. destruct (In_dec peq b' (GMem.validblocks gm')); auto.
  exploit GMem.invalid_noaccess; eauto. intro. unfold GMem.perm in H5.
  erewrite H7 in H5. inversion H5. exact 0. unfold in_fl, get_block in *; inv H; eauto.
  unfold construct_inj; destruct plt; [xomega|auto].

  (* content eq*)
  unfold inject_memory, construct_inj. simpl.
  destruct (proj2_sig (inject_content_c j j' bound (Mem.mem_contents m) (GMem.mem_contents gm'))).
  intros. rewrite (H0 b). unfold inject_content.
  destruct plt.
  (* * b < bound *)
  rewrite H1. destruct (proj2_sig (inject_zmap_memval_c j' (GMem.mem_contents gm') !! b')).
  rewrite H4. unfold inject_zmap_memval. unfold inject_memval.
  destruct (ZMap.get ofs (GMem.mem_contents gm') !! b') eqn:HFrag; try constructor.
  destruct v; simpl; try constructor.
  (* by reach_close, b0 in bound, thus exists b'0, j' b0 = b'0 *)
  inv GRELY. destruct H7 as [H7 _ _]. exploit (H7 b0). econstructor. instantiate (1:=((b',i)::nil)).
  econstructor; eauto. econstructor. unfold Bset.belongsto. inv MEMREL.
  inv mem_related_inj_j0. exploit Bset.inj_range'; eauto.
  unfold Mem.perm in H2. simpl in H2.
  destruct (proj2_sig (inject_access_c j j' bound (Mem.mem_access m) (GMem.mem_access gm'))).
  rewrite H9 in H2. unfold inject_access in H2. rewrite H1 in H2. destruct plt; [|xomega].
  generalize H2; clear; simpl; intros. 
  unfold GMem.perm, Memperm.perm_order''. destruct ((GMem.mem_access gm')!!b' ofs Memperm.Max);[|inv H2].
  destruct p; simpl; inv H2; constructor.
  unfold Bset.belongsto; intros.
  assert (exists b'0, j' b0 = Some b'0).
  { inv MEMREL. inv mem_related_inj_j0.
    exploit Bset.inj_range; eauto. intros [b'0 ?]. rewrite REV in H9. eauto. }
  destruct H9 as [b'0 H9].
  rewrite H9. econstructor. unfold Bset.inj_to_meminj. rewrite <- REV in H9. rewrite H9.
  destruct plt. eauto.
  exfalso. apply n0. inv MEMREL. inv mem_related_inj_j0. exploit Bset.inj_dom'; eauto.
  rewrite <- Integers.Ptrofs.unsigned_zero,
  Integers.Ptrofs.repr_unsigned, Integers.Ptrofs.add_zero. auto.
  (* * b >= bound *)
  assert (in_fl fl b').
  { inv H1. unfold in_fl, get_block. eauto. }
  assert (construct_inj j bound fl b = Some b').
  { unfold construct_inj; destruct plt; [xomega|inv H1; auto]. }
  destruct (proj2_sig (inject_access_c j j' bound (Mem.mem_access m) (GMem.mem_access gm'))).
  unfold Mem.perm in *. simpl in *.
  rewrite H6 in H2. unfold inject_access in H2. destruct plt; auto. xomega. clear H5 H6.
  inv GRELY. inv H6. rewrite unchanged_on_contents; auto.
  apply mem_related_mem_val_inject; eauto.
  rewrite mem_related_mem_perm_eq; eauto; constructor.
Qed.

Lemma Rely_mem_related:
  forall j bound fl gm m gm',
    norep fl ->
    no_overlap fl (fun b => Plt b bound) ->
    mem_related j bound fl gm m ->
    Rely fl (fun b => Plt b bound) gm gm' ->
    exists m', mem_related j bound fl gm' m' /\
          LDSimDefs_local.LDefs.Rely (fun b => Plt b bound) m m'.
Proof.
  intros j bound fl gm m gm' NOREP NOOVERLAP MEMREL RELY.

  exploit mem_related_inj_j; eauto. intro INJECT_j.
  exploit bset_inject_revert; eauto. intros [j' [INJECT_j' REV]].
  (* construct content *)
  (** memrelated => nextblock eq? *)
  exploit Rely_mem_related_exists; eauto. intros (m' & MEMREL').
  exploit mem_related_Rely_LRely. eauto. eauto. apply MEMREL. eauto. eauto. intro LRELY.
  exists m'. auto.
Qed.

Lemma Inv_localize:
  forall j21 j23 bound fl fl' mu lmu m lm lm' m',
    Inj_lift j21 j23 mu lmu ->
    Inv mu m m' ->
    mem_related j21 bound fl m lm ->
    mem_related j23 bound fl' m' lm' ->
    LDefs.Inv lmu lm lm'.
Proof.
  intros. 
  constructor. 
  (* mem_inj *)
  exploit GMem.mi_inj; eauto. intro. eapply mem_inj_localize; eauto.
  (* invalid block *)
  intros. destruct (plt b bound).
  clear H2. exploit mem_related_shared_valid_local; eauto. intro. contradiction.
  inv H. destruct (Injections.inj lmu b) eqn:Hbimg.
  apply Consist2 in Hbimg. destruct Hbimg as (b1 & b3 & J21b & J23b0 & Hb1img).
  exploit mem_related_inj_j; [eapply H1|]. intros [? _]. inv inj_weak. apply inj_dom' in J21b.
  contradiction. unfold Bset.inj_to_meminj. rewrite Hbimg. auto.
  (* valid block *)
  intros. unfold Bset.inj_to_meminj in H3. destruct (Injections.inj lmu b) eqn:Hbimg; inv H3.
  inv H. apply Consist2 in Hbimg. destruct Hbimg as (b1 & b3 & J21b & J23b'& INJ13).
  exploit GMem.mi_mappedblocks; eauto. unfold Bset.inj_to_meminj. rewrite INJ13. eauto. intro.
  rewrite mem_related_valid_block; eauto.
  unfold construct_inj. destruct plt. auto.
  inv H2. inv mem_related_inj_j0. inv inj_weak. apply inj_dom' in J23b'. contradiction.
  (* no overlap *)
  intros b1 b1' d1 b2 b2' d2 ofs1 ofs2 ? ? ? ? ?.
  unfold Bset.inj_to_meminj in *.
  do 2 match goal with
       | H: match ?x with _ => _ end = _  |- _ => destruct x eqn:?; inv H end.
  inv H. apply Consist2 in Heqo. apply Consist2 in Heqo0.
  clear BSETEQ21 BSETEQ23 Consist1 Consist2.
  destruct Heqo as (b21 & b23 & J212 & J232& INJ2).
  destruct Heqo0 as (b11 & b13 & J211 & J231& INJ1).
  assert (b11 <> b21).
  { inv INJ21. inv inj_weak. intro. apply H3. eapply inj_injective; subst; eauto. }
  assert (b13 <> b23 \/ ofs1 + 0 <> ofs2 + 0).
  { inv H0. eapply mi_no_overlap. apply H.
    unfold Bset.inj_to_meminj. rewrite INJ1. auto.
    unfold Bset.inj_to_meminj. rewrite INJ2. auto.
    rewrite mem_related_mem_perm_eq; eauto.
    unfold construct_inj. destruct plt; auto.
    exfalso; apply n. inv H1. inv mem_related_inj_j0. inv inj_weak.
    unfold Bset.belongsto in *; eauto.
    constructor. constructor.
    rewrite mem_related_mem_perm_eq; eauto.
    unfold construct_inj. destruct plt; auto.
    exfalso; apply n. inv H1. inv mem_related_inj_j0. inv inj_weak.
    unfold Bset.belongsto in *; eauto.
    constructor. constructor.
  }
  destruct H4; auto. left.
  inv INJ23. inv inj_weak. intro. apply H4. subst. rewrite J231 in J232. inv J232. auto.
  (* representable *)
  intros b b' delta ofs H3 H4.
  unfold Bset.inj_to_meminj in H3. destruct (Injections.inj lmu b) eqn:?; inv H3.
  split; [xomega|]. exploit Integers.Ptrofs.unsigned_range_2. 
  instantiate (1:= ofs). intro. xomega.
  (* perm inv *)
  unfold Bset.inj_to_meminj. intros. destruct (Injections.inj lmu b1) eqn:?; inv H3.
  inv H. exploit Consist2; eauto. intros (b11 & b23 & J21 & J23 & J13).
  exploit (GMem.mi_perm_inv); eauto. unfold Bset.inj_to_meminj. rewrite J13. eauto.
  assert (construct_inj j23 bound fl' b2 = Some b23).
  { unfold construct_inj. destruct plt; auto.
    exfalso; apply n. inv H2. inv mem_related_inj_j0. inv inj_weak.
    unfold Bset.belongsto in *; eauto. }
  rewrite mem_related_mem_perm_eq; eauto.
  apply perm_kind_convert_eq. apply permission_convert_eq.
  assert (construct_inj j21 bound fl b1 = Some b11) as Hb1img.
  { unfold construct_inj. destruct plt; [auto|exfalso; apply n].
    inv H1. inv mem_related_inj_j0. inv inj_weak. unfold Bset.belongsto in *; eauto. }
  intros [GPERM|GPERM]; [left|right; intro; apply GPERM].
  rewrite <- mem_related_mem_perm_eq; eauto. apply perm_kind_convert_eq. apply permission_convert_eq.
  rewrite mem_related_mem_perm_eq; eauto. constructor. constructor. 
Qed.

Lemma Inv_localize':
  forall j21 j23 bound fl fl' mu lmu m lm lm' m',
    Inj_lift j21 j23 mu lmu ->
    LDefs.Inv lmu lm lm' ->
    mem_related j21 bound fl m lm ->
    mem_related j23 bound fl' m' lm' ->
    Inv mu m m'.
Proof.
  intros. 
  constructor. 
  (* mem_inj *)
  exploit Mem.mi_inj; eauto. intro. eapply mem_inj_localize'; eauto.
  (* invalid block *)
  intros. destruct (Injections.inj mu b) eqn:Hbimg; auto.
  exfalso.
  inv H. apply Consist1 in Hbimg. destruct Hbimg as (b1 & b3 & J21b & Hb1img & J23b0). clear Consist1 Consist2.
  exploit mem_related_inj_j; [eapply H1|]. intros [? _]. inv inj_weak. apply inj_range' in J21b.
  clear H2. exploit mem_related_shared_valid_global; eauto.
  unfold Bset.inj_to_meminj. rewrite Hbimg. auto.
  (* valid block *)
  intros. unfold Bset.inj_to_meminj in H3. destruct (Injections.inj mu b) eqn:Hbimg; inv H3.
  inv H. apply Consist1 in Hbimg. destruct Hbimg as (b1 & b3 & J21b & INJ13 & J23b').
  exploit Mem.mi_mappedblocks; eauto. unfold Bset.inj_to_meminj. rewrite INJ13. eauto. intro.
  rewrite <- mem_related_valid_block; eauto.
  unfold construct_inj. destruct plt. auto.
  inv H2. inv mem_related_inj_j0. inv inj_weak. apply inj_dom' in J23b'. contradiction.
  (* no overlap *)
  intros b1 b1' d1 b2 b2' d2 ofs1 ofs2 ? ? ? ? ?.
  unfold Bset.inj_to_meminj in *.
  do 2 match goal with
       | H: match ?x with _ => _ end = _  |- _ => destruct x eqn:?; inv H end.
  inv H. apply Consist1 in Heqo. apply Consist1 in Heqo0.
  clear BSETEQ21 BSETEQ23 Consist1 Consist2.
  destruct Heqo as (b21 & b23 & J212 & INJ2 & J232).
  destruct Heqo0 as (b11 & b13 & J211 & INJ1 & J231).
  assert (b11 <> b21).
  { intro. apply H3. subst. congruence. }
  assert (b13 <> b23 \/ ofs1 + 0 <> ofs2 + 0).
  { inv H0. eapply mi_no_overlap. apply H.
    unfold Bset.inj_to_meminj. rewrite INJ1. auto.
    unfold Bset.inj_to_meminj. rewrite INJ2. auto.
    rewrite <- mem_related_mem_perm_eq; eauto.
    unfold construct_inj. destruct plt; auto.
    exfalso; apply n. inv H1. inv mem_related_inj_j0. inv inj_weak.
    unfold Bset.belongsto in *; eauto.
    constructor. constructor.
    rewrite <- mem_related_mem_perm_eq; eauto.
    unfold construct_inj. destruct plt; auto.
    exfalso; apply n. inv H1. inv mem_related_inj_j0. inv inj_weak.
    unfold Bset.belongsto in *; eauto.
    constructor. constructor.
  }
  destruct H4; auto. left.
  inv INJ23. inv inj_weak. intro. apply H4. subst.
  eapply inj_injective; eauto.
  (* representable *)
  intros b b' delta ofs H3 H4.
  unfold Bset.inj_to_meminj in H3. destruct (Injections.inj mu b) eqn:?; inv H3.
  split; [xomega|]. exploit Integers.Ptrofs.unsigned_range_2. 
  instantiate (1:= ofs). intro. xomega.
  (* perm inv *)
  unfold Bset.inj_to_meminj. intros. destruct (Injections.inj mu b1) eqn:?; inv H3.
  inv H. exploit Consist1; eauto. intros (b11 & b23 & J21 & J22 & J23).
  exploit (Mem.mi_perm_inv); eauto. unfold Bset.inj_to_meminj. rewrite J22. eauto.
  assert (construct_inj j23 bound fl' b23 = Some b2).
  { unfold construct_inj. destruct plt; auto.
    exfalso; apply n. inv H2. inv mem_related_inj_j0. inv inj_weak.
    unfold Bset.belongsto in *; eauto. }
  rewrite <- mem_related_mem_perm_eq; eauto.
  instantiate (1:= perm_kind_convert' k). destruct k; constructor.
  instantiate (1:= permission_convert' p). destruct p; constructor.
  assert (construct_inj j21 bound fl b11 = Some b1) as Hb1img.
  { unfold construct_inj. destruct plt; [auto|exfalso; apply n].
    inv H1. inv mem_related_inj_j0. inv inj_weak. unfold Bset.belongsto in *; eauto. }
  intros [GPERM|GPERM]; [left|right; intro; apply GPERM].
  rewrite mem_related_mem_perm_eq; eauto. destruct k; constructor. destruct p; constructor.
  rewrite <- mem_related_mem_perm_eq; eauto. constructor. constructor.
Qed.
  
Lemma HLRely_Inj_lift:
  forall j21 j23 mu lmu bound sfl tfl Hm lHm lLm Lm,
    Injections.SharedSrc mu = (fun b => Plt b bound) ->
    Injections.SharedTgt mu = (fun b => Plt b bound) ->
    norep sfl -> norep tfl ->
    no_overlap sfl (fun b => Plt b bound) ->
    no_overlap tfl (fun b => Plt b bound) ->    
    Inj_lift j21 j23 mu lmu ->
    mem_related j21 bound sfl Hm lHm ->
    mem_related j23 bound tfl Lm lLm ->
    LDSimDefs_local.LDefs.Inv lmu lHm lLm ->
    forall Hm' Lm',
      HLRely sfl tfl mu Hm Hm' Lm Lm' ->
      exists lHm' lLm',
        mem_related j21 bound sfl Hm' lHm' /\
        mem_related j23 bound tfl Lm' lLm' /\
        LDSimDefs_local.LDefs.HLRely lmu lHm lHm' lLm lLm'.
Proof.
  intros j21 j23 mu lmu bound sfl tfl Hm lHm lLm Lm
         SSrc STgt NOREPS NOREPT NOOVERLAPS NOOVERLAPT
         INJLIFT MEMREL21 MEMREL23 MEMINJ Hm' Lm' RELYs.
  inv RELYs.
  rewrite SSrc in H. rewrite STgt in H0.
  exploit (Rely_mem_related j21 bound sfl); eauto. intros (lHm' & MEMREL21' & ?).
  exploit (Rely_mem_related j23 bound tfl); eauto. intros (lLm' & MEMREL23' & ?).  
  exists lHm', lLm'. split; auto. split; auto.
  constructor.
  eapply bset_eq_Rely_local; eauto. inv INJLIFT. intro. rewrite BSETEQ21, SSrc. tauto.
  eapply bset_eq_Rely_local; eauto. inv INJLIFT. intro. rewrite BSETEQ23, STgt. tauto.
  eapply Inv_localize; eauto.
Qed.





Section SIM_LOCALIZE.

Context {F1 V1 G1 comp_unit1 core1: Type}.

Context {internal_fn1: comp_unit1 -> list AST.ident}
        {init_genv1: comp_unit1 -> Genv.t F1 V1 -> G1 -> Prop}
        {init_gmem1: Genv.t F1 V1 -> gmem -> Prop}
        {init_core1: G1 -> AST.ident -> list val -> option core1}
        {halt1: core1 -> option val}
        {step1: G1 -> freelist -> core1 -> gmem -> FP.t -> core1 -> gmem -> Prop}
        {at_external1: G1 -> core1 -> option (AST.ident * AST.signature * list val)}
        {after_external1: core1 -> option val -> option core1}
        {init_genv_local1: comp_unit1 -> Genv.t F1 V1 -> G1 -> Prop}
        {init_mem1: Genv.t F1 V1 -> mem -> Prop}
        {init_core_local1: G1 -> AST.ident -> list val -> option core1}
        {halt_local1: core1 -> option val}
        {step_local1: G1 -> core1 -> mem -> FP.t -> core1 -> mem -> Prop}
        {at_external_local1: G1 -> core1 -> option (AST.ident * AST.signature * list val)}
        {after_external_local1: core1 -> option val -> option core1}.

Let sl := (Build_Language F1 V1 G1 comp_unit1 core1
                          init_core1 step1 at_external1 after_external1 halt1 
                          internal_fn1 init_genv1 init_gmem1).

Let ssem := (Build_sem_local F1 V1 G1 comp_unit1 core1
                             init_genv_local1 init_mem1 init_core_local1
                             halt_local1 step_local1
                             at_external_local1 after_external_local1).

Context {F2 V2 G2 comp_unit2 core2: Type}.

Context {internal_fn2: comp_unit2 -> list AST.ident}
        {init_genv2: comp_unit2 -> Genv.t F2 V2 -> G2 -> Prop}
        {init_gmem2: Genv.t F2 V2 -> gmem -> Prop}
        {init_core2: G2 -> AST.ident -> list val -> option core2}
        {halt2: core2 -> option val}
        {step2: G2 -> freelist -> core2 -> gmem -> FP.t -> core2 -> gmem -> Prop}
        {at_external2: G2 -> core2 -> option (AST.ident * AST.signature * list val)}
        {after_external2: core2 -> option val -> option core2}
        {init_genv_local2: comp_unit2 -> Genv.t F2 V2 -> G2 -> Prop}
        {init_mem2: Genv.t F2 V2 -> mem -> Prop}
        {init_core_local2: G2 -> AST.ident -> list val -> option core2}
        {halt_local2: core2 -> option val}
        {step_local2: G2 -> core2 -> mem -> FP.t -> core2 -> mem -> Prop}
        {at_external_local2: G2 -> core2 -> option (AST.ident * AST.signature * list val)}
        {after_external_local2: core2 -> option val -> option core2}.

Let tl := Build_Language F2 V2 G2 comp_unit2 core2
                         init_core2 step2 at_external2 after_external2 halt2 
                         internal_fn2 init_genv2 init_gmem2.

Let tsem := Build_sem_local F2 V2 G2 comp_unit2 core2
                            init_genv_local2 init_mem2 init_core_local2 halt_local2 step_local2
                            at_external_local2 after_external_local2.

Context {wdcu1: comp_unit1 -> Prop}.
Context {wdcu2: comp_unit2 -> Prop}.

Hypothesis SLocalize: LangLocalize comp_unit1 wdcu1 sl ssem.

Hypothesis TLift: LangLift comp_unit2 wdcu2 tl tsem.

Inductive LIFTED_MATCH
          (sfl tfl: freelist)
          (bound: block)
          (I: Type) (I_order : I -> I -> Prop)
          (j21 j23: Bset.inj)
          (lmu: Injections.Mu)
          (R12: Bset.inj -> freelist -> core1 -> gmem -> core1 -> mem -> Prop)
          (R22: bool -> I -> Injections.Mu -> FP.t -> FP.t ->
                (core1 * mem) -> (core2 * mem) -> Prop)
          (R32: Bset.inj -> freelist -> core2 -> gmem -> core2 -> mem -> Prop)
  : bool -> I -> Injections.Mu -> FP.t -> FP.t -> (core1 * gmem) -> (core2 * gmem) -> Prop :=
  
  MATCH_true:
    forall i mu fpS fpT sc sm tc tm
      lsc lsm ltc ltm lfpS lfpT
      (MATCH12: R12 j21 sfl sc sm lsc lsm)
      (FPINJ12: FPlocalize (construct_inj j21 bound sfl) fpS lfpS)
      (MATCH32: R32 j23 tfl tc tm ltc ltm)
      (FPINJ32: FPlocalize (construct_inj j23 bound tfl) fpT lfpT)
      (MATCH22: R22 true i lmu lfpS lfpT (lsc, lsm) (ltc, ltm))
      (INJLIFT: Inj_lift j21 j23 mu lmu)
      (TFPG: fpG tfl (Injections.SharedTgt mu) fpT),
      LIFTED_MATCH sfl tfl bound I I_order j21 j23 lmu R12 R22 R32
                   true i mu fpS fpT (sc, sm) (tc, tm)
                   
| MATCH_false:
    forall i mu sc sm tc tm lsc lsm ltc ltm  
      (MATCH12: R12 j21 sfl sc sm lsc lsm)
      (MATCH32: R32 j23 tfl tc tm ltc ltm)
      (MATCH22: R22 false i lmu FP.emp FP.emp (lsc, lsm) (ltc, ltm))
      (INJLIFT: Inj_lift j21 j23 mu lmu)
      (INV: LDSimDefs_local.LDefs.Inv lmu lsm ltm)
    ,
      LIFTED_MATCH sfl tfl bound I I_order j21 j23 lmu R12 R22 R32
                   false i mu FP.emp FP.emp (sc, sm) (tc, tm).


Hypothesis (H_def_ident:
              forall scu, wdcu1 scu ->
                     forall sge sG, init_genv_local1 scu sge sG ->
                               forall b gd, (Genv.genv_defs sge) ! b = Some gd ->
                                       exists id, (Genv.genv_symb sge) ! id = Some b).
Hypothesis (H_def_ident':
              forall tcu, wdcu2 tcu ->
                     forall tge tG, init_genv_local2 tcu tge tG ->
                               forall b gd, (Genv.genv_defs tge) ! b = Some gd ->
                                       exists id, (Genv.genv_symb tge) ! id = Some b).

(** ** Main result: lifting lemma *)
Theorem localize:
  forall scu tcu
    (Hwdscu: wdcu1 scu)
    (Hwdtcu: wdcu2 tcu),
    @ldsim_local ssem tsem scu tcu ->
    @ldsim sl tl scu tcu.
Proof.
  subst sl ssem tl tsem. simpl in *.
  intros. unfold ldsim_local in H; simpl in H.
  unfold ldsim; simpl.
  
  intros sG sge tG tge sfl tfl INITSG INITTG GENVDOMEQ. 
  apply localize_localizesim with (cu:=scu) (ge:=sge) (Ge:=sG) in SLocalize; auto .

  destruct SLocalize as (j21_ident & sge_local & sG_local & R12 & INITSG_local & SGEMATCH & Hj21_ident & SLocalize').
  edestruct (lift_liftsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TLift
                         tcu Hwdtcu tge tG INITTG) as
      (j23_ident & tge_local & tG_local & R32 & INITTG_local & TGEMATCH & Hj23_ident & TLift').
  
  clear SLocalize TLift. simpl in *.
  specialize (H sG_local sge_local tG_local tge_local INITSG_local INITTG_local).
  assert (Genv.genv_next sge_local = Genv.genv_next tge_local) as GENVDOMEQ'.
  { apply ge_match_strict_next in SGEMATCH. apply ge_match_strict_next in TGEMATCH.
    simpl in *. congruence. }
  specialize (H GENVDOMEQ').
  destruct H as (I, I_order, R22, SIM_local). simpl in *.
  exists I, I_order.
  
  pose proof SIM_local as GEMATCH22. apply match_genv in GEMATCH22.
  assert (Constr: forall mu, ge_init_inj mu sge tge ->
                        exists j21 j23 mu_local,
                        inject_incr (Bset.inj_to_meminj j21_ident) (Bset.inj_to_meminj j21) /\
                        inject_incr (Bset.inj_to_meminj j23_ident) (Bset.inj_to_meminj j23) /\
                        inject_incr (Bset.inj_to_meminj (Injections.inj mu_local)) inject_id /\
                        Inj_lift j21 j23 mu mu_local ).
  { specialize (H_def_ident _ Hwdscu _ _ INITSG_local). specialize (H_def_ident' _ Hwdtcu _ _ INITTG_local).
    generalize H_def_ident H_def_ident' SGEMATCH TGEMATCH Hj21_ident Hj23_ident GEMATCH22 GENVDOMEQ'. clear; intros.
    assert (exists j21, inject_incr (Bset.inj_to_meminj j21_ident) (Bset.inj_to_meminj j21) /\
                   Bset.inject j21 (fun b => Plt b (Genv.genv_next sge_local))
                               (fun b => Plt b (Genv.genv_next sge))) as [j21 [Hj21 Hj21']].
    { assert (forall b b', j21_ident b = Some b' -> Plt b (Genv.genv_next sge_local) /\ Plt b' (Genv.genv_next sge)).
      { intros. exploit Hj21_ident; eauto. intros [gd Hb]. apply H_def_ident in Hb. destruct Hb as [id Hid].
        inv SGEMATCH. specialize (ge_match_strict_senv0 id). unfold Senv.find_symbol in *; simpl in *.
        unfold Genv.find_symbol in *. rewrite Hid in ge_match_strict_senv0. inv ge_match_strict_senv0.
        rewrite H0 in H4. inv H4. symmetry in H3.
        eapply Genv.genv_symb_range in Hid. apply Genv.genv_symb_range in H3. auto. }
      inv SGEMATCH. generalize H0 ge_match_strict_next0 ge_match_strict_inj_injective0. clear.
      intros H1 H2 H3. rewrite H2 in *. clear H2. revert H1 H3. generalize (Genv.genv_next sge_local). clear.
      rename j21_ident into j. intros BOUND DOMRANGE INJECTIVE.
      apply inj_extension; auto.
    }
    exists j21.
    exists (fun b => match j23_ident b with
             | Some b' => Some b'
             | None => match j21 b with
                      | Some b1 => Injections.inj mu b1
                      | None => None
                      end
             end).
    exists (Injections.Build_Mu (fun b => if plt b (Genv.genv_next sge_local) then Some b else None)
                           (fun b => Plt b (Genv.genv_next sge_local))
                           (fun b => Plt b (Genv.genv_next tge_local))).
    split; auto.
    split. intros b b' delta. unfold Bset.inj_to_meminj. destruct (j23_ident b);[congruence|discriminate].
    split. intros b b' delta. unfold Bset.inj_to_meminj. simpl. destruct plt;[intro C; inv C; auto|discriminate].
    pose proof (ge_init_inj_SharedSrc _ _ _ _ mu sge tge H).
    pose proof (ge_init_inj_SharedTgt _ _ _ _ mu sge tge H).
    pose proof (ge_match_strict_next j21_ident _ _ SGEMATCH).
    pose proof (ge_match_strict_next j23_ident _ _ TGEMATCH).
    constructor; simpl; auto.
    rewrite H0, H2; auto. rewrite H0; auto. rewrite H1, H3; auto.
    { rewrite H1. constructor. constructor.
      (* inj_dom' *)
      { intros b b'. destruct j23_ident eqn:J23. apply Hj23_ident in J23. destruct J23 as [gd Hb].
        apply Genv.genv_defs_range in Hb. intro. inv H4. auto.
        destruct j21 eqn:J21; [|discriminate]. intro. eapply Bset.inj_dom' in J21; [|inv Hj21'; eauto].
        rewrite GENVDOMEQ' in J21. auto. }
      (* inj_range *)
      { rewrite <- H1. intros b' Hrange. eapply Bset.inj_range in Hrange;[|apply mu_inject in H; inv H; eauto].
        destruct Hrange as [b1 J13]. exploit Bset.inj_dom'. inv H. inv mu_inject. eauto. eauto.
        rewrite H0. intro Hdom. eapply Bset.inj_range in Hdom; [|inv Hj21'; eauto]. destruct Hdom as [b2 J21].
        exists b2. destruct (j23_ident b2) eqn:J23. pose proof J23 as J23'.
        apply Hj23_ident in J23'. destruct J23' as [gd Hgd]. eapply H_def_ident' in Hgd. destruct Hgd as [id Hid'].
        assert (Hid: (Genv.genv_symb sge_local) ! id = Some b2) by (unfold block; rewrite <- Hid'; inv GEMATCH22; auto).
        assert (j21_ident b2 = Some b1).
        { apply ge_match_strict_senv with (id0:=id) in SGEMATCH.
          unfold Senv.find_symbol; simpl in SGEMATCH; unfold Genv.find_symbol in SGEMATCH; simpl in SGEMATCH.
          rewrite Hid in SGEMATCH. inv SGEMATCH. pose proof H7. eapply inject_incr_bset_inj_incr in H7; eauto.
          rewrite J21 in H7. inv H7. auto. }
        Ltac simplsymb := unfold Senv.find_symbol in *; simpl in *; unfold Genv.find_symbol in *. 
        assert (Hid0: (Genv.genv_symb sge) ! id = Some b1).
        { inv SGEMATCH. specialize (ge_match_strict_senv0 id). simplsymb. rewrite Hid in ge_match_strict_senv0.
          inv ge_match_strict_senv0. congruence. }
        assert (Hid0': (Genv.genv_symb tge) ! id = Some b).
        { inv TGEMATCH. specialize (ge_match_strict_senv0 id). simplsymb. rewrite Hid' in ge_match_strict_senv0.
          inv ge_match_strict_senv0. congruence. }
        apply senv_injected with (id0:=id) in H. unfold Senv.find_symbol in H; simpl in H.
        unfold Genv.find_symbol in H. rewrite Hid0, Hid0' in H. inv H. congruence.
        rewrite J21. auto. }
      (* inj_range' *)
      { intros b b'. destruct j23_ident eqn:J23. pose proof J23 as J23'.
        apply Hj23_ident in J23. destruct J23 as [gd Hb]. intro C. inv C.
        apply H_def_ident' in Hb. destruct Hb as [id Hid'].
        assert (Hid0': (Genv.genv_symb tge) ! id = Some b').
        { inv TGEMATCH. unfold Senv.find_symbol in *. simpl in *. unfold Genv.find_symbol in *.
          specialize (ge_match_strict_senv0 id). rewrite Hid' in ge_match_strict_senv0. inv ge_match_strict_senv0.
          congruence. }
        unfold Bset.belongsto. eapply Genv.genv_symb_range. eauto.
        destruct j21;[|discriminate]. intro. eapply Bset.inj_range'; eauto. inv H. inv mu_inject. rewrite <- H1; eauto.
      }
      (* injective *)
      { intros b1 b2 b'. destruct (j23_ident b1) eqn:Hb1; destruct (j23_ident b2) eqn:Hb2.
        intros A1 A2; inv A1; inv A2. eapply ge_match_strict_inj_injective; eauto.
        { intro A1; inv A1. destruct j21 eqn: Hb2'; [|discriminate]. intro.
          exploit Hj23_ident; eauto. intros [gd' Hgd']. apply H_def_ident' in Hgd'. destruct Hgd' as [id Hid'].
          exploit (ge_match_strict_senv j23_ident _ _ TGEMATCH). simplsymb. rewrite Hid'. intro A; inv A.
          symmetry in H7. rewrite Hb1 in H8; inv H8.
          exploit (senv_injected mu _ _ H). simplsymb. rewrite H7. intro A. inv A.
          symmetry in H5. exploit Bset.inj_injective. inv H. inv mu_inject; eauto. exact H4. exact H9.
          intro. subst. exploit (ge_match_strict_senv j21_ident _ _ SGEMATCH). simplsymb. rewrite H5.
          intro A. inv A. symmetry in H6.
          exploit inject_incr_bset_inj_incr. exact Hj21. eauto. intro.
          exploit Bset.inj_injective. inv Hj21'; eauto. exact Hb2'. exact H8. intro; subst. clear H8.
          assert (Hid'': (Genv.genv_symb tge_local) ! id = Some b) by (erewrite <- genv_symb_eq; eauto).
          rewrite Hid'' in Hid'. congruence. }
        { destruct j21 eqn:J21 ;[|discriminate]. intros. inv H5.
          exploit Hj23_ident; eauto. intros [gd' Hgd']. apply H_def_ident' in Hgd'. destruct Hgd' as [id Hid'].
          exploit (ge_match_strict_senv j23_ident _ _ TGEMATCH). simplsymb. rewrite Hid'. intro A; inv A.
          symmetry in H7. rewrite Hb2 in H8; inv H8.
          exploit (senv_injected mu _ _ H). simplsymb. rewrite H7. intro A. inv A.
          symmetry in H5. exploit Bset.inj_injective. inv H. inv mu_inject; eauto. exact H4. exact H9.
          intro. subst. exploit (ge_match_strict_senv j21_ident _ _ SGEMATCH). simplsymb. rewrite H5.
          intro A. inv A. symmetry in H6.
          exploit inject_incr_bset_inj_incr. exact Hj21. eauto. intro.
          exploit Bset.inj_injective. inv Hj21'; eauto. exact J21. exact H8. intro; subst. clear H8.
          erewrite genv_symb_eq in H6; eauto. congruence. }
        destruct (j21 b1) eqn:Hb1'; [|discriminate]; (destruct (j21 b2) eqn:Hb2'; [|discriminate]).
        intros. exploit Bset.inj_injective. inv H. inv mu_inject; eauto. exact H4. exact H5. intro; subst.
        eapply Bset.inj_injective; eauto. inv Hj21'; eauto. }
      (* inj_dom *)
      { intros. destruct (j23_ident b) eqn: Hb. eauto.
        rewrite <- GENVDOMEQ' in H4. eapply Bset.inj_dom in H4; eauto. destruct H4 as [b1 Hb1].
        rewrite Hb1. eapply Bset.inj_range' in Hb1. eapply Bset.inj_dom in Hb1; eauto.
        inv H; eauto. inv Hj21'; eauto. rewrite H0. eauto.  }
    }
    (* consist 1 *)
    { intros. exploit Bset.inj_dom'. inv H. inv mu_inject. eauto. eauto. intro Hb1.
      erewrite H0, ge_match_strict_next in Hb1; eauto.
      exploit Bset.inj_range. inv Hj21'; eauto. rewrite H2. eauto. intros [b2 J21]. exists b2, b2.
      exploit Bset.inj_dom'. inv Hj21'; eauto. exact J21. intro Hb2. destruct plt; [|congruence].
      do 2 (split; [auto|]). rewrite J21. destruct (j23_ident b2) eqn:Hb2';[|auto].
      destruct (Hj23_ident _ _ Hb2') as [gd' Hgd']. apply H_def_ident' in Hgd'. destruct Hgd' as [id Hid'].
      assert (Hid: (Genv.genv_symb sge_local) ! id = Some b2).
      { inv GEMATCH22. rewrite genv_symb_eq; auto. }
      exploit (ge_match_strict_senv j23_ident _ _ TGEMATCH). simplsymb. rewrite Hid'. intro A. inv A.
      rewrite Hb2' in H8. inv H8. symmetry in H7.
      exploit (ge_match_strict_senv j21_ident _ _ SGEMATCH). simplsymb. rewrite Hid. intro A. inv A.
      eapply inject_incr_bset_inj_incr in H9; eauto. rewrite J21 in H9. inv H9. symmetry in H8.
      exploit (senv_injected mu _ _ H). simplsymb. rewrite H7, H8. intro. inv H5. congruence.
    }
    (* consist 2*)
    {
      intros b2 b2'. destruct plt;[|discriminate]. intro A. inv A.
      exploit Bset.inj_dom. exact Hj21'. eauto. intros [b1 J21].
      exists b1. rewrite J21. destruct (j23_ident b2') eqn:J23.
      exploit Hj23_ident. eauto. intros [gd' Hgd']. apply H_def_ident' in Hgd'. destruct Hgd' as [id Hid'].
      assert (Hid: (Genv.genv_symb sge_local) ! id = Some b2').
      { inv GEMATCH22. rewrite genv_symb_eq; auto. }
      exploit (ge_match_strict_senv j23_ident _ _ TGEMATCH). simplsymb. rewrite Hid'. intro A. inv A.
      rewrite J23 in H7. inv H7. symmetry in H6.
      exploit (ge_match_strict_senv j21_ident _ _ SGEMATCH). simplsymb. rewrite Hid. intro A. inv A.
      eapply inject_incr_bset_inj_incr in H8; eauto. rewrite J21 in H8. inv H8. symmetry in H7.
      exploit (senv_injected mu _ _ H). simplsymb. rewrite H7, H6. intro. inv H4. eauto.
      eapply Bset.inj_range' in J21; [|inv Hj21'; eauto].
      eapply Bset.inj_dom in J21;[|inv H; rewrite <- H0; eauto]. destruct J21 as [b3 J13]. eauto.
    }
  }
    
  assert (GEMATCH: ge_match sge tge).
  { pose proof (match_genv _ _ _ _ _ _ _ SIM_local).
    inv H; inv SGEMATCH; inv TGEMATCH. constructor.
    { intro. erewrite ge_match_strict_public0, ge_match_strict_public1. auto. }
    { intros. simplsymb.
      specialize (ge_match_strict_senv0 id); inv ge_match_strict_senv0;
        specialize (ge_match_strict_senv1 id); inv ge_match_strict_senv1; unfold Genv.find_symbol in *; simpl in *. split; discriminate. 3: tauto.
      erewrite genv_symb_eq in H; eauto. congruence.
      erewrite genv_symb_eq in H1; eauto. congruence.  }
    { intros. simplsymb.
      specialize (ge_match_strict_senv0 id). specialize (ge_match_strict_senv1 id).
      rewrite H in ge_match_strict_senv0. rewrite H0 in ge_match_strict_senv1.
      inv ge_match_strict_senv0; inv ge_match_strict_senv1.
      exploit (genv_defs_match id b0 b1); eauto.
      apply ge_match_strict_defs0 in H4. apply ge_match_strict_defs1 in H6.
      generalize H4 H6. clear. intros H H1 H2; inv H; inv H1; inv H2; try congruence; constructor.
      repeat match goal with
             | H1: _ = ?x, H2: _ = ?x |- _ => rewrite <- H1 in H2; inv H2; clear H1
             end.
      inv H4; inv H6; inv H8; constructor.
      inv H1; inv H2; inv H5; constructor.  }
    congruence.
  }
  
  remember (fun b:block => Plt b (Genv.genv_next sge)) as SharedSrc.
  remember (fun b:block => Plt b (Genv.genv_next tge)) as SharedTgt.

  remember ( fun b i mu fp fp' cg1 cg2 =>
               no_overlap sfl (Injections.SharedSrc mu) /\
               no_overlap tfl (Injections.SharedTgt mu) /\
               norep sfl /\ norep tfl /\
               ge_init_inj mu sge tge /\
               exists j21 j23 mu_local,
                 inject_incr (Bset.inj_to_meminj j21_ident) (Bset.inj_to_meminj j21) /\
                 inject_incr (Bset.inj_to_meminj j23_ident) (Bset.inj_to_meminj j23) /\
                 inject_incr (Bset.inj_to_meminj (Injections.inj mu_local)) inject_id /\
                 Inj_lift j21 j23 mu mu_local /\
                 LIFTED_MATCH sfl tfl (Genv.genv_next sge) I I_order j21 j23 mu_local R12 R22 R32
                              b i mu fp fp' cg1 cg2) as MATCHSTATE.
  
  Ltac invMS M :=
    destruct M as (NOOVERLAP & NOOVERLAP' & NOREP & NOREP' & GEINITINJ & 
                   j21 & j23 & mu_local & Hj21 & Hj23 & Hmu_local
                   & INJLIFT & LIFTMATCH);
    pose proof INJLIFT as INJLIFT';
    destruct INJLIFT' as [j21 j23 mu mu_local _ Hj21' _ Hj23' _ _];
    match goal with
    | HS: context[LocalizeSim], HT: context[LiftSim] |- _ =>
      specialize (HS j21 Hj21); specialize (HT j23 Hj23)
    end.
          
  exists MATCHSTATE. constructor; simpl in *.
  
  - (* * wd index *)
    destruct SIM_local. auto.
  
  - (* * wd mu *) 
    intros b i mu Hfp Lfp (Hcore, Hmem) (Lcore, Lmem) MATCH. subst.
    generalize R12 R32 R22 SLocalize' TLift' SIM_local MATCH. clear. intros.
    invMS MATCH.
    split. eapply Inj_lift_inject; eauto.
    inv LIFTMATCH; destruct SIM_local; eapply wd_mu; eauto.
    auto.

  - (* * fl norep *)
    intros b i mu Hfp Lfp Hc Lc MATCH. subst. invMS MATCH. auto.
    
  - (* * ge_match *)
    auto.
    
  - (* * ge_init_inj *)
    intros b i mu Hfp Lfp Hc Lc MATCH. subst.
    invMS MATCH. auto.
    
  - (* * init match *)
    intros mu id argSrc argTgt score GEREL GARGS ARGREL INITCORE.
    specialize (Constr mu GEREL).
    destruct Constr as (j21 & j23 & mu_local & Hj21 & Hj23 & MULOCAL & LIFTMU).
    assert (Hj23':Bset.inject j23 (fun b : block => Plt b (Genv.genv_next tge_local)) SharedTgt).
    { inv LIFTMU. inv TGEMATCH. rewrite BSETEQ23 in INJ23. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_tgt; eauto. }
    assert (Hj21':Bset.inject j21 (fun b : block => Plt b (Genv.genv_next sge_local)) SharedSrc).
    { inv LIFTMU. inv SGEMATCH. rewrite BSETEQ21 in INJ21. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_src; eauto. }
    specialize (SLocalize' j21 Hj21 Hj21'). specialize (TLift' j23 Hj23 Hj23').
    
    (* construct local initial core on source *)
    pose proof (localize_init _ _ _ _ _ _ SLocalize' id argSrc score) as INITLOCALIZE. simpl in INITLOCALIZE.
    assert (INITARGS: G_args SharedSrc argSrc).
    { subst SharedSrc. generalize GARGS GEREL. clear. intros.
      inv GEREL. rewrite <- mu_shared_src. auto. }
    rewrite HeqSharedSrc in INITARGS. specialize (INITLOCALIZE INITARGS INITCORE).
    destruct INITLOCALIZE as (argSrc_local & lsc & ARGLOCALIZE & INITCORE_local & INITLOCALIZE).
    (* construct local initial core on traget *)
    pose proof (match_init _ _ _ _ _ _ _ SIM_local) as INITSIM; simpl in *.
    (* construct local args on target *)
    pose proof (lift_init _ _ _ _ _ _ TLift' argTgt) as INITLIFT; simpl in *.
    assert (INITARGT: G_args (fun b => Plt b (Genv.genv_next tge)) argTgt).
    { subst SharedTgt. generalize GARGS ARGREL GEREL. clear. intros.
      induction ARGREL. constructor.
      constructor; auto.
      inversion H; try constructor.
      subst v v'. inversion GEREL.
      unfold G_arg. unfold Bset.inj_to_meminj in H0. destruct (Injections.inj mu b1) eqn:?; try inv H0.
      eapply Bset.inj_range'; eauto. inv mu_inject. rewrite mu_shared_tgt in inj_weak. eauto.
      subst. inv GARGS. contradiction.
      inv GARGS. apply IHARGREL. auto.
    }
    specialize (INITLIFT INITARGT). 
    destruct INITLIFT as (argTgt_local & ARGLIFT & INITLIFT).

    assert (GEREL_LOCAL: ge_init_inj mu_local sge_local tge_local).
    { simpl in *. eapply ge_localize in LIFTMU; eauto. auto.
      simpl in *. auto. }

    assert (ARGREL_LOCAL: arg_rel (Injections.inj mu_local) argSrc_local argTgt_local).
    { eapply arg_rel_strict_lift; eauto. }

    assert (GARGS_local: G_args (Injections.SharedSrc mu_local) argSrc_local).
    { generalize LIFTMU ARGLOCALIZE GARGS. clear. intros LIFTMU.
      inv LIFTMU. generalize INJ21; clear. intro. revert argSrc.
      induction argSrc_local; intros; inv ARGLOCALIZE. constructor.
      inv GARGS. constructor. inv H1; auto.
      unfold Bset.inj_to_meminj in H. destruct (j21 b0) eqn:J21; inv H.
      simpl in *.  eapply Bset.inj_dom'; eauto. inv INJ21; eauto. eapply IHargSrc_local; eauto. }

    specialize (INITSIM mu_local id argSrc_local argTgt_local lsc GEREL_LOCAL MULOCAL GARGS_local ARGREL_LOCAL INITCORE_local).
    destruct INITSIM as (ltc & INITCORE_local' & INITSIM).

    specialize (INITLIFT id ltc INITCORE_local').
    destruct INITLIFT as (tcore & INITCORE' & INITLIFT).
    
    exists tcore. split. auto.
    intros sm tm INITSM INITTM MEMINITREL.

    (* construct local initial memory *)
    inv MEMINITREL. 
    erewrite mu_shared_src in rc_shared_Src; eauto.
    erewrite mu_shared_tgt in rc_shared_Tgt; eauto.
    destruct (INITLOCALIZE sm sfl INITSM sfl_norep sfl_free rc_shared_Src)
      as (lsm & INITSM' & MEMREL21 & MATCH12).
    clear INITLOCALIZE.
    destruct (INITLIFT tm tfl INITTM tfl_norep tfl_free rc_shared_Tgt)
      as (ltm & INITTM' & MEMREL23 & MATCH23).
    clear INITLIFT.
    specialize (INITSIM lsm ltm INITSM' INITTM').
    assert (MEMINITREL': mem_init_inj mu_local lsm ltm).
    { generalize GEREL LIFTMU valid_Src valid_Tgt rc_shared_Src rc_shared_Tgt Binj init_mu
                 MEMREL21 MEMREL23 GENVDOMEQ MULOCAL.
      clear. intros. inv LIFTMU. constructor.
      { intro b. rewrite BSETEQ21 in INJ21. inv GEREL. rewrite mu_shared_src in *.
        exploit construct_inj_total. exact INJ21. instantiate (1:= b). intros [b' J21].
        exploit mem_related_valid_block. exact MEMREL21. eauto. intro.
        rewrite H, valid_Src. rewrite BSETEQ21. unfold Bset.belongsto.
        split; intro.
        unfold construct_inj in J21. destruct plt.
        pattern b'. eapply Bset.inj_range'. inv INJ21; eauto. eauto. contradiction.
        unfold construct_inj in J21. destruct plt.
        pattern b. eapply Bset.inj_dom'. inv INJ21; eauto. eauto.
        exfalso. destruct init_mu as [_ [A _]]. inv J21. eapply A; unfold Bset.belongsto; eauto. }
      { intro b. rewrite BSETEQ23 in INJ23. inv GEREL. rewrite mu_shared_tgt in *.
        exploit construct_inj_total. exact INJ23. instantiate (1:= b). intros [b' J23].
        exploit mem_related_valid_block. exact MEMREL23. eauto. intro.
        rewrite H, valid_Tgt. rewrite BSETEQ23. unfold Bset.belongsto.
        split; intro.
        unfold construct_inj in J23. destruct plt.
        pattern b'. eapply Bset.inj_range'. inv INJ23; eauto. eauto. contradiction.
        unfold construct_inj in J23. destruct plt.
        pattern b. eapply Bset.inj_dom'. inv INJ23; eauto. eauto.
        exfalso. destruct init_mu as [_ [_ A]]. inv J23. eapply A; unfold Bset.belongsto; eauto. }
      {
        destruct mu as (j13, MUS, MUT). destruct mu_local as (j22, MUS', MUT').
        inv GEREL. simpl in *. subst MUS' MUT' MUS MUT.
        destruct init_mu as (INJ13 & NOOVERLAP1 & NOOVERLAP3). inv Binj. rename bmiw_inject into MEMINJ13.
        constructor.
        (* mi *)
        { constructor.
          { (* perm *)
            intros. unfold Bset.inj_to_meminj in H. destruct (j22 b1) eqn:?; inv H.
            exploit Consist2; eauto. intros (b1' & b2' & J21 & J23 & J13).
            rewrite <- mem_related_mem_perm_eq in H0; eauto;
              try eapply perm_kind_convert_eq; try eapply permission_convert_eq. 
            instantiate (1:= b1') in H0.
            eapply GMem.mi_perm in H0.
            instantiate (1:= 0) in H0. instantiate (1:= b2') in H0. instantiate (1:= tm) in H0.
            rewrite mem_related_mem_perm_eq in H0; eauto.
            unfold construct_inj. destruct plt. eauto. eapply Bset.inj_dom' in J23.
            exfalso; apply n. pattern b2. eapply J23. inv INJ23. eauto.
            eapply perm_kind_convert_eq. eapply permission_convert_eq.
            inv MEMINJ13. eauto.
            unfold Bset.inj_to_meminj. rewrite J13. auto.
            unfold construct_inj. destruct plt. auto.
            exfalso; apply n. pattern b1. eapply Bset.inj_dom' in J21. eauto. inv INJ21. eauto. } 
          { (* align *)
            intros. unfold Bset.inj_to_meminj in H. destruct (j22 b1); inv H.
            apply Z.divide_0_r. }
          { (* memval *)
            rewrite GENVDOMEQ in *. simpl in *.
            intros b1 ofs b2 delta J22 PERM1. unfold Bset.inj_to_meminj in J22.
            destruct (j22 b1) eqn:?; inv J22.
            exploit Consist2; eauto. intros (b1' & b2' & J21 & J23 & J13).
            (* by memrel21, GMem.perm sm b1' ofs Cur Readable *)
            assert (PERM1': GMem.perm sm b1' ofs (perm_kind_convert Max) (permission_convert Readable)).
            { eapply mem_related_mem_perm_eq; eauto; try constructor.
              exploit Bset.inj_dom'. inv INJ21; eauto. eauto. unfold Bset.belongsto. intros.
              unfold construct_inj. destruct plt; auto. contradiction. }
            (* by MEMINJ13, memval_inject j13 (b1', ofs) (b2', ofs) *)
            exploit GMem.mi_memval. inv MEMINJ13; eauto.
            unfold Bset.inj_to_meminj. rewrite J13. eauto. eauto.
            intros MEMVALINJ13.
            remember (fun b => Plt b (Genv.genv_next tge)) as S.
            remember (Injections.Build_Mu j22 S S) as lmu.
            remember (Injections.Build_Mu j13 S S) as mu.
            exploit (memval_inject_strict_memval_inject' j21 j23 mu lmu); try (subst; eauto; fail).
            econstructor; subst; eauto. subst. simpl in *.
            (* by memrel21 and memrel 23 *)
            assert (Hb1: Plt b1 (Genv.genv_next tge)).
            { destruct (plt b1 (Genv.genv_next tge)); eauto.
              inv INJ21. pattern b1. eapply Bset.inj_dom'; eauto. }
            exploit (mem_related_mem_val_inject j21); eauto.
            unfold construct_inj. destruct plt; eauto. contradiction.
            eapply mem_related_reach_closed in rc_shared_Src; eauto.
            generalize rc_shared_Src Hb1 INJ21 PERM1. clear. intros. inv H; try (constructor; fail).
            constructor. inv H2; try constructor.
            assert (Bset.belongsto (fun b => Plt b (Genv.genv_next tge)) b0).
            { apply rc_shared_Src. econstructor. instantiate (1:= ((b1, ofs1)::nil)).
              econstructor; eauto. constructor; auto. }
            unfold Bset.belongsto, Bset.inj_to_meminj, construct_inj in *.
            destruct plt; [|contradiction]. econstructor; eauto.

            assert (Hb2: Plt b2 (Genv.genv_next tge)).
            { destruct (plt b2 (Genv.genv_next tge)); eauto.
              inv INJ23. pattern b2. eapply Bset.inj_dom'; eauto. }
            assert (PERM2: Mem.perm ltm b2 ofs Max Readable).
            { eapply GMem.mi_perm in PERM1'.
              2: inv MEMINJ13; eauto.
              2: unfold Bset.inj_to_meminj; rewrite J13; eauto.
              rewrite Z.add_0_r in PERM1'.
              eapply mem_related_mem_perm_eq; eauto.
              unfold construct_inj. destruct plt; [auto|contradiction].
              apply perm_kind_convert_eq. apply permission_convert_eq. }
            exploit (mem_related_mem_val_inject j23); eauto.
            unfold construct_inj. destruct plt; eauto. contradiction.
            eapply mem_related_reach_closed in rc_shared_Tgt; eauto.
            generalize rc_shared_Tgt Hb2 INJ23 PERM2. clear. intros. rewrite Z.add_0_r.
            inv H; try (constructor; fail).
            constructor. inv H2; try constructor.
            assert (Bset.belongsto (fun b => Plt b (Genv.genv_next tge)) b1).
            { apply rc_shared_Tgt. econstructor. instantiate (1:= ((b2, _)::nil)).
              econstructor; eauto. constructor; auto. }
            unfold Bset.belongsto, Bset.inj_to_meminj, construct_inj in *.
            destruct plt; [|contradiction]. econstructor; eauto.
          }
        }
        (* mapped valid *)
        { intros.
          (* construct image of b in sm *)
          destruct (construct_inj_total _ _ sfl INJ21 b) as [b' J21'].
          unfold construct_inj in J21'. destruct plt.
          assert (p': Plt b' (Genv.genv_next sge)).
          { pattern b'. eapply Bset.inj_range'; eauto. inv INJ21. eauto. }
          rewrite <- valid_Src, <- mem_related_valid_block in p'.
          exfalso. apply H. eauto. eauto. unfold construct_inj. destruct plt;[auto|contradiction].
          (* don't care b outside of S *)
          unfold Bset.inj_to_meminj. destruct (j22 b) eqn:?; auto.
          apply Consist2 in Heqo. destruct Heqo as (b'' & b3' & J21 & J23 & J13).
          exfalso. apply n. pattern b. eapply Bset.inj_dom' in J21. eauto. inv INJ21. eauto.
        } 
        (* mapped valid' *)
        { intros. unfold Bset.inj_to_meminj in H. destruct (j22 b) eqn:J22; inv H.
          apply Consist2 in J22. destruct J22 as (b1 & b3 & J21 & J23 & J13).
          exploit (Bset.inj_dom' j23). inv INJ23; eauto. eauto.
          exploit (Bset.inj_range' j23). inv INJ23; eauto. eauto.
          unfold Bset.belongsto; intros Hb3 Hb'.
          eapply mem_related_valid_block; eauto. unfold construct_inj.
          destruct plt;[eauto|contradiction].
          apply valid_Tgt; auto.
        }
        (* inject no overlap *)
        { unfold Mem.meminj_no_overlap, Bset.inj_to_meminj.
          intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 H H0 H1 H2 H3.
          destruct (j22 b1) eqn:J22; inv H0. destruct (j22 b2) eqn:J22'; inv H1.
          left. apply Consist2 in J22. apply Consist2 in J22'.
          destruct J22 as (b1'' & b1''' & J21 & J23 & J13).
          destruct J22' as (b2'' & b2''' & J21' & J23' & J13').
          assert (NEQ:b1'' <> b2'').
          { intro. apply H. subst. eapply Bset.inj_injective. inv INJ21; eauto. eauto. eauto. }
          assert (NEQ':b1''' <> b2''').
          { intro. apply NEQ. subst. eapply (Bset.inj_injective j13). inv mu_inject; eauto. eauto. eauto. }
          intro. apply NEQ'. subst. rewrite J23 in J23'; inv J23'. auto.
        }
        (* representable *)
        { unfold Bset.inj_to_meminj. intros.
          destruct (j22 b) eqn:J22; inv H. split; [omega|].
          rewrite Z.add_0_r. apply Integers.Ptrofs.unsigned_range_2.
        }
        (* perm_inv *)
        { unfold Bset.inj_to_meminj. intros.
          destruct (j22 b1) eqn:J22; inv H. 
          apply Consist2 in J22. destruct J22 as (b1' & b2' & J21 & J23 & J13).
          cut (construct_inj j23 (Genv.genv_next tge) tfl b2 = Some b2'). intro J23'.
          cut (construct_inj j21 (Genv.genv_next sge) sfl b1 = Some b1'). intro J21'.
          rewrite <- (mem_related_mem_perm_eq j23 _ _ _ _ MEMREL23) in H0; eauto;
            try eapply perm_kind_convert_eq; try eapply permission_convert_eq.
          eapply GMem.mi_perm_inv in H0; eauto.
          2: unfold Bset.inj_to_meminj; rewrite J13; eauto.
          rewrite (mem_related_mem_perm_eq j21 _ _ _ _ MEMREL21) in H0; eauto;
            try eapply perm_kind_convert_eq; try eapply permission_convert_eq.
          rewrite (mem_related_mem_perm_eq j21 _ _ _ _ MEMREL21) in H0; eauto;
            try eapply perm_kind_convert_eq; try eapply permission_convert_eq.
          constructor. constructor.
          unfold construct_inj. destruct plt; auto. exfalso; apply n.
          pattern b1. eapply Bset.inj_dom'. inv INJ21. eauto. eauto.
          unfold construct_inj. destruct plt; auto. exfalso; apply n.
          pattern b2. eapply Bset.inj_dom'. inv INJ23. eauto. eauto.
        }
      }

      destruct GEREL.
      eapply Inj_lift_inject'; eauto. econstructor; eauto.
      auto.
    }
    
    specialize (INITSIM MEMINITREL').

    (* construct matching relation after rely *)
    intros sm' tm' HLRELY.
    exploit HLRely_Inj_lift.
    eapply mu_shared_src. eexact GEREL.
    rewrite GENVDOMEQ. eapply mu_shared_tgt; eauto.
    eexact sfl_norep. eexact tfl_norep.
    { unfold no_overlap; intros. intro.
      eapply sfl_free; eauto. unfold Bset.belongsto in *.
      apply valid_Src. inv GEREL. rewrite mu_shared_src. auto. }
    { unfold no_overlap; intros. rewrite GENVDOMEQ. intro.
      eapply tfl_free; eauto. unfold Bset.belongsto in *.
      apply valid_Tgt. inv GEREL. rewrite mu_shared_tgt. auto. }
    eauto. eauto. rewrite GENVDOMEQ. eauto.
    eapply Inv_localize; eauto. inversion Binj. eauto.
    rewrite GENVDOMEQ. eauto. eauto.
    intros (lsm' & ltm' & MEMREL21' & MEMREL23' & HLRELY').
    destruct (INITSIM lsm' ltm' HLRELY') as [i' MATCH22'].
    exploit (localize_rely _ _ _ _ _ _ SLocalize'); eauto.
    inv HLRELY. inv H. auto.
    exploit (lift_rely _ _ _ _ _ _ TLift'). eauto.
    inv HLRELY. inv H0. eauto. simpl. rewrite <- GENVDOMEQ. eapply MEMREL23'.
    intros MATCH32' MATCH12'.
    exists i'.
    split. tauto. split. tauto. split. auto. split. auto. split. auto.
    exists j21, j23, mu_local. do 4 (split; [auto|]). 
    econstructor; eauto. apply FPlocalize_emp. apply FPlocalize_emp. apply fpG_emp.
    
  - (* tau step *)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MATCH HSTEP HFPG.
    subst MATCHSTATE. invMS MATCH. subst. inv LIFTMATCH. clear Constr.
    assert (Hj23'':Bset.inject j23 (fun b : block => Plt b (Genv.genv_next tge_local))
                              (fun b => Plt b (Genv.genv_next tge))).
    { inv INJLIFT. inv TGEMATCH. rewrite BSETEQ23 in INJ23. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_tgt; eauto. }
    assert (Hj21'':Bset.inject j21 (fun b : block => Plt b (Genv.genv_next sge_local))
                               (fun b => Plt b (Genv.genv_next sge))).
    { inv INJLIFT. inv SGEMATCH. rewrite BSETEQ21 in INJ21. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_src; eauto. }
    specialize (SLocalize' Hj21''); specialize (TLift' Hj23'').
    (* localize src step *)
    inversion HFPG. rename H into HFPG'.

    pose proof (localize_lockstep _ _ _ _ _ _ SLocalize' sfl Hcore lsc Hm lsm
                                  Hfp' Hcore' Hm' MATCH12 HSTEP) as STEPLOCALIZE.
    assert (HFPG'': fpG sfl (fun b => Plt b (Genv.genv_next sge)) Hfp').
    { rewrite bset_eq_fpG; eauto.
      (* by config_ldsim, need modification TODO *)
      (* ????? why need modification??? - 2018-03-08 *)
      destruct SIM_local. exploit match_mu_ge; eauto. intro A; inv A.
      destruct SLocalize'. destruct localize_ge0.
      intro. erewrite ge_match_strict_next; eauto. inv INJLIFT. rewrite <- BSETEQ21. rewrite mu_shared_src. tauto. }
    specialize (STEPLOCALIZE HFPG'').
    destruct STEPLOCALIZE as
        (lfpS' & lsc' & lsm' & STEPLOCALIZE & FPLOCALIZE & MATCH12').

    (* construct local tgt step *)
    pose proof (match_tau_step _ _ _ _ _ _ _ SIM_local
                               _ _ _ _ _ _ _ _ _ _ _ MATCH22 STEPLOCALIZE
               ) as LSTEP_local.

    (* cases *)
    destruct LSTEP_local as [LSTEP_local | LSTEP_local].
    (* - no step *)
    left.
    destruct LSTEP_local as (i' & DECR_i' & MATCH22').
    exists i'. do 6 (split; [auto|]). exists j21, j23, mu_local. do 4 (split; [auto|]).
    econstructor; eauto; simpl in *.
    eapply (FPlocalize_union _ _ _ _ _ FPINJ12); eauto.
    (* - matched step *)
    right.
    destruct LSTEP_local as (i' & lfpT' & ltc' & ltm' & LSTEP_local & FPINJ22 & MATCH22').
    (* lift tgt step *)
    eapply lift_lockstep_plus in LSTEP_local; eauto.
    destruct LSTEP_local as (Lfp' & Lcore' & Lm' & PLUS & FPINJ32' & FPG' &  MATCH32').
    exists i', Lfp', Lcore', Lm'.
    split; auto.
    (** Could these assertions wrapped into lemmas or tactics? *)
    assert (FPINJ12'': FPlocalize (construct_inj j21 (Genv.genv_next sge) sfl) (FP.union Hfp Hfp') (FP.union lfpS lfpS')).
    { eapply FPlocalize_union; eauto. }
    assert (FPINJ32'': FPlocalize (construct_inj j23 (Genv.genv_next sge) tfl) (FP.union Lfp Lfp') (FP.union lfpT lfpT')).
    { eapply FPlocalize_union; eauto. rewrite GENVDOMEQ. auto. }
    assert (FPG'': fpG tfl (Injections.SharedTgt mu) (FP.union Lfp Lfp')).
    { eapply fpG_union; eauto.
      eapply bset_eq_fpG; eauto.
      intro b. rewrite Inj_lift_SharedTgt; eauto.
      rewrite local_ldsim_SharedTgt; eauto.
      erewrite <- ge_match_strict_next; eauto. split; eauto. }
    split. constructor.
    eapply FPlocalize_FPMatch; try eassumption. eapply wd_mu; eauto.
    apply construct_inj_incr. intros. inv GEINITINJ. pattern b. fold block. rewrite <- mu_shared_src.
    inv INJLIFT. inv INJ21. inv inj_weak. rewrite <- BSETEQ21. eapply inj_dom'; eauto.
    apply construct_inj_incr. intros. inv GEINITINJ. rewrite GENVDOMEQ. pattern b. fold block. rewrite <- mu_shared_tgt.
    inv INJLIFT. inv INJ23. inv inj_weak. rewrite <- BSETEQ23. eapply inj_dom'; eauto.
    auto.
    do 5 (split; [auto|]). exists j21, j23, mu_local. do 4 (split; [auto|]).
    econstructor; eauto.

  - (* * at_ext *)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MATCH ATEXT HG GARGS.
    inversion HG. clear HG. inversion H. clear H. rename H0 into SFPG. rename H1 into SCLOSED.
    subst. invMS MATCH. inv LIFTMATCH. simpl in *.
    assert (Hj23'':Bset.inject j23 (fun b : block => Plt b (Genv.genv_next tge_local))
                              (fun b => Plt b (Genv.genv_next tge))).
    { inv INJLIFT. inv TGEMATCH. rewrite BSETEQ23 in INJ23. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_tgt; eauto. }
    assert (Hj21'':Bset.inject j21 (fun b : block => Plt b (Genv.genv_next sge_local))
                               (fun b => Plt b (Genv.genv_next sge))).
    { inv INJLIFT. inv SGEMATCH. rewrite BSETEQ21 in INJ21. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_src; eauto. }
    specialize (SLocalize' Hj21''); specialize (TLift' Hj23'').
    
    pose proof (local_ldsim_SharedSrc _ _ _ _ _ _ _ _ _
                                      SIM_local _ _ _ _ _ _ _ MATCH22) as HSharedSrc.
    pose proof (Inj_lift_SharedSrc _ _ _ _ INJLIFT) as HSharedSrc'.
    pose proof (local_ldsim_SharedTgt _ _ _ _ _ _ _ _ _
                                      SIM_local _ _ _ _ _ _ _ MATCH22) as HSharedTgt.
    pose proof (Inj_lift_SharedTgt _ _ _ _ INJLIFT) as HSharedTgt'.
   

    exploit (localize_at_external _ _ _ _ _ _ SLocalize'); eauto.
    rewrite bset_eq_G_args. eauto.
    (** this routine occurs too often.. should be wrapped into a lemma or tactic *)
    intro. rewrite Inj_lift_SharedSrc; eauto.
    rewrite local_ldsim_SharedSrc; eauto. erewrite ge_match_strict_next; eauto. split; eauto.
    intros [args_local [L_ATEXT ARGS_LOCALIZED]].
    
    exploit (match_at_external _ _ _ _ _ _ _ SIM_local); eauto.
    exploit (localize_mem _ _ _ _ _ _ SLocalize'); eauto. intro.
    rewrite MemClosures.bset_eq_reach_closed in SCLOSED; eauto.
    erewrite <- ge_match_strict_next in HSharedSrc.
    rewrite MemClosures.bset_eq_reach_closed in SCLOSED; [|eapply HSharedSrc].
    eapply mem_related_reach_closed in SCLOSED; eauto.
    rewrite MemClosures_local.bset_eq_reach_closed_local; eauto. 
    destruct SLocalize'. destruct localize_ge0. eauto.
    eapply args_related_G_args_1; eauto.
    unfold Bset.belongsto. intros.
    
    eapply Inj_lift_j21_dom; eauto.
    intros (i' & args'_local & L_ATEXT' & ARGSREL & TCLOSED' & FPMATCH & INV & MATCH22').
    exists i'.
    exploit (lift_at_external _ _ _ _ _ _ TLift'); eauto.
    { inv SIM_local; simpl in *. apply wd_mu in MATCH22.
      revert GARGS ARGS_LOCALIZED ARGSREL MATCH22 HSharedTgt TGEMATCH. clear.
      intros. erewrite <- ge_match_strict_next in HSharedTgt; eauto. clear TGEMATCH.
      revert args_local args'_local ARGS_LOCALIZED ARGSREL.
      induction argSrc; intros; inv ARGS_LOCALIZED; inv ARGSREL; inv GARGS; constructor.
      destruct a; try contradiction; inv H1; inv H2; simpl; auto.
      apply HSharedTgt. eapply Bset.inj_range'; eauto using Bset.inj_weak.
      unfold Bset.inj_to_meminj in H. instantiate (1:= b1). destruct (Injections.inj mu_local b1).
      inv H. auto. discriminate.
      eapply IHargSrc; eauto. }
      
    intros (args' & ATEXT' & ARGS_LIFT).
    exists args'. split; auto.
    split.
    { generalize INJLIFT ARGS_LOCALIZED ARGSREL ARGS_LIFT; clear; intro.
      revert args_local args'_local args'. induction argSrc.
      intros l2 l2' l3 A B C. inv A; inv B; inv C. constructor.
      intros l2 l2' l3 A B C. inv A; inv B; inv C. constructor.
      inv H2; inv H1; inv H4; try constructor.
      unfold Bset.inj_to_meminj in *.
      destruct (j21 b0) eqn:A; inv H.
      destruct (j23 b4) eqn:B; inv H2.
      destruct (Injections.inj mu_local b0) eqn:C; inv H6.
      inv INJLIFT. exploit Consist2; eauto. intros (b2' & b4' & A' & B' & C').
      rewrite A in A'; inv A'. rewrite B in B'; inv B'.
      econstructor; eauto. rewrite C'. auto.
      eapply IHargSrc; eauto. }
    split.
    { constructor.
      constructor; auto. 
      erewrite MemClosures.bset_eq_reach_closed; eauto.
      destruct SIM_local. eapply match_mu_ge in MATCH22'; eauto. inv MATCH22'. rewrite mu_shared_tgt in TCLOSED'|- * .
      destruct TLift'. destruct lift_ge0. erewrite <- ge_match_strict_next in TCLOSED' |- *; eauto.
      eapply mem_related_reach_closed; eauto. 
      eapply FPlocalize_FPMatch; try eassumption. eapply wd_mu; eauto.
      apply construct_inj_incr. intros. inv GEINITINJ. pattern b. fold block. rewrite <- mu_shared_src.
      inv INJLIFT. inv INJ21. inv inj_weak. rewrite <- BSETEQ21. eapply inj_dom'; eauto.
      apply construct_inj_incr. intros. inv GEINITINJ. rewrite GENVDOMEQ. pattern b. fold block. rewrite <- mu_shared_tgt.
      inv INJLIFT. inv INJ23. inv inj_weak. rewrite <- BSETEQ23. eapply inj_dom'; eauto.
      generalize INV INJLIFT SLocalize' TLift' MATCH12 MATCH32 GENVDOMEQ; clear. intros.
      destruct TLift' as [_ _ _ lift_mem0 _ _ _ _ _ _]. apply lift_mem0 in MATCH32; clear lift_mem0.
      destruct SLocalize' as [_ _ _ localize_mem0 _ _ _ _ _ _]. apply localize_mem0 in MATCH12. clear localize_mem0.
      destruct sge, tge; simpl in *. subst.
      eapply Inv_localize'; eauto.
    }
    do 5 (split; [auto|]). exists j21, j23, mu_local. do 4 (split; [auto|]). econstructor; eauto.
    
  - (* after external *)
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MATCH GRES AFTEXT RESREL.
    subst. invMS MATCH. inv LIFTMATCH.
    assert (Hj23'':Bset.inject j23 (fun b : block => Plt b (Genv.genv_next tge_local))
                              (fun b => Plt b (Genv.genv_next tge))).
    { inv INJLIFT. inv TGEMATCH. rewrite BSETEQ23 in INJ23. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_tgt; eauto. }
    assert (Hj21'':Bset.inject j21 (fun b : block => Plt b (Genv.genv_next sge_local))
                               (fun b => Plt b (Genv.genv_next sge))).
    { inv INJLIFT. inv SGEMATCH. rewrite BSETEQ21 in INJ21. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_src; eauto. }
    specialize (SLocalize' Hj21''); specialize (TLift' Hj23'').

    exploit ores_rel_strict_lift; eauto.
    intros (ores_local & ores_local' & RESLOCALIZE & RESREL' & RESLIFT).
    
    exploit (localize_after_external _ _ _ _ _ _ SLocalize'); eauto.
    intros (lc' & L_AFTEXT & MATCH12').
    assert (GRES_local: G_oarg (Injections.SharedSrc mu_local) ores_local).
    { generalize GRES RESLOCALIZE INJLIFT. clear. intros.
      unfold G_oarg. destruct ores_local; auto.
      unfold oarg_related in RESLOCALIZE.
      destruct oresSrc. 
      exploit arg_related_G_arg_1; eauto. intros.
      exploit Inj_lift_j21_dom; eauto.
      contradiction. }
    exploit (match_after_external _ _ _ _ _ _ _ SIM_local); eauto.
    intros (ltc' & L_AFTEXT' & RELY22).
    exploit (lift_after_external _ _ _ _ _ _ TLift'); eauto.
    intros (tc' & AFTEXT' & MATCH23').
    exists tc'. split; auto.
    intros Hm' Lm' RELY.
    
    assert (HBound: Genv.genv_next sge = Genv.genv_next tge) by auto.

    exploit (localize_mem _ _ _ _ _ _ SLocalize'); eauto.
    exploit (lift_mem _ _ _ _ _ _ TLift'); eauto.
    intros T1 T2. exploit HLRely_Inj_lift.
    { inv INJLIFT. rewrite <- BSETEQ21.
      destruct SIM_local as [_ _ GEREL _ _ _ _ _ _]. apply GEREL in MATCH22. inv MATCH22.
      rewrite mu_shared_src.
      destruct SLocalize' as [[GEREL' _] _ _ _ _ _ _ _ _ _]. erewrite <- ge_match_strict_next; eauto. }
    { inv INJLIFT. rewrite <- BSETEQ23. simpl in *. rewrite HBound.
      destruct SIM_local as [_ _ GEREL _ _ _ _ _ _]. apply GEREL in MATCH22. inv MATCH22.
      rewrite mu_shared_tgt.
      destruct TLift' as [[GEREL' _] _ _ _ _ _ _ _ _ _]. erewrite <- ge_match_strict_next; eauto. }
    exact NOREP. exact NOREP'.
    erewrite <- mu_shared_src; eauto.
    simpl in *. erewrite HBound, <- mu_shared_tgt; eauto.
    eauto. eauto. simpl in *; rewrite HBound; eauto. eauto. eauto.
    intros (lHm' & lLm' & MEMREL21 & MEMREL23 & INV').
    inv RELY. inv H. inv H0.
    pose proof (localize_rely _ _ _ _ _ _ SLocalize' _ _ _ _ _ MATCH12' _ _ H3 MEMREL21).
    simpl in *. rewrite HBound in MEMREL23.
    pose proof (lift_rely _ _ _ _ _ _ TLift' _ _ _ _ _ MATCH23'  _ _ H5 MEMREL23).     
    exploit RELY22; eauto. intros (i' & MATCH22').
    exists i'. do 5 (split; [auto|]). exists j21, j23, mu_local. do 4 (split; [auto|]).
    econstructor; eauto. apply FPlocalize_emp. apply FPlocalize_emp. apply fpG_emp.

  - (* halt *)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MATCH HALT HGUAR GRES.
    subst. invMS MATCH. inv LIFTMATCH. simpl in *.
    assert (Hj23'':Bset.inject j23 (fun b : block => Plt b (Genv.genv_next tge_local))
                              (fun b => Plt b (Genv.genv_next tge))).
    { inv INJLIFT. inv TGEMATCH. rewrite BSETEQ23 in INJ23. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_tgt; eauto. }
    assert (Hj21'':Bset.inject j21 (fun b : block => Plt b (Genv.genv_next sge_local))
                               (fun b => Plt b (Genv.genv_next sge))).
    { inv INJLIFT. inv SGEMATCH. rewrite BSETEQ21 in INJ21. rewrite <- ge_match_strict_next0.
      erewrite <- mu_shared_src; eauto. }
    specialize (SLocalize' Hj21''); specialize (TLift' Hj23'').
    assert (HBound: Genv.genv_next sge = Genv.genv_next tge) by auto.
    assert (HS1: Injections.SharedSrc mu = (fun b => Plt b (Genv.genv_next sge))).
    { inv INJLIFT. rewrite <- BSETEQ21.
      destruct SIM_local as [_ _ GEREL _ _ _ _ _].
      apply GEREL in MATCH22. inv MATCH22. rewrite mu_shared_src.
      destruct SLocalize' as [[GEREL' _] _ _ _ _ _ _ _ _ _]. erewrite <- ge_match_strict_next; eauto. }
    assert (HS3: Injections.SharedTgt mu = (fun b => Plt b (Genv.genv_next tge))).
    { inv INJLIFT. rewrite <- BSETEQ23.
      destruct SIM_local as [_ _ GEREL _ _ _ _ _].
      apply GEREL in MATCH22. inv MATCH22. rewrite mu_shared_tgt.
      destruct TLift' as [[GEREL' _]  _ _ _ _ _ _ _ _ _]. erewrite <- ge_match_strict_next; eauto. }
    exploit (localize_halt _ _ _ _ _ _ SLocalize'); eauto.
    simpl in *. rewrite HS1 in GRES; auto.
    intros (lres & L_HALT & RESREL12).
    exploit (match_halt _ _ _ _ _ _ _ SIM_local); eauto.
    inv INJLIFT. rewrite BSETEQ21, HS1.
    inv HGUAR. inv H. rewrite HS1 in H1.
    eapply mem_related_reach_closed; eauto. destruct SLocalize' as [_ _ _ A _ _ _ _ _ _]; eauto. 
    eapply arg_related_G_arg_1; eauto.
    intros. inv INJLIFT. eapply Bset.inj_dom'; eauto. inv INJ21; eauto.
    intros (lres' & L_HALT' & RESREL22 & LCLOSED & FPMATCH & INV).
    exploit (lift_halt _ _ _ _ _ _ TLift'); eauto.
    { inv SIM_local; simpl in *. exploit match_mu_ge; eauto. intro. destruct H.
      apply wd_mu in MATCH22. erewrite ge_match_strict_next; eauto.
      revert GRES RESREL12 RESREL22 MATCH22 mu_shared_tgt. clear.
      intros. destruct resSrc; try contradiction; inv RESREL12; inv RESREL22; auto. simpl.
      rewrite <- mu_shared_tgt. eapply Bset.inj_range'; eauto using Bset.inj_weak.
      unfold Bset.inj_to_meminj in H1. instantiate (1:= b1). destruct (Injections.inj mu_local b1).
      inv H1. auto. discriminate. }
    intros (res' & HALT' & RESREL23).
    exists res'. simpl in *. split; auto.
    split.
    { generalize RESREL12 RESREL23 RESREL22 INJLIFT; clear. intros.
      inv RESREL12; inv RESREL22; inv RESREL23; try constructor.
      unfold Bset.inj_to_meminj in *.
      destruct (j21 b1) eqn:J21; inv H.
      destruct (j23 b3) eqn:J23; inv H3.
      destruct (Injections.inj mu_local b1) eqn:J22; inv H2.
      inv INJLIFT. apply Consist2 in J22. destruct J22 as (b2' & b4' & J21' & J23' & J13).
      rewrite J21 in J21'; inv J21'. rewrite J23 in J23'; inv J23'. 
      econstructor; eauto. unfold Bset.inj_to_meminj. rewrite J13; eauto. }
    constructor. constructor; auto.
    rewrite HS3. eapply mem_related_reach_closed.
    destruct TLift' as [_ _ _ A _ _ _ _ _ _]; eauto.
    inv INJLIFT. rewrite BSETEQ23, HS3 in LCLOSED. auto.
    eapply FPlocalize_FPMatch; try eassumption.
    destruct SIM_local as [_ _ GEREL _ _ _ _ _ _]. eapply mu_inject; eauto. 
    apply construct_inj_incr. intros. inv GEINITINJ. pattern b. fold block. rewrite <- mu_shared_src.
    inv INJLIFT. inv INJ21. inv inj_weak. rewrite <- BSETEQ21. eapply inj_dom'; eauto.
    apply construct_inj_incr. intros. inv GEINITINJ. rewrite GENVDOMEQ. pattern b. fold block. rewrite <- mu_shared_tgt.
    inv INJLIFT. inv INJ23. inv inj_weak. rewrite <- BSETEQ23. eapply inj_dom'; eauto.
    eapply Inv_localize'; eauto.
    eapply localize_mem; eauto.
    destruct TLift' as [_ _ _ lift_mem0 _ _ _ _ _ _]. apply lift_mem0 in MATCH32; clear lift_mem0.
    simpl in *. rewrite HBound. eauto.
Qed.

End SIM_LOCALIZE.

