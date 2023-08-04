Require Import Coqlib Lia.
Require Import List.

Definition dom (B: positive) : list positive :=
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

Lemma incl_length_lt:
  forall B pl,
    (forall p, In p pl -> Plt p B) ->
    NoDup pl ->
    (length pl < Pos.to_nat B)%nat.
Proof.
  intros.
  cut (length pl <= Pos.to_nat B - 1)%nat. lia.
  rewrite <- dom_length.
  apply NoDup_incl_length; auto.
  unfold incl. intros. apply H in H1. apply dom_correct; auto.
Qed.