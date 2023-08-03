From mathcomp.ssreflect Require Import fintype ssrnat.
Require Import Coqlib Maps Axioms.
Require Import InteractionSemantics.
Require Import ClightLang AsmLang SpecLang.


Definition NL : nat := 3.

Program Definition id0 : 'I_NL := @Ordinal NL 0 _.
Program Definition id1 : 'I_NL := @Ordinal NL 1 _.
Program Definition id2 : 'I_NL := @Ordinal NL 2 _.

Program Definition L (i: 'I_NL): Language :=
  if eqn i 0 then Clight_IS_2
  else if eqn i 1 then AsmLang
       else speclang.

Lemma L_sound_1: L id0 = Clight_IS_2. Proof. auto. Qed.
Lemma L_sound_2: L id1 = AsmLang. Proof. auto. Qed.
Lemma L_sound_3: L id2 = speclang. Proof. auto. Qed.

Lemma eq_ord: forall i:'I_NL,
    i = id0 \/ i = id1 \/ i = id2.
Proof.
  unfold id0, id1, id2.
  intro. destruct i.
  destruct m.
  left. cut (i = id0_obligation_1). intro; subst; auto.
  apply proof_irr.
  destruct m.
  right. cut (i = id1_obligation_1). intro; subst; auto.
  apply proof_irr.
  destruct m.
  right. cut (i = id2_obligation_1). intro; subst; auto.
  apply proof_irr.
  inversion i.
Qed.