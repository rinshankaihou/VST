
From iris_ora Require Import own algebra.frac_auth.
From iris Require Import proofmode.proofmode.
From diaframe Require Import proofmode_base.

(* ora version of diaframe/lib/own_hints *)

Class OraSubtract {A : ora} (a b : A) (φ : Prop) (c : option A) :=
ora_subtract : φ → default b (c' ← c; Some $ b ⋅ c') ≡ a.

Global Hint Mode OraSubtract ! ! ! - - : typeclass_instances.


Class UoraSubtract {A : uora} (a b : A) (φ : Prop) (c : A) :=
#[global] uora_subtract :: @OraSubtract A a b φ (Some c).

Global Hint Mode UoraSubtract ! ! ! - - : typeclass_instances.

Section base_instances_ora.
Context {A : ora}.

Global Instance ora_subtract_None (a : A) : OraSubtract a a True None | 50.
Proof. by rewrite /OraSubtract /=. Qed.

Global Instance ora_subtract_explicit_l (a b : A) : OraSubtract (a ⋅ b) a True (Some b) | 500.
Proof. by rewrite /OraSubtract /=. Qed.

Global Instance ora_subtract_explicit_r (a b : A) : OraSubtract (a ⋅ b) b True (Some a) | 500.
Proof. by rewrite /OraSubtract /= comm. Qed.
End base_instances_ora.

Global Instance biabd_ora_subtract {A : ora} `{!inG Σ A} (a b : A) γ φ mc :
OraSubtract a b φ mc →
  HINT own γ a ✱ [- ; <affine> ⌜φ⌝] ⊫ [id]; own γ b ✱ [match mc with | Some c => own γ c | None => emp%I end] | 41.
Proof.
  rewrite /OraSubtract => Hφ.
  iStep as (Hwit) "Hown".
  rewrite -Hφ //.
  destruct mc as [c|] => /=.
  - by rewrite own_op.
  - by rewrite right_id.
Qed.