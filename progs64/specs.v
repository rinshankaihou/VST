From iris.bi Require Export bi telescopes derived_laws.
From diaframe.symb_exec Require Import defs weakestpre.
From diaframe Require Export spec_notation.
From diaframe Require Import proofmode_base.
From diaframe.lib Require Import iris_hints.
Require Import VST.veric.SeparationLogic VST.floyd.proofauto.

Require Import VST.floyd.base.
Require Import VST.floyd.canon.

Import bi.
Import LiftNotation.

Unset Universe Polymorphism.

Section clight_instances.
  Context  `{!default_VSTGS Σ}.
  
Definition wp (cs:compspecs) (E:coPset) (Delta: tycontext) (c: statement) (Q: ret_assert): assert :=
  ∃ P: assert, ⌜@semax _ _ _ _ cs E Delta P c Q⌝ ∧ P.

Definition

  
  Open Scope expr_scope.

  Global Instance semax_load_wp E (Delta: tycontext) sh id P e1 t2 (v2: val):
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    (local (tc_environ Delta) ∧ P ⊢ 
      <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    SPEC {{ 
      (* (▷ (tc_lvalue Delta e1 ∧
                ⌜tc_val (typeof e1) v2⌝ ∧
                P)) *)
                True
          }}
      (Sset id e1)
      {{ r, RET r; True }}.
      (* {{ normal_ret_assert (∃ old:val, local (`eq (eval_id id) (`v2)) ∧
                                      assert_of (subst id (`old) P)) }}. *)

  

