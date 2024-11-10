Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.

(* This file contains two parts:
   1. Proof of semax_conseq.
   2. Deriving simpler and older version of consequence rules from semax_conseq.
   3. semax_extract_pre, and proof of semax_adapt_frame rules from semax_conseq, and 2 specializations of semax_adapt_frame. *)

(* Part 1: Proof of semax_conseq *)

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty}.

Lemma fupd_fupd_andp_prop : forall E P (Q : assert), (|={E}=> (⌜P⌝ ∧ |={E}=> Q)) ⊣⊢ (|={E}=> (⌜P⌝ ∧ Q)).
Proof.
  intros; iSplit; iIntros "H".
  - iMod "H" as "[$ $]".
  - iMod "H" as "[$ $]"; done.
Qed.

(* After deep embedded hoare logic (SL_as_Logic) is ported, maybe the frame does not need to be
   quantified in the semantic definition of semax. *)

(*Lemma assert_safe_fupd':
  forall gx vx tx E (P: assert) Delta f k rho,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := ⌜guard_environ Delta f rho⌝ in
    let PP2 := funassert Delta rho in
    (PP1 ∧ P rho ∗ PP2 -∗ assert_safe OK_spec gx E f vx tx k rho) ⊣⊢
    (PP1 ∧ (|={E}=> P rho) ∗ PP2 -∗ assert_safe OK_spec gx E f vx tx k rho).
Proof.
  intros.
  iSplit.
  * iIntros "H (% & P & ?)".
    iApply assert_safe_fupd; first done; iMod "P"; iApply "H"; auto.
    by iFrame.
  * iIntros "H (% & P & ?)"; iApply "H"; auto.
    by iFrame.
Qed.

Lemma assert_safe_fupd:
  forall gx vx tx rho E (F P: assert) Delta f k,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := ⌜guard_environ Delta f rho⌝ in
    let PP2 := funassert Delta rho in
    (PP1 ∧ (F ∗ P) rho ∗ PP2 -∗
    assert_safe OK_spec gx E f vx tx k rho) ⊣⊢
    (PP1 ∧ (F ∗ |={E}=> P) rho ∗ PP2 -∗
    assert_safe OK_spec gx E f vx tx k rho).
Proof.
  intros.
  iSplit.
  * iIntros "H (% & P & ?)".
    rewrite (assert_safe_fupd' _ _ _ _ (F ∗ P)); last done.
    iApply "H"; iFrame "%"; iFrame.
    monPred.unseal; by iDestruct "P" as "($ & >$)".
  * iIntros "H (% & P & ?)"; iApply "H"; iFrame.
    iFrame "%"; monPred.unseal; by iDestruct "P" as "($ & $)".
Qed. *)

Lemma fupd_fupd_frame_l : forall E (P Q : assert), (|={E}=> (P ∗ |={E}=> Q)) ⊣⊢ |={E}=> (P ∗ Q).
Proof.
  intros; iSplit.
  - by iIntros ">[$ >$]".
  - by iIntros ">[$ $]".
Qed.

(*Lemma proj_fupd_ret_assert_frame: forall E F Q ek vl,
  (|={E}=> (F ∗ proj_ret_assert (fupd_ret_assert E Q) ek vl)) ⊣⊢ |={E}=> (F ∗ proj_ret_assert Q ek vl).
Proof.
  intros.
  destruct ek; simpl; auto;
    rewrite -fupd_fupd_frame_l fupd_fupd_andp_prop fupd_fupd_frame_l; auto.
Qed.

Global Instance guard_proper ge E Delta f : Proper (equiv ==> eq ==> equiv) (_guard OK_spec ge E Delta f).
Proof.
  intros ????? ->; rewrite /_guard.
  do 7 f_equiv.
  by rewrite H.
Qed.

Global Instance guard'_proper ge E Delta f : Proper (equiv ==> eq ==> equiv) (guard' OK_spec ge E Delta f).
Proof.
  solve_proper.
Qed.

Global Instance rguard_proper ge E Delta f : Proper (equiv ==> eq ==> equiv) (rguard OK_spec ge E Delta f).
Proof.
  intros ????? ->; rewrite /rguard.
  do 3 f_equiv; intros ?.
  apply guard_proper; last done.
  destruct H as (? & ? & ? & ?).
  destruct a; simpl; last done; f_equiv; done.
Qed.

Global Instance frame_ret_assert_proper : Proper (equiv ==> equiv ==> equiv) frame_ret_assert.
Proof.
  intros [????] [????] (? & ? & ? & ?); repeat intro; simpl in *.
  split3; last split; simpl; intros; f_equiv; done.
Qed. *)

Global Instance frame_ret_assert_proper : Proper (equiv ==> equiv ==> equiv) frame_ret_assert.
Proof.
  intros [] [] (H1 & H2 & H3 & H4) ?? HP; split; [|split3]; simpl in *; intros; rewrite HP.
  - rewrite H1 //.
  - rewrite H2 //.
  - rewrite H3 //.
  - rewrite H4 //.
Qed.

Global Instance semax_proper {CS} E Delta : Proper (equiv ==> eq ==> equiv ==> iff) (semax(CS := CS) OK_spec E Delta).
Proof.
  repeat intro; subst.
  rewrite !semax_unfold.
  split; intros.
  - iIntros "TY F B" (?) "H".
    rewrite -H -H1; iApply (H0 with "TY F B"); eauto.
  - iIntros "TY F B" (?) "H".
    rewrite H H1; iApply (H0 with "TY F B"); eauto.
Qed.

Lemma typecheck_environ_sub' : forall Delta Delta', tycontext_sub Delta Delta' ->
  local (typecheck_environ Delta') ⊢ local (typecheck_environ Delta).
Proof.
  split => rho /=.
  by apply bi.pure_mono, typecheck_environ_sub.
Qed.

Lemma semax'_conseq {CS: compspecs}:
 forall E Delta P' (R': ret_assert) P c (R: ret_assert),
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   (|={E}=> P')) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_normal R') ⊢
                   (|={E}=> RA_normal R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_break R') ⊢
                   (|={E}=> RA_break R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_continue R') ⊢
                   (|={E}=> RA_continue R)) ->
   (forall vl, local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_return R' vl) ⊢
                   (|={E}=> RA_return R vl)) ->
   semax' OK_spec E Delta P' c R' ⊢ semax' OK_spec E Delta P c R.
Proof.
  intros.
  rewrite /semax'.
  iIntros "H" (??? [??]).
  iIntros "#TY F #B" (?) "P".
  iDestruct (funassert_allp_fun_id_sub' with "F") as "(#? & F)"; first done.
  iDestruct (typecheck_environ_sub' with "TY") as "?"; first done.
  iMod (H with "[P]"); first by auto.
  rewrite -wp_conseq; first by iApply ("H" with "[%] [] [$] [] [$]").
  all: destruct R, R'; simpl in *.
  - iIntros "(R & #TY & F)".
    iDestruct (funassert_allp_fun_id_sub' with "F") as "(#? & F)"; first done.
    iDestruct (typecheck_environ_sub' with "TY") as "?"; first done.
    iMod (H0 with "[R]") as "$"; auto.
  - iIntros "(R & #TY & F)".
    iDestruct (funassert_allp_fun_id_sub' with "F") as "(#? & F)"; first done.
    iDestruct (typecheck_environ_sub' with "TY") as "?"; first done.
    iMod (H1 with "[R]") as "$"; auto.
  - iIntros "(R & #TY & F)".
    iDestruct (funassert_allp_fun_id_sub' with "F") as "(#? & F)"; first done.
    iDestruct (typecheck_environ_sub' with "TY") as "?"; first done.
    iMod (H2 with "[R]") as "$"; auto.
  - intros; iIntros "(R & #TY & F)".
    iDestruct (funassert_allp_fun_id_sub' with "F") as "(#? & F)"; first done.
    iDestruct (typecheck_environ_sub' with "TY") as "?"; first done.
    iMod (H3 with "[R]") as "$"; auto.
Qed.

Lemma semax_conseq {CS: compspecs}:
 forall E Delta P' (R': ret_assert) P c (R: ret_assert) ,
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   (|={E}=> P') ) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_normal R') ⊢
                   (|={E}=> RA_normal R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_break R') ⊢
                   (|={E}=> RA_break R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_continue R') ⊢
                   (|={E}=> RA_continue R)) ->
   (forall vl, local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_return R' vl) ⊢
                   (|={E}=> RA_return R vl)) ->
   semax OK_spec E Delta P' c R' ->  semax OK_spec E Delta P c R.
Proof.
  intros.
  eapply bi.bi_emp_valid_mono, H4; apply semax'_conseq; auto.
Qed.

(* Part 2: Deriving simpler and older version of consequence rules from semax_conseq. *)
Lemma semax'_post_fupd:
 forall {CS: compspecs} (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, local (typecheck_environ Delta) ∧
                proj_ret_assert R' ek vl
         ⊢ |={E}=> proj_ret_assert R ek vl) ->
   semax' OK_spec E Delta P c R' ⊢ semax' OK_spec E Delta P c R.
Proof.
intros.
apply semax'_conseq; [by iIntros "(_ & _ & $)" | ..]; intros.
- specialize (H EK_normal None); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; iIntros "(? & _ & $)"; auto.
- specialize (H EK_break None); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; iIntros "(? & _ & $)"; auto.
- specialize (H EK_continue None); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; iIntros "(? & _ & $)"; auto.
- specialize (H EK_return vl); simpl in H.
  rewrite -H; iIntros "(? & _ & $)"; auto.
Qed.

Lemma semax'_post:
 forall {CS: compspecs} (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, local (typecheck_environ Delta) ∧
                proj_ret_assert R' ek vl
         ⊢ proj_ret_assert R ek vl) ->
   semax' OK_spec E Delta P c R' ⊢ semax' OK_spec E Delta P c R.
Proof.
intros.
apply semax'_post_fupd.
by intros; iIntros "? !>"; iApply H.
Qed.

Lemma semax'_pre_fupd:
 forall {CS: compspecs} (P' : assert) E Delta R (P : assert) c,
  (forall rho, typecheck_environ Delta rho -> P rho ⊢ |={E}=> (P' rho)) -> 
  semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R.
Proof.
intros.
apply semax'_conseq; intros; [| by iIntros "(_ & _ & $)"..].
split => ?; monPred.unseal; iIntros "(% & _ & ?)"; iApply H; auto.
Qed.

Lemma semax'_pre:
 forall {CS: compspecs} (P': assert) E Delta R (P: assert) c,
  (forall rho, typecheck_environ Delta rho -> P rho ⊢ P' rho) ->
  semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R.
Proof.
intros; apply semax'_pre_fupd.
by intros; iIntros "? !>"; iApply H.
Qed.

Lemma semax'_pre_post_fupd:
 forall
      {CS: compspecs} (P' : assert) (R': ret_assert) E Delta (R: ret_assert) (P: assert) c,
   (forall rho, typecheck_environ Delta rho -> P rho ⊢ |={E}=> (P' rho)) ->
   (forall ek vl, local (typecheck_environ Delta)
                       ∧  proj_ret_assert R ek vl
                    ⊢ |={E}=> proj_ret_assert R' ek vl) ->
   semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R'.
Proof.
intros.
rewrite semax'_pre_fupd; last done.
apply semax'_post_fupd; auto.
Qed.

Lemma semax'_pre_post:
 forall
      {CS: compspecs} (P': assert) (R': ret_assert) E Delta (R: ret_assert) (P: assert) c,
   (forall rho, typecheck_environ Delta rho -> P rho ⊢ P' rho) ->
   (forall ek vl, local (typecheck_environ Delta)
                       ∧  proj_ret_assert R ek vl
                    ⊢ proj_ret_assert R' ek vl) ->
   semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R'.
Proof.
intros.
rewrite semax'_pre; last done.
apply semax'_post; auto.
Qed.

Lemma semax_post'_fupd {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, local (typecheck_environ Delta)
                      ∧  proj_ret_assert R' ek vl
                        ⊢ |={E}=> proj_ret_assert R ek vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post_fupd; auto.
Qed.

Lemma semax_post_fupd {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ |={E}=> RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ |={E}=> RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ |={E}=> RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ |={E}=> RA_return R vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post_fupd; eauto.
destruct ek; intros; simpl;
  ((iIntros "(? & -> & ?)"; rewrite -> bi.pure_True by done; rewrite bi.True_and) || iIntros "(? & ?)"); [rewrite -H | rewrite -H0 | rewrite -H1 | rewrite -H2]; auto.
Qed.

Lemma semax_post' {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, local (typecheck_environ Delta)
                      ∧  proj_ret_assert R' ek vl
                        ⊢ proj_ret_assert R ek vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post; auto.
Qed.

Lemma semax_post {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post; auto.
destruct ek; simpl; auto; intros;
  iIntros "(? & -> & ?)"; rewrite -> bi.pure_True by done; rewrite bi.True_and; [rewrite -H | rewrite -H0 | rewrite -H1]; auto.
Qed.

Lemma semax_pre_fupd {CS: compspecs} :
 forall P' E Delta P c R,
   (local (typecheck_environ Delta) ∧ P ⊢ |={E}=> P') ->
     semax OK_spec E Delta P' c R  -> semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_pre_fupd; auto.
intros; inversion H as [H']. revert H'; monPred.unseal; intros <-; auto.
Qed.

Lemma semax_pre {CS: compspecs} :
 forall P' E Delta P c R,
   (local (typecheck_environ Delta) ∧ P ⊢ P') ->
     semax OK_spec E Delta P' c R  -> semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_pre; auto.
intros; inversion H as [H']; revert H'; monPred.unseal; intros <-; auto.
Qed.

Lemma semax_pre_post_fupd {CS: compspecs}:
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
   (local (typecheck_environ Delta) ∧ P ⊢ |={E}=> P') ->
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ |={E}=> RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ |={E}=> RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ |={E}=> RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ |={E}=> RA_return R vl) ->
   semax OK_spec E Delta P' c R' ->  semax OK_spec E Delta P c R.
Proof.
intros.
eapply semax_pre_fupd; eauto.
eapply semax_post_fupd; eauto.
Qed.

Lemma semax_pre_post {CS: compspecs}:
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
   (local (typecheck_environ Delta) ∧ P ⊢ P') ->
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax OK_spec E Delta P' c R' ->  semax OK_spec E Delta P c R.
Proof.
intros.
eapply semax_pre; eauto.
eapply semax_post; eauto.
Qed.

Lemma semax_fupd_elim {CS: compspecs}:
 forall E Delta P c R,
  semax OK_spec E Delta P c R -> semax OK_spec E Delta (|={E}=> P) c R.
Proof.
intros; eapply semax_pre_fupd, H.
by intros; rewrite bi.and_elim_r.
Qed.

Lemma semax_skip {CS: compspecs}:
   forall E Delta P, semax OK_spec E Delta P Sskip (normal_ret_assert P).
Proof.
intros.
apply derives_skip.
intros.
rewrite /= bi.pure_True // left_id //.
Qed.

(*Taken from floyd.SeparationLogicFacts.v*)
Lemma semax_extract_prop:
  forall {CS: compspecs},
  forall E Delta (PP: Prop) (P:assert) c (Q:ret_assert),
           (PP -> semax OK_spec E Delta P c Q) ->
           semax OK_spec E Delta (⌜PP⌝ ∧ P) c Q.
Proof.
  intros.
  eapply semax_pre with (∃ H: PP, P).
  + intros; iIntros "(? & %HPP & ?)"; iExists HPP; auto.
  + apply extract_exists_pre, H.
Qed.

Lemma semax_adapt_frame {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   ∃ F: mpred, (|={E}=> (P' ∗ ⎡F⎤) ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_normal (frame_ret_assert Q' ⎡F⎤) ⊢ |={E}=> RA_normal Q⌝ ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_break (frame_ret_assert Q' ⎡F⎤) ⊢ |={E}=> RA_break Q⌝ ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_continue (frame_ret_assert Q' ⎡F⎤) ⊢ |={E}=> RA_continue Q⌝ ∧
                         ⌜forall vl, local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_return (frame_ret_assert Q' ⎡F⎤) vl ⊢ |={E}=> RA_return Q vl⌝))
   (SEM: semax(CS := cs) OK_spec E Delta P' c Q'):
   semax OK_spec E Delta P c Q.
Proof.
  intros.
  eapply semax_conseq; [| by intros; iIntros "(_ & _ & $)" .. |].
  { by intros; iIntros "? !>"; iApply (H with "[-]"). }
  apply extract_exists_pre. intros F. clear H.
  eapply semax_pre_fupd. { iIntros "(_ & $)". }
  rewrite bi.and_comm -!bi.pure_and. apply semax_extract_prop; intros (? & ? & ? & ?).
  eapply semax_conseq, semax_frame, SEM; eauto.
  by iIntros "(_ & _ & $ & $)".
Qed.

Lemma semax_adapt_frame' {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   ∃ F: mpred, (|={E}=> (P' ∗ ⎡F⎤) ∧
                         ⌜RA_normal (frame_ret_assert Q' ⎡F⎤) ⊢ |={E}=> RA_normal Q⌝ ∧
                         ⌜RA_break (frame_ret_assert Q' ⎡F⎤) ⊢ |={E}=> RA_break Q⌝ ∧
                         ⌜RA_continue (frame_ret_assert Q' ⎡F⎤) ⊢ |={E}=> RA_continue Q⌝ ∧
                         ⌜forall vl, RA_return (frame_ret_assert Q' ⎡F⎤) vl ⊢ |={E}=> RA_return Q vl⌝))
   (SEM: semax(CS := cs) OK_spec E Delta P' c Q'):
   semax OK_spec E Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame, SEM.
  rewrite H.
  do 4 f_equiv.
  iIntros "(% & % & % & %)"; iPureIntro; split; [|split3]; intros; rewrite /bi_affinely bi.and_elim_r bi.and_elim_l left_id; auto.
Qed.

Lemma semax_adapt {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   (|={E}=> P' ∧
                        ⌜RA_normal Q' ⊢ |={E}=> RA_normal Q⌝ ∧
                        ⌜RA_break Q' ⊢ |={E}=> RA_break Q⌝ ∧
                        ⌜RA_continue Q' ⊢ |={E}=> RA_continue Q⌝ ∧
                        ⌜forall vl, RA_return Q' vl ⊢ |={E}=> RA_return Q vl⌝))
   (SEM: semax(CS := cs) OK_spec E Delta P' c Q'):
   semax OK_spec E Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame'; eauto. intros. rewrite H; rewrite -(bi.exist_intro emp).
  do 2 f_equiv.
  { rewrite embed_emp bi.sep_emp //. }
  iIntros "(% & % & % & %)"; iPureIntro; split; [|split3]; intros; destruct Q'; simpl; rewrite embed_emp bi.sep_emp //.
Qed.

End mpred.
