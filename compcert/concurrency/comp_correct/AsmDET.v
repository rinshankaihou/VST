Require Import helpers Events InteractionSemantics AsmLang Coqlib FMemory FMemLemmas.
Local Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Local Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Ltac solv_eq:=
  match goal with
  | [H1: ?P , H2 : ?P |- _] => clear H1
  | [H1: ?P = _, H2: ?P = _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: ?P = _ , H2: _ = ?P |- _] =>
    rewrite H1 in H2; inv H2
(*  | [H1: _ = ?P, H2: _ = ?P |- _] =>
    rewrite <- H1 in H2; inv H2*)
  end
.
Ltac inv_eq:=
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try (inversion H; fail)
         | H: ?a _ = ?a _ |- _ => inv H
         | H: ?a _ _ = ?a _ _ |- _ => inv H
         | H: false = true |- _ => inv H
         | H: true = false |- _ => inv H
         | H: None = Some _ |- _=> inv H
         | H: Some _ = None |- _=> inv H
         | H: Stuck = Next _ _ |- _ => inv H
         | H: Next _ _ = Stuck |- _ => inv 
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;try contradiction.
           
Lemma embed_eq:
  forall fm m,
    embed (strip fm) (Mem.freelist fm) m ->
    m = fm.
Proof.
  destruct fm, m; intro; inv H. unfold strip in *; simpl in *.
  inv H1.
  assert (nextblockid = nextblockid0).
  { generalize valid_wd valid_wd0. clear. intros.
    destruct (Nat.lt_total nextblockid nextblockid0).
    eapply valid_wd0 in H; eauto. eapply valid_wd in H; eauto. omega.
    destruct H. auto.
    eapply valid_wd in H; eauto. eapply valid_wd0 in H; eauto. omega.
  }
  subst. f_equal; apply Axioms.proof_irr.
Qed.
Lemma extcall_arg_pair_fp_determ:
  forall rs a fp fp',
    ASM_local.extcall_arg_pair_fp rs a fp->
    ASM_local.extcall_arg_pair_fp rs a fp'->
    fp = fp'.
Proof.
  destruct a;intros;inv H;inv H0.
  inv H1;inv H2;auto.
  inv H3;inv H4;inv H2;inv H5;auto.
Qed.
Lemma extcall_arguments_fp_determ:
  forall rs sg fp1 fp2,
    ASM_local.extcall_arguments_fp rs sg fp1 ->
    ASM_local.extcall_arguments_fp rs sg fp2 ->
    fp1 = fp2.
Proof.
  unfold ASM_local.extcall_arguments_fp.
  intros rs sg.
  remember (Conventions1.loc_arguments sg) as a.
  clear sg Heqa.
  induction a; intros; inv H;inv H0;auto.
  
  eapply extcall_arg_pair_fp_determ in H3;eauto.
  subst.
  eapply IHa in H4;eauto.
  subst. auto.
Qed.
Lemma extcall_arguments_determ:
  forall rs m sg res res',
    extcall_arguments rs m sg res->
    extcall_arguments rs m sg res'->
    res = res'.
Proof.
  unfold extcall_arguments.
  intros.
  remember (Conventions1.loc_arguments sg) as a.
  clear sg Heqa.
  revert rs m res res' H H0  .
  induction a;intros. inv H;inv H0;auto.
  
  inv H. inv H0.
  eapply IHa in H5;eauto. subst.
  f_equal.
  clear H6.
  inv H2;inv H3;auto. inv H;inv H1;auto. solv_eq;auto.
  inv H;inv H0;inv H4;inv H6;inv_eq;auto.
Qed.
Lemma eval_builtin_args_fp_determ:
  forall A ge rs i args fp1 fp2,
    @MemOpFP.eval_builtin_args_fp A ge rs i args fp1->
    MemOpFP.eval_builtin_args_fp ge rs i args fp2->
    fp1 = fp2.
Proof.
  induction args;intros.
  inv H;inv H0;auto.
  
  inv H;inv H0.
  assert(forall A ge rs i a fp fp',
            @MemOpFP.eval_builtin_arg_fp A ge rs i a fp ->
            MemOpFP.eval_builtin_arg_fp ge rs i a fp'->
            fp = fp').
  clear.
  induction a;intros;inv H;inv H0;auto.
  eapply IHa1 in H3;eauto. eapply IHa2 in H4;eauto.
  subst;auto.
  
  eapply H in H3;eauto.
  subst. eapply IHargs in H4;eauto. subst;auto.
Qed.
Lemma i64ext_sem_determ:
  forall  (ge : Globalenvs.Senv.t) a b res res',
    i64ext_sem a b res->
    i64ext_sem a b res'->
    res = res'.
Proof.
  intros.
  pose i64ext_det.
  apply i64ext_extcall in H as [].
  apply i64ext_extcall in H0 as [].
  specialize (H1 ge Memory.Mem.empty).
  specialize (H2 ge Memory.Mem.empty).
  eapply i64ext_det in H1 as [?[]];eauto.
Qed.
Theorem Asm_det: lang_det AsmLang.
Proof.
  unfold lang_det,step_det.
  intros.
  inv H.
  inv H0.
  inv H1. apply embed_eq in H. subst.
  inv H3;inv H2;inv_eq;inv_eq;auto.
(*  {
    unfold ASM_local.lock_prefixed in H13.
    ex_match2;try contradiction.
  } *)
  {
    eapply eval_builtin_args_determ in H13;try apply H5;subst.
    eapply eval_builtin_args_fp_determ in H6;eauto;subst.
    Esimpl;eauto.
    eapply i64ext_sem_determ in H7;eauto.
    subst;auto.
    apply (Globalenvs.Genv.to_senv ge).
  }
  {
    eapply extcall_arguments_fp_determ in H4 ;eauto;subst.
    eapply extcall_arguments_determ in H1;eauto.
    subst. auto.
  }

  {
    Esimpl;eauto. f_equal. f_equal. f_equal.
    eapply i64ext_sem_determ;eauto.
    apply (Globalenvs.Genv.to_senv ge).
  }
(*  {
    unfold ASM_local.lock_prefixed in *.
    ex_match2;try contradiction.
  } *)
Qed.