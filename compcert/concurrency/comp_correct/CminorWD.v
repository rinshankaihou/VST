Require Import Coqlib FMemory GMemory Footprint FMemLemmas DetLemma InteractionSemantics CminorLang.

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

Section EVALDET.
  Lemma eval_expr_det:
    forall ge sp e m a v,
      eval_expr ge sp e m a v ->
      forall v', eval_expr ge sp e m a v' -> v = v'.
  Proof.
    induction 1; intros v' EVAL; inv EVAL; try congruence.
    apply IHeval_expr in H3. subst. congruence.
    apply IHeval_expr1 in H5. apply IHeval_expr2 in H7. subst. congruence.
    apply IHeval_expr in H3. subst. congruence.
  Qed.
  Lemma eval_expr_fp_det:
    forall ge sp e m a v,
      eval_expr_fp ge sp e m a v ->
      forall v', eval_expr_fp ge sp e m a v' -> v = v'.
  Proof.
    induction 1; intros v' EVAL; inv EVAL; try congruence.
    apply IHeval_expr_fp in H5. subst. congruence.
    apply IHeval_expr_fp1 in H10. apply IHeval_expr_fp2 in H12. subst.
    eapply eval_expr_det in H1;eauto. subst.
    eapply eval_expr_det in H;eauto. subst.
    rewrite H4 in H15. inv H15.
    congruence.
    apply IHeval_expr_fp in H7. subst.
    eapply eval_expr_det in H;eauto.
    subst. rewrite H1 in H8;inv H8.
    congruence.
  Qed.
      
  Lemma eval_exprlist_det:
    forall ge sp e m al vl,
      eval_exprlist ge sp e m al vl ->
      forall vl', eval_exprlist ge sp e m al vl' -> vl = vl'.
  Proof.
    induction al; intros vl1 EVAL1 vl2 EVAL2;
      inv EVAL1; inv EVAL2; auto.
    eapply IHal in H3; eauto. subst. exploit eval_expr_det. exact H1. exact H2. intro. subst. auto.
  Qed.

  Lemma eval_exprlist_fp_det:
    forall ge sp e m al vl,
      eval_exprlist_fp ge sp e m al vl ->
      forall vl', eval_exprlist_fp ge sp e m al vl' -> vl = vl'.
  Proof.
    induction al; intros vl1 EVAL1 vl2 EVAL2;
      inv EVAL1; inv EVAL2; auto.
    eapply IHal in H4; eauto. subst. exploit eval_expr_det. exact H1. exact H5. intro. subst. auto.
    f_equal.
    eapply eval_expr_fp_det;eauto.
  Qed.
End EVALDET.
Local Ltac solv_eq:=
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
Local Ltac eval_det:=
  repeat match goal with
         | H1: eval_expr ?a ?b ?c ?d ?e _, H2: eval_expr ?a ?b ?c ?d ?e _ |- _ =>
           eapply eval_expr_det in H1;try apply H2;subst
         | H1: eval_expr_fp ?a ?b ?c ?d ?e _, H2: eval_expr_fp ?a ?b ?c ?d ?e _ |- _ =>       eapply eval_expr_fp_det in H1;try apply H2;subst
         | H1: eval_exprlist ?a ?b ?c ?d ?e _, H2: eval_exprlist ?a ?b ?c ?d ?e _ |- _ =>     eapply eval_exprlist_det in H1;try apply H2;subst
         | H1: eval_exprlist_fp ?a ?b ?c ?d ?e _, H2: eval_exprlist_fp ?a ?b ?c ?d ?e _ |- _ =>     eapply eval_exprlist_fp_det in H1;try apply H2;subst
         end.
Local Ltac inv_eq:=
  repeat (try match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: Cminor.funsig _ |- _ => unfold Cminor.funsig in H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try (inversion H; fail)
         | H: false = true |- _ => inv H
         | H: true = false |- _ => inv H
         | H: None = Some _ |- _=> inv H
         | H: Some _ = Some _ |- _ => inv H
         | H: Some _ = None |- _=> inv H
         | H: Values.Val.bool_of_val _ _ |- _ => inv H
         | H:  Switch.switch_argument _  _ _ |- _ => inv H
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;try eval_det;simpl in *;subst;try contradiction).
Section DET.

  Lemma Cminor_det:
    lang_det CminorLang.
  Proof.
    unfold lang_det,step_det;intros.
    inversion H;subst. inversion H0;subst.
    inv H1.
    apply embed_eq in H3. subst.
    
    inv H2;inv H4;try solv_eq;try(Esimpl;eauto;fail);try(match goal with H:Cminor.is_call_cont _ |- _ => inv H end);try(inv_eq; Esimpl;eauto;fail).
Qed.    
End DET. 


Local Ltac emp_eff:=
  try (unfold FP.emp,effects;simpl;repeat rewrite Locs.emp_union_locs;repeat rewrite Locs.locs_union_emp;apply Locs.eq_refl).


Lemma Cminor_eff:
  corestep_local_eff (InteractionSemantics.step CminorLang).
Proof.
  unfold corestep_local_eff.
  intros.
  inv H. inv H0.
  inv H1;try apply LEffect_refl;try (rewrite FP.union_comm_eq;apply LEffect_union_fp);try (eapply mem_free_eff;eauto;fail);try (eapply mem_alloc_eff;eauto;fail);try(eapply mem_storev_eff;eauto;fail).
Qed.
Lemma eval_binop_fp_empeff:
  forall b v1 v2 m fp,
    eval_binop_fp b v1 v2 m = Some fp ->
    Locs.eq (effects fp) Locs.emp.
Proof.
  induction b;intros;inv H;inv_eq;subst;emp_eff;unfold cmpu_bool_fp_total;destruct v1,v2,Archi.ptr64;subst;auto;emp_eff.
  cmpu_bool_destruct_int_fp.
  cmpu_bool_destruct_int_fp.
  cmpu_bool_destruct_b_fp;destruct (Mem.valid_pointer m b0 (Integers.Ptrofs.unsigned i0));emp_eff;destruct Values.Val.cmp_different_blocks;emp_eff.
  all :inv H1;emp_eff.
Qed.
Lemma eval_expr_fp_empeff:
  forall ge sp e m a fp,
    eval_expr_fp ge sp e m a fp ->
    Locs.eq (effects fp) Locs.emp.
Proof.
  induction a;intros;inv H;emp_eff;try (eapply IHa;eauto;fail).
  
  eapply IHa1 in H4. eapply IHa2 in H6.
  do 2 rewrite effects_union.
  apply Locs.locs_eq in H4. apply Locs.locs_eq in H6.
  rewrite H4,H6,Locs.emp_union_locs.
  eapply eval_binop_fp_empeff;eauto.

  eapply IHa in H3. apply Locs.locs_eq in H3. 
  rewrite effects_union,H3,Locs.emp_union_locs.
  apply loadv_fp_emp_effects.
Qed.
Lemma MemPre_weak_valid_pointer_fp_eq:
  forall m b i m' fp,
    FMemOpFP.weak_valid_pointer_fp m b i = fp ->
    MemPre (strip m) (strip m') fp ->
    FMemOpFP.weak_valid_pointer_fp m' b i = fp.
Proof.
  intros. destruct H0 as [_ ? _].
  unfold FMemOpFP.weak_valid_pointer_fp in *;intros;inv_eq.
  erewrite unchanged_perm_cmp in Heqb0;try erewrite Heqb0;eauto.
  unfold FMemOpFP.weak_valid_pointer_fp. rewrite Heqb0;auto.
  
  simpl in CmpMemPermExists.
  erewrite unchanged_perm_cmp in Heqb0;try erewrite Heqb0;eauto.
  unfold FMemOpFP.weak_valid_pointer_fp. rewrite Heqb0;auto.
Qed.
Lemma MemPre_eval_binop_eq:
  forall b v1 v2 m v fp m',
    MemPre (strip m)(strip m') fp ->
    eval_binop b v1 v2 m = Some v->
    eval_binop_fp b v1 v2 m = Some fp ->
    eval_binop b v1 v2 m' = Some v /\ eval_binop_fp b v1 v2 m' = Some fp.
Proof.
  unfold eval_binop,eval_binop_fp.
  intros;inv_eq;auto.
  split.
  
  Focus 2.
  f_equal. 
  unfold cmpu_bool_fp_total in *.
  inv_eq;auto;try eapply MemPre_weak_valid_pointer_fp_eq;eauto.
  apply MemPre_split in H as [].
  eapply MemPre_weak_valid_pointer_fp_eq in H;eauto.
  eapply MemPre_weak_valid_pointer_fp_eq in H0;eauto.
  congruence.
  
  unfold cmpu_bool_fp_total in H; inv_eq;auto;try rewrite Heqb0 in H0;unfold option_map in *;inv_eq;try (destruct H as [_ ? _];erewrite unchanged_perm_cmp_valid_pointer in Heqb1;eauto;rewrite Heqb1;auto).
  apply MemPre_split in H as [[_ ? _][_ ? _]];do 2 (erewrite unchanged_perm_cmp_valid_pointer with(m:=m) in Heqb;eauto);rewrite Heqb;auto.
  apply MemPre_split in H as [[_ ? _][_ ? _]].
  do 2 (erewrite unchanged_perm_range_locset_1_valid_pointer with(m:=m) in Heqb0;eauto); rewrite Heqb0;auto.
Qed.
Lemma MemPre_eval_expr_eq:
  forall a ge sp e m v fp m',
    MemPre (strip m)(strip m') fp->
    FreelistEq (strip m)(strip m')(Mem.freelist m)->
    eval_expr ge sp e m a v ->
    eval_expr_fp ge sp e m a fp->
    eval_expr ge sp e m' a v /\ eval_expr_fp ge sp e m' a fp .
Proof.
  induction a;intros;inv H1;inv H2;try solv_eq;inv_eq;try(split;econstructor;eauto;fail);try solv_eq.
  {
    eapply IHa in H as ?;try apply H5;eauto.
    Hsimpl;Esimpl;eauto;econstructor;eauto.
  }
  {
    eapply MemPre_subset in H as ?;[|apply FP.union_subset].
    eapply MemPre_subset in H1 as ?;[|apply FP.union_subset].
    eapply MemPre_subset in H1;[|rewrite FP.union_comm_eq ;apply FP.union_subset].
    eapply MemPre_subset in H;[|rewrite FP.union_comm_eq ;apply FP.union_subset].

    eapply IHa1 in H2;eauto.
    eapply IHa2 in H1;eauto.
    Hsimpl.
    eapply MemPre_eval_binop_eq in H14 as ?;eauto.
    Hsimpl.
    Esimpl;eauto; econstructor;eauto.
  }
  {
    eapply MemPre_subset in H as ?;[|apply FP.union_subset].
    eapply MemPre_subset in H as ?;[|rewrite FP.union_comm_eq ;apply FP.union_subset].
    eapply IHa in H1 as ?;try apply H5;eauto.
    eapply MemPre_mem_loadv_eq2 in H7 as ?;eauto.

    Hsimpl;Esimpl;eauto;econstructor;eauto.
  }
Qed.
Lemma MemPre_eval_exprlist_eq:
  forall a ge sp e m v fp m',
    MemPre (strip m)(strip m') fp->
    FreelistEq (strip m)(strip m')(Mem.freelist m)->
    eval_exprlist ge sp e m a v ->
    eval_exprlist_fp ge sp e m a fp->
    eval_exprlist ge sp e m' a v /\ eval_exprlist_fp ge sp e m' a fp .
Proof.
  induction a;intros;inv H1;inv H2;try solv_eq;inv_eq.
  split;econstructor;eauto.
  apply MemPre_split in H as [].
  
  eapply MemPre_eval_expr_eq in H4 as [];try apply H6;eauto.
  eapply IHa in H0 as ?;eauto. Hsimpl.

  split;econstructor;eauto.
Qed.
Lemma eval_exprlist_fp_empeff:
  forall ge sp e m a fp,
    eval_exprlist_fp ge sp e m a fp ->
    Locs.eq (effects fp) Locs.emp.
Proof.
  induction a;intros. inv H;auto. emp_eff.
  inv H. eapply IHa in H5.
  rewrite effects_union. apply Locs.locs_eq in H5.
  rewrite H5,Locs.locs_union_emp.
  eapply eval_expr_fp_empeff;eauto.
Qed.
Lemma Cminor_loc1:
  corestep_locality_1 (InteractionSemantics.step CminorLang).
Proof.
  unfold corestep_locality_1.
  intros.
  inv H. inv H1.
  inv H0.
  set (fm1:= (combine m0 (Mem.freelist m1)(Mem.nextblockid m1)(FreelistEq_mem_fl_wd m1 m0 H1))).
  pose proof H1 as Fleq1. pose proof H as Memeq1.
  assert(Eq1:m0 = strip fm1). unfold fm1;rewrite strip_combine;auto.
  rewrite Eq1 in Fleq1,Memeq1.  clear Eq1. 
  inv H2;try (exists (strip fm1); split;[econstructor;eauto;[|econstructor;eauto]|split;eauto;apply MemPostemp];econstructor;eauto; unfold fm1; apply strip_combine;fail);try (match goal with H:Mem.free m1 _ _ _ = Some _ |- _ => eapply LPre_mem_free_LPost with(Fleq:=H1) in H;eauto end;Hsimpl;Esimpl;try apply LPost_comm;eauto;econstructor;eauto;try apply gmem_fl_wd_embed;econstructor;eauto;fail);try(eapply MemPre_eval_expr_eq in H0 as [];eauto;Esimpl;eauto;[|split;eauto;eapply MemPost_effect_emp;eapply eval_expr_fp_empeff;eauto];econstructor;eauto;[apply gmem_fl_wd_embed|econstructor;eauto];fail).

  {
    repeat apply MemPre_split in Memeq1 as [Memeq1 ?].
    eapply MemPre_eval_expr_eq in H0 as [];try apply H3;eauto.
    eapply MemPre_eval_expr_eq in H5 as [];try apply H0;eauto.
    
    eapply LPre_mem_storev_LPost with(Fleq:=Fleq1) in H6;eauto.
    Hsimpl. Esimpl.
    econstructor;eauto. Focus 2.
    econstructor;eauto.
    erewrite (combine_refl fm1),combine_equiv2;eauto.
    econstructor;eauto;unfold fm1;rewrite strip_combine;auto.
    destruct H10;split;auto.
    unfold MemPost. rewrite FP.union_comm_eq,effects_union.
    apply unchanged_content_union2;auto.
    rewrite effects_union;apply unchanged_content_union2;eapply MemPost_effect_emp;eapply eval_expr_fp_empeff;eauto.
  }
  {
    apply MemPre_split in Memeq1 as [Memeq1 Memeq2].
    eapply MemPre_eval_expr_eq in Memeq1 as [];eauto.
    eapply MemPre_eval_exprlist_eq in Memeq2 as [];eauto.
    eexists. split.
    econstructor;eauto. Focus 2. econstructor;eauto.
    constructor;eauto. unfold fm1. apply strip_combine.
    split;auto. apply MemPost_effect_emp.
    apply eval_expr_fp_empeff in H7. apply eval_exprlist_fp_empeff in H9.
    apply Locs.locs_eq in H7. apply Locs.locs_eq in H9. rewrite effects_union,H7,H9;apply Locs.union_refl.
  }
  {
    apply MemPre_split in Memeq1 as [Memeq1 Memeq2].
    apply MemPre_split in Memeq1 as [Memeq1 Memeq3].
    eapply MemPre_eval_expr_eq in Memeq1 as [];eauto.
    eapply MemPre_eval_exprlist_eq in Memeq3 as [];eauto.
    eapply LPre_mem_free_LPost with(Fleq:=Fleq1) in H8 as ?;eauto. Hsimpl.
    Esimpl;eauto.
    econstructor;eauto. Focus 2. econstructor;eauto.
    erewrite (combine_refl fm1),combine_equiv2,H11;eauto.
    econstructor;eauto. unfold fm1;apply strip_combine.
    apply LPost_comm in H12.
    destruct H12;split;auto.
    unfold MemPost.  do 2  rewrite effects_union.
    try apply unchanged_content_union2;auto.
    apply unchanged_content_union2. apply MemPost_effect_emp. eapply eval_expr_fp_empeff;eauto. apply MemPost_effect_emp. eapply eval_exprlist_fp_empeff;eauto.
  }
  {
    apply MemPre_split in Memeq1 as [Memeq1 Memeq2].
    eapply MemPre_eval_expr_eq in Memeq1 as [];eauto.
    eapply LPre_mem_free_LPost with(Fleq:=Fleq1) in H4 as ?;eauto. Hsimpl.
    Esimpl;eauto.
    econstructor;eauto. Focus 2. econstructor;eauto.
    erewrite (combine_refl fm1),combine_equiv2,H6;eauto.
    econstructor;eauto. unfold fm1;apply strip_combine.
    apply LPost_comm in H7.
    destruct H7;split;auto.
    unfold MemPost.  rewrite effects_union.
    try apply unchanged_content_union2;auto.
    apply MemPost_effect_emp. eapply eval_expr_fp_empeff;eauto.
  }
  {
    eapply MemPre_mem_alloc_LPost with(Fleq:=Fleq1) in H0;eauto.
    Hsimpl. Esimpl;eauto. econstructor;eauto;[|econstructor;eauto].
    econstructor;eauto. rewrite strip_combine;auto. unfold fm1. rewrite strip_combine;auto.
  }
Qed.
Theorem Cminor_wd: wd CminorLang.CminorLang.
Proof.
  constructor.
  (*forward*)
  {
    unfold corestep_forward.
    intros.
    inv H. inversion H0;subst;inv H1;try  apply GMem.forward_refl;try (eapply free_forward;eauto;fail).
    unfold Mem.storev in H5. ex_match.
    eapply store_forward;eauto.
    eapply alloc_forward;eauto.
  }
  (*eff*)
  apply Cminor_eff.
  (*loc1*)
  apply Cminor_loc1.
  (*loc2*)
  apply step_det_loc1_loc2.
  apply Cminor_det.
  apply Cminor_loc1.
  (*init*)
  unfold init_gmem_valid'.
  unfold init_gmem_valid'.
  intros. unfold init_gmem in H. simpl in H.
  unfold init_mem in H. inv H. inv H1. inv H2. eapply dom_match_fm;eauto.
  (*eqmem_eqstep*)
  apply eff_loc1_memeqcorestep.
  unfold step_mem_injc;intros.
  inv H. Esimpl;eauto.
  apply Cminor_eff.
  apply Cminor_loc1.
  (*core_not_ext*)
  {
    unfold corestep_not_at_external.
    intros.
    unfold CminorLang. simpl.
    unfold at_external.
    inv H. inv H1;inv_eq;auto.
  }
  (*core_not_halt*)
  {
    unfold corestep_not_halted.
    intros.
    unfold CminorLang,halt,halted.
    inv H;inv H1;inv_eq;auto.
  }
  (*ext_not_halt*)
  {
    unfold at_external_halted_excl.
    intros.
    unfold CminorLang,halt,halted;simpl.
    destruct q;simpl;auto.
  }
Qed.