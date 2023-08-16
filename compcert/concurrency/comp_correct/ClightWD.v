Require Import Values Coqlib Clight GMemory FMemory FMemLemmas Footprint InteractionSemantics  Cop_fp ClightLang DetLemma.
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
    eapply valid_wd0 in H; eauto. eapply valid_wd in H; eauto. Lia.lia.
    destruct H. auto.
    eapply valid_wd in H; eauto. eapply valid_wd0 in H; eauto. Lia.lia.
  }
  subst. f_equal; apply Axioms.proof_irr.
Qed.
Local Ltac solv_eq:=
  match goal with
  | [H1: ?P , H2 : ?P |- _] => clear H1
  | [H1: ?P = _, H2: ?P = _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: ?P = _ , H2: _ = ?P |- _] =>
    rewrite H1 in H2; inv H2
  | H: Vptr _ _ = Vptr _ _ |- _=> inv H
  end
.

Local Ltac inv_eq:=
  repeat (try match goal with
              | H:?P , H1: ?P |- _ => clear H
              | H: Cminor.funsig _ |- _ => unfold Cminor.funsig in H
              | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try (inversion H; fail)
              | H: None = Some _ |- _=> inv H
              | H: Some _ = Some _ |- _ => inv H
              | H: Some _ = None |- _=> inv H
              | H: Values.Val.bool_of_val _ _ |- _ => inv H
              | H:  Switch.switch_argument _  _ _ |- _ => inv H
              | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
              | H:?P = ?Q |- context [ ?P ] => rewrite H 
              end;simpl in *;subst;try contradiction;try discriminate).

Ltac inv_expr:=try  match goal with H: eval_expr _ _ _ _ _ _|- _ => inv H end;repeat solv_eq;auto.
Ltac check_lvalue:= try (repeat match goal with H:eval_lvalue _ _ _ _ _ _ _ |- _ => inv H end;fail).
Ltac inv_lvalue:= repeat (match goal with H:eval_lvalue _ _ _ _ _ _ _|- _ => inv H end;repeat solv_eq);auto.
Ltac lvalue_det:=
  match goal with
  |  H1: eval_lvalue ?ge ?e ?le ?m ?a ?loc ?ofs ,
         H2: eval_lvalue ?ge ?e ?le ?m ?a ?loc' ?ofs',
             H3: eval_lvalue ?ge ?e ?le ?m ?a ?loc ?ofs->
                 forall loc0 ofs0,
                   eval_lvalue ?ge ?e ?le ?m ?a loc0 ofs0->
                   loc0 = ?loc /\ ofs0 = ?ofs
                   |- _ => eapply H3 in H2 as [];eauto
  end;subst;try congruence.
Ltac expr_det:=
  match goal with
  |  H1: eval_expr ?ge ?e ?le ?m ?a ?v,
         H2: forall v',
         eval_expr ?ge ?e ?le ?m ?a v'->
         ?v2 = v'
         |- _ => eapply H2 in H1;eauto
  end;subst;try congruence.
Lemma deref_loc_det:
  forall ty m loc ofs v,
    deref_loc ty m loc ofs v ->
    forall v',
      deref_loc ty m loc ofs v'->
      v = v'.
Proof.
  inversion 1;subst;inversion 1;subst;repeat solv_eq;auto.
Qed.
Ltac solv_deref_loc_det:=
  match goal with
    H: deref_loc ?ty ?m ?loc ?ofs ?v,
       H':deref_loc ?ty ?m ?loc ?ofs' ?v'|- _ =>
    eapply deref_loc_det in H';try apply H;subst
  end.
Lemma eval_expr_det:
  forall ge e le m a v1,
    eval_expr ge e le m a v1 ->
    forall v2,
      eval_expr ge e le m a v2 ->
      v1 = v2.
Proof.
  intros until 1.
  pattern a,v1.

  eapply eval_expr_ind2
    with(ge:=ge)(e:=e)(le:=le)(m:=m)
        (P0:=(fun a loc' ofs'=> 
                eval_lvalue ge e le m a loc' ofs'->
                forall loc ofs,
                  eval_lvalue ge e le m a loc ofs ->
                  loc = loc' /\ ofs = ofs'))
  ;eauto;intros.
  all : try(inv_expr;try lvalue_det;try expr_det;inv_lvalue;fail).
  try(inv_expr;check_lvalue; repeat expr_det).
  inv_expr;check_lvalue; repeat expr_det;repeat lvalue_det;try eapply deref_loc_det;eauto.
  all: inv_lvalue;repeat (expr_det;solv_eq;auto).
Qed.
Ltac solv_expr_det:=
  match goal with
    H1: eval_expr ?ge ?e ?le ?m ?a ?v, H2 : eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
    eapply eval_expr_det in H2;try apply H1;subst
  end.
Lemma eval_lvalue_det:
  forall ge e le m a loc ofs,
    eval_lvalue ge e le m a loc ofs->
    forall loc' ofs',
      eval_lvalue ge e le m a loc' ofs' ->
      loc = loc' /\ ofs = ofs'.
Proof.
  induction 1;intros;inv_lvalue;try solv_expr_det;try solv_eq;auto.
Qed.
Ltac solv_lvalue_det:=
  match goal with
    H1: eval_lvalue ?ge ?e ?le ?m ?a ?l ?o ,
        H2 : eval_lvalue ?ge ?e ?le ?m ?a ?l' ?o' |- _ =>
    eapply eval_lvalue_det in H2 as [];try apply H1;subst
  end.
Ltac inv_exprfp:=try  match goal with H: eval_expr_fp _ _ _ _ _ _|- _ => inv H end;repeat solv_eq;auto.
Ltac check_lvaluefp:= try (repeat match goal with H:eval_lvalue_fp _ _ _ _ _ _ _ |- _ => inv H end;fail).
Ltac inv_lvaluefp:= repeat (match goal with H:eval_lvalue_fp _ _ _ _ _ _|- _ => inv H end;repeat solv_eq);auto.
Ltac lvaluefp_det:=
  match goal with
  |  H1: eval_lvalue_fp ?ge ?e ?le ?m ?a ?fp,
         H2: eval_lvalue_fp ?ge ?e ?le ?m ?a ?fp',
             H3: eval_lvalue_fp ?ge ?e ?le ?m ?a ?fp->
                 forall fp,
                   eval_lvalue_fp ?ge ?e ?le ?m ?a fp->
                   ?fp = fp
                   |- _ => eapply H3 in H2;eauto
  end;subst;try congruence.
Ltac expr_fp_det:=
  match goal with
  |  H1: eval_expr_fp ?ge ?e ?le ?m ?a ?v,
         H2: forall v',
         eval_expr_fp ?ge ?e ?le ?m ?a v'->
         ?v2 = v'
         |- _ => eapply H2 in H1;eauto
  end;subst;try congruence.
Lemma deref_loc_fp_det:
  forall ty b ofs fp,
    deref_loc_fp ty b ofs fp->
    forall fp',
      deref_loc_fp ty b ofs fp'->
      fp = fp'.
Proof. intros;inv H;inv H0;solv_eq;auto. Qed.
Ltac solv_deref_loc_fp_det:=
  match goal with
    H: deref_loc_fp ?ty ?b ?ofs ?fp,
       H': deref_loc_fp ?ty ?b ?ofs ?fp' |- _ =>
    eapply deref_loc_fp_det in H';try apply H;subst
  end.
Lemma eval_expr_fp_det:
  forall ge e le m a fp,
    eval_expr_fp ge e le m a fp ->
    forall fp',
      eval_expr_fp ge e le m a fp'->
      fp = fp'.
Proof.
  intros until 1.
  pattern a,fp.
  eapply eval_expr_fp_ind2
    with(ge:=ge)(e:=e)(le:=le)(m:=m)
        (P0:= fun a0 fp0 =>
                eval_lvalue_fp ge e le m a0 fp0 ->
                forall fp',
                  eval_lvalue_fp ge e le m a0 fp'->
                  fp0 = fp')
  ;eauto;intros.
  all: try (inv_exprfp;inv_lvalue;fail).
  all: try (inv_exprfp;check_lvalue;repeat solv_expr_det;repeat solv_lvalue_det;repeat expr_fp_det;repeat lvaluefp_det;repeat solv_deref_loc_det;repeat solv_deref_loc_fp_det;auto;fail).
  inv H1;auto.
  inv_lvaluefp.
  inv_lvaluefp.
Qed.    

Ltac solv_expr_fp_det:=
  match goal with
    H1: eval_expr_fp ?ge ?e ?le ?m ?a ?v, H2 : eval_expr_fp ?ge ?e ?le ?m ?a ?v2 |- _ =>
    eapply eval_expr_fp_det in H2;try apply H1;subst
  end.


Lemma eval_lvalue_fp_det:
  forall ge e le m a fp,
    eval_lvalue_fp ge e le m a fp ->
    forall fp',
      eval_lvalue_fp ge e le m a fp'->
      fp = fp'.
Proof.
  inversion 1;subst;inversion 1;subst;auto.
  all : solv_expr_det;solv_expr_fp_det;auto.
Qed.
Ltac solv_lvalue_fp_det:=
  match goal with
    H1: eval_lvalue_fp ?ge ?e ?le ?m ?a ?v, H2 : eval_lvalue_fp ?ge ?e ?le ?m ?a ?v2 |- _ =>
    eapply eval_lvalue_fp_det in H2;try apply H1;subst
  end.
Lemma assign_loc_det:
  forall ce ty m b ofs v m',
    assign_loc ce ty m b ofs v m'->
    forall m'',
      assign_loc ce ty m b ofs v m''->
      m' = m''.
Proof. intros;inv H;inv H0;repeat solv_eq;auto. Qed.
Ltac solv_assign_loc_det:=
  match goal with
    H1: assign_loc ?ce ?ty ?m ?b ?ofs ?v _,
        H2 : assign_loc ?ce ?ty ?m ?b ?ofs ?v _ |- _ =>
    eapply assign_loc_det in H2;try apply H1;subst
  end.
Lemma assign_loc_fp_det:
  forall ce ty m b ofs fp,
    assign_loc_fp ce ty m b ofs fp->
    forall fp',
      assign_loc_fp ce ty m b ofs fp'->
      fp = fp'.
Proof. intros;inv H;inv H0;repeat solv_eq;auto. Qed.
Ltac solv_assign_loc_fp_det:=
  match goal with
    H1: assign_loc_fp ?ce ?ty ?m ?b ?ofs _,
        H2 : assign_loc_fp ?ce ?ty ?m ?b ?ofs _ |- _ =>
    eapply assign_loc_fp_det in H2;try apply H1;subst
  end.
Lemma eval_exprlist_det:
  forall ge e le m a vl v1,
    eval_exprlist ge e le m a  vl v1->
    forall v2,
      eval_exprlist ge e le m a vl v2->
      v1 = v2.
Proof.
  induction 1;intros.
  inv H;auto.
  inv H2. solv_expr_det.
  eapply IHeval_exprlist in H10;eauto. subst.
  solv_eq. auto.
Qed.
Ltac solv_exprlist_det:=
  match goal with
    H1: eval_exprlist ?ge ?e ?le ?lm ?a ?vl _,
        H2 : eval_exprlist ?ge ?e ?le ?m ?a ?vl _ |- _ =>
    eapply eval_exprlist_det in H2;try apply H1;subst
  end.
Lemma eval_exprlist_fp_det:
  forall ge e le m a vl v1,
    eval_exprlist_fp ge e le m a  vl v1->
    forall v2,
      eval_exprlist_fp ge e le m a vl v2->
      v1 = v2.
Proof.
  induction 1;intros.
  inv H;auto.
  inv H5.
  solv_expr_det.
  solv_expr_fp_det.
  eapply IHeval_exprlist_fp in H15;eauto. subst.
  solv_eq. auto.
Qed.
Ltac solv_exprlist_fp_det:=
  match goal with
    H1: eval_exprlist_fp ?ge ?e ?le ?lm ?a ?vl _,
        H2 : eval_exprlist_fp ?ge ?e ?le ?m ?a ?vl _ |- _ =>
    eapply eval_exprlist_fp_det in H2;try apply H1;subst
  end.  

Lemma alloc_variables_det:
  forall ge env m f e m',
    alloc_variables ge env m f e m'->
    forall e' m'',
      alloc_variables ge env m f e' m''->
      e = e' /\  m' = m''.
Proof.
  induction 1;intros.
  inv H;auto.
  inv H1. solv_eq.
  eapply IHalloc_variables in H10;eauto.
Qed.
Ltac solv_alloc_variables_det:=
  match goal with
    H1: alloc_variables ?ge ?e  ?lm ?f _ _,
        H2 : alloc_variables ?ge ?e ?lm ?f _ _ |- _ =>
    eapply alloc_variables_det in H2 as [];try apply H1;subst
  end.  
Lemma alloc_variables_fp_det:
  forall ge  m f  m',
    alloc_variables_fp ge  m f m'->
    forall m'',
      alloc_variables_fp ge  m f  m''->
      m' = m''.
Proof.
  induction 1;intros.
  inv H;auto.
  inv H2. solv_eq. solv_eq.
  eapply IHalloc_variables_fp in H10;subst. auto.
Qed.
Ltac solv_alloc_variables_fp_det:=
  match goal with
    H1: alloc_variables_fp ?ge ?e  ?lm _,
        H2 : alloc_variables_fp ?ge ?e ?lm _ |- _ =>
    eapply alloc_variables_fp_det in H2;try apply H1;subst
  end.
Ltac solv_det:=
  repeat solv_expr_det;repeat solv_eq;repeat solv_expr_fp_det;repeat solv_eq;
  repeat solv_lvalue_det;repeat solv_eq;repeat solv_lvalue_fp_det;repeat solv_eq;
  repeat solv_assign_loc_det;repeat solv_eq;repeat solv_assign_loc_fp_det;repeat solv_eq;
  repeat solv_deref_loc_det;repeat solv_eq;repeat solv_deref_loc_fp_det;repeat solv_eq;
  repeat solv_exprlist_det;repeat solv_eq;repeat solv_exprlist_fp_det;repeat solv_eq;
  repeat solv_alloc_variables_det;repeat solv_eq;repeat solv_alloc_variables_fp_det;repeat solv_eq.
Theorem Clight_det2: lang_det Clight_IS_2.
Proof.
  unfold lang_det,step_det,Clight_IS_2;simpl;intros.
  inv H;inv H0;inv H1. apply embed_eq in H;subst.
  pose proof H2 as STEP1;pose proof H3 as STEP2.
  inv H2;inv H3;repeat (solv_det;auto).
  all: try (match goal with
              H: _ \/ _ |- _=> destruct H as [R|R];inv R
            end;fail).
  all: try match goal with H:is_call_cont _ |- _ => inv H end.
  inv H;inv H0;inv H9;inv H10;solv_det;auto.
Qed.

Lemma bind_parameters_det:
  forall ge e p m v m1 m2,
    bind_parameters ge e m p v m1 ->
    bind_parameters ge e m p v m2 ->
    m1 = m2.
Proof.        
  induction p;intros;inv H;inv H0;auto.
  solv_eq. solv_det.
  eapply IHp in H8;eauto.
Qed.
Lemma function_entry1_det:
  forall ge f v m e le m' m2 e2 le2,
    function_entry1 ge f v m e le m'->
    function_entry1 ge f v m e2 le2 m2->
    e = e2 /\ le = le2 /\  m' = m2.
Proof.
  intros.
  inv H. inv H0.
  solv_det. 
  eapply bind_parameters_det in H3;try apply H5;eauto.
Qed.
Lemma bind_parameters_fp_det:
  forall ge e p m m1 m2,
    bind_parameters_fp ge e m p m1 ->
    bind_parameters_fp ge e m p m2 ->
    m1 = m2.
Proof.        
  induction p;intros;inv H;inv H0;auto.
  solv_eq. solv_det.
  eapply IHp in H7;eauto. subst.
  auto.
Qed.
Lemma function_entry1_fp_det:
  forall ge f v m e m' m2,
    function_entry1_fp ge f v m e m'->
    function_entry1_fp ge f v m e m2->
    m' = m2.
Proof.
  intros.
  inv H. inv H0.
  solv_det.
  eapply bind_parameters_fp_det in H3;try apply H2;eauto.
  subst;auto.
Qed.

Theorem Clight_det:lang_det Clight_IS.
Proof.
  
  unfold lang_det,step_det,Clight_IS_2;simpl;intros.
  
  inv H;inv H0;inv H1. apply embed_eq in H;subst.
  inv H2;inv H3;repeat (solv_det;auto).
  all: try (match goal with
              H: _ \/ _ |- _=> destruct H as [R|R];inv R
            end;fail).
  all: try match goal with H:is_call_cont _ |- _ => inv H end.
  eapply function_entry1_det in H as (?&?&?);eauto;subst.
  eapply function_entry1_fp_det in H0 ;eauto;subst;auto.
Qed.
Lemma assign_loc_eff:
  forall ge ty m loc ofs v m' fp,
    assign_loc ge ty m loc ofs v m'->
    assign_loc_fp ge ty loc ofs v fp ->
    LEffect (strip m)(strip m') fp (Mem.freelist m).
Proof.
  intros.
  inv H;inv H0;solv_eq.
  eapply mem_storev_eff;eauto.
Qed.
Lemma mem_freelist_eff:
  forall b m m',
    Mem.free_list m b = Some m'->
    LEffect (strip m)(strip m')(FMemOpFP.free_list_fp b)(Mem.freelist m).
Proof.
  induction b;intros.
  inv H. apply LEffect_refl.
  simpl in H.
  ex_match;subst.
  eapply IHb in H.
  eapply mem_free_eff in Hx1 as ?.
  eapply mem_free_fleq in Hx1.
  simpl. 
  eapply LEffect_trans_union;eauto.
  rewrite Hx1;auto.
Qed.
Lemma alloc_variables_eff:
  forall ge e l e0 m0 m'0 fp,
    alloc_variables_fp ge m0 l fp ->
    alloc_variables ge e0 m0 l e m'0 ->
    LEffect (strip m0) (strip m'0) fp (Mem.freelist m0).
Proof.
  induction l;intros;inv H;inv H0. apply LEffect_refl.
  solv_eq.
  eapply IHl in H7;eauto.
  apply mem_alloc_fleq in H3 as ?.
  apply mem_alloc_eff in H3.
  eapply LEffect_trans_union;eauto.
  rewrite H;auto.
Qed.
Lemma assign_loc_fleq:
  forall ge ty m b o v m',
    assign_loc ge ty m b o v m'->
    Mem.freelist m = Mem.freelist m'.
Proof.
  intros.
  inv H. eapply mem_storev_fleq in H1;eauto.
Qed.
Lemma bind_parameters_eff:
  forall ge e l m vargs m' fp,
    bind_parameters ge e m l vargs m'->
    bind_parameters_fp ge e l vargs fp ->
    LEffect (strip m)(strip m') fp (Mem.freelist m).
Proof.
  induction l; intros. inv H. apply LEffect_refl.
  inv H. inv H0.
  eapply IHl in H11;eauto.
  solv_eq.
  apply assign_loc_fleq in H5 as ?.
  eapply assign_loc_eff in H5;eauto.
  eapply LEffect_trans_union;eauto.
  rewrite H;auto.
Qed.
Lemma alloc_variables_fleq:
  forall ge p e a m m',
    alloc_variables ge e m p a m'->
    Mem.freelist m = Mem.freelist m'.
Proof.
  induction p;intros.
  inv H;auto.
  inv H. eapply IHp in H7;eauto.
  apply mem_alloc_fleq in H4.
  congruence.
Qed.
Lemma Clight_eff:corestep_local_eff (InteractionSemantics.step Clight_IS).
Proof.
  unfold corestep_local_eff.
  intros.
  inv H. inv H0. inv H1.
  all: try apply LEffect_refl.
  eapply assign_loc_eff in H7;eauto;rewrite FP.union_comm_eq;apply LEffect_union_fp;auto.
  eapply mem_freelist_eff;eauto.
  all : try eapply mem_freelist_eff;eauto.
  eapply mem_freelist_eff in H2;rewrite FP.union_comm_eq;apply LEffect_union_fp;auto.
  inv H;inv H0.
  apply alloc_variables_fleq in H2 as ?.
  eapply alloc_variables_eff in H2;eauto.
  eapply bind_parameters_eff in H3;eauto.
  eapply LEffect_trans_union;eauto.
  congruence.
Qed.
Lemma Clight_eff_2: corestep_local_eff (InteractionSemantics.step Clight_IS_2).
Proof.
  unfold corestep_local_eff.
  intros.
  inv H. inv H0. inv H1.
  all: try apply LEffect_refl.
  eapply assign_loc_eff in H7;eauto;rewrite FP.union_comm_eq;apply LEffect_union_fp;auto.
  eapply mem_freelist_eff;eauto.
  all : try eapply mem_freelist_eff;eauto.
  eapply mem_freelist_eff in H2;rewrite FP.union_comm_eq;apply LEffect_union_fp;auto.
  inv H;inv H0.
  eapply alloc_variables_eff;eauto.
Qed.
Lemma deref_loc_loc:
  forall ty m loc ofs v fp,
    deref_loc ty m loc ofs v ->
    deref_loc_fp ty loc ofs fp ->
    forall m',
      MemPre (strip m)(strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m) ->
      deref_loc ty m' loc ofs v.
Proof.
  intros. 
  inv H0;inv H;solv_eq.
  eapply MemPre_mem_loadv_eq2 in H4;eauto. econstructor;eauto.
  econstructor 2;eauto. econstructor 3;eauto.
Qed.
Lemma sem_unary_operation_loc:
  forall op v ty m fp v1,
    FCop.sem_unary_operation op v ty m = Some v1->
    sem_unary_operation_fp op v ty m = Some fp->
    forall m',
      MemPre (strip m)(strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      FCop.sem_unary_operation op v ty m' = Some v1 /\
      sem_unary_operation_fp op v ty m' = Some fp.
Proof.
  unfold FCop.sem_unary_operation,sem_unary_operation_fp.
  intros;ex_match2;inv_eq;auto.
  unfold FCop.sem_notbool,sem_notbool_fp in *.
  unfold FCop.bool_val,bool_val_fp in *.
  ex_match;inv_eq;auto.
  unfold Mem.weak_valid_pointer in *.
  erewrite unchanged_perm_cmp_valid_pointer,Heqb0.
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto.

  inversion H1 as [_ ? _].
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto.
  apply unchanged_perm_comm;auto.
Qed.
Lemma sem_cast_loc:
  forall v ty f m res fp,
    FCop.sem_cast v ty f m = Some res ->
    sem_cast_fp v ty f m = Some fp ->
    forall m',
      MemPre (strip m)(strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      FCop.sem_cast v ty f m' = Some res /\
      sem_cast_fp v ty f m' = Some fp.
Proof.
  unfold FCop.sem_cast,sem_cast_fp;intros;ex_match;inv_eq;auto.
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto.
  unfold Mem.weak_valid_pointer in *.
  erewrite unchanged_perm_cmp_valid_pointer,Hx2;auto.
  inversion H1 as [_ ? _].
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto.
  apply unchanged_perm_comm;auto.
Qed.
Lemma sem_binarith_loc:
  forall a b c d v ty v' ty' m f1 fp,
    FCop.sem_binarith a b c d v ty v' ty' m = Some f1->
    sem_binarith_fp a b c d v ty v' ty' m = Some fp ->
    forall m',
      MemPre (strip m)(strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      FCop.sem_binarith a b c d v ty v' ty' m' = Some f1/\
      sem_binarith_fp a b c d v ty v' ty' m' = Some fp.
Proof.
  unfold FCop.sem_binarith,sem_binarith_fp;intros;ex_match;inv_eq.
  all: apply MemPre_split in H1 as [];eapply sem_cast_loc in Hx as [];eauto;rewrite H1, H3;eapply sem_cast_loc in Hx1 as [];eauto;rewrite H4,H5,Hx6;auto.
Qed.
Lemma cmp_ptr_loc:  
  forall c v v' res fp m,
    FCop.cmp_ptr m c v v' = Some res ->
    cmp_ptr_fp m c v v' = Some fp ->
    forall m',
      MemPre (strip m)(strip m') fp->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      FCop.cmp_ptr m' c v v' = Some res /\
      cmp_ptr_fp m' c v v'=Some fp.
Proof.
  unfold FCop.cmp_ptr,cmp_ptr_fp;intros;ex_match.
  unfold Val.cmpu_bool,cmpu_bool_fp in *;ex_match;inv_eq;auto.
  all: try(erewrite unchanged_perm_cmp_valid_pointer,Heqb1;eauto;[erewrite LPre_weak_valid_pointer_fp_eq2;eauto|inversion H1 as [_ ? _];erewrite LPre_weak_valid_pointer_fp_eq2;eauto;apply unchanged_perm_comm;auto];fail).

  destruct ((Mem.valid_pointer m b0 (Integers.Ptrofs.unsigned i)|| Mem.valid_pointer m b0 (Integers.Ptrofs.unsigned i - 1))) eqn:?;inv Heqb.
  apply MemPre_split in H1 as [].
  erewrite unchanged_perm_cmp_valid_pointer,Heqb0,unchanged_perm_cmp_valid_pointer,H0;eauto.
  simpl. split;auto. do 2 (erewrite LPre_weak_valid_pointer_fp_eq2 with(m:=m)(m':=m');eauto).
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto;destruct H1;auto;apply unchanged_perm_comm;auto.
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto;destruct H;apply unchanged_perm_comm;auto.

  apply MemPre_split in H1 as [[_ ? _][_ ? _]].
  do 2 erewrite unchanged_perm_range_locset_1_valid_pointer with(m:=m)(m':=m') in Heqb2;eauto.
  rewrite Heqb2;auto.
Qed.
Lemma sem_cmp_loc:
  forall c v ty v' ty' m v1 fp,
    FCop.sem_cmp c v ty v' ty' m = Some v1 ->
    sem_cmp_fp c v ty v' ty' m = Some fp->
    forall m',
      MemPre (strip m)(strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      FCop.sem_cmp c v ty v' ty' m' = Some v1 /\
      sem_cmp_fp c v ty v' ty' m' = Some fp.
Proof.
  unfold FCop.sem_cmp,sem_cmp_fp;intros;ex_match;inv_eq;auto.
  all: try eapply cmp_ptr_loc;eauto.
  eapply sem_binarith_loc;eauto.
Qed.
Lemma sem_binary_operation_loc:
  forall e op v ty v' ty' m fp v1,
    FCop.sem_binary_operation e op v ty v' ty' m = Some v1->
    sem_binary_operation_fp e op v ty v' ty' m = Some fp->
    forall m',
      MemPre (strip m)(strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      FCop.sem_binary_operation e op v ty v' ty' m' = Some v1 /\
      sem_binary_operation_fp e op v ty v' ty' m' = Some fp.
Proof.
  unfold FCop.sem_binary_operation,sem_binary_operation_fp;intros;ex_match;subst;try solv_eq;auto.
  all: try(unfold FCop.sem_add,sem_add_fp,FCop.sem_sub,sem_sub_fp,FCop.sem_mul,sem_mul_fp,FCop.sem_div,sem_div_fp,FCop.sem_mod,sem_mod_fp,FCop.sem_and,sem_and_fp,FCop.sem_or,sem_or_fp,FCop.sem_cmp,sem_cmp_fp in *;ex_match;inv_eq;auto;eapply sem_binarith_loc in H;eauto;fail).

  all: eapply sem_cmp_loc;eauto.
Qed.

Lemma eval_expr_loc:
  forall ge e le m a v fp,
    eval_expr ge e le m a v ->
    eval_expr_fp ge e le m a fp ->
    forall m',
      MemPre (strip m) (strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      eval_expr ge e le m' a v /\
      eval_expr_fp ge e le m' a fp.
Proof.
  intros until 2.
  revert fp H0.
  pattern a,v.
  eapply eval_expr_ind2 with
      (P0:=
         fun a0 loc ofs=>
           eval_lvalue ge e le m a0 loc ofs->
           forall fp : FP.t,
             eval_lvalue_fp ge e le m a0 fp ->
             forall m' : mem,
               MemPre (strip m) (strip m') fp ->
               FreelistEq (strip m) (strip m') (Mem.freelist m) ->
               eval_lvalue ge e le m' a0 loc ofs /\
               eval_lvalue_fp ge e le m' a0 fp)
  ;eauto;intros.
  all: try(inv_exprfp;check_lvalue;split;try constructor;auto;fail).
  {
    inv_exprfp;check_lvalue.
    eapply H1 in H3 as [];eauto.
    split;econstructor;eauto.
  }
  {
    inv H3;check_lvalue;solv_det.
    apply MemPre_split in H4 as [].
    eapply H1 in H3 as [];eauto.
    eapply sem_unary_operation_loc in H2 as [];eauto.
    split;econstructor;eauto.
  }
  {
    inv_exprfp;check_lvalue.
    repeat solv_det.
    apply MemPre_split in H6 as ?.
    destruct H5.
    apply MemPre_split in H5 as [].
    eapply H1 in H5 as [];eauto.
    eapply H3 in H9 as [];eauto.
    eapply sem_binary_operation_loc in H4 as [];eauto.
    split;econstructor;eauto.
  }
  {
    inv_exprfp;check_lvalue;repeat solv_det.
    apply MemPre_split in H4 as [].
    eapply H1 in H3 as [];eauto.
    eapply sem_cast_loc in H2 as [];eauto.
    split;econstructor;eauto.
  }
  {
    inv_exprfp;check_lvalue;repeat solv_det.
    apply MemPre_split in H4 as [].
    eapply H1 in H0 as [];eauto.
    eapply deref_loc_loc in H2;eauto.
    split;econstructor;eauto.
  }
  {
    split. econstructor;eauto.
    inv H2. constructor.
  }
  {
    inv H3. split. econstructor 2;eauto.
    constructor.
  }
  {
    inv H2;inv H3.
    solv_det.
    eapply H1 in H5 as [];eauto.
    split; econstructor;eauto.
  }
  {
    inv H6. solv_det.
    eapply H1 in H14 as [];eauto.
    split;econstructor;eauto.
  }
  {
    inv H5;solv_det.
    eapply H1 in H13 as [];eauto.
    split;econstructor;eauto.
  }
Qed.  




Lemma eval_lvalue_loc:
  forall ge e le m a b v fp,
    eval_lvalue ge e le m a b v ->
    eval_lvalue_fp ge e le m a fp ->
    forall m',
      MemPre (strip m) (strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      eval_lvalue ge e le m' a b v /\
      eval_lvalue_fp ge e le m' a fp.
Proof.
  intros.
  inv H0;solv_det;inv H;solv_det.
  all : try (split;econstructor;eauto;fail).
  all: try (eapply eval_expr_loc in H4 as [];eauto;split;econstructor;eauto;fail).
Qed.
Lemma eval_exprlist_loc:
  forall ge e le vl m a v  fp,
    eval_exprlist ge e le m a v vl->
    eval_exprlist_fp ge e le m a v fp ->
    forall m',
      MemPre (strip m) (strip m') fp ->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      eval_exprlist ge e le m' a v vl /\
      eval_exprlist_fp ge e le m' a v fp.
Proof.
  induction vl;intros.
  inv H. inv H0. split;constructor.

  inv H. inv H0. solv_det.
  apply MemPre_split in H1 as [].
  apply MemPre_split in H as [].
  eapply IHvl in H9 as [];eauto.
  eapply sem_cast_loc in H12 as [];eauto.
  eapply eval_expr_loc in H5 as [];eauto.
  split;econstructor;eauto.
Qed.
Lemma sem_unary_operation_emp_eff:
  forall op v ty m fp,
    sem_unary_operation_fp op v ty m = Some fp->
    Locs.eq (effects fp) Locs.emp.
Proof.
  unfold sem_unary_operation_fp.
  intros;ex_match;unfold sem_notbool_fp,bool_val_fp in *;ex_match;inv_eq.
  Focus 2.
  unfold FMemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp,effects.
  ex_match2;simpl;rewrite Locs.locs_union_emp;apply Locs.eq_refl.
  all: unfold FP.emp,effects;rewrite Locs.locs_union_emp;apply Locs.eq_refl.
Qed.
Local Ltac emp_eff:=
  try (unfold FP.emp,effects;simpl;repeat rewrite Locs.emp_union_locs;repeat rewrite Locs.locs_union_emp;apply Locs.eq_refl).

Lemma sem_cast_fp_emp_eff:
  forall v ty f m fp,
    sem_cast_fp v ty f m = Some fp ->
    Locs.eq (effects fp) Locs.emp.
Proof.
  unfold sem_cast_fp;intros;ex_match;inv_eq;emp_eff.
  unfold FMemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp;ex_match2;emp_eff.
Qed.
Lemma sem_binarith_fp_emp_eff:
  forall a b c d v ty v' ty' m fp,
    sem_binarith_fp a b c d v ty v' ty' m = Some fp ->
    Locs.eq (effects fp) Locs.emp.
Proof.
  unfold sem_binarith_fp;intros;ex_match;inv_eq.

  all : eapply sem_cast_fp_emp_eff in Hx0;apply sem_cast_fp_emp_eff in Hx2;apply Locs.locs_eq in Hx0;apply Locs.locs_eq in Hx2;rewrite effects_union,Hx0,Hx2;emp_eff.
Qed.
Lemma cmp_ptr_fp_emp_eff:
  forall m c v v' fp,
    cmp_ptr_fp m c v v' = Some fp->
    Locs.eq (effects fp) Locs.emp.
Proof.
  unfold cmp_ptr_fp.
  intros. ex_match.
  assert(of_optfp (cmpu_bool_fp m c v v') = fp).
  rewrite H;auto.
  rewrite <- H0.
  eapply cmpu_bool_fp_effemp0;eauto.
Qed.
Lemma sem_binary_operation_emp_eff:
  forall op e v ty v' ty' m fp,
    sem_binary_operation_fp e op v ty v' ty' m = Some fp->
    Locs.eq (effects fp) Locs.emp.
Proof.
  unfold sem_binary_operation_fp;intros;ex_match.
  all: try(unfold FCop.sem_add,sem_add_fp,FCop.sem_sub,sem_sub_fp,FCop.sem_mul,sem_mul_fp,FCop.sem_div,sem_div_fp,FCop.sem_mod,sem_mod_fp,FCop.sem_and,sem_and_fp,FCop.sem_or,sem_or_fp,FCop.sem_cmp,sem_cmp_fp in *;ex_match;inv_eq;emp_eff).
  all: try (eapply sem_binarith_fp_emp_eff;eauto;fail).
  all: try (eapply cmp_ptr_fp_emp_eff;eauto;fail).
Qed.
Lemma deref_loc_emp_eff:
  forall ty loc ofs fp,
    deref_loc_fp ty loc ofs fp ->
    Locs.eq (effects fp) Locs.emp.
Proof.
  inversion 1;subst;emp_eff.
Qed.
Lemma eval_expr_emp_eff:
  forall ge e le m a fp,
    eval_expr_fp ge e le m a fp->
    Locs.eq (effects fp) Locs.emp.
Proof.
  intros until 1.
  pattern a,fp.
  eapply eval_expr_fp_ind2 with
      (P0:=
         fun a fp=>
           eval_lvalue_fp ge e le m a fp ->
           Locs.eq (effects fp) Locs.emp);eauto;intros.
  all: try(unfold effects,FP.emp;simpl;try rewrite Locs.locs_union_emp;try apply Locs.eq_refl;fail).
  eapply sem_unary_operation_emp_eff in H4;eauto.
  apply Locs.locs_eq in H4. apply Locs.locs_eq in H2.
  rewrite <- H5,effects_union,H2,H4,Locs.locs_union_emp;apply Locs.eq_refl.

  eapply sem_binary_operation_emp_eff in H7.
  rewrite <- H8. apply Locs.locs_eq in H2. apply Locs.locs_eq in H5. apply Locs.locs_eq in H7.
  repeat (rewrite effects_union).
  rewrite H2,H5,H7;emp_eff.

  apply sem_cast_fp_emp_eff in H4. apply Locs.locs_eq in H4.
  apply Locs.locs_eq in H2.
  rewrite <- H5,effects_union,H2,H4;emp_eff.

  eapply deref_loc_emp_eff in H4. Hsimpl.
  apply Locs.locs_eq in H4. apply Locs.locs_eq in H2.
  rewrite <- H5,effects_union,H2,H4;emp_eff.
Qed.
Lemma eval_lvalue_emp_eff:
  forall ge e le m ex fp,
    eval_lvalue_fp ge e le m ex fp->
    Locs.eq (effects fp)Locs.emp.
Proof.
  inversion 1;subst;emp_eff.
  all : apply eval_expr_emp_eff in H1;auto.
Qed.
Lemma eval_exprlist_emp_eff:
  forall ge e le m vl a fp,
    eval_exprlist_fp ge e le m a vl fp ->
    Locs.eq (effects fp)Locs.emp.
Proof.
  induction vl;intros.
  inv H;emp_eff.
  inv H. apply eval_expr_emp_eff in H3.
  apply sem_cast_fp_emp_eff in H5. apply IHvl in H7.
  apply Locs.locs_eq in H3. apply Locs.locs_eq in H5. apply Locs.locs_eq in H7.
  rewrite effects_union,effects_union,H3,H5,H7;emp_eff.
Qed.
Lemma MemPost_union:
  forall m m' fp fp',
    MemPost m m' fp->
    MemPost m m' fp'->
    MemPost m m' (FP.union fp fp').
Proof.
  intros.
  unfold MemPost in *.
  rewrite effects_union.
  eapply unchanged_content_union2;eauto.
Qed.
Lemma mem_freelist_loc:
  forall l m m',
    Mem.free_list m l = Some m'->
    forall m2,
      MemPre (strip m)(strip m2) (FMemOpFP.free_list_fp l) ->
      FreelistEq (strip m)(strip m2)(Mem.freelist m) ->
      exists m3,Mem.free_list m2 l = Some m3 /\ LPost (strip m')(strip m3)(FMemOpFP.free_list_fp l)(Mem.freelist m).
Proof.
  induction l;intros.
  inv H. exists m2. split;auto;split;auto.
  apply MemPostemp.
  simpl in H.
  ex_match.
  simpl in *.
  assert(L:LPre (strip m)(strip m2) (FP.union (FMemOpFP.free_fp b z0 z) (FMemOpFP.free_list_fp l))(Mem.freelist m)).
  split;auto.
  apply MemPre_split in H0 as [].
  eapply LPre_mem_free_LPost2 in Hx1 as ?;eauto.
  Hsimpl.
  rewrite H3.

  apply mem_free_eff in Hx1 as ?.
  apply mem_free_eff in H3 as ?.
  apply mem_free_fleq in Hx1 as ?.
  apply mem_free_fleq in H3 as ?.
  apply LPost_comm in H4.
  eapply LPre_LEffect_LPost_Rule in L as [];eauto;try congruence.
  eapply IHl in H as ?;eauto;try congruence.
  Hsimpl.
  Esimpl;eauto.

  apply mem_freelist_eff in H as ?.
  apply mem_freelist_eff in H11 as ?.
  eapply LPost_LEffect_LPost_Rule in H12;try apply H14;eauto;congruence.
  rewrite <- H7. auto.
Qed.
Lemma bool_val_loc:
  forall v ty m b fp,
    FCop.bool_val v ty m = Some b ->
    bool_val_fp v ty m = Some fp->
    forall m',
      MemPre (strip m)(strip m') fp->
      FreelistEq (strip m)(strip m')(Mem.freelist m)->
      FCop.bool_val v ty m' = Some b/\
      bool_val_fp v ty m' = Some fp.
Proof.
  unfold FCop.bool_val,bool_val_fp;intros;ex_match;inv_eq;auto.
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto;split;auto.
  unfold Mem.weak_valid_pointer in *.
  erewrite unchanged_perm_cmp_valid_pointer,Hx2;eauto.
  inversion H1 as [_ ? _].
  apply unchanged_perm_comm;auto.
  erewrite LPre_weak_valid_pointer_fp_eq2;eauto.
Qed.
Lemma bool_val_emp_eff:
  forall v ty m fp,
    bool_val_fp v ty m = Some fp->
    Locs.eq (effects fp) Locs.emp.
Proof.
  unfold bool_val_fp;intros;ex_match;inv_eq;emp_eff.
  unfold FMemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp;ex_match2;emp_eff.
Qed.
Lemma alloc_variables_loc:
  forall ge p f m e m' fp,
    alloc_variables ge f m p e m'->
    alloc_variables_fp ge m p fp ->
    forall m2,
      MemPre (strip m)(strip m2) fp->
      Mem.freelist m = Mem.freelist m2 ->
      Mem.nextblockid m = Mem.nextblockid m2 ->
      FreelistEq (strip m)(strip m2)(Mem.freelist m)->
      exists m3,alloc_variables ge f m2 p e m3 /\
           alloc_variables_fp ge m2 p fp /\
           LPost (strip m')(strip m3) fp (Mem.freelist m)/\
           Mem.freelist m' = Mem.freelist m3 /\
           Mem.nextblockid m' = Mem.nextblockid m3.
Proof.
  induction p;intros.
  inv H;inv H0. Esimpl;eauto;econstructor;eauto. apply MemPostemp.

  inv H;inv H0;solv_eq.
  assert(LPre(strip m)(strip m2)(FP.union (FMemOpFP.alloc_fp m 0 (Ctypes.sizeof ge ty)) fp')(Mem.freelist m)).
  split;auto.

  apply mem_alloc_eff in H9 as ?.
  apply MemPre_split in H1 as [].
  
  eapply MemPre_mem_alloc_LPost with(Fleq:=H4) in H9 as ?;eauto.
  
  Hsimpl.
  apply mem_alloc_fleq in H6 as L1.
  apply mem_alloc_fleq in H9 as L2.
  apply Mem.alloc_nextblockid in H6 as L3.
  apply Mem.alloc_nextblockid in H9 as L4.
  assert(m2 = combine (strip m2)(Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m (strip m2) H4)).
  pose proof combine_refl m2.
  assert(combine (strip m2) (Mem.freelist m2) (Mem.nextblockid m2)  (fmem_strip_fl_wd m2)= combine (strip m2) (Mem.freelist m) (Mem.nextblockid m)(FreelistEq_mem_fl_wd m (strip m2) H4)).
  eapply combine_equiv2;eauto.
  congruence.

  rewrite <- H10 in *.

  apply mem_alloc_eff in H9 as ?.
  apply mem_alloc_eff in H6 as ?.
  rewrite <- H7 in *.
  eapply LPre_LEffect_LPost_Rule in H8 as ?;eauto.
  destruct H15.
  eapply IHp in H15;eauto;try congruence.
  Hsimpl.

  eapply alloc_variables_eff in H15 as ?;eauto.
  eapply alloc_variables_eff in H12 as ?;eauto.
  pose proof LPost_LEffect_LPost_Rule _ _ _ _ _ _ _ _ _ _ H8 H22 H21 H18.
  Esimpl;eauto.
  econstructor;eauto. econstructor;eauto.
  congruence.
  rewrite <- L2. auto.
Qed.
Lemma bind_parameters_loc:
  forall ge e p m v m' fp,
    bind_parameters ge e m p v m'->
    bind_parameters_fp ge e p v fp ->
    forall m2,
      MemPre (strip m)(strip m2) fp ->
      FreelistEq (strip m)(strip m2)(Mem.freelist m)->
      Mem.freelist m = Mem.freelist m2 ->
      Mem.nextblockid m = Mem.nextblockid m2 ->
      exists m3,
        bind_parameters ge e m2 p v m3 /\
        LPost (strip m')(strip m3) fp (Mem.freelist m).
Proof.
  induction p.
  intros.
  inv H;inv H0.
  Esimpl;eauto. constructor. split;auto. apply MemPostemp.
  intros.

  inv H;inv H0. inv_eq.
  inv H9;inv H14;inv_eq.
  inv H5.
  assert(Mem.storev chunk0 m (Vptr b0 Integers.Ptrofs.zero) v1 = Some m1).
  unfold Mem.storev;auto.
  apply MemPre_split in H1 as ?;Hsimpl.
  eapply LPre_mem_storev_LPost2 in H5 as ?;eauto;try unfold FMemOpFP.storev_fp;auto;try rewrite H3;auto.
  Hsimpl.
  apply mem_storev_eff in H5 as ?.
  apply mem_storev_eff in H9 as ?.
  assert(LPre (strip m)(strip m2) (FP.union  (FMemOpFP.store_fp chunk0 b0 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero)) fp')(Mem.freelist m)).
  rewrite H3. split;auto.
  eapply LPre_LEffect_LPost_Rule in H17 as [];eauto.

  eapply IHp in H12 as ?;eauto.
  
  Hsimpl.
  eapply bind_parameters_eff in H12 as ?;eauto.
  eapply bind_parameters_eff in H19 as ?;eauto.
  eapply LPost_LEffect_LPost_Rule in H20;try apply H10;eauto.
  Esimpl;eauto.
  econstructor;eauto. econstructor;eauto.
  apply mem_storev_fleq in H9.
  apply mem_storev_fleq in H5.
  rewrite H9,H11;auto.
  apply mem_storev_fleq in H5.
  rewrite<- H5. auto.
Qed.

Lemma function_entry1_loc:
  forall ge f vargs m e le m' fp,
    function_entry1 ge f vargs m e le m'->
    function_entry1_fp ge f vargs m e fp ->
    forall m2,
      MemPre (strip m)(strip m2) fp->
      Mem.freelist m =Mem.freelist m2 ->
      Mem.nextblockid m = Mem.nextblockid m2 ->
      FreelistEq (strip m)(strip m2)(Mem.freelist m)->
      exists m3,function_entry1 ge f vargs m2 e le m3 /\
           function_entry1_fp ge f vargs m2 e fp /\
           LPost (strip m')(strip m3) fp (Mem.freelist m).
Proof.
  intros.
  inv H;inv H0.
  assert(LPre (strip m)(strip m2)(FP.union fp1 fp2)(Mem.freelist m)).
  split;auto.
  apply MemPre_split in H1 as [].
  eapply alloc_variables_loc in H6 as ?;eauto.
  Hsimpl.

  eapply alloc_variables_eff in H10 as ?;eauto.
  eapply alloc_variables_eff in H6 as ?;eauto.
  eapply LPre_LEffect_LPost_Rule in H0 as [];eauto.
  
  eapply bind_parameters_loc in H0;eauto.
  Hsimpl.
  Esimpl;eauto.
  econstructor;eauto. econstructor;eauto.
  eapply bind_parameters_eff in H7 as ?;eauto.
  eapply bind_parameters_eff in H0 as ?;eauto.
  eapply LPost_LEffect_LPost_Rule in H18;try apply H19;try apply H20 ;eauto.
  apply alloc_variables_fleq in H6. rewrite H6;auto.
  apply alloc_variables_fleq in H6;rewrite<- H6;auto.
Qed.
Lemma Clight_loc:corestep_locality_1 (InteractionSemantics.step Clight_IS) .
Proof.
  unfold corestep_locality_1,Clight_IS;simpl;intros.
  inv H. inv H1.
  inv H0.
  set(m2:= combine m0 (Mem.freelist m1)(Mem.nextblockid m1)(FreelistEq_mem_fl_wd m1 m0 H1)).
  assert(strip m2 = m0). unfold m2;apply strip_combine.
  pose proof H1 as ?.
  rewrite <- H0 in H,H3.
  clear H0.
  inv H2.
  {
    repeat apply MemPre_split in H as [].
    repeat solv_det.
    eapply eval_lvalue_loc in H as [];eauto.
    eapply eval_expr_loc in H12 as [];eauto.
    eapply sem_cast_loc in H11 as [];eauto.
    inv H6. inv H10. repeat solv_det.
    unfold m2 in H2;rewrite strip_combine in H2.
    eapply LPre_mem_storev_LPost with(Fleq:=H1) in H16;eauto;Hsimpl.
    exists (strip x). split.
    econstructor;eauto. eapply gmem_fl_wd_embed.
    econstructor;eauto. fold m2;auto.
    econstructor;eauto. econstructor;eauto.
    destruct H10.
    split;auto.
    repeat (eapply MemPost_union;eauto).
    all : apply MemPost_effect_emp. 
    eapply eval_lvalue_emp_eff;eauto.
    eapply eval_expr_emp_eff;eauto.
    eapply sem_cast_fp_emp_eff;eauto.

  }
  {
    eapply eval_expr_loc in H0 as [];eauto.
    exists m0. split.
    econstructor;eauto. eapply gmem_fl_wd_embed;eauto.
    econstructor;eauto. rewrite strip_combine;auto.
    split;auto.
    apply MemPost_effect_emp. eapply eval_expr_emp_eff;eauto.
  }
  {
    apply MemPre_split in H as [].
    eapply eval_expr_loc in H4 as [];eauto.
    eapply eval_exprlist_loc in H5 as [];eauto.
    exists m0. split;econstructor;eauto.
    eapply gmem_fl_wd_embed;eauto.
    econstructor;eauto. apply strip_combine.
    apply MemPost_effect_emp.
    apply eval_exprlist_emp_eff in H11.
    apply eval_expr_emp_eff in H10.
    apply Locs.locs_eq in H10;apply Locs.locs_eq in H11.
    rewrite effects_union,H10,H11;emp_eff.
  }
  
  Ltac triv:=
    match goal with H:MemPre _ ?m FP.emp |- _=>
                    exists m;split;econstructor;eauto;try apply MemPostemp;try apply gmem_fl_wd_embed;econstructor;eauto end.
  all: try(triv;fail).

  apply MemPre_split in H as [].
  eapply eval_expr_loc in H0 as [];eauto.
  eapply bool_val_loc in H4 as [];eauto.
  Esimpl;eauto.
  econstructor;eauto. apply gmem_fl_wd_embed.
  econstructor;eauto.
  split;auto. apply MemPost_union;apply MemPost_effect_emp.
  eapply eval_expr_emp_eff;eauto.
  eapply bool_val_emp_eff;eauto.

  eapply mem_freelist_loc in H0;eauto.
  Hsimpl.
  Esimpl;eauto.
  econstructor;eauto. apply gmem_fl_wd_embed.
  econstructor;eauto.
  {
    assert(LPre (strip m1)(strip m2)(FP.union (FP.union fp1 fp2) (FMemOpFP.free_list_fp (blocks_of_env ge e)))(Mem.freelist m1)).
    split;auto.
    apply MemPre_split in H as [].
    apply MemPre_split in H as [].
    eapply eval_expr_loc in H0 as ?;eauto.
    eapply sem_cast_loc in H4 as ?;eauto.
    eapply mem_freelist_loc in H5 as ?;eauto.

    Hsimpl.
    Esimpl;eauto.
    econstructor;eauto. eapply gmem_fl_wd_embed.
    econstructor;eauto.
    destruct H15.
    split;auto.
    apply MemPost_union;auto.
    apply MemPost_union;apply MemPost_effect_emp.
    eapply eval_expr_emp_eff;eauto.
    eapply sem_cast_fp_emp_eff;eauto.
  }
  eapply mem_freelist_loc in H4;eauto.
  Hsimpl.
  Esimpl;eauto. econstructor;eauto.
  eapply gmem_fl_wd_embed.
  econstructor;eauto.
  
  eapply eval_expr_loc in H0 as [];eauto.
  exists m0. split;econstructor;eauto. apply gmem_fl_wd_embed;eauto.
  econstructor;eauto. apply strip_combine.
  apply MemPost_effect_emp. eapply eval_expr_emp_eff;eauto.

  eapply function_entry1_loc in H0;eauto.
  Hsimpl.
  Esimpl;eauto.
  econstructor;eauto.
  eapply gmem_fl_wd_embed.
  econstructor;eauto.
Qed.
Lemma freelist_forward:
  forall l m m',
    Mem.free_list m l = Some m'->
    GMem.forward (strip m)(strip m').
Proof.
  induction l;intros.
  inv H. apply GMem.forward_refl.
  inv H. ex_match. eapply free_forward in Hx1;eauto.
  Focus 2. econstructor;eauto.
  eapply IHl in H1.
  eapply GMem.forward_trans;eauto.
Qed.

Lemma function_entry2_loc:
  forall ge f vargs m e le m' fp,
    function_entry2 ge f vargs m e le m'->
    function_entry2_fp ge f vargs m e fp ->
    forall m2,
      MemPre (strip m)(strip m2) fp->
      Mem.freelist m =Mem.freelist m2 ->
      Mem.nextblockid m = Mem.nextblockid m2 ->
      FreelistEq (strip m)(strip m2)(Mem.freelist m)->
      exists m3,function_entry2 ge f vargs m2 e le m3 /\
           function_entry2_fp ge f vargs m2 e fp /\
           LPost (strip m')(strip m3) fp (Mem.freelist m).
Proof.
  intros.
  inv H;inv H0.
  assert(LPre (strip m)(strip m2)fp (Mem.freelist m)). 
  split;auto.
  inversion H0.
  eapply alloc_variables_loc in H10 as ?;eauto.
  Hsimpl.

  Esimpl;eauto.
  econstructor;eauto. econstructor;eauto.
Qed.
Lemma Clight_loc2:corestep_locality_1 (InteractionSemantics.step Clight_IS_2) .
Proof.
  unfold corestep_locality_1,Clight_IS_2;simpl;intros.
  inv H. inv H1.
  inv H0.
  set(m2:= combine m0 (Mem.freelist m1)(Mem.nextblockid m1)(FreelistEq_mem_fl_wd m1 m0 H1)).
  assert(strip m2 = m0). unfold m2;apply strip_combine.
  pose proof H1 as ?.
  rewrite <- H0 in H,H3.
  clear H0.
  inv H2.
  {
    repeat apply MemPre_split in H as [].
    repeat solv_det.
    eapply eval_lvalue_loc in H as [];eauto.
    eapply eval_expr_loc in H12 as [];eauto.
    eapply sem_cast_loc in H11 as [];eauto.
    inv H6. inv H10. repeat solv_det.
    unfold m2 in H2;rewrite strip_combine in H2.
    eapply LPre_mem_storev_LPost with(Fleq:=H1) in H16;eauto;Hsimpl.
    exists (strip x). split.
    econstructor;eauto. eapply gmem_fl_wd_embed.
    econstructor;eauto. fold m2;auto.
    econstructor;eauto. econstructor;eauto.
    destruct H10.
    split;auto.
    repeat (eapply MemPost_union;eauto).
    all : apply MemPost_effect_emp. 
    eapply eval_lvalue_emp_eff;eauto.
    eapply eval_expr_emp_eff;eauto.
    eapply sem_cast_fp_emp_eff;eauto.

  }
  {
    eapply eval_expr_loc in H0 as [];eauto.
    exists m0. split.
    econstructor;eauto. eapply gmem_fl_wd_embed;eauto.
    econstructor;eauto. rewrite strip_combine;auto.
    split;auto.
    apply MemPost_effect_emp. eapply eval_expr_emp_eff;eauto.
  }
  {
    apply MemPre_split in H as [].
    eapply eval_expr_loc in H4 as [];eauto.
    eapply eval_exprlist_loc in H5 as [];eauto.
    exists m0. split;econstructor;eauto.
    eapply gmem_fl_wd_embed;eauto.
    econstructor;eauto. apply strip_combine.
    apply MemPost_effect_emp.
    apply eval_exprlist_emp_eff in H11.
    apply eval_expr_emp_eff in H10.
    apply Locs.locs_eq in H10;apply Locs.locs_eq in H11.
    rewrite effects_union,H10,H11;emp_eff.
  }
  
  all: try(triv;fail).

  apply MemPre_split in H as [].
  eapply eval_expr_loc in H0 as [];eauto.
  eapply bool_val_loc in H4 as [];eauto.
  Esimpl;eauto.
  econstructor;eauto. apply gmem_fl_wd_embed.
  econstructor;eauto.
  split;auto. apply MemPost_union;apply MemPost_effect_emp.
  eapply eval_expr_emp_eff;eauto.
  eapply bool_val_emp_eff;eauto.

  eapply mem_freelist_loc in H0;eauto.
  Hsimpl.
  Esimpl;eauto.
  econstructor;eauto. apply gmem_fl_wd_embed.
  econstructor;eauto.
  {
    assert(LPre (strip m1)(strip m2)(FP.union (FP.union fp1 fp2) (FMemOpFP.free_list_fp (blocks_of_env ge e)))(Mem.freelist m1)).
    split;auto.
    apply MemPre_split in H as [].
    apply MemPre_split in H as [].
    eapply eval_expr_loc in H0 as ?;eauto.
    eapply sem_cast_loc in H4 as ?;eauto.
    eapply mem_freelist_loc in H5 as ?;eauto.

    Hsimpl.
    Esimpl;eauto.
    econstructor;eauto. eapply gmem_fl_wd_embed.
    econstructor;eauto.
    destruct H15.
    split;auto.
    apply MemPost_union;auto.
    apply MemPost_union;apply MemPost_effect_emp.
    eapply eval_expr_emp_eff;eauto.
    eapply sem_cast_fp_emp_eff;eauto.
  }
  eapply mem_freelist_loc in H4;eauto.
  Hsimpl.
  Esimpl;eauto. econstructor;eauto.
  eapply gmem_fl_wd_embed.
  econstructor;eauto.
  
  eapply eval_expr_loc in H0 as [];eauto.
  exists m0. split;econstructor;eauto. apply gmem_fl_wd_embed;eauto.
  econstructor;eauto. apply strip_combine.
  apply MemPost_effect_emp. eapply eval_expr_emp_eff;eauto.

  eapply function_entry2_loc in H0;eauto.
  Hsimpl.
  Esimpl;eauto.
  econstructor;eauto.
  eapply gmem_fl_wd_embed.
  econstructor;eauto.
Qed.
Lemma alloc_variables_forward:
  forall ge p f m e m',
    alloc_variables ge f m p e m'->
    GMem.forward (strip m)(strip m').
Proof.
  induction p;intros.
  inv H;apply GMem.forward_refl.
  inv H. eapply alloc_forward in H4;[|econstructor;eauto].
  eapply IHp in H7;eauto.
  eapply GMem.forward_trans;eauto.
Qed.

Lemma bind_parameters_forward:
  forall ge l e m v m',
    bind_parameters ge e m l v m'->
    GMem.forward (strip m)(strip m').
Proof.
  induction l;intros;inv H;try apply GMem.forward_refl.
  inv H4. unfold Mem.storev in H0.
  eapply store_forward in H0;eauto;[|econstructor;eauto].
  eapply IHl in H7;eauto.
  eapply GMem.forward_trans;eauto.
Qed.
Theorem Clight_wd: wd Clight_IS.
Proof.
  constructor.
  
  {(*forward*)
    unfold corestep_forward;intros.
    inv H. inv H0.
    inv H1;try apply GMem.forward_refl;try (eapply free_forward;eauto;fail);try (eapply freelist_forward;eauto;fail).

    inv H3;inv H7.
    unfold Mem.storev in *.
    eapply store_forward in H8;eauto.
    econstructor;eauto.

    inv H;inv H0.
    eapply alloc_variables_forward in H2;eauto.
    eapply bind_parameters_forward in H3;eauto.
    eapply GMem.forward_trans;eauto.
  }
  { (*eff*)
    apply Clight_eff.
  }
  { (*loc1*)
    apply Clight_loc.
  }
  { (*loc2*)
    apply step_det_loc1_loc2.
    apply Clight_det.
    apply Clight_loc.
  }
  (*init*)
  unfold init_gmem_valid'.
  intros. unfold InteractionSemantics.init_gmem in H. simpl in H.
  unfold init_gmem in H. inv H. inv H1. inv H2. eapply dom_match_fm;eauto.
  { (*memeqcorestep*)
    eapply eff_loc1_memeqcorestep;eauto.
    unfold step_mem_injc;intros.
    inv H;eauto.
    apply Clight_eff.
    apply Clight_loc.
  }
  {(*core not ext*)
    unfold corestep_not_at_external.
    intros.
    unfold Clight_IS.
    simpl.
    unfold at_external.
    inv H. inv H1;inv_eq;auto.
  }
  {(*core not halt*)
    unfold corestep_not_halted.
    unfold Clight_IS,halted;simpl;intros.
    destruct q eqn:?;simpl;auto.
    inv H. inv H1;auto.
  }
  {(*ext not halt*)
    unfold at_external_halted_excl;intros;unfold Clight_IS,halted;simpl;ex_match2;auto.
  }
Qed.

Theorem Clight_wdFP: wdFP Clight_IS.
Proof. apply wd_wdFP. apply Clight_wd. Qed.

Theorem Clight_wd2: wd Clight_IS_2.
Proof.
  constructor.
  {(*forward*)
    unfold corestep_forward;intros.
    inv H. inv H0.
    inv H1;try apply GMem.forward_refl;try (eapply free_forward;eauto;fail);try (eapply freelist_forward;eauto;fail).

    inv H3;inv H7.
    unfold Mem.storev in *.
    eapply store_forward in H8;eauto.
    econstructor;eauto.

    inv H;inv H0.
    eapply alloc_variables_forward in H4;eauto.
  }
  { (*eff*)
    apply Clight_eff_2.
  }
  { (*loc1*)
    apply Clight_loc2.
  }
  { (*loc2*)
    apply step_det_loc1_loc2.
    apply Clight_det2.
    apply Clight_loc2.
  }
  (*init*)
  unfold init_gmem_valid'.
  intros. unfold InteractionSemantics.init_gmem in H. simpl in H.
  unfold init_gmem in H. inv H. inv H1. inv H2. eapply dom_match_fm;eauto.
  { (*memeqcorestep*)
    eapply eff_loc1_memeqcorestep;eauto.
    unfold step_mem_injc;intros.
    inv H;eauto.
    apply Clight_eff_2.
    apply Clight_loc2.
  }
  {(*core not ext*)
    unfold corestep_not_at_external.
    intros.
    unfold Clight_IS.
    simpl.
    unfold at_external.
    inv H. inv H1;inv_eq;auto.
  }
  {(*core not halt*)
    unfold corestep_not_halted.
    unfold Clight_IS,halted;simpl;intros.
    destruct q eqn:?;simpl;auto.
    inv H. inv H1;auto.
  }
  {(*ext not halt*)
    unfold at_external_halted_excl;intros;unfold Clight_IS_2,halted;simpl;ex_match2;auto.
  }
Qed.