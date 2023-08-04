Require Import Coqlib InteractionSemantics Footprint loadframe AsmLang AsmDET DetLemma helpers FMemory GMemory FMemLemmas.



Lemma store_args_fleq:
  forall args tys ofs sp m m',
    store_args_rec_fmem m (Values.Vptr sp Integers.Ptrofs.zero) ofs args tys = Some m' ->
    Mem.freelist m' = Mem.freelist m.
Proof.
  induction args;intros;simpl in H;ex_match;try (unfold store_stack_fmem in Hx1;try eapply mem_storev_fleq in Hx1 as ?;try eapply mem_storev_fleq in Hx2 as ?;try eapply mem_storev_fleq in Hx3 as ?;eapply IHargs in H;eauto;congruence). 
Qed.  
Lemma store_args_eff:
  forall args tys ofs sp m m'
    (*wd':val_casted.wd_args args tys = true*),
    store_args_rec_fmem m (Values.Vptr sp Integers.Ptrofs.zero) ofs args tys = Some m' ->
    LEffect (strip m)(strip m')(store_args_rec_fp sp ofs tys)(Mem.freelist m).
Proof.
  
  induction args;intros.
  unfold store_args_rec_fmem in H.
  ex_match;inv H. apply LEffect_refl.
  pose proof H as R1. unfold store_args_rec_fmem in H.
  unfold store_args_rec_fp.

  ex_match;subst;fold store_args_rec_fmem in H;apply IHargs in H as R;fold store_args_rec_fp;try (unfold store_stack_fmem in Hx1;eapply mem_storev_fleq in Hx1 as ?;apply mem_storev_eff in Hx1;rewrite <-H0 in R;eapply LEffect_trans_union;eauto;fail).

  unfold store_stack_fmem in Hx2;eapply mem_storev_fleq in Hx2 as ?;apply mem_storev_eff in Hx2.
  unfold store_stack_fmem in Hx3;eapply mem_storev_fleq in Hx3 as ?;apply mem_storev_eff in Hx3.
  rewrite <- H1 in *. rewrite <- H0 in *.
  eapply LEffect_trans_union in Hx3;eauto.
  eapply LEffect_trans_union in R;try apply Hx3.
  unfold store_stack_fp.
  rewrite FP.union_comm_eq with(fp1:= (FMemOpFP.storev_fp (AST.chunk_of_type AST.Tint)(Values.Val.offset_ptr (Values.Vptr sp Integers.Ptrofs.zero)(Integers.Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs))))).
  auto.
Qed.

Lemma MemPre_compare_ints_eq:
  forall m m' rs i j,
    MemPre (strip m)(strip m')(compare_ints_fp i j m)->
    compare_ints i j rs m= compare_ints i j rs m'.
Proof.
  unfold compare_ints,compare_ints_fp.
  intros.
  f_equal. f_equal. f_equal. f_equal.
  unfold Values.Val.cmpu.
  erewrite MemPre_cmpu_valid_pointer_eq;eauto.

  unfold Values.Val.cmpu.
  erewrite MemPre_cmpu_valid_pointer_eq;eauto.
Qed.

Lemma MemPre_compare_ints_fp_eq:
  forall m m' i j,
    MemPre (strip m)(strip m')(compare_ints_fp i j m)->
    compare_ints_fp i j m = compare_ints_fp i j m'.
Proof.
  unfold compare_ints_fp.
  unfold Cop_fp.cmpu_bool_fp_total.
  unfold FMemOpFP.weak_valid_pointer_fp.
  unfold FMemOpFP.valid_pointer_fp.
  intros.
  destruct H as [_ ? _].
  ex_match2;simpl in *.
  all :
    try
      match goal with
      |H1:Mem.valid_pointer ?a ?b ?c = true, H2:Mem.valid_pointer ?d ?b ?c = false |-_=>
       try erewrite unchanged_perm_range_locset_1_valid_pointer with(m:=a)(m':=d) in H1;try apply H2;try congruence;try eapply unchanged_perm_implies;try (try apply CmpMemPermExists;try apply unchanged_perm_comm in CmpMemPermExists;try apply CmpMemPermExists);try apply belongsto_subset;simpl;try solv_locs
      end.
Qed.

Lemma compare_ints_fp_emp_eff:
  forall m i j,
    Locs.eq (effects (compare_ints_fp i j m)) Locs.emp.
Proof.
  unfold effects.
  unfold compare_ints_fp.
  unfold Cop_fp.of_optfp.
  unfold Cop_fp.cmpu_bool_fp.
  simpl.
  intros.
  destruct i,j;simpl;repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl;destruct Archi.ptr64;simpl;repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl.
  destruct Integers.Int.eq;simpl;repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl.
  unfold FMemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp.
  destruct Mem.valid_pointer;simpl;repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl.
  destruct Integers.Int.eq;simpl;repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl.
  unfold FMemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp.
  destruct Mem.valid_pointer;simpl;repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl.

  destruct Values.eq_block;unfold FMemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp.
  repeat (destruct Mem.valid_pointer;simpl;repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl).

  unfold FP.union. simpl.
  repeat rewrite Locs.locs_union_emp;try apply Locs.eq_refl.
Qed.  
Lemma MemPre_compare_ints_LPost:
  forall m m0 rs i j rs' m' (Fleq:FreelistEq (strip m) m0 (Mem.freelist m)),
    let m0' := combine m0 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq) in                         
    Next (Asm.nextinstr (compare_ints i j rs m)) m = Next rs' m'->
    MemPre (strip m) m0 (compare_ints_fp i j m) ->
    m = m' /\
    Next (Asm.nextinstr (compare_ints i j rs m0')) m0' = Next rs' m0'/\
    compare_ints_fp i j m = compare_ints_fp i j m0'/\
          LPost (strip m)(strip m0')(compare_ints_fp i j m)(Mem.freelist m).
Proof.
  intros.
  inv H. split;auto.
  assert(strip m0' = m0). unfold m0'. rewrite strip_combine. auto.
  rewrite <- H in H0.
  split. f_equal. 
  eapply MemPre_compare_ints_eq in H0.  rewrite H0. auto.
  split. erewrite MemPre_compare_ints_fp_eq;eauto.
  split;auto. apply MemPost_effect_emp.
  eapply compare_ints_fp_emp_eff;eauto.
Qed.
Lemma MemPre_check_compare_ints_eq:
  forall m m0 i j (Fleq:FreelistEq (strip m) m0 (Mem.freelist m)),
    let m0' := combine m0 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq) in
    MemPre (strip m) m0 (compare_ints_fp i j m) ->
    check_compare_ints i j m = check_compare_ints i j m0'.
Proof.
  intros. unfold check_compare_ints.
  assert (strip m0' = m0).
  subst m0'. rewrite strip_combine. auto. rewrite <- H0 in H.
  erewrite (MemPre_cmpu_valid_pointer_eq m m0'); eauto.
Qed.
Lemma MemPre_compare_longs_LPost:
  forall m m0 rs i j rs' m' (Fleq:FreelistEq (strip m) m0 (Mem.freelist m)),
    let m0' := combine m0 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m0 Fleq) in                         
    Next (Asm.nextinstr (compare_longs i j rs m)) m = Next rs' m'->
    MemPre (strip m) m0 (compare_longs_fp i j m) ->
    m = m' /\
    Next (Asm.nextinstr (compare_longs i j rs m0')) m0' = Next rs' m0'/\
    compare_longs_fp i j m = compare_longs_fp i j m0'/\
    LPost (strip m)(strip m0')(compare_longs_fp i j m)(Mem.freelist m).
Proof.
  intros.
  inv H.
  split;auto.
  split;auto.
  split;auto.
  split;auto.
  apply MemPost_effect_emp.
  unfold compare_longs_fp in *.
  unfold Cop_fp.cmplu_bool_fp_total in *.
  ex_match2;auto;try rewrite effects_union;unfold effects;simpl.
  all: repeat rewrite Locs.emp_union_locs;apply Locs.eq_refl.
Qed.

Lemma LPre_evalbuiltin_args_equiv:
  forall F V m m' fp ge rs args vargs (Memeq:MemPre (strip m) m' fp)(Fleq:FreelistEq (strip m) m' (Mem.freelist m)),
    MemOpFP.eval_builtin_args_fp (Globalenvs.Genv.to_senv ge) rs
         (rs (Asm.IR Asm.RSP)) args fp ->
    eval_builtin_args (@Globalenvs.Genv.to_senv F V ge) rs (rs(Asm.IR Asm.RSP)) m args vargs ->
    eval_builtin_args (Globalenvs.Genv.to_senv ge) rs (rs(Asm.IR Asm.RSP)) (combine m' (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq)) args vargs.
Proof.
  unfold eval_builtin_args.
  intros.
  revert fp Memeq H.
  induction H0;intros. constructor.
  econstructor;eauto.
  Focus 2.
  inv H1. rewrite FP.union_comm_eq in Memeq;eapply MemPre_subset in Memeq;[|apply FP.union_subset].
  eapply IHlist_forall2;eauto.
  inv H1. eapply MemPre_subset in Memeq;[|apply FP.union_subset].
  clear H5 IHlist_forall2 H0.

  revert fp1 H4 Memeq.
  induction H;intros;try (constructor;fail).
  Focus 3.
  inv H4. econstructor;eauto. eapply IHeval_builtin_arg1;eauto.
  eapply MemPre_subset;eauto. eapply FP.union_subset.
  eapply IHeval_builtin_arg2;eauto;eapply MemPre_subset;eauto;rewrite FP.union_comm_eq;apply FP.union_subset.

  inv H4. eapply MemPre_mem_loadv_eq in H;eauto. econstructor;eauto.
  inv H4. eapply MemPre_mem_loadv_eq in H;eauto. econstructor;eauto.
Qed.

Lemma Mempre_store_args_rec_fmem_LPost:
  forall args m m' sp ofs tys m1 (Memeq:MemPre (strip m) m'(store_args_rec_fp sp ofs tys))(Fleq:FreelistEq (strip m) m' (Mem.freelist m)),
    store_args_rec_fmem m  (Values.Vptr sp Integers.Ptrofs.zero) ofs args tys = Some m1 ->
    exists m1',
      store_args_rec_fmem (combine m' (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m' Fleq))  (Values.Vptr sp Integers.Ptrofs.zero) ofs args tys = Some m1' /\
      LPost (strip m1) (strip m1') (store_args_rec_fp sp ofs tys) (Mem.freelist m) /\
      Mem.freelist m1 = Mem.freelist m1' /\
      Mem.nextblockid m1 = Mem.nextblockid m1'.
Proof.
  induction args;intros. 
  inv H;ex_match. inv H1.
  eexists. split;simpl. eauto.
  simpl. Esimpl;eauto. split;auto. apply MemPostemp.

  inv H. ex_match;subst;try(unfold store_stack_fmem in Hx1;assert(Memeq2:MemPre (strip m) m'(FMemOpFP.storev_fp (AST.chunk_of_type AST.Tint)(Values.Val.offset_ptr (Values.Vptr sp Integers.Ptrofs.zero)(Integers.Ptrofs.repr ofs))));[eapply MemPre_subset;eauto;apply FP.union_subset|];eapply LPre_mem_storev_LPost with(Fleq:=Fleq)in Hx1 as Lp1;eauto;Hsimpl;eapply mem_storev_eff in Hx1 as e1;apply mem_storev_eff in H as e2;eapply LPre_LEffect_LPost_Rule in H0 as Lp2;eauto;[|split;rewrite strip_combine;eauto];fold store_args_rec_fp in Lp2;destruct Lp2 as [Memeq3 Fleq3];rewrite (mem_storev_fleq _ _ _ _ _ Hx1) in Fleq3;eapply IHargs with(Fleq:=Fleq3) in H1 as ?;eauto;Hsimpl;apply store_args_eff in H1 as e3;apply store_args_eff in H4 as e4;rewrite strip_combine in *;eapply LPost_LEffect_LPost_Rule in H5 as Lp2;try apply H0;eauto;Esimpl;eauto;simpl;[unfold store_stack_fmem;rewrite H;pose proof combine_refl x as R1;pose proof combine_equiv2 (strip x) (Mem.freelist x)(Mem.freelist m0) (Mem.nextblockid x) (Mem.nextblockid m0)(fmem_strip_fl_wd x) (FreelistEq_mem_fl_wd m0 (strip x) Fleq3);Hsimpl;rewrite R1,H8;auto|unfold store_stack_fp;auto;simpl in Lp2;apply mem_storev_fleq in Hx1;rewrite Hx1;auto];fail).
  unfold store_stack_fmem in Hx1; assert(Memeq2:MemPre (strip m) m'(FMemOpFP.storev_fp (AST.chunk_of_type AST.Tfloat)(Values.Val.offset_ptr (Values.Vptr sp Integers.Ptrofs.zero)(Integers.Ptrofs.repr ofs))));[eapply MemPre_subset;eauto;apply FP.union_subset|];eapply LPre_mem_storev_LPost with(Fleq:=Fleq)in Hx1 as Lp1;eauto;Hsimpl;eapply mem_storev_eff in Hx1 as e1;apply mem_storev_eff in H as e2;eapply LPre_LEffect_LPost_Rule in H0 as Lp2;eauto;[|split;rewrite strip_combine;eauto];fold store_args_rec_fp in Lp2;destruct Lp2 as [Memeq3 Fleq3];rewrite (mem_storev_fleq _ _ _ _ _ Hx1) in Fleq3;eapply IHargs with(Fleq:=Fleq3) in H1 as ?;eauto;Hsimpl;apply store_args_eff in H1 as e3;apply store_args_eff in H4 as e4;rewrite strip_combine in *;eapply LPost_LEffect_LPost_Rule in H5 as Lp2;try apply H0;eauto;Esimpl;eauto;simpl;[unfold store_stack_fmem;rewrite H;pose proof combine_refl x as R1;pose proof combine_equiv2 (strip x) (Mem.freelist x)(Mem.freelist m0) (Mem.nextblockid x) (Mem.nextblockid m0)(fmem_strip_fl_wd x) (FreelistEq_mem_fl_wd m0 (strip x) Fleq3);Hsimpl;rewrite R1,H8;auto|unfold store_stack_fp;auto;simpl in Lp2;apply mem_storev_fleq in Hx1;rewrite Hx1;auto].
  Focus 2.
  unfold store_stack_fmem in Hx1; assert(Memeq2:MemPre (strip m) m'(FMemOpFP.storev_fp (AST.chunk_of_type AST.Tany64)(Values.Val.offset_ptr (Values.Vptr sp Integers.Ptrofs.zero)(Integers.Ptrofs.repr ofs))));[eapply MemPre_subset;eauto;apply FP.union_subset|];eapply LPre_mem_storev_LPost with(Fleq:=Fleq)in Hx1 as Lp1;eauto;Hsimpl;eapply mem_storev_eff in Hx1 as e1;apply mem_storev_eff in H as e2;eapply LPre_LEffect_LPost_Rule in H0 as Lp2;eauto;[|split;rewrite strip_combine;eauto];fold store_args_rec_fp in Lp2;destruct Lp2 as [Memeq3 Fleq3];rewrite (mem_storev_fleq _ _ _ _ _ Hx1) in Fleq3;eapply IHargs with(Fleq:=Fleq3) in H1 as ?;eauto;Hsimpl;apply store_args_eff in H1 as e3;apply store_args_eff in H4 as e4;rewrite strip_combine in *;eapply LPost_LEffect_LPost_Rule in H5 as Lp2;try apply H0;eauto;Esimpl;eauto;simpl;[unfold store_stack_fmem;rewrite H;pose proof combine_refl x as R1;pose proof combine_equiv2 (strip x) (Mem.freelist x)(Mem.freelist m0) (Mem.nextblockid x) (Mem.nextblockid m0)(fmem_strip_fl_wd x) (FreelistEq_mem_fl_wd m0 (strip x) Fleq3);Hsimpl;rewrite R1,H8;auto|unfold store_stack_fp;auto;simpl in Lp2;apply mem_storev_fleq in Hx1;rewrite Hx1;auto].

  unfold store_stack_fmem in Hx2,Hx3.
  assert(Memeq2:MemPre (strip m) m'(FMemOpFP.storev_fp (AST.chunk_of_type AST.Tint)(Values.Val.offset_ptr (Values.Vptr sp Integers.Ptrofs.zero)(Integers.Ptrofs.repr (ofs +4))))).
  eapply MemPre_subset;eauto. simpl.
  rewrite FP.union_comm_eq with(fp1:=(store_stack_fp (Values.Vptr sp Integers.Ptrofs.zero) AST.Tint (Integers.Ptrofs.repr ofs))),<- FP.fp_union_assoc.  apply FP.union_subset.
  
  eapply LPre_mem_storev_LPost with(Fleq:=Fleq) in Hx2 as ?;eauto.
  Hsimpl.
  apply mem_storev_eff in Hx2 as e1.
  apply mem_storev_eff in H as e2.
  rewrite strip_combine in *.
  eapply LPre_LEffect_LPost_Rule in H0 as ?;try apply e1;try apply e2.
  Focus 2. split;eauto.
  simpl in Memeq.
  rewrite FP.union_comm_eq with(fp1:= (store_stack_fp (Values.Vptr sp Integers.Ptrofs.zero) AST.Tint (Integers.Ptrofs.repr ofs))) in Memeq.
  rewrite <- FP.fp_union_assoc in Memeq. eauto.

  apply mem_storev_fleq in Hx2 as fleq1.

  pose proof H4 as [Memeq3 Fleq3].
  assert(Memeq4:MemPre (strip m0) (strip x) (FMemOpFP.storev_fp (AST.chunk_of_type AST.Tint)(Values.Val.offset_ptr (Values.Vptr sp Integers.Ptrofs.zero)(Integers.Ptrofs.repr ofs )))). 
  eapply MemPre_subset;eauto. simpl. apply FP.union_subset.
  rewrite fleq1 in Fleq3.
  eapply LPre_mem_storev_LPost with(Fleq:=Fleq3) in Hx3 as ?;eauto.
  Hsimpl.

  apply mem_storev_eff in Hx3 as e3.
  apply mem_storev_eff in H5 as e4.
  rewrite strip_combine in *.
  apply mem_storev_fleq in Hx3 as fleq2.
  eapply LPost_LEffect_LPost_Rule in H6 as ?;try apply H0;eauto.

  eapply LPre_LEffect_LPost_Rule in H6 as ?;try apply Memeq4;eauto.
  pose proof H10 as [Memeq5 Fleq5].
  rewrite fleq2 in Fleq5.
  eapply IHargs with(Fleq:=Fleq5) in Memeq5 as ?;eauto.
  Hsimpl.

  apply store_args_eff in H11 as e6.
  apply store_args_eff in H1 as e5.
  eapply LPost_LEffect_LPost_Rule in H12 as ?;try apply e5;eauto.
  pose proof combine_refl x as R1.
  pose proof combine_equiv2 (strip x) (Mem.freelist x)(Mem.freelist m0) (Mem.nextblockid x) (Mem.nextblockid m0)(fmem_strip_fl_wd x) (FreelistEq_mem_fl_wd m0 (strip x) Fleq3).
  Hsimpl. 

  pose proof combine_refl x0 as R2.
  pose proof combine_equiv2 (strip x0) (Mem.freelist x0)(Mem.freelist m2) (Mem.nextblockid x0) (Mem.nextblockid m2)(fmem_strip_fl_wd x0) (FreelistEq_mem_fl_wd m2 (strip x0) Fleq5).
  Hsimpl.
  Esimpl;eauto.
  
  simpl. unfold store_stack_fmem. rewrite H,R1,H16,H5,R2,H17;auto.
  simpl.
  rewrite fleq1,fleq2, FP.union_comm_eq with(fp1:=(store_stack_fp (Values.Vptr sp Integers.Ptrofs.zero) AST.Tint (Integers.Ptrofs.repr ofs))).
  auto.
Qed.  
Lemma cmpu_bool_fp_total_eq:
  forall m c i j,
    Cop_fp.of_optfp (Cop_fp.cmpu_bool_fp m c i j) = Cop_fp.cmpu_bool_fp_total m c i j.
Proof.
  unfold Cop_fp.of_optfp,Cop_fp.cmpu_bool_fp,Cop_fp.cmpu_bool_fp_total.
  intros.
  ex_match2;auto.
Qed.
Lemma Asm_local_eff:corestep_local_eff (InteractionSemantics.step AsmLang).
Proof.
  unfold corestep_local_eff. intros.
    inv H. inv H1;try(inv H0;apply LEffect_refl;fail).
    {
      inv H0.
      unfold exec_instr in H4;unfold exec_instr_fp.
      destruct i;
        try(inv H4;apply LEffect_refl;fail);
        try( unfold exec_load in H4;ex_match;inv H4;apply LEffect_refl);
        try( unfold exec_store in H4;ex_match;inv H4;unfold exec_store_fp;eapply mem_storev_eff;eauto);
        try ( unfold goto_label in H4;ex_match;inv H4;apply LEffect_refl).
      ex_match. inv H4.

      eapply mem_alloc_eff in Hx as ?;eauto.
      eapply mem_storev_eff in Hx0 as ?;eauto.
      eapply mem_storev_eff in Hx1 as ?;eauto.
      rewrite <- (mem_storev_fleq _ _ _ _ _ Hx0) in *;eauto.
      rewrite (Mem.alloc_freelist _ _ _ _ _ Hx) in *.

      eapply LEffect_trans_union in H1 ;try apply H0.
      eapply LEffect_trans_union in H4;try apply H1.
      rewrite FP.fp_union_assoc. auto.

      ex_match.
      rewrite FP.union_comm_eq;apply LEffect_union_fp.
      eapply mem_free_eff in Hx2;eauto.
      inv H4. auto.
    }
    eapply mem_alloc_fleq in H2 as ?.
    eapply store_args_fleq in H4 as ?.
    eapply store_args_eff in H4;eauto.
    eapply mem_alloc_eff in H2;eauto.
    inv H0.
    eapply LEffect_trans_union;eauto.
    unfold store_args_fp. congruence.
(*    {
      unfold exec_locked_instr in H4.
      unfold exec_locked_instr_fp.
      destruct i;inv H4.
      {
        unfold exec_load,Mem.loadv in H5.
        unfold exec_load_fp,FMemOpFP.loadv_fp. 
        destruct ASM_local.eval_addrmode;inv H5.
        destruct Mem.load;inv H4.
        inv H0. apply LEffect_refl.
      }
      {
        ex_match.
        inv H5.
        eapply mem_storev_eff in Hx0.
        rewrite FP.union_comm_eq.
        eapply LEffect_union_fp.
        inv H0. auto.
      }
      {
        ex_match. 
        subst. inv H5.
        eapply mem_storev_eff in Hx2.
        rewrite FP.union_comm_eq;apply LEffect_union_fp.
        rewrite FP.union_comm_eq;apply LEffect_union_fp.
        inv H0;auto.
        inv H5.
        inv H0. apply LEffect_refl.
      }
    } *)
Qed.

Lemma Asm_locality_1: corestep_locality_1 (InteractionSemantics.step AsmLang).
Proof.
  unfold corestep_locality_1. intros.
  pose proof H as R.
  inv H. inv H1.
  inv H2.
  {
    destruct H0 as [Memeq Fleq].
    unfold exec_instr in H4.
    unfold exec_instr_fp in *.
    ex_match;subst;
      try (inv H4;exists (strip (combine m0 (Mem.freelist m'0)(Mem.nextblockid m'0) (FreelistEq_mem_fl_wd _ _ Fleq))); split;[econstructor;eauto;[eapply gmem_fl_wd_embed;eauto|econstructor;eauto;unfold exec_instr;eauto; try rewrite Hx1; try rewrite Hx2; try rewrite Hx0; try rewrite Hx3; eauto]|rewrite strip_combine;split;auto;apply MemPostemp];fail);
      try (unfold goto_label in H4;ex_match;inv H4;inv H;exists (strip (combine m0 (Mem.freelist m'0)(Mem.nextblockid m'0) (FreelistEq_mem_fl_wd _ _ Fleq)));split;[econstructor;eauto;[eapply gmem_fl_wd_embed;eauto|econstructor;eauto;unfold exec_instr,goto_label;try rewrite Hx;try rewrite Hx0;try rewrite Hx1;try rewrite Hx2;try rewrite Hx;try rewrite Hx0;try rewrite Hx1;try rewrite Hx2;eauto]|rewrite strip_combine;split;auto;apply MemPostemp];fail);
      try (unfold exec_load,exec_load_fp in *;ex_match;inv H4;eapply MemPre_mem_loadv_eq in Hx as ?;eauto; exists (strip (combine m0 (Mem.freelist m'0)(Mem.nextblockid m'0) (FreelistEq_mem_fl_wd m'0 m0 Fleq)));split;[econstructor;eauto;[eapply gmem_fl_wd_embed;eauto|econstructor;eauto;unfold exec_instr,exec_load;try rewrite Hx;eauto;erewrite H0;eauto]| rewrite strip_combine;split;auto;apply MemPost_loadv_fp];fail);
      try (unfold exec_store,exec_store_fp in *;ex_match;inv H4; eapply LPre_mem_storev_LPost with(Fleq:=Fleq) in Hx as ?;eauto;Hsimpl;eexists;split;eauto;econstructor;eauto;[eapply gmem_fl_wd_embed|];econstructor;eauto;unfold exec_instr,exec_store;try rewrite H0;auto;fail).
    all: try (try erewrite MemPre_check_compare_ints_eq in Hx1;
              try eapply MemPre_compare_ints_LPost with(Fleq:=Fleq) in H4;
              try eapply MemPre_compare_longs_LPost with(Fleq:=Fleq) in H4;
              eauto;Hsimpl;subst;eexists;split;eauto;econstructor;
              try eapply gmem_fl_wd_embed with(wd:=FreelistEq_mem_fl_wd m'0 m0 Fleq);
              eauto;econstructor;eauto;unfold exec_instr;try rewrite Hx0;eauto;auto;fail).
    { erewrite MemPre_check_compare_ints_eq in Hx1; eauto.
      eapply MemPre_compare_ints_LPost with (Fleq:=Fleq) in H4; eauto.
      Hsimpl. subst. eexists; split; eauto. econstructor; eauto.
      eapply gmem_fl_wd_embed with (wd:=FreelistEq_mem_fl_wd m'0 m0 Fleq).
      econstructor; eauto; unfold exec_instr; try rewrite Hx0, Hx1; eauto. }
    { erewrite MemPre_check_compare_ints_eq in Hx1; eauto.
      eapply MemPre_compare_ints_LPost with (Fleq:=Fleq) in H4; eauto.
      Hsimpl. subst. eexists; split; eauto. econstructor; eauto.
      eapply gmem_fl_wd_embed with (wd:=FreelistEq_mem_fl_wd m'0 m0 Fleq).
      econstructor; eauto; unfold exec_instr; try rewrite Hx0, Hx1; eauto. }
    {
      eapply MemPre_mem_alloc_LPost with(Fleq:=Fleq) in Hx0 as ?;[|eapply MemPre_subset;eauto;eapply FP.union_subset].
      Hsimpl.
      assert(LPre (strip m1) m0  (FP.union (FMemOpFP.alloc_fp m1 0 sz)(FP.union(FMemOpFP.storev_fp AST.Mptr  (Values.Val.offset_ptr (Values.Vptr b0 Integers.Ptrofs.zero) ofs_link))(FMemOpFP.storev_fp AST.Mptr  (Values.Val.offset_ptr (Values.Vptr b0 Integers.Ptrofs.zero)ofs_ra)))) (Mem.freelist m1)).
      split;auto.
      
      apply mem_alloc_eff in Hx0 as e1.
      apply mem_alloc_eff in H0 as e2.
      rewrite strip_combine in e2.
      eapply LPre_LEffect_LPost_Rule in H6;eauto.
      pose proof Hx0 as A1.
      apply Mem.alloc_freelist in Hx0.
      rewrite<- Hx0 in H6.
      assert(LPre (strip m)(strip x)  (FMemOpFP.storev_fp AST.Mptr (Values.Val.offset_ptr (Values.Vptr b0 Integers.Ptrofs.zero) ofs_link))(Mem.freelist m)).
      eapply LPre_subset;eauto. apply FP.union_subset.
      pose proof H7 as [Mempre2 Fleq2].
      eapply LPre_mem_storev_LPost with(Fleq:=Fleq2) in Mempre2 as ?;eauto;Hsimpl.
      
      apply mem_storev_eff in Hx1 as e3.
      apply mem_storev_eff in H8 as e4.
      apply LPost_comm in H9. apply LPost_comm in H5.
      eapply LPost_LEffect_LPost_Rule in H9 as Lp1;try apply e3;try apply e4;try rewrite strip_combine;eauto.
      apply LPost_comm in H9.
      rewrite strip_combine in e4.
      eapply LPre_LEffect_LPost_Rule in H9 as ?;try apply e3;try apply e4;eauto.
      apply mem_storev_fleq in Hx1.
      rewrite Hx1 in H12.
        
      pose proof H12 as [Mempre3 Fleq3].
      eapply LPre_mem_storev_LPost with(Fleq:=Fleq3) in Mempre3 as ?;eauto;Hsimpl.
      apply mem_storev_eff in Hx2 as e5.
      apply mem_storev_eff in H13 as e6.
      apply mem_storev_fleq in Hx2.
      rewrite<- Hx1,Hx0 in H14.
      
      apply LPost_comm in H14. 
      eapply LPost_LEffect_LPost_Rule in H14;try apply e5;try apply e6;eauto.
      inv H4. rewrite<- FP.fp_union_assoc in H14.
      apply LPost_comm in H14.
      Esimpl;eauto.
      econstructor;eauto. eapply gmem_fl_wd_embed.
      econstructor;eauto. unfold exec_instr.
      rewrite H0.
      assert(Mem.freelist x = Mem.freelist m /\ Mem.nextblockid x = Mem.nextblockid m).
      Local Transparent Mem.alloc.
      revert A1 H0;clear;unfold Mem.alloc;intros.
      inv A1;inv H0. simpl. auto.
      destruct H4.
      assert(x =(combine (strip x) (Mem.freelist m) (Mem.nextblockid m)
                           (FreelistEq_mem_fl_wd m (strip x) Fleq2))).
      pose proof combine_refl x.
      pose proof combine_equiv2 (strip x) (Mem.freelist x)(Mem.freelist m) (Mem.nextblockid x) (Mem.nextblockid m)(fmem_strip_fl_wd x) (FreelistEq_mem_fl_wd m (strip x) Fleq2) H4 H17. congruence.
      rewrite <- H18 in *. rewrite H8.
      rewrite strip_combine in *.
      assert( x0 =   (combine (strip x0) (Mem.freelist m2) (Mem.nextblockid m2)
                              (FreelistEq_mem_fl_wd m2 (strip x0) Fleq3))).
      pose proof combine_refl x0.
      pose proof combine_equiv2 (strip x0) (Mem.freelist x0)(Mem.freelist m2) (Mem.nextblockid x0) (Mem.nextblockid m2)(fmem_strip_fl_wd x0) (FreelistEq_mem_fl_wd m2 (strip x0) Fleq3). Hsimpl. congruence.
      rewrite <- H19 in *. rewrite H13. auto.

      unfold exec_instr_fp;rewrite H0; auto.
    } 
    {
      eapply LPre_mem_free_LPost with(Fleq:=Fleq) in Hx3 as ?;eauto.

      Focus 2.
      eapply MemPre_subset;eauto.
      rewrite FP.union_comm_eq; apply FP.union_subset.
      Hsimpl. inv H4. apply LPost_comm in H2.
      eapply MemPre_mem_loadv_eq with(Fleq:=Fleq) in Hx0 as ?;eauto.
      Focus 2. eapply MemPre_subset;eauto.
      rewrite<- FP.fp_union_assoc. apply FP.union_subset.
      eapply MemPre_mem_loadv_eq with(Fleq:=Fleq) in Hx1 as ?;eauto.
      Focus 2. eapply MemPre_subset;eauto.
      rewrite FP.union_comm_eq with(fp2:= (FMemOpFP.loadv_fp AST.Mptr(Values.Val.offset_ptr (Values.Vptr b0 i0) ofs_link))),<- FP.fp_union_assoc. apply FP.union_subset.
        
      Esimpl;eauto.
      econstructor;eauto.
      eapply gmem_fl_wd_embed. instantiate(2:=(Mem.nextblockid m1)).
      instantiate(1:=FreelistEq_mem_fl_wd m1 m0 Fleq).
      econstructor. eauto. eauto. eauto.
      unfold exec_instr.
      
      rewrite Hx2,H4,H7,H0; auto.
      unfold exec_instr_fp.
      rewrite Hx2. auto.
    }
  }
  {
    destruct H0 as [Mempre Fleq].
    exists m0. split;auto. pose proof FreelistEq_mem_fl_wd _ _ Fleq.
    econstructor .
    eapply gmem_fl_wd_embed;eauto.
    econstructor 2;eauto.
    Focus 2. rewrite strip_combine;eauto.
    eapply LPre_evalbuiltin_args_equiv;eauto.
    split;auto.
    apply MemPost_effect_emp.
    revert H6. clear.
    revert rs ge fp.
    induction args. intros. inv H6. unfold FP.emp,effects;simpl. apply Locs.union_refl.
    intros.
    inv H6.
    eapply IHargs in H2.
    enough(Locs.eq (effects fp1) Locs.emp).
    apply Locs.locs_eq in H. apply Locs.locs_eq in H2.
    rewrite effects_union. rewrite H,H2. apply Locs.union_refl.

    clear args H2 IHargs fp2.
    revert rs ge fp1 H1.
    induction a;intros;inv H1;try(unfold effects;simpl;apply Locs.union_refl;fail);try apply loadv_fp_emp_effects.
    apply IHa1 in H2. apply IHa2 in H3.
    rewrite effects_union.  apply Locs.locs_eq in H2. apply Locs.locs_eq in H3. rewrite H2,H3. apply Locs.union_refl.
  }
  {
    destruct H0.
    assert(forall m args rs ef,
              extcall_arguments rs m ef args ->
              forall m' fp ,
                MemPre (strip m)(strip m') fp ->
                FreelistEq (strip m)(strip m')(Mem.freelist m) ->
                ASM_local.extcall_arguments_fp rs ef fp ->
                extcall_arguments rs m' ef args).
    clear. unfold extcall_arguments,ASM_local.extcall_arguments_fp.
    induction 1;intros. constructor.
    inv H3.
    econstructor;eauto. 
    Focus 2. eapply IHlist_forall2;try apply H7;eauto.
    eapply MemPre_subset. eapply FP.union_subset. rewrite FP.union_comm_eq;eauto.
    pose proof FP.union_subset fp1 fp2.
    eapply MemPre_subset in H1;eauto.
    revert H H1 H2 H6. clear;intros.
    inv H; constructor.
    inv H0. constructor. 
    econstructor;eauto. inv H6. inv H0. eapply MemPre_mem_loadv_eq2;eauto.
    inv H0;econstructor;eauto.
    inv H6. inv H5. eapply MemPre_mem_loadv_eq2;eauto. eapply MemPre_subset;eauto.
    eapply FP.union_subset.
    inv H3;econstructor;eauto.
    inv H6. inv H7. eapply MemPre_mem_loadv_eq2;eauto. eapply MemPre_subset;eauto.
    rewrite FP.union_comm_eq. eapply FP.union_subset.
    
    remember (combine m0 (Mem.freelist m'0)(Mem.nextblockid m'0)(FreelistEq_mem_fl_wd m'0 m0 H2)) as m1.
    assert(strip m1 = m0). rewrite Heqm1,strip_combine;auto.
    pose proof H2 as L. rewrite <- H6 in *.
    eapply H5 in H4 as ?;eauto.
    assert( embed m0 (Mem.freelist m'0) m1). econstructor;eauto.
    rewrite Heqm1;auto.
    exists m0. split. econstructor. rewrite H6. eauto.
    econstructor;eauto. auto.
    split;auto. apply MemPost_effect_emp.
    revert H4. clear;intros.
    unfold ASM_local.extcall_arguments_fp in H4.
    induction H4. unfold FP.emp,effects;simpl. apply Locs.union_refl.
    rewrite <- H0. rewrite effects_union.
    apply Locs.locs_eq in IHload_arguments_fp.
    rewrite IHload_arguments_fp. rewrite Locs.locs_union_emp.
    clear fp2 H0 H4 fp pll IHload_arguments_fp.
    inv H. inv H0. unfold FP.emp,effects;apply Locs.union_refl.
    apply loadv_fp_emp_effects.
    inv H0;inv H1. rewrite FP.fp_union_emp. unfold FP.emp,effects;apply Locs.union_refl.
    rewrite FP.emp_union_fp. apply loadv_fp_emp_effects.
    rewrite FP.fp_union_emp. apply loadv_fp_emp_effects.
    rewrite effects_union.
    pose proof loadv_fp_emp_effects.
    specialize (H (AST.chunk_of_type ty)(Values.Val.offset_ptr (rs (Asm.IR Asm.RSP))(Integers.Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))) as ?.
    specialize (H (AST.chunk_of_type ty0) (Values.Val.offset_ptr (rs (Asm.IR Asm.RSP))(Integers.Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs0)))).
    apply Locs.locs_eq in H. apply Locs.locs_eq in H0.
    rewrite H,H0. apply Locs.union_refl.
  }
  {
    exists m0. split;auto. econstructor;eauto;[|econstructor;eauto|].
    eapply gmem_fl_wd_embed;eauto. rewrite strip_combine. auto.
    destruct H0;split;auto. apply MemPostemp.
  } 
  {
    pose proof H0 as [Memeq Fleq].
    eapply MemPre_mem_alloc_LPost with(Fleq:=Fleq) in H1 as ?;eauto.
    Focus 2. eapply MemPre_subset;eauto. apply FP.union_subset.
    Hsimpl.

    apply mem_alloc_eff in H1 as e1.
    apply mem_alloc_eff in H2 as e2.
    rewrite strip_combine in e2.
    eapply LPre_LEffect_LPost_Rule in H5 as ?;eauto.

    pose proof H6 as [Memeq2 Fleq2].
    apply mem_alloc_fleq in H1 as fleq1.
    rewrite fleq1 in Fleq2.
    eapply Mempre_store_args_rec_fmem_LPost with(Fleq:=Fleq2) in Memeq2 as ?;eauto.
    Hsimpl.

    
    apply store_args_eff in H7 as e4.
    apply store_args_eff in H4 as e3.
    rewrite strip_combine in *.
    simpl in e4.
    eapply LPost_LEffect_LPost_Rule in H8 as ?;try apply e3;eauto.
    rewrite <- fleq1 in H11.
    unfold store_args_fp.
    apply store_args_fleq in H4 as fleq2.
    pose proof combine_refl x as R1.
    pose proof combine_equiv2 (strip x) (Mem.freelist x)(Mem.freelist m2) (Mem.nextblockid x) (Mem.nextblockid m2)(fmem_strip_fl_wd x) (FreelistEq_mem_fl_wd m2 (strip x) Fleq2).
    assert(Mem.freelist x = Mem.freelist m2).
    apply Mem.alloc_freelist in H2. rewrite H2. simpl. auto.
    assert(Mem.nextblockid x = Mem.nextblockid m2).
    unfold Mem.alloc in H2. inv H2. simpl.
    unfold Mem.alloc in H1. inv H1. simpl.
    auto.
    Hsimpl.
    Esimpl;eauto.
    econstructor;eauto.
    eapply gmem_fl_wd_embed.

    econstructor;eauto.
    unfold store_args_fmem.
    rewrite R1,H12;auto.
  }
  (*
  {
    exists m0. destruct H0;split;econstructor;eauto;try apply MemPostemp.
    Focus 2. econstructor;eauto.
    eapply gmem_fl_wd_embed;eauto. rewrite strip_combine;eauto.
  }
  {
    destruct H0 as [Memeq Fleq].
    unfold exec_locked_instr in H4.
    ex_match;subst.
    {
      unfold exec_load,exec_load_fp in *;ex_match;inv H4.
      eapply MemPre_mem_loadv_eq in Hx as ?;eauto.
      exists (strip (combine m0 (Mem.freelist m'0)(Mem.nextblockid m'0) (FreelistEq_mem_fl_wd m'0 m0 Fleq)));split;[econstructor;eauto;[eapply gmem_fl_wd_embed;eauto|econstructor;eauto;unfold exec_locked_instr,exec_load;try rewrite Hx;eauto;erewrite H0;eauto]| rewrite strip_combine;split;auto;apply MemPost_loadv_fp].
    }
    {
      unfold exec_store,exec_store_fp in *;ex_match;inv H4.
      eapply LPre_mem_storev_LPost with(Fleq:=Fleq) in Hx1 as ?;eauto;Hsimpl.
      Focus 2. unfold exec_locked_instr_fp in Memeq. eapply MemPre_subset;eauto. rewrite FP.union_comm_eq. apply FP.union_subset.
      eapply MemPre_mem_loadv_eq in Hx0 as ?;eauto.
      Focus 2. unfold exec_locked_instr_fp in Memeq. eapply MemPre_subset;eauto. apply FP.union_subset.
      
      eexists. split;eauto. econstructor;eauto. apply gmem_fl_wd_embed.
      econstructor;eauto. unfold exec_locked_instr.
      rewrite H0. rewrite H6. eauto.
      unfold exec_locked_instr_fp.
      rewrite FP.union_comm_eq.
      destruct H2;split;auto.
      unfold MemPost.
      rewrite effects_union.
      apply unchanged_content_union2;auto.
      apply MemPost_effect_emp. apply loadv_fp_emp_effects.
    }
    {
      
      unfold exec_store,exec_store_fp in *;ex_match;inv H4.
      eapply LPre_mem_storev_LPost with(Fleq:=Fleq) in Hx3 as ?;eauto;Hsimpl.
      Focus 2. unfold exec_locked_instr_fp in Memeq. eapply MemPre_subset;eauto.
      rewrite Hx0,Hx1,FP.fp_union_assoc,FP.union_comm_eq;apply FP.union_subset.
      eapply MemPre_mem_loadv_eq in Hx0 as ?;eauto.
      Focus 2. unfold exec_locked_instr_fp in Memeq. eapply MemPre_subset;eauto.
      rewrite Hx0,Hx1.  apply FP.union_subset.

      pose proof Hx1 as ?.
      enough(E1: MemPre (strip m1)(strip(combine m0 (Mem.freelist m1) (Mem.nextblockid m1)(FreelistEq_mem_fl_wd m1 m0 Fleq)))((Cop_fp.cmpu_bool_fp_total m1 Integers.Ceq v (rs (Asm.IR Asm.RAX))))).
      erewrite MemPre_cmpu_valid_pointer_ceq in Hx1;eauto.
      Focus 2. eapply MemPre_subset;eauto.
      Focus 2. rewrite strip_combine. eauto.
      unfold exec_locked_instr_fp.
      rewrite Hx0,Hx1,FP.union_comm_eq,<- FP.fp_union_assoc.
      rewrite cmpu_bool_fp_total_eq.
      apply FP.union_subset.
      
      eexists. split;eauto. econstructor;eauto. apply gmem_fl_wd_embed.
      econstructor;eauto. unfold exec_locked_instr.
      rewrite H0. rewrite H6. rewrite Hx1. eauto.
      unfold exec_locked_instr_fp.
      rewrite H6. rewrite Hx0. rewrite Hx1.
      erewrite MemPre_cmpu_valid_pointer_ceq,Hx1.
      f_equal. f_equal.
      
      Focus 3. destruct H2.
      split;auto.
      unfold MemPost,exec_locked_instr_fp. rewrite Hx0,H7.
      rewrite effects_union.
      apply unchanged_content_union2;auto.
      apply MemPost_effect_emp. apply loadv_fp_emp_effects.
      rewrite effects_union.
      apply unchanged_content_union2;auto.
      apply MemPost_effect_emp.
      rewrite cmpu_bool_fp_total_eq.
      apply cmpu_bool_fp_effemp.

      rewrite strip_combine in *. auto. do 2  rewrite cmpu_bool_fp_total_eq.
      eapply  LPre_cmpu_bool_fp_total_eq;eauto.
      rewrite strip_combine.
      eapply MemPre_subset;eauto.
      unfold exec_locked_instr_fp. rewrite Hx0,H7.
      rewrite FP.union_comm_eq. rewrite <- FP.fp_union_assoc.
      rewrite cmpu_bool_fp_total_eq.
      eapply FP.union_subset.
    }
    {
      inv H4.
      
      unfold exec_locked_instr_fp in *.
      rewrite Hx0 in *. rewrite Hx1 in *.
      enough(MemPre (strip m'0) m0 ((Cop_fp.cmpu_bool_fp_total m'0 Integers.Ceq v (rs (Asm.IR Asm.RAX))))).
      enough(MemPre (strip m'0) m0 (FMemOpFP.loadv_fp AST.Mint32 (ASM_local.eval_addrmode ge a rs))).
      eexists;split. econstructor;eauto. eapply gmem_fl_wd_embed.
      econstructor;eauto. unfold exec_locked_instr.
      erewrite MemPre_mem_loadv_eq.
      erewrite MemPre_cmpu_valid_pointer_ceq. rewrite Hx1.
      eauto.
      rewrite strip_combine.
      apply MemPre_comm.
      erewrite LPre_cmpu_bool_fp_total_eq;eauto. eauto. eauto.
      unfold exec_locked_instr_fp.
      erewrite MemPre_mem_loadv_eq;eauto.
      erewrite MemPre_cmpu_valid_pointer_ceq;eauto. rewrite Hx1. 
      f_equal. f_equal. erewrite LPre_cmpu_bool_fp_eq;eauto.
      {
        eapply MemPre_subset;try apply H0.
        unfold Cop_fp.of_optfp,Cop_fp.cmpu_bool_fp,Cop_fp.cmpu_bool_fp_total.
        ex_match2;try inv Hx;try apply FP.subset_refl.
      }
      rewrite strip_combine.
      erewrite LPre_cmpu_bool_fp_total_eq;eauto.
      apply MemPre_comm;auto.

      rewrite strip_combine.
      split;auto.
      unfold MemPost. rewrite effects_union;apply unchanged_content_union2.
      apply MemPost_effect_emp. apply loadv_fp_emp_effects.
      apply MemPost_effect_emp.
      apply cmpu_bool_fp_effemp0.
      
      eapply MemPre_subset;try apply Memeq;eauto. apply FP.union_subset.
      eapply MemPre_subset;eauto. rewrite FP.union_comm_eq.
      assert(FP.subset (Cop_fp.cmpu_bool_fp_total m'0 Integers.Ceq v (rs (Asm.IR Asm.RAX)))(ASM_local.of_optfp (Cop_fp.cmpu_bool_fp m'0 Integers.Ceq v (rs (Asm.IR Asm.RAX))))).
      unfold Cop_fp.cmpu_bool_fp,Cop_fp.cmpu_bool_fp_total,ASM_local.of_optfp.
      ex_match2;try apply FP.subset_refl.
      eapply FP.subset_union_subset;eauto.
    }
  } *)
  Unshelve.
  auto.
  Focus 2.
  destruct H0. eapply FreelistEq_mem_fl_wd in f;eauto.
  (* Focus 2. eapply FreelistEq_mem_fl_wd;eauto.
  eauto. *)
Qed.


(** Forward *)
Lemma exec_store_forward:
  forall m m0 m0' fl ge chunk a rs ir vl rs',
    FMemory.embed m fl m0 ->
    exec_store ge chunk m0 a rs ir vl = Next rs' m0' ->
    GMemory.GMem.forward m (FMemory.strip m0').
Proof.
  unfold exec_store. intros.
  destruct (ASM_local.eval_addrmode ge a rs); simpl in *; try discriminate.
  destruct FMemory.Mem.store eqn:STORE; try discriminate.
  inv H0. eapply store_forward; eauto.
Qed.

Lemma store_args_forward:
  forall m fl m0 stk args tys m1,
    FMemory.embed m fl m0 ->
    loadframe.store_args_fmem m0 stk args tys = Some m1 ->
    GMemory.GMem.forward m (FMemory.strip m1).
Proof.
  intros until args. revert m fl m0 stk.
  unfold loadframe.store_args_fmem. generalize 0.  induction args.
  unfold loadframe.store_args_rec_fmem. intros. destruct tys; try discriminate.
  inv H0; inv H. auto using GMemory.GMem.forward_refl.
  intros. destruct tys. inv H0.
  simpl in H0.
  destruct t;
    repeat match goal with
           | H: match ?x with _ => _ end = Some _ |- _ => destruct x eqn:?Hx; try discriminate
           end;
    try (unfold loadframe.store_stack_fmem in *; simpl in *;
         eapply store_forward in Hx; eauto;
         eapply GMemory.GMem.forward_trans; eauto;
         eapply IHargs; inv H; eauto using embed_refl).
  eapply store_forward in Hx0; eauto. 
  eapply store_forward in Hx1; eauto using embed_refl.
  do 2 (eapply GMemory.GMem.forward_trans; eauto).
  eapply IHargs; inv H; eauto using embed_refl.
Qed.


Theorem Asm_wd: wd AsmLang.
Proof.
  constructor.

  (** forward [*] *)
  { unfold corestep_forward. intros.
    inv H. inv H1; subst; simpl in *.
    Opaque Mem.store Mem.alloc.
    destruct i; simpl in H4; inv H4; unfold exec_load, goto_label in *;
    (* exec load *)
      repeat match goal with
             | H: match ?x with _ => _ end = Next _ _ |- _ =>
               destruct x eqn:?Hx; inv H
             end;
      try (inv H0; auto using GMemory.GMem.forward_refl; fail);
      try (eapply exec_store_forward; eauto; fail).
    (** alloc frame *)
    apply GMemory.GMem.forward_trans with (FMemory.strip m1).
    eapply alloc_forward; eauto.
    apply GMemory.GMem.forward_trans with (FMemory.strip m2).
    eapply store_forward; eauto.
    instantiate (1:= fl). constructor; auto.
    inv H0. eapply FMemory.Mem.alloc_freelist; eauto.
    eapply store_forward; eauto.
    instantiate (1:= fl). constructor; auto.
    inv H0.
    eapply FMemory.Mem.store_freelist in Hx1.
    eapply FMemory.Mem.store_freelist in Hx0.
    eapply FMemory.Mem.alloc_freelist in Hx.
    congruence.
    (** free frame *)
    eapply free_forward; eauto.
    all: try (inv H0; apply GMemory.GMem.forward_refl; fail).
    (** store_args *)
    exploit alloc_forward ; eauto. intro.
    eapply store_args_forward in H4. eapply GMemory.GMem.forward_trans. exact H1. eauto.
    instantiate (1 := fl). constructor; auto.
    erewrite FMemory.Mem.alloc_freelist; eauto. inv H0; auto.
    (** exec locked instr *)
(*    destruct i; try discriminate; unfold exec_locked_instr in H4.
    unfold exec_load in H4. destruct FMemory.Mem.loadv; inv H4. inv H0; auto using GMemory.GMem.forward_refl.
    destruct FMemory.Mem.loadv; try discriminate; destruct FMemory.Mem.storev eqn:STORE; inv H4.
    destruct (ASM_local.eval_addrmode); simpl in STORE; try discriminate; eapply store_forward; eauto.
    repeat match goal with
             | H: match ?x with _ => _ end = Next _ _ |- _ =>  destruct x eqn:?Hx; inv H
           end.
    destruct ASM_local.eval_addrmode; try discriminate.  eapply store_forward; eauto.
    inv H0; auto using GMemory.GMem.forward_refl. *)
  }
  (** local eff [***] *)
  {
    apply Asm_local_eff.
  }
  (** locality 1 [***] *)
  {
    apply Asm_locality_1.
  
  }
  (** locality 2 [*] *)
  {
    apply step_det_loc1_loc2.
    apply Asm_det.
    apply Asm_locality_1.
  }

  (** init forward *)
  unfold init_gmem_valid'.
  intros. unfold init_gmem in H. simpl in H.
  unfold init_mem in H. inv H. inv H1. inv H2. eapply dom_match_fm;eauto.
  
  (** eqmem [*] *)
  {
    eapply eff_loc1_memeqcorestep.
    unfold step_mem_injc;intros.
    inv H;eauto.
    apply Asm_local_eff.
    apply Asm_locality_1.
  }
  
  
  { unfold corestep_not_at_external.
    intros. destruct q; simpl in *; auto.
    inversion H. subst. inversion H1. subst.
    destruct f; auto. 
    apply i64ext_extcall in H12. destruct H12. inversion H2.
  }
  { unfold corestep_not_halted.
    intros. destruct q; simpl in *; auto. destruct l.
    inversion H; subst.
    inversion H1; subst; rewrite H4; simpl; auto.
  }
  { unfold at_external_halted_excl.
    intros. destruct q; simpl; auto.
  }
Qed.

Theorem Asm_wdFP: wdFP AsmLang.
Proof. apply wd_wdFP, Asm_wd. Qed.