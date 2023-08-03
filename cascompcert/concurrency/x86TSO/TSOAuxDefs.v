From mathcomp.ssreflect Require Import fintype ssrnat.
Require Import Coqlib Maps Axioms.
Require Import Locations AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Stacklayout Conventions.

Require Import Asm CUAST ValFP val_casted.
Require Import loadframe Footprint FPLemmas GMemory FMemory FMemOpFP FMemLemmas TSOMem TSOMemLemmas Memperm.
Require Import GAST GlobDefs ETrace Blockset.

Require Import Languages.
Require Import TSOGlobSem GlobSemantics InteractionSemantics RGRels ClientSim ObjectSim.
Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.
Require Import MemAux TSOStepAuxLemmas.
Local Ltac simpls := simpl in *.
Local Transparent Mem.load Mem.alloc Mem.store Mem.free.
Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Ltac ex_match:=
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?Hx; try discriminate
         end;try congruence.
Ltac ex_match2:=
  repeat match goal with
         | H: context[match ?x with _ => _ end]  |- _ => destruct x eqn:?Hx; try discriminate
         | H: _ |- context[match ?x with _ => _ end ] => destruct x eqn:?Hx;try discriminate
         end;try congruence;try contradiction.
 
Fixpoint bf_footprint (bf:buffer):FP.t:=
  match bf with
  | nil => FP.emp
  | x::ls => FP.union (bi_footprint x)(bf_footprint ls)
  end.
Lemma bf_footprint_app_union:
  forall bf1 bf2,
    bf_footprint (bf1 ++ bf2) = FP.union (bf_footprint bf1)(bf_footprint bf2).
Proof.
  induction bf1;intros.
  simpl. rewrite FP.emp_union_fp;auto.

  simpl. rewrite <-FP.fp_union_assoc. f_equal.
  eauto.
Qed.
Lemma bi_footprint_cmps_emp:
  forall bi, FP.cmps (bi_footprint bi) = Locs.emp.
Proof. unfold bi_footprint. destruct bi;auto. Qed.
Lemma bi_footprint_reads_emp:
  forall bi, FP.reads (bi_footprint bi) = Locs.emp.
Proof. unfold bi_footprint. destruct bi;auto. Qed.
Lemma bf_footprint_cmps_emp:
  forall bf, FP.cmps (bf_footprint bf) = Locs.emp.
Proof. induction bf;auto. simpl. rewrite bi_footprint_cmps_emp. auto. Qed.
Lemma bf_footprint_reads_emp:
  forall bf, FP.reads (bf_footprint bf) = Locs.emp.
Proof. induction bf;auto;simpl. rewrite bi_footprint_reads_emp;auto. Qed.
Definition eff_eq fp1 fp2 :=
  FP.writes fp1 = FP.writes fp2 /\ FP.frees fp1 = FP.frees fp2.
Lemma eff_eq_refl:forall fp, eff_eq fp fp. Proof. split;auto. Qed.
Lemma eff_eq_union: forall fp1 fp2 fp1' fp2',eff_eq fp1 fp1'->eff_eq fp2 fp2'->eff_eq (FP.union fp1 fp2)(FP.union fp1' fp2').
Proof. unfold eff_eq;constructor;Hsimpl;unfold FP.union;simpl; congruence. Qed.
Lemma fpsmile_eff_eq_trans:
  forall fp0 fp1 fp2,
    FP.smile fp0 fp1 ->
    eff_eq fp0 fp2 ->
    FP.reads fp2 = Locs.emp ->
    FP.cmps fp2 = Locs.emp->
    FP.smile fp2 fp1.
Proof.
  intros ? ? ? [] [] ? ?;Hsimpl;subst.
  econstructor;try split;try congruence.
  rewrite H2. Locs.unfolds. auto.
  rewrite H1. Locs.unfolds. auto.
  rewrite H1. Locs.unfolds. auto.
Qed.
Definition buffer_item_local_alloc bi fl:=  
  match bi with
  | BufferedAlloc b _ _ => in_fl fl b
  | _ => True
  end.
Definition buffer_local_alloc bf fl:=
  forall bi, In bi bf-> buffer_item_local_alloc bi fl.
Lemma buffer_local_alloc_app:
  forall bf1 bf2 fl,
    buffer_local_alloc bf1 fl->
    buffer_local_alloc bf2 fl->
    buffer_local_alloc (bf1 ++ bf2) fl.
Proof.
  unfold buffer_local_alloc in *;intros.
  apply in_app_or in H1 as [];eauto.
Qed.
Definition BufferEff bf bf' fp fl:=
  exists ls, bf' = bf ++ ls /\ eff_eq (bf_footprint ls) fp /\ buffer_local_alloc ls fl.
Lemma BufferEff_refl:
  forall bf fl,BufferEff bf bf FP.emp fl.
Proof. unfold BufferEff;intros;Esimpl;eauto. rewrite app_nil_r;auto. apply eff_eq_refl. unfold buffer_local_alloc;intros;inv H. Qed.
Lemma BufferEff_refl2:
  forall bf fl fp,effects fp = Locs.emp -> BufferEff bf bf fp fl.
Proof.
  unfold BufferEff;intros;Esimpl;eauto. rewrite app_nil_r;auto.
  assert(Locs.eq (effects fp) Locs.emp). rewrite H;apply Locs.eq_refl.
  clear H.
  Locs.unfolds. unfold effects in H0. destruct fp;simpls.
  unfold eff_eq;split;simpl.
  apply Locs.locs_eq. Locs.unfolds. intros.
  specialize (H0 b ofs). apply orb_false_iff in H0 as [];auto.
  apply Locs.locs_eq. Locs.unfolds. intros.
  specialize (H0 b ofs). apply orb_false_iff in H0 as [];auto.
  unfold buffer_local_alloc;intros;inv H0.
Qed.
Lemma BufferEff_union:
  forall bf bf' bf'' fp fp' fl,
    BufferEff bf bf' fp fl ->
    BufferEff bf' bf'' fp' fl->
    BufferEff bf bf'' (FP.union fp fp') fl.
Proof.
  unfold BufferEff;intros.
  Hsimpl. exists (x0 ++ x). rewrite H0,H. split. rewrite app_assoc;auto.
  split. rewrite bf_footprint_app_union. apply eff_eq_union;auto.
  eapply buffer_local_alloc_app;eauto.
Qed.

Definition eff_chg (bf bf':buffer):bool:=
  buffer_eq bf nil && buffer_eq bf bf'.

Lemma eff_chg_f:
  forall bf bf', eff_chg bf bf'= false -> bf <> nil \/ bf <> bf'.
Proof.
  unfold eff_chg. intros.
  destruct buffer_eq;try contradiction;auto.
  simpl in H.
  destruct buffer_eq;try congruence;auto.
Qed.
Lemma eff_chg_t:
  forall bf bf', eff_chg bf bf'= true -> bf = nil /\ bf = bf'.
Proof.
  unfold eff_chg. intros.
  destruct buffer_eq;try discriminate;auto;subst;simpl in H.
  destruct buffer_eq;try discriminate;auto.
Qed.
Section EFFBASE.
  CoFixpoint NFL:freelist:= Streams.const 1%positive.
Lemma tsostorev_app:
  forall chunk m b v m',
    tsostorev chunk m b v =Some m'->
    exists ls, tbuffer m' = tbuffer m ++ ls.
Proof. unfold tsostorev,tsostore;intros. ex_match;inv H. simpl;eauto. Qed.
Lemma tsostorev_bfeff:
  forall chunk m b v m',
    tsostorev chunk m b v =Some m'->
    forall fl,
      BufferEff (tbuffer m)(tbuffer m') (storev_fp chunk b) fl.
Proof.
  unfold tsostorev,tsostore;intros.
  ex_match;inv H. unfold buffer_insert,BufferEff;simpl;eauto.
  eexists;split;eauto.
  simpl. rewrite !FP.fp_union_emp. split;auto.
  apply eff_eq_refl.
  unfold buffer_local_alloc;intros.
  inv H;simpl;auto. inv H0.
Qed.
Lemma store_stack_fmem_bfeff:
  forall m stk ty v a m',
    store_stack_fmem m stk ty v a = Some m'->
    forall fl,
      BufferEff (tbuffer m)(tbuffer m')(store_stack_fp stk ty v) fl.
Proof.
  unfold store_stack_fmem;intros.
  eapply tsostorev_bfeff;eauto.
Qed.
Lemma store_stack_fmem_bf_app:
  forall m stk ty v a m',
    store_stack_fmem m stk ty v a = Some m'->
    exists ls, tbuffer m' = tbuffer m ++ ls.
Proof.
  intros.
  exploit store_stack_fmem_bfeff;eauto.
  instantiate(1:=NFL).
  unfold BufferEff;intros;Hsimpl;eauto.
Qed.
Lemma tsoalloc_app:
  forall m lo hi m' b,
    tsoalloc m lo hi (m',b)->
    exists ls,tbuffer m' = tbuffer m ++ls.
Proof.
  inversion 1;subst. unfold buffer_insert;simpl;eauto.
Qed.
Lemma tsoalloc_bfeff:
  forall m lo hi m' b,
    tsoalloc m lo hi (m',b)->
    BufferEff (tbuffer m)(tbuffer m')(tsoalloc_fp b lo hi)(Mem.freelist (fmemory m)).
Proof.
  unfold BufferEff;intros.
  inv H. simpl. Esimpl;eauto.
  simpl. rewrite FP.fp_union_emp. apply eff_eq_refl.
  unfold buffer_local_alloc;intros.
  inv H. unfold buffer_item_local_alloc. unfold Mem.nextblock,get_block,in_fl;eauto.
  inv H6. rewrite H. eauto.
  inv H0.
Qed.
Local Ltac trynil:=
  try (exists nil;rewrite app_nil_r;auto;fail).
Lemma store_args_fmem_bf_app:
  forall args tys z m stk m',
    store_args_rec_fmem m stk z args tys = Some m'->
    exists ls, tbuffer m' = tbuffer m ++ ls.
Proof.
  induction args;simpl;intros. ex_match;inv H;eauto. trynil.
  ex_match;subst.
  1,2,4,5,6: apply IHargs in H;apply store_stack_fmem_bf_app in Hx1; Hsimpl; rewrite H,H0,<-app_assoc; eauto.
  apply IHargs in H;apply store_stack_fmem_bf_app in Hx2;apply store_stack_fmem_bf_app in Hx3;Hsimpl;rewrite H,H0,H1,<-!app_assoc; eauto.
Qed.
Lemma store_args_fmem_bfeff:
  forall args tys z m stk m',
    store_args_rec_fmem m (Vptr stk Ptrofs.zero) z args tys = Some m'->
    forall fl,
      BufferEff (tbuffer m)(tbuffer m')(store_args_rec_fp stk z tys) fl.
Proof.
  induction args;simpl;intros.
  ex_match. inv Hx. inv H.
  simpl. unfold BufferEff.
  exists nil;rewrite app_nil_r;split;auto.
  split;try apply eff_eq_refl.
  unfold buffer_local_alloc;intros;inv H.
  ex_match;subst;simpls;subst.
  all: try solve[eapply IHargs with(fl:=fl) in H;eauto;simpl in H;eapply BufferEff_union;eauto;unfold BufferEff;Esimpl;simpl;eauto;simpl;[rewrite FP.fp_union_emp;apply eff_eq_refl|unfold buffer_local_alloc,buffer_item_local_alloc;intros;inv H0;[auto|inv H1]]].
  eapply IHargs with(fl:=fl) in H;eauto;simpl in H.
  eapply BufferEff_union;eauto.
  unfold BufferEff;Esimpl;simpl;eauto;simpl.
  rewrite app_assoc;eauto.
  simpl. rewrite FP.fp_union_emp,FP.union_comm_eq. apply eff_eq_refl.
  unfold buffer_local_alloc,buffer_item_local_alloc;intros.
  inv H0;auto. inv H1;auto. inv H0.
Qed.
Lemma loadv_eff_emp:
  forall ge chunk a rs,
    effects (exec_load_fp ge chunk a rs) = Locs.emp .
Proof.
  unfold effects,exec_load_fp,loadv_fp;Locs.unfolds;intros;simpl.
  ex_match2;auto.
Qed.

Lemma TSO_bf_add:
  forall ge fl c gm bf fp c' gm' bf',
    tsostep ge fl c (bf,gm) fp c' (bf',gm')->
    exists ls, bf' = bf ++ ls.
Proof.
  intros.
  inv H. inv H5.
  assert(bf = tbuffer {|tbuffer:=bf;fmemory:=fm|}). auto.
  generalize dependent {|tbuffer:=bf;fmemory:=fm|}.
  intros.
  inv H8;trynil.
  {
    destruct i;simpl in *;try contradiction;inv H4.

    all: trynil.
    all: unfold exec_load_TSO in H5;ex_match;inv H5;trynil.
    all: try (unfold exec_store_TSO in H4;ex_match;inv H4;eapply tsostorev_app;eauto;fail).
    all: try (unfold tso_goto_label in H4;    ex_match;inv H4; trynil).
    unfold buffer_insert;simpl;eauto.
  }
  {
    eapply tsostorev_app in H6.
    eapply tsostorev_app in H5.
    eapply tsoalloc_app in H3.
    Hsimpl. rewrite H4,H,H3.
    rewrite <-!app_assoc. eauto.
  }
  apply tsoalloc_app in H1.
  apply store_args_fmem_bf_app in H3.
  Hsimpl. rewrite H,H1,<-app_assoc;eauto.
Qed.
Lemma TSO_bfeff:
  forall ge fl c gm bf fp c' gm' bf',
    tsostep ge fl c (bf,gm) fp c' (bf',gm')->
    eff_chg bf bf' = false ->
    BufferEff bf bf' fp fl.
Proof.
  intros. rename H0 into R. inv H;inv H5.
  assert(bf = tbuffer {|tbuffer:=bf;fmemory:=fm|}). auto.
  assert(fm = fmemory {|tbuffer:=bf;fmemory:=fm|}). auto.
  generalize dependent {|tbuffer:=bf;fmemory:=fm|}.
  intros. rename H0 into R2.
  inv H8;try apply BufferEff_refl.
  {
    destruct i;simpl in *;ex_match;try contradiction;inv H4;try apply BufferEff_refl.
    all: try (unfold exec_load_TSO in H5;ex_match;inv H5;try apply BufferEff_refl2;try apply loadv_eff_emp;fail).
    all: try (unfold exec_store_TSO in H5;ex_match;inv H5;eapply tsostorev_bfeff;eauto;fail).
    Local Ltac loc_emp:= try rewrite !Locs.locs_union_emp,!Locs.emp_union_locs;auto.
    Local Ltac loc_emp':=
      unfold effects,compare_ints_TSO_fp,tso_cmpu_bool_fp_total,
      compare_longs_TSO_fp,tso_cmplu_bool_fp_total,
      tso_weak_valid_pointer_fp,valid_pointer_fp;simpl;ex_match2;simpl;loc_emp.
    all: try (apply BufferEff_refl2;loc_emp';fail).
    all: try solve[unfold tso_goto_label in H5;ex_match;inv H5;apply BufferEff_refl].
    eapply BufferEff_union. apply BufferEff_refl2;unfold loadv_fp,load_fp;loc_emp.
    {
      simpl. unfold BufferEff. Esimpl;eauto.
      simpl. rewrite FP.fp_union_emp. apply eff_eq_refl.
      unfold buffer_local_alloc. intros. inv H;auto. inv H4.
    }
    all: simpls;apply eff_chg_f in R as [];contradiction.
  }
  {
    eapply tsoalloc_bfeff in H3;eauto.
    eapply BufferEff_union;eauto.
    eapply BufferEff_union;eapply tsostorev_bfeff;eauto.
  }
  {
    eapply BufferEff_refl2.
    revert H5;clear.
    revert ge fp rs.
    induction args;simpl;intros. inv H5;auto.
    inv H5. apply IHargs in H2.
    rewrite effects_union,H2,Locs.locs_union_emp.
    clear H2 IHargs.
    induction H1;auto;unfold loadv_fp;ex_match2;auto.
    rewrite <- H,effects_union,IHeval_builtin_arg_fp1,IHeval_builtin_arg_fp2;auto.
  }
  {
    eapply BufferEff_refl2;eauto.
    revert H3. clear. intros.
    induction H3;auto. rewrite <- H0,effects_union,IHload_arguments_fp,Locs.locs_union_emp.
    revert H;clear.
    intros. induction H;inv H;try inv H0;unfold loadv_fp;ex_match2;auto.
  }
  {
    eapply tsoalloc_bfeff in H1 as ?.
    eapply BufferEff_union;eauto.
    eapply store_args_fmem_bfeff;eauto.
  }
Qed.  
Lemma tsostorev_memunchg:
  forall chunk m b v m',
    tsostorev chunk m b v = Some m'->
    strip (fmemory m) = strip (fmemory m').
Proof.
  unfold tsostorev,tsostore;intros. ex_match;inv H;auto.
Qed.
Lemma store_stack_fmem_memunchg:
  forall m stk ty v a m',
    store_stack_fmem m stk ty v a = Some m'->
    strip (fmemory m) = strip (fmemory m').
Proof. unfold store_stack_fmem. intros; eapply tsostorev_memunchg;eauto. Qed.
Lemma store_args_fmem_memunchg:
  forall args tys z m stk m',
    store_args_rec_fmem m stk z args tys = Some m'->
    strip (fmemory m) = strip (fmemory m').
Proof.
  induction args;simpl;intros;ex_match;subst.
  1,2,4,5,6:apply IHargs in H; apply store_stack_fmem_memunchg in Hx1; congruence.
  apply IHargs in H. apply store_stack_fmem_memunchg in Hx2;apply store_stack_fmem_memunchg in Hx3;congruence.
Qed.
       
Lemma tsoalloc_memunchg:
  forall m lo hi m' b,
    tsoalloc m lo hi (m',b)->
    strip (fmemory m) = strip (fmemory m').
Proof. inversion 1;subst;auto. Qed.
Lemma tsofree_memunchg:
  forall m lo hi m' b,
    tsofree m b lo hi = Some m'->
    strip (fmemory m) = strip (fmemory m').
Proof. inversion 1;subst;auto. Qed.
Lemma TSO_memchg:
  forall ge fl c gm bf fp c' gm' bf',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    gm <> gm' ->
    bf = nil /\ bf' = nil.
Proof.
  intros. inv H. inv H6. inv H9.
  {
    unfold exec_instr_TSO in H4;ex_match;inv H4;auto;try contradiction.
    all: try (unfold exec_load_TSO in H6;ex_match;inv H6;auto; contradiction).
    
    all: try (unfold exec_store_TSO in H6;ex_match;inv H6;apply tsostorev_memunchg in Hx; contradiction).
    all: unfold tso_goto_label in *;ex_match;try inv H6;try contradiction.
    eapply tsofree_memunchg in Hx3. contradiction.
  }
  {
    apply tsoalloc_memunchg in H3.
    apply tsostorev_memunchg in H5;apply tsostorev_memunchg in H6.
    simpl in *. congruence.
  }
  all: try contradiction.
  eapply store_args_fmem_memunchg in H3.
  apply tsoalloc_memunchg in H1.
  simpl in *;congruence.
Qed.  
Lemma TSO_memunchg:
  forall ge fl c gm bf fp c' gm' bf',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    bf <> nil \/ bf' <> bf ->
    gm = gm'.
Proof.
  intros.
  inv H. inv H6. inv H9.
  {
    destruct i;inv H4;inv H3;simpl;auto.
    all: try (unfold exec_load_TSO in H6;ex_match;inv H6;auto).
    all: try(unfold exec_store_TSO in H4;ex_match;inv H4;eapply tsostorev_memunchg in Hx;eauto).
    all: try (unfold tso_goto_label in H4;ex_match;inv H4;auto).
    all: destruct H0;contradiction.
  }
  {
    apply tsoalloc_memunchg in H3.
    apply tsostorev_memunchg in H5;apply tsostorev_memunchg in H6.
    simpl in *. congruence.
  }
  auto.
  auto.
  auto.
  eapply store_args_fmem_memunchg in H3.
  apply tsoalloc_memunchg in H1.
  simpl in *;congruence.
Qed.
End EFFBASE.

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
Definition buffer_safe (bf:buffer)(m:gmem):Prop:= exists m', apply_buffer bf m = Some m'.
Lemma unbuffer_safe_buffer_safe :
  forall m ,
    unbuffer_safe m ->
    forall t,
      buffer_safe (tso_buffers m t) (memory m).
Proof.
  intros.
  eapply unbuffer_safe_apply_buffer' in H;eauto.
Qed.  
Lemma unchanged_content_equiv:
  forall (P : block -> Z -> Prop) (m m' : GMem.gmem'),
    unchanged_content P m m' <-> GMem.unchanged_on P m m'.
Proof.
  split;auto. apply unchanged_content_equiv.
  intro. inv H. econstructor;eauto. econstructor;eauto. econstructor;eauto.
  intro. apply Memperm_validblock in H0 as ?. eapply unchanged_on_perm;auto.
  intro. apply Memperm_validblock in H0 as ?. eapply unchanged_on_perm;eauto.
  eapply unchanged_on_validity in H1;eauto.
Qed.
Lemma alloc_mempost:
  forall m1 m2 b z z0 m1' m2',
    alloc m1 b z z0 = Some m1' ->
    alloc m2 b z z0 = Some m2' ->
    GMem.unchanged_on (belongsto (effects (FMemOpFP.uncheck_alloc_fp b z z0))) m1' m2'.
Proof.
  unfold alloc in *;intros.
  inv H. inv H0.
  constructor.
  {
    unfold GMem.valid_block;simpl.
    unfold belongsto,Locs.belongsto,effects,FMemOpFP.uncheck_alloc_fp;simpl.
    rewrite Locs.emp_union_locs.
    intros.
    ex_match. 
    tauto.
  }
  {
    unfold GMem.valid_block,GMem.perm;simpl.
    unfold belongsto,Locs.belongsto,effects,FMemOpFP.uncheck_alloc_fp;simpl.
    rewrite Locs.emp_union_locs.
    intros.
    ex_match. subst.
    rewrite !PMap.gss.
    tauto.
  }
  {
    unfold GMem.valid_block,GMem.perm;simpl.
    unfold belongsto,Locs.belongsto,effects,FMemOpFP.uncheck_alloc_fp;simpl.
    rewrite Locs.emp_union_locs.
    intros.
    ex_match. subst.
    rewrite !PMap.gss.
    tauto.
  }
Qed.

Lemma free_mempost:
  forall m1 m2 b z z0 m1' m2',
    free m1 b z z0 = Some m1' ->
    free m2 b z z0 = Some m2' ->
    GMem.unchanged_on (belongsto (effects (FMemOpFP.free_fp b z z0))) m1' m2'.
Proof.
  intros.
  unfold free in *.
  ex_match.
  inv H. inv H0.
  constructor.
  {
    unfold GMem.valid_block;simpl.
    unfold belongsto,Locs.belongsto,effects,FMemOpFP.free_fp;simpl.
    rewrite Locs.emp_union_locs.
    intros.
    apply FMemOpFP.range_locset_loc in H. Hsimpl. subst.
    exploit r0. instantiate(1:=ofs) ;omega.
    intro;apply Memperm_validblock in H.
    exploit r. instantiate(1:=ofs) ;omega.
    intro;apply Memperm_validblock in H2.
    tauto.
  }
  {
    unfold GMem.valid_block,GMem.perm;simpl.
    unfold belongsto,Locs.belongsto,effects,FMemOpFP.free_fp;simpl.
    rewrite Locs.emp_union_locs.
    intros.
    apply FMemOpFP.range_locset_loc in H;Hsimpl;subst.
    rewrite !PMap.gss.
    destruct zle;try omega.
    destruct zlt;try omega.
    tauto.
  }
  {
    unfold GMem.valid_block,GMem.perm;simpl.
    unfold belongsto,Locs.belongsto,effects,FMemOpFP.free_fp;simpl.
    rewrite Locs.emp_union_locs.
    intros.
    apply FMemOpFP.range_locset_loc in H;Hsimpl;subst.
    rewrite PMap.gss in H0.
    ex_match2.
    apply andb_false_iff in Hx1.
    destruct Hx1. destruct zle;try omega;try discriminate.
    destruct zlt;try discriminate;try omega.
  }
Qed.

Lemma apply_buffer_app_eq:
  forall bf1 bf2 m m1,
    apply_buffer bf1 m = Some m1 ->
    apply_buffer (bf1++bf2) m = apply_buffer bf2 m1.
Proof.
  induction bf1;intros;simpl.
  inv H;auto.
  simpl in H. unfold optbind in *.
  ex_match.

  eapply IHbf1 in H;eauto.
Qed.  
Lemma alloc_eff:
  forall m b z z0 m',
    alloc m b z z0 = Some m'->
    MemEffect m m' (FMemOpFP.uncheck_alloc_fp b z z0).
Proof.
  intros; unfold alloc in *;inv H.
  unfold FMemOpFP.uncheck_alloc_fp.
  constructor;simpl.
  {
    unfold effects,notbelongsto;simpl. rewrite Locs.emp_union_locs.
    constructor. constructor.
    {
      unfold unchanged_validity;intros.
      ex_match. unfold GMem.valid_block;simpl.
      split;intro;auto.
      destruct H0;auto;try contradiction.
    }
    {
      unfold GMem.eq_perm;intros.
      ex_match.
      unfold GMem.perm;simpl.
      rewrite PMap.gso;auto.
      tauto.
    }
    {
      intros.
      simpl.
      rewrite PMap.gsspec.
      ex_match2;auto;subst;try congruence.
    }
  }
  {
    split.
    unfold unchanged_validity.
    unfold notbelongsto,GMem.valid_block;simpl.
    intros;ex_match.
    split;intro;try tauto.
    destruct H0;try congruence.
    unfold GMem.eq_perm,notbelongsto.
    intros. ex_match.
    unfold GMem.perm;simpl.
    rewrite PMap.gso;auto. tauto.
  }
  {
    intros.
    inv H.
    {
      unfold GMem.perm in *. simpl in *.
      rewrite PMap.gsspec in H1.
      ex_match2;subst.
      contradict H1. constructor.
      unfold Locs.belongsto.
      ex_match2.
    }
    {
      unfold GMem.perm in *;simpl in*.
      rewrite PMap.gsspec in H1;unfold Locs.belongsto;ex_match2.
      subst;contradiction.
    }
  }
  {
    unfold GMem.valid_block;simpl;tauto.
  }
Qed.
Lemma tsoalloc_eff:
  forall m lo hi m' b,
    tsoalloc m lo hi (m',b) ->
    exists m1,
      apply_buffer (tbuffer m) (strip (fmemory m)) = Some m1 /\
      exists m2,
        apply_buffer (tbuffer m')(strip (fmemory m')) = Some m2 /\
        LEffect m1 m2 (tsoalloc_fp b lo hi)(Mem.freelist (fmemory m)).
Proof.
  inversion 1;subst. clear H.
  simpl. intros.
  exists gm'. split;auto.
  erewrite apply_buffer_app_eq;eauto.
  assert(exists m2,  apply_buffer (BufferedAlloc (Mem.nextblock fm') lo hi :: nil) gm' = Some m2).
  eexists. constructor.
  Hsimpl;Esimpl;eauto. 
  unfold apply_buffer,apply_buffer_item,optbind in H.
  ex_match.
  apply alloc_eff in Hx as ?.
  inv H. split;auto.
  unfold LocalAlloc.
  unfold alloc in Hx;inv Hx.
  unfold GMem.valid_block;simpl;intros;try contradiction.
  destruct H1;try contradiction.
  unfold Mem.nextblock,get_block in H1.
  unfold in_fl.
  inv H6. rewrite H2.
  eauto.
Qed.
Lemma free_eff:
  forall m b lo hi m',
    free m b lo hi = Some m'->
    MemEffect m m' (free_fp b lo hi).
Proof.
  intros.
  unfold free in H;ex_match.
  clear Hx.
  unfold unchecked_free in H. inv H.
  constructor;gmem_unfolds;simpl;Esimpl;intros;try tauto.
  {
    rewrite Locs.emp_union_locs in *.
    unfold range_locset in H. ex_match;subst.
    rewrite PMap.gss.
    assert(lo + (hi - lo) = hi). omega.
    rewrite <- H0,H. tauto.

    rewrite PMap.gso;auto. tauto.
  }
  {
    unfold range_locset in H. ex_match;subst.
    rewrite PMap.gss.
    assert(lo + (hi - lo) = hi). omega.
    rewrite <- H0,H. tauto.

    rewrite PMap.gso;auto. tauto.
  }
  {
    inv H;gmem_unfolds.
    rewrite PMap.gsspec in H1.
    unfold range_locset. ex_match2.
    assert(lo + (hi - lo) = hi). omega.
    rewrite H;auto.

    rewrite PMap.gsspec in H1.
    unfold range_locset. ex_match2.
  }
Qed.
Lemma store_eff:
  forall m chunk b ofs v m',
    store chunk m b ofs v = Some m'->
    MemEffect m m' (store_fp chunk b ofs).
Proof.
  unfold store;intros;ex_match;inv H.
  unfold store_fp.
  constructor;gmem_unfolds;simpl;Esimpl;intros;try tauto.
  rewrite Locs.locs_union_emp in H.
  unfold range_locset in H.
  ex_match.
  subst. rewrite PMap.gss.
  rewrite Mem.setN_outside;auto.
  destruct zle. Focus 2. left. omega.
  destruct zlt. inv H. right. rewrite encode_val_length. rewrite <-size_chunk_conv. auto.

  rewrite PMap.gso;auto.

  inv H;unfold GMem.perm in *;simpl in *;contradiction.
Qed.
Lemma MemPre_union:
  forall m0 m1 fp fp',
    MemPre m0 m1 fp->
    MemPre m0 m1 fp'->
    MemPre m0 m1 (FP.union fp fp').
Proof.
  intros. inv H. inv H0.
  constructor.
  eapply unchanged_content_union2 in ReadMemEq0;try apply ReadMemEq;eauto.
  eapply unchanged_perm_union2 in CmpMemPermExists0;try exact CmpMemPermExists;eauto.

  unfold FP.union,effects in *;simpl in *.
  unfold belongsto,Locs.belongsto,Locs.union in *.
  intros.
  apply orb_true_iff in H as [|];apply orb_true_iff in H as [|].
  all: try (apply EffectPermEqPre;rewrite H;auto with bool).
  all: try (apply EffectPermEqPre0;rewrite H;auto with bool).
Qed.
Lemma Fleq_apply_buffer_item_preserve:
  forall m0 m1 bf m0' m1' fl,
    FreelistEq m0 m1 fl ->
    apply_buffer_item bf m0 = Some m0' ->
    apply_buffer_item bf m1 = Some m1' ->
    FreelistEq m0' m1' fl.
Proof.
  destruct bf;simpl;intros.
  {
    unfold FreelistEq in *.
    intros.
    specialize (H _ H2).
    destruct (peq b b0).
    {
      subst.
      apply alloc_add_new_vb in H1.
      apply alloc_add_new_vb in H0.
      unfold GMem.valid_block. rewrite<- H1,<- H0.
      simpl;split;intro; auto.
    }
    {
      unfold alloc in H0,H1;inv H0;inv H1;unfold GMem.valid_block;simpl.
      split;intro;inv H0;try contradiction;right;eauto;eapply H;eauto.
    }
  }
  {
    unfold FreelistEq in *.
    intros. specialize (H _ H2).
    unfold free in *;ex_match.
    unfold unchecked_free in *;inv H0;inv H1.
    unfold GMem.valid_block;simpl.
    auto.
  }
  {
    unfold FreelistEq in *.
    intros. specialize (H _ H2).
    unfold store in *;ex_match. inv H1. inv H0.
    unfold GMem.valid_block;simpl. auto.
  }
Qed.
Lemma MemPre_apply_buffer_item_preserve:
  forall m0 m1 bf m0' m1' fp,
    MemPre m0 m1 fp->
    apply_buffer_item bf m0 = Some m0'->
    apply_buffer_item bf m1 = Some m1'->
    MemPre m0' m1' fp.
Proof.
  destruct bf;simpl;  intros;pose proof True as H2.
  {
    {
      apply alloc_eff in H0 as ?.
      apply alloc_eff in H1 as ?.
      eapply alloc_mempost in H0 as ?;eauto.
      constructor.
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            eapply H;eauto.
          }
        }
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5. unfold belongsto;Locs.unfolds. ex_match2. auto.
            unfold alloc in H1. inv H1.
            unfold GMem.valid_block;simpl;auto.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            eapply H;eauto.
          }
        }
        {
          destruct (peq b0 b).
          {
            subst. apply unchanged_on_sym in H5.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. ex_match2. auto.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(GMem.perm m0 b0 ofs Max Readable).
            {
              unfold alloc in H0;inv H0.
              simpl in H7. rewrite PMap.gso in H7;auto.
            }
            eapply H3 in H8 as ?;eauto.
            eapply H4 in H8 as ?;eauto.
            rewrite H10,H11.
            eapply H;eauto.
            eapply H;eauto.
          }
        }
      }
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            inv H. eapply CmpMemPermExists;eauto.
          }
        }
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5. unfold belongsto;Locs.unfolds. ex_match2. auto.
            unfold alloc in H1. inv H1.
            unfold GMem.valid_block;simpl;auto.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            inv H. eapply CmpMemPermExists;eauto.
          }
        }
      }
      {
        intros. gmem_unfolds.
        destruct (peq b0 b).
        {
          subst. symmetry.
          eapply H5. unfold belongsto;Locs.unfolds. ex_match2. auto.
          unfold alloc in H1. inv H1.
          unfold GMem.valid_block;simpl;auto.
        }
        {
          assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
          unfold notbelongsto,effects,uncheck_alloc_fp.
          simpl. Locs.unfolds.
          ex_match2;auto.
          assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H3;auto.
          assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
          destruct H8 as [[_ ?] _].
          destruct H9 as [[_ ?] _].
          specialize (H8 _ _ k p H7).
          specialize (H9 _ _ k p H7).
          rewrite<- H8. rewrite <- H9.
          inv H. eapply EffectPermEqPre;eauto.
        }
      }
    }

  }
  {
    {
      apply free_eff in H0 as ?.
      apply free_eff in H1 as ?.
      eapply free_mempost in H0 as ?;eauto.
      constructor.
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            eapply H;eauto.
          }
        }
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            split;intro;eapply H5;eauto;apply Memperm_validblock in H7;auto.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            eapply H;eauto.
          }
        }
        {
          destruct  (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            eapply H5;eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(GMem.perm m0 b0 ofs Max Readable).
            {
              unfold free in H0;ex_match.
              unfold unchecked_free in H0;inv H0.
              simpl in *.
              unfold range_locset in Heqb1. ex_match.
              assert(z+(z0-z) = z0). omega.
              rewrite H0 in Heqb1. subst.
              rewrite PMap.gss in H7.
              rewrite Heqb1 in H7.
              auto.

              rewrite PMap.gso in H7; auto.
            }
            
            eapply H3 in H8 as ?;eauto.
            eapply H4 in H8 as ?;eauto.
            rewrite H10,H11.
            eapply H;eauto.
            eapply H;eauto.
          }
        }
      }
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            inv H. eapply CmpMemPermExists;eauto.
          }
        }
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            split;intro;eapply H5;eauto;apply Memperm_validblock in H7;auto.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            inv H. eapply CmpMemPermExists;eauto.
          }
        }
      }
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            split;intro;eapply H5;eauto;apply Memperm_validblock in H7;auto.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H3;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            inv H. eapply EffectPermEqPre;eauto.
          }
        }
      }
    }
  }
  {
    rename H2 into R. rename H into H2. rename R into H3.
    {
      constructor;gmem_unfolds;Esimpl;intros;unfold store in *;ex_match;inv H0;inv H1;simpl;try (eapply H2;eauto;fail).
      destruct (range_locset b z (size_chunk m) b0 ofs) eqn:?.
      {
        unfold range_locset in Heqb1. ex_match. subst.
        rewrite! PMap.gss.
        apply andb_true_iff in Heqb1 as [].
        destruct zle;try discriminate.
        destruct zlt;try discriminate.
        apply setN_geteq2;auto.
        rewrite encode_val_length.
        rewrite<- size_chunk_conv. auto.
      }
      {
        unfold range_locset in Heqb1. ex_match;subst.
        {
          rewrite! PMap.gss.
          apply andb_false_iff in Heqb1.
          destruct Heqb1;[destruct zle|destruct zlt];try discriminate.
          erewrite !Mem.setN_outside;eauto;try (left;omega).
          apply H2;auto.

          erewrite !Mem.setN_outside;eauto. apply H2;auto.
          rewrite encode_val_length,<-size_chunk_conv;auto.
          rewrite encode_val_length,<-size_chunk_conv;auto.
        }
        {
          rewrite !PMap.gso;auto.
          apply H2;auto.
        }
      }
      
      inv H2. eapply CmpMemPermExists;eauto.
      inv H2. eapply CmpMemPermExists;eauto.
      inv H2. eapply EffectPermEqPre;eauto.
    }
  }
Qed.    
Lemma LPre_apply_buffer_item_preserve:
  forall m0 m1 bf m0' m1' fp fl,
    LPre m0 m1 fp fl->
    apply_buffer_item bf m0 = Some m0'->
    apply_buffer_item bf m1 = Some m1'->
    LPre m0' m1' fp fl.
Proof.
  destruct bf;simpl;  intros.
  {
    inv H;constructor.
    {
      apply alloc_eff in H0 as ?.
      apply alloc_eff in H1 as ?.
      eapply alloc_mempost in H0 as ?;eauto.
      
      constructor.
      {
        
        gmem_unfolds;Esimpl;intros.
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            eapply H2;eauto.
          }
        }
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5. unfold belongsto;Locs.unfolds. ex_match2. auto.
            unfold alloc in H1. inv H1.
            unfold GMem.valid_block;simpl;auto.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            eapply H2;eauto.
          }
        }
        {
          destruct (peq b0 b).
          {
            subst. apply unchanged_on_sym in H5.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. ex_match2. auto.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(GMem.perm m0 b0 ofs Max Readable).
            {
              unfold alloc in H0;inv H0.
              simpl in H7. rewrite PMap.gso in H7;auto.
            }
            eapply H in H8 as ?;eauto.
            eapply H4 in H8 as ?;eauto.
            rewrite H10,H11.
            eapply H2;eauto.
            eapply H2;eauto.
          }
        }
      }
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            inv H2. eapply CmpMemPermExists;eauto.
          }
        }
        {
          destruct (peq b0 b).
          {
            subst. symmetry.
            eapply H5. unfold belongsto;Locs.unfolds. ex_match2. auto.
            unfold alloc in H1. inv H1.
            unfold GMem.valid_block;simpl;auto.
          }
          {
            assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,uncheck_alloc_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            inv H2. eapply CmpMemPermExists;eauto.
          }
        }
      }
      {
        intros. gmem_unfolds.
        destruct (peq b0 b).
        {
          subst. symmetry.
          eapply H5. unfold belongsto;Locs.unfolds. ex_match2. auto.
          unfold alloc in H1. inv H1.
          unfold GMem.valid_block;simpl;auto.
        }
        {
          assert(notbelongsto (effects (uncheck_alloc_fp b z z0)) b0 ofs).
          unfold notbelongsto,effects,uncheck_alloc_fp.
          simpl. Locs.unfolds.
          ex_match2;auto.
          assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m0 m0'). inv H;auto.
          assert(unchanged_content (notbelongsto (effects (uncheck_alloc_fp b z z0))) m1 m1'). inv H4;auto.
          destruct H8 as [[_ ?] _].
          destruct H9 as [[_ ?] _].
          specialize (H8 _ _ k p H7).
          specialize (H9 _ _ k p H7).
          rewrite<- H8. rewrite <- H9.
          inv H2. eapply EffectPermEqPre;eauto.
        }
      }
    }
    {
      unfold FreelistEq in *.
      intros.
      specialize (H3 _ H).
      destruct (peq b b0).
      {
        subst.
        apply alloc_add_new_vb in H1.
        apply alloc_add_new_vb in H0.
        unfold GMem.valid_block. rewrite<- H1,<- H0.
        simpl;split;intro; auto.
      }
      {
        unfold alloc in H0,H1;inv H0;inv H1;unfold GMem.valid_block;simpl.
        split;intro;inv H0;try contradiction;right;eauto;eapply H3;eauto.
      }
    }
  }
  {
    inv H. constructor.
    {
      apply free_eff in H0 as ?.
      apply free_eff in H1 as ?.
      eapply free_mempost in H0 as ?;eauto.
      constructor.
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            eapply H2;eauto.
          }
        }
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            split;intro;eapply H5;eauto;apply Memperm_validblock in H7;auto.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            eapply H2;eauto.
          }
        }
        {
          destruct  (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            eapply H5;eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(GMem.perm m0 b0 ofs Max Readable).
            {
              unfold free in H0;ex_match.
              unfold unchecked_free in H0;inv H0.
              simpl in *.
              unfold range_locset in Heqb1. ex_match.
              assert(z+(z0-z) = z0). omega.
              rewrite H0 in Heqb1. subst.
              rewrite PMap.gss in H7.
              rewrite Heqb1 in H7.
              auto.

              rewrite PMap.gso in H7; auto.
            }
            
            eapply H in H8 as ?;eauto.
            eapply H4 in H8 as ?;eauto.
            rewrite H10,H11.
            eapply H2;eauto.
            eapply H2;eauto.
          }
        }
      }
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. symmetry.
            eapply H5.
            instantiate(1:=ofs).
            unfold belongsto.
            Locs.unfolds. ex_match2. auto with bool.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[? _] _].
            destruct H9 as [[? _] _].
            apply H8 in H7 as ?.
            apply H9 in H7 as ?.
            rewrite <-H11. rewrite <- H10.
            inv H2. eapply CmpMemPermExists;eauto.
          }
        }
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            split;intro;eapply H5;eauto;apply Memperm_validblock in H7;auto.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            inv H2. eapply CmpMemPermExists;eauto.
          }
        }
      }
      {
        gmem_unfolds;Esimpl;intros.
        {
          destruct (range_locset b z (z0 -z) b0 ofs) eqn:?.
          {
            subst. apply unchanged_on_sym in H5.
            split;intro;eapply H5;eauto;apply Memperm_validblock in H7;auto.
            eapply H5;eauto.
            unfold belongsto;Locs.unfolds. eauto.
          }
          {
            assert(notbelongsto (effects (free_fp b z z0)) b0 ofs).
            unfold notbelongsto,effects,free_fp.
            simpl. Locs.unfolds.
            ex_match2;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m0 m0'). inv H;auto.
            assert(unchanged_content (notbelongsto (effects (free_fp b z z0))) m1 m1'). inv H4;auto.
            destruct H8 as [[_ ?] _].
            destruct H9 as [[_ ?] _].
            specialize (H8 _ _ k p H7).
            specialize (H9 _ _ k p H7).
            rewrite<- H8. rewrite <- H9.
            inv H2. eapply EffectPermEqPre;eauto.
          }
        }
      }
    }
    {
      unfold FreelistEq in *.
      intros. specialize (H3 _ H).
      unfold free in *;ex_match.
      unfold unchecked_free in *;inv H0;inv H1.
      unfold GMem.valid_block;simpl.
      auto.
    }
  }
  {
    inv H. constructor.
    {
      constructor;gmem_unfolds;Esimpl;intros;unfold store in *;ex_match;inv H0;inv H1;simpl;try (eapply H2;eauto;fail).
      destruct (range_locset b z (size_chunk m) b0 ofs) eqn:?.
      {
        unfold range_locset in Heqb1. ex_match. subst.
        rewrite! PMap.gss.
        apply andb_true_iff in Heqb1 as [].
        destruct zle;try discriminate.
        destruct zlt;try discriminate.
        apply setN_geteq2;auto.
        rewrite encode_val_length.
        rewrite<- size_chunk_conv. auto.
      }
      {
        unfold range_locset in Heqb1. ex_match;subst.
        {
          rewrite! PMap.gss.
          apply andb_false_iff in Heqb1.
          destruct Heqb1;[destruct zle|destruct zlt];try discriminate.
          erewrite !Mem.setN_outside;eauto;try (left;omega).
          apply H2;auto.

          erewrite !Mem.setN_outside;eauto. apply H2;auto.
          rewrite encode_val_length,<-size_chunk_conv;auto.
          rewrite encode_val_length,<-size_chunk_conv;auto.
        }
        {
          rewrite !PMap.gso;auto.
          apply H2;auto.
        }
      }
      
      inv H2. eapply CmpMemPermExists;eauto.
      inv H2. eapply CmpMemPermExists;eauto.
      inv H2. eapply EffectPermEqPre;eauto.
    }
    {
      unfold FreelistEq in *.
      intros. specialize (H3 _ H).
      unfold store in H0,H1;ex_match;inv H0;inv H1.
      unfold GMem.valid_block;simpl.
      auto.
    }
  }
Qed.
Lemma Fleq_apply_buffer_preserve:
  forall bf m0 m1 m0' m1' fl,
    FreelistEq m0 m1 fl ->
    apply_buffer bf m0 = Some m0' ->
    apply_buffer bf m1 = Some m1' ->
    FreelistEq m0' m1' fl.
Proof.
  induction bf;intros; simpl in *. do 2 inv_some. auto.
  unfold optbind in H0,H1. ex_match.
  eapply Fleq_apply_buffer_item_preserve in H;try exact Hx0;eauto.
Qed.
Lemma MemPre_apply_buffer_preserve:
  forall bf m0 m1 m0' m1' fp,
    MemPre m0 m1 fp->
    apply_buffer bf m0 = Some m0'->
    apply_buffer bf m1 = Some m1'->
    MemPre m0' m1' fp.
Proof.
  induction bf;simpl;intros.
  inv H0;inv H1;auto.
  unfold optbind in *. ex_match.
  exploit MemPre_apply_buffer_item_preserve;eauto.
Qed.
Lemma LPre_apply_buffer_preserve:
  forall bf m0 m1 m0' m1' fp fl,
    LPre m0 m1 fp fl->
    apply_buffer bf m0 = Some m0'->
    apply_buffer bf m1 = Some m1'->
    LPre m0' m1' fp fl.
Proof.
  induction bf;simpl;intros.
  inv H0;inv H1;auto.
  unfold optbind in *. ex_match.
  exploit LPre_apply_buffer_item_preserve;eauto.
Qed.


Lemma apply_buffer_item_eff:
  forall bi m m',
    apply_buffer_item bi m = Some m'->
    MemEffect m m' (bi_footprint bi).
Proof.
  destruct bi;unfold apply_buffer_item;intros.
  apply alloc_eff;auto.
  apply free_eff;auto.
  apply store_eff in H;auto.
Qed.

Lemma apply_buffer_eff:
  forall bi m m',
    apply_buffer bi m = Some m'->
    MemEffect m m' (bf_footprint bi).
Proof.
  induction bi;intros;inv H. simpl. apply MemEffect_refl.
  unfold optbind in H1;ex_match;inv H1.
  apply IHbi in H0.
  apply apply_buffer_item_eff in Hx.
  eapply MemEffect_trans;eauto. eapply MemEffect_union_fp;eauto.
  simpl. rewrite FP.union_comm_eq. eapply MemEffect_union_fp;eauto.
Qed.
Lemma exec_store_TSO_eff:
  forall ge chunk m a rs b c rs' m' m1 m2,
    exec_store_TSO ge chunk m a rs b c = Next rs' m'->
    apply_buffer (tbuffer m)(strip (fmemory m)) = Some m1->
    apply_buffer (tbuffer m')(strip (fmemory m')) = Some m2 ->
    LEffect m1 m2 (exec_store_fp ge chunk a rs)(Mem.freelist (fmemory m)).
Proof.
  intros.
  unfold exec_store_TSO,tsostorev,tsostore in H.
  ex_match.
  inv H. inv Hx. simpl in *.
  apply apply_buffer_split in H1 as [?[]].
  rewrite H0 in H;inv H.
  simpl in H1. unfold optbind in H1.
  ex_match. inv H1.
  apply store_eff in Hx as ?.
  split;auto. unfold exec_store_fp,storev_fp. rewrite Hx0. auto.
  unfold LocalAlloc.
  intros. unfold store in Hx. ex_match. inv Hx.
  unfold GMem.valid_block in H2. simpl in H2. contradiction.
Qed.
Lemma store_args_rec_fmem_applyable_backwards:
  forall args m1 b i tys m2,
    store_args_rec_fmem m1 (Vptr b Ptrofs.zero) i args tys = Some m2 ->
    forall m2',
      apply_buffer (tbuffer m2)(strip (fmemory m2)) = Some m2'->
      exists m1',
        apply_buffer (tbuffer m1)(strip (fmemory m1)) = Some m1'.
Proof.
  intros.
  apply store_args_fmem_bf_app in H as ?. Hsimpl.
  apply store_args_fmem_memunchg in H as ?;subst.
  rewrite H1 in H0. apply apply_buffer_split in H0.
  Hsimpl.
  rewrite H2.
  eauto.
Qed.
Lemma store_args_rec_fmem_eff_inv:
  forall args m1 b i tys m2,
    store_args_rec_fmem m1 (Vptr b Ptrofs.zero) i args tys = Some m2 ->
    forall m1',
      apply_buffer (tbuffer m1)(strip (fmemory m1)) = Some m1' ->
      forall m2',
        apply_buffer (tbuffer m2)(strip (fmemory m2)) = Some m2'->
        LEffect m1' m2' (loadframe.store_args_rec_fp b i tys)(Mem.freelist (fmemory m1)).
Proof.
  induction args;simpl;intros.
  ex_match. inv H. rewrite H0 in H1. inv H1. apply LEffect_refl.

  ex_match;subst;simpl in *.
  {
    exploit store_args_rec_fmem_applyable_backwards;eauto;simpl;intros [].
    apply apply_buffer_split in H2 as ?;Hsimpl.
    rewrite H3 in H0;inv H0.

    exploit IHargs;eauto;simpl;intro.
    eapply LEffect_trans_union;eauto.
    unfold apply_buffer,optbind in H4;ex_match;inv H4.
    apply apply_buffer_item_eff in Hx as ?.
    split;auto. simpl in Hx. unfold store in Hx;ex_match;inv Hx.
    unfold LocalAlloc,GMem.valid_block;simpl;intros;contradiction.
  }
  {
    exploit store_args_rec_fmem_applyable_backwards;eauto;simpl;intros [].
    apply apply_buffer_split in H2 as ?;Hsimpl.
    rewrite H3 in H0;inv H0.

    exploit IHargs;eauto;simpl;intro.
    eapply LEffect_trans_union;eauto.
    unfold apply_buffer,optbind in H4;ex_match;inv H4.
    apply apply_buffer_item_eff in Hx as ?.
    split;auto. simpl in Hx. unfold store in Hx;ex_match;inv Hx.
    unfold LocalAlloc,GMem.valid_block;simpl;intros;contradiction.
  }
  {
    exploit store_args_rec_fmem_applyable_backwards;eauto;simpl;intros [].
    apply apply_buffer_split in H2 as ?;Hsimpl.
    apply apply_buffer_split in H3 as ?;Hsimpl.
    rewrite H5 in H0;inv H0.

    exploit IHargs;eauto;simpl;intro.
    eapply LEffect_trans_union;eauto.
    unfold apply_buffer,optbind in H4,H6;ex_match;inv H4;inv H6.
    apply apply_buffer_item_eff in Hx as ?.
    apply apply_buffer_item_eff in Hx0 as ?.
    rewrite FP.union_comm_eq.
    eapply LEffect_trans_union with(m2:=x0).
    split;auto.
    simpl in *. unfold store in Hx0;ex_match;inv Hx0.
    unfold LocalAlloc,GMem.valid_block;simpl;intros;try contradiction.

    split;auto.
    simpl in *. unfold store in Hx;ex_match;inv Hx.
    unfold LocalAlloc,GMem.valid_block;simpl;intros;try contradiction.
  }
  {
    exploit store_args_rec_fmem_applyable_backwards;eauto;simpl;intros [].
    apply apply_buffer_split in H2 as ?;Hsimpl.
    rewrite H3 in H0;inv H0.

    exploit IHargs;eauto;simpl;intro.
    eapply LEffect_trans_union;eauto.
    unfold apply_buffer,optbind in H4;ex_match;inv H4.
    apply apply_buffer_item_eff in Hx as ?.
    split;auto. simpl in Hx. unfold store in Hx;ex_match;inv Hx.
    unfold LocalAlloc,GMem.valid_block;simpl;intros;contradiction.
  }
  {
    exploit store_args_rec_fmem_applyable_backwards;eauto;simpl;intros [].
    apply apply_buffer_split in H2 as ?;Hsimpl.
    rewrite H3 in H0;inv H0.

    exploit IHargs;eauto;simpl;intro.
    eapply LEffect_trans_union;eauto.
    unfold apply_buffer,optbind in H4;ex_match;inv H4.
    apply apply_buffer_item_eff in Hx as ?.
    split;auto. simpl in Hx. unfold store in Hx;ex_match;inv Hx.
    unfold LocalAlloc,GMem.valid_block;simpl;intros;contradiction.
  }
  {
    exploit store_args_rec_fmem_applyable_backwards;eauto;simpl;intros [].
    apply apply_buffer_split in H2 as ?;Hsimpl.
    rewrite H3 in H0;inv H0.

    exploit IHargs;eauto;simpl;intro.
    eapply LEffect_trans_union;eauto.
    unfold apply_buffer,optbind in H4;ex_match;inv H4.
    apply apply_buffer_item_eff in Hx as ?.
    split;auto. simpl in Hx. unfold store in Hx;ex_match;inv Hx.
    unfold LocalAlloc,GMem.valid_block;simpl;intros;contradiction.
  }
Qed.

Record TEffect gm bf gm' bf' fp fl:=
  {
    img_eff:forall m1', apply_buffer bf gm = Some m1' ->
                   forall m2', apply_buffer bf' gm' = Some m2' ->
                          LEffect m1' m2' fp fl;
    mem_unchg: bf <> nil \/ bf <> bf' -> gm = gm';
    mem_chg: gm <> gm' -> bf = bf' /\ bf = nil;
    bf_chg: exists ls, bf' = bf ++ ls;
    bf_eff: bf <> nil \/ bf <> bf' -> BufferEff bf bf' fp fl;
  }.
Lemma TSO_eff:
  forall ge fl c gm bf fp c' gm' bf',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    TEffect gm bf gm' bf' fp fl.
Proof.
  intros.
  constructor.
  {
    intros.
    inv H. inv H7. inv H10.
    {
      destruct i;inv H5;inv H4;simpl in *.
      all: try(rewrite H0 in H1;inv H1; apply LEffect_refl;fail).
      all: try(unfold exec_load_TSO in H7;ex_match;inv H7;simpl in *;rewrite H0 in H1;inv H1;apply LEffect_refl).
      all: try (eapply exec_store_TSO_eff in H7;eauto;fail).
      all: try (unfold tso_goto_label in H7;ex_match;inv H7;simpl in *;rewrite H0 in H1;inv H1;apply LEffect_refl;fail).
      {
        ex_match;inv H7;simpl in *.
        ex_match.
        inv H0.
        apply apply_buffer_split in H1;Hsimpl.
        rewrite H0 in Hx2;inv Hx2.
        simpl in H1. unfold optbind in H1.
        ex_match. inv H1.
        apply free_eff in Hx2 as ?.
        split.
        rewrite FP.union_comm_eq. apply MemEffect_union_fp. auto.
        unfold LocalAlloc. intros.
        unfold free in Hx2;ex_match;inv Hx2. unfold unchecked_free,GMem.valid_block in H5;simpl in H5. contradiction.
      }
      {
        ex_match;inv H7;simpl in *.
        inv H0;inv H1.
        apply mem_storev_eff in Hx1.
        destruct Hx1;split;auto.
        rewrite FP.union_comm_eq. apply MemEffect_union_fp;auto.
      }
      {
        ex_match; inv H7;simpl in *;inv H0;inv H1.
        apply mem_storev_eff in Hx3 as [];split;auto.
        rewrite FP.fp_union_assoc,FP.union_comm_eq. apply MemEffect_union_fp;auto.

        apply LEffect_refl.
      }
      {
        ex_match. inv H7. simpl in *. inv H0;inv H1.
        apply mem_storev_eff in Hx2 as [];split;auto.
        rewrite FP.union_comm_eq;apply MemEffect_union_fp;auto.
      }
    }
    {
      inv H4;inv H6;inv H7.
      simpl in *.
      repeat apply apply_buffer_split in H1 as [?[]].
      rewrite H1 in H12;inv H12.
      rewrite H1 in H0;inv H0.
      eapply LEffect_trans_union with(m2:=x0).
      {
        unfold apply_buffer,apply_buffer_item,optbind in H6.
        ex_match;inv H6.
        apply alloc_eff in Hx as ?.
        split;auto.
        unfold alloc in Hx;inv Hx.
        unfold LocalAlloc,GMem.valid_block;simpl.
        intros. destruct H7;try contradiction.
        unfold Mem.nextblock,get_block in H7.
        unfold in_fl. inv H14. rewrite H8. eauto.
      }
      eapply LEffect_trans_union with(m2:=x).
      {
        unfold apply_buffer,apply_buffer_item,optbind in H5.
        ex_match;inv H5.
        apply store_eff in Hx as ?.
        split;auto.
        unfold LocalAlloc,GMem.valid_block;simpl;intros.
        unfold store in Hx;ex_match;inv Hx.
        simpl in H7. contradiction.
      }
      unfold apply_buffer,apply_buffer_item,optbind in H4.
      ex_match;inv H4.
      apply store_eff in Hx as ?.
      split;auto.
      unfold LocalAlloc,GMem.valid_block.
      unfold store in Hx;ex_match;inv Hx;simpl;intros;contradiction.
    }
    simpl in H1;rewrite H0 in H1;inv H1;apply LEffect_refl.
    simpl in H1;rewrite H0 in H1;inv H1;apply LEffect_refl.
    simpl in H1;rewrite H0 in H1;inv H1;apply LEffect_refl.

    eapply tsoalloc_eff in H2 as ?.
    Hsimpl. simpl in H3.
    rewrite H0 in H3;inv H3.
    

    eapply LEffect_trans_union;eauto.
    unfold store_args_fmem in H4.
    eapply store_args_rec_fmem_eff_inv in H4;eauto.
    assert(Mem.freelist (fmemory bm1) = Mem.freelist fm).
    inv H2. inv H13. simpl. auto.
    unfold loadframe.store_args_fp.
    rewrite H3 in H4. auto.
  }
  intros. eapply TSO_memunchg;eauto. destruct H0;auto.
  intro. eapply TSO_memchg in H0;eauto. Hsimpl;subst;eauto.
  eapply TSO_bf_add in H. eauto.
  intros.
  eapply TSO_bfeff;eauto.
  destruct (eff_chg) eqn:?;auto.
  apply eff_chg_t in Heqb as [];subst.
  destruct H0;contradiction.
Qed.

Lemma TEffect_LocalAlloc:
  forall gm bf gm' bf' fp fl,
    TEffect gm bf gm' bf' fp fl ->
    LocalAlloc gm gm' fl.
Proof.
  intros.
  destruct (eff_chg bf bf') eqn:?.
  {
    apply eff_chg_t in Heqb as [];subst.
    exploit img_eff;try exact H;simpl;eauto.
    inversion 1;subst;auto.
  }
  {
    apply eff_chg_f in Heqb.
    exploit mem_unchg;eauto;intro;subst.
    apply LocalAlloc_refl.
  }
Qed.

Definition TEffect2  gm bf gm' bf' fp fl:=
  if eff_chg bf bf' then LEffect gm gm' fp fl
  else BufferEff bf bf' fp fl /\ gm = gm'.

Lemma MemEffect_eq_on_eff:
  forall fp1 fp2,
    eff_eq fp1 fp2->
    forall m1 m2,
      MemEffect m1 m2 fp1->
      MemEffect m1 m2 fp2.
Proof.
  unfold eff_eq.
  intros. inv H0.
  Hsimpl.
  constructor;auto.
  unfold effects. rewrite <- H,<- H0;auto.
  congruence.
  rewrite <- H0. auto.
Qed.
Lemma buffer_item_local_alloc_local_alloc:
  forall bf m m' fl,
    buffer_item_local_alloc bf fl->
    apply_buffer_item bf m = Some m'->
    LocalAlloc m m' fl.
Proof.
  destruct bf;simpl;unfold LocalAlloc;intros.
  unfold alloc in H0;inv H0.
  unfold GMem.valid_block in H2;simpl in H2. destruct H2;try congruence;try contradiction.

  unfold free in H0. ex_match;inv H0.
  unfold unchecked_free,GMem.valid_block in H2. contradiction.
  unfold store in H0. ex_match;inv H0.
  contradiction.
Qed.
Lemma buffer_local_alloc_apply_buffer_local_alloc:
  forall bf m m' fl,
    buffer_local_alloc bf fl->
    apply_buffer bf m = Some m'->
    LocalAlloc m m' fl.
Proof.
  induction bf;intros. simpl in H0;inv H0;auto. apply LocalAlloc_refl.
  simpl in H0. unfold optbind in H0;ex_match;inv H0.
  apply IHbf with(fl:=fl) in H2. eapply LocalAlloc_trans;eauto.
  eapply buffer_item_local_alloc_local_alloc in Hx;eauto.
  eapply H;simpl;auto.

  unfold buffer_local_alloc in *.
  intros. apply H. simpl;auto.
Qed.
Lemma TEffect_TEffect2_eq:
  forall m bf m' bf' fp fl,
  TEffect m bf m' bf' fp fl <-> TEffect2 m bf m' bf' fp fl.
Proof.
  intros.
  split;intro.
  {
    unfold TEffect2. ex_match2.
    apply eff_chg_t in Hx as []; subst.
    exploit img_eff;try exact H;simpl;eauto.

    apply eff_chg_f in Hx.
    split;eapply H;eauto.
  }
  {
    unfold TEffect2 in H.
    ex_match2.
    {
      apply eff_chg_t in Hx as [];subst.
      constructor.
      intros. simpl in *. inv H0;inv H1;auto.
      intros [];contradiction.
      split;auto.
      eexists;rewrite app_nil_r;eauto.
      intros [];contradiction.
    }
    {
      apply eff_chg_f in Hx.
      Hsimpl.
      constructor;auto.
      {
        intros. subst.
        unfold BufferEff in H. Hsimpl.
        subst. apply apply_buffer_split in H2 as ?.
        Hsimpl. rewrite H1 in H;inv H.
        constructor;auto.

        apply apply_buffer_eff in H4.
        eapply MemEffect_eq_on_eff;eauto.

        eapply buffer_local_alloc_apply_buffer_local_alloc;eauto.
      }
      {
        intros;contradiction.
      }
      {
        unfold BufferEff in H. Hsimpl.
        Esimpl;eauto.
      }
    }
  }
Qed.
Lemma load_locality:
  forall m m' chunk b ofs v,
    MemPre m m' (load_fp chunk b ofs) ->
    load chunk m b ofs = Some v ->
    load chunk m' b ofs = Some v.
Proof.
  inversion 1;subst.
  unfold load;intros.
  ex_match2.
  Focus 2. clear Hx0;contradict n.
  inversion v0. split;auto.
  unfold range_perm. intros.
  apply H1 in H3 as ?.
  eapply ReadMemEq;eauto.
  unfold load_fp,belongsto,range_locset;Locs.unfolds. simpl.
  ex_match2. destruct H3.
  destruct zle;try contradiction.
  destruct zlt;try contradiction. auto.

  inv H0.
  f_equal. f_equal.
  apply Mem.getN_exten.
  intros. rewrite <-size_chunk_conv in H0.
  inversion v1.
  exploit H1;eauto. intro;auto.
  assert(belongsto (FP.reads (load_fp chunk b ofs)) b i).
  unfold load_fp,belongsto,range_locset;Locs.unfolds. simpl.
  ex_match2. destruct H0.
  destruct zle;try contradiction.
  destruct zlt;try contradiction. auto.
  apply ReadMemEq;auto.
  inversion v0. apply H5. auto.
Qed.

Lemma load_fp_effect_emp:
  forall ge chunk a rs,
    Locs.eq (effects(exec_load_fp ge chunk a rs )) Locs.emp.
Proof.
  intros.
  unfold effects,exec_load_fp,loadv_fp,load_fp;ex_match2;simpl;
    rewrite Locs.emp_union_locs;apply Locs.eq_refl.
Qed.

Local Transparent Mem.load Mem.alloc Mem.store Mem.free.
Local Ltac unfold_unchanged_perm :=
  unfold unchanged_perm,unchanged_validity,GMem.eq_perm,GMem.valid_block,GMem.perm in *.

Local Ltac unfold_belongsto :=
  unfold belongsto, Locs.belongsto in *.

Ltac unfold_effects :=
  unfold effects, Locs.union in *. 
Lemma store_locality:
  forall chunk m m0 b z v m',
    MemPre m m0 (store_fp chunk b z) ->
    store chunk m b z v = Some m'->
    exists m0' : gmem, store chunk m0 b z v = Some m0' /\ MemPost m' m0' (store_fp chunk b z).
Proof.
  intros. inv H.
  unfold store in *.
  ex_match2.
  {
    eexists; split; eauto.
    inv H0; simpls.
    unfold MemPost, unchanged_content; simpls.
    split.
    {
      unfold_unchanged_perm; simpls.
      split; intros; eauto.
      unfold_belongsto.
      unfold_effects.
      unfold FMemOpFP.store_fp in *; simpls.
      unfold FMemOpFP.range_locset in *.
      ex_match2; subst.
      unfold Locs.emp in *; simpls.
      destruct (zle z ofs); destruct (zlt ofs (z + size_chunk chunk));
        simpls; try discriminate ;try contradiction.
      inversion v0.
      exploit H0;eauto. intro.
      inversion v1. exploit H3;eauto. intro.
      apply Memperm_validblock in H2.
      apply Memperm_validblock in H5.
      split;auto.
    }
    {
      intros.
      unfold GMem.perm in *; simpls.
      unfold_belongsto.
      unfold_effects; simpls.
      unfold FMemOpFP.range_locset in *.
      ex_match2; subst.
      destruct (zle z ofs); destruct (zlt ofs (z + size_chunk chunk));
        simpls; try discriminate; try contradiction.
      assert (z <= ofs < z + size_chunk chunk); eauto.
      do 2 rewrite PMap.gss; eauto.
      eapply setN_geteq2; eauto.
      rewrite encode_val_length.
      rewrite <- size_chunk_conv; eauto.
    }
  }
  {
    inv H0. 
    contradiction n; clear - v0 EffectPermEqPre.
    unfold valid_access, range_perm in *; simpls.
    destruct v0.
    split; eauto.
    intros.
    pose proof H1 as Hrange.
    eapply H in H1.
    eapply EffectPermEqPre;eauto.
    unfold_belongsto.
    unfold_effects; simpls.
    unfold FMemOpFP.range_locset in *.
    ex_match2; subst.
    destruct (zle z ofs); destruct (zlt ofs (z + size_chunk chunk));
      try discriminate;try contradiction; try omega; simpls.
    auto.
  }
Qed.
Lemma alloc_locality:
  forall m m0 b z z0 m',
    MemPre m m0 (uncheck_alloc_fp b z z0) ->
    alloc m b z z0 = Some m'->
    exists m0', alloc m0 b z z0 = Some m0' /\ MemPost m' m0' (uncheck_alloc_fp b z z0).
Proof.
  intros.
  unfold alloc in *.
  inv H.
  eexists; split; eauto.
  unfold MemPost, unchanged_content; simpls.
  split.
  {
    inv H0.
    unfold_unchanged_perm; simpls.
    unfold FMemOpFP.uncheck_alloc_fp in *.
    unfold_effects; simpls.
    unfold_belongsto.
    split; intros.
    ex_match2; subst.
    split; intro; eauto.
    ex_match2; subst.
    do 2 rewrite PMap.gss; eauto.
    split; intro; eauto.
  }
  {
    inv H0.
    unfold GMem.perm in *; simpls.
    intros.
    unfold_belongsto.
    unfold_effects; simpls.
    ex_match2; subst.
    rewrite! PMap.gss in *; eauto.
  }
Qed.
Lemma free_locality:
  forall m m0 b z z0 m',
    MemPre m m0 (free_fp b z z0) ->
    free m b z z0 = Some m'->
    exists m0' : gmem, free m0 b z z0 = Some m0' /\ MemPost m' m0' (free_fp b z z0).
Proof.
  intros.
  unfold free in *.
  inv H0. 
  ex_match2; inv H.
  {
    eexists; split; eauto.
    unfold MemPost, unchanged_content, unchecked_free in *; simpls.
    unfold_belongsto; unfold_effects; simpls.
    unfold FMemOpFP.range_locset in *.
    inv H2;simpl.
    split.
    {
      unfold_unchanged_perm; simpls.
      split; intros.
      ex_match2; subst.
      unfold range_perm in *.
      rewrite Zplus_minus in H.
      destruct (zle z ofs); destruct (zlt ofs z0); simpls; try discriminate;try contradiction.
      assert (z <= ofs < z0); eauto.
      exploit r0;eauto.
      exploit r;eauto.
      intros.
      apply Memperm_validblock in H1.
      apply Memperm_validblock in H2.
      split;auto.
      
      ex_match2; subst.
      rewrite Zplus_minus in H.
      do 2 rewrite PMap.gss; eauto. 
      destruct (zle z ofs); destruct (zlt ofs z0); simpls; try discriminate.
      split; intro; auto.
    }
    {
      intros.
      unfold GMem.perm in *; simpls.
      ex_match2; subst.
      rewrite PMap.gss in H0; simpls.
      rewrite Zplus_minus in H.
      destruct (zle z ofs); destruct (zlt ofs z0); simpls; try discriminate;try contradiction.
    }
  }
  {
    contradiction n; clear - r EffectPermEqPre.
    unfold range_perm in *; intros.
    pose proof H as Hrange.
    eapply r in H.
    eapply EffectPermEqPre;eauto.
    unfold belongsto,effects. Locs.unfolds.
    unfold free_fp. simpl. 
    unfold FMemOpFP.range_locset.
    ex_match2; subst; rewrite Zplus_minus.
    destruct (zle z ofs); destruct (zlt ofs z0); simpls;
      try discriminate; try contradiction; try omega; eauto.
  }
Qed.
Lemma buf_item_unbuf_locality_1 :
  forall bi m m',
    unbuf_locality_1 bi m m'.
Proof.
  intros.
  unfold unbuf_locality_1; intros.
  destruct bi; simpls.
  eapply alloc_locality;eauto.
  eapply free_locality;eauto.
  eapply store_locality;eauto.
Qed.

(* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>*)
Lemma tsoloadv_locality1:
  forall m m' chunk addr v,
      tsoloadv chunk m addr = Some v ->
      MemPre (strip (fmemory m))(strip (fmemory m')) (loadv_fp chunk addr) ->
      tbuffer m = tbuffer m' ->
      buffer_safe (tbuffer m')(strip (fmemory m'))->
      tsoloadv chunk m' addr = Some v.
Proof.
  unfold tsoloadv,tsoload;intros;ex_match2;simpl in *;subst;try discriminate.
  inv Hx1;inv Hx3.
  eapply load_locality;eauto. inv H2;auto.
  eapply MemPre_apply_buffer_preserve;eauto.
  destruct H2. congruence.
Qed.


Lemma validity_preserve:
  forall ge fl c bf gm fp c' bf' gm',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    forall b,
      GMem.valid_block  gm b -> GMem.valid_block gm' b.
Proof.
  inversion 1;subst.
  inv H5. inv H8.
  {
    destruct i;inv H4;auto.
    all: try (unfold exec_load_TSO in H6; ex_match;inv H6;auto;fail).
    all: try (unfold exec_store_TSO in H6;ex_match;inv H6;unfold tsostorev,tsostore in Hx;inv Hx;ex_match;auto;inv H5;simpl;auto;fail).
    all: try(unfold tso_goto_label in H6;ex_match;inv H6;auto;fail).
    all: try (ex_match;inv H6; simpl;unfold Mem.storev,Mem.store in Hx1;ex_match;inv Hx1;auto;fail).
    ex_match. inv H6. simpl. unfold Mem.storev,Mem.store in Hx3;ex_match;inv Hx3;auto. inv H6;auto.

    ex_match. inv H6. simpl. unfold Mem.storev,Mem.store in Hx2;ex_match;inv Hx2;auto.
  }
  {
    apply tsostorev_memunchg in H5.
    apply tsostorev_memunchg in H6.
    apply tsoalloc_memunchg in H3.
    simpl in *. rewrite H3,H5,H6;auto.
  }
  auto.
  auto.
  auto.
  apply store_args_fmem_memunchg in H3.
  apply tsoalloc_memunchg in H1.
  simpl in *. rewrite H1,H3;auto.
Qed.
Lemma embed_preserve:
  forall ge fl c bf gm fp c' bf' gm',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    exists fm', embed gm' fl fm'.
Proof.
  intros.
  assert(gm = gm' \/ gm <> gm'). apply Classical_Prop.classic.
  destruct H0. inv H;eauto.
  eapply mem_chg in H0 as ?;subst;try eapply TSO_eff;eauto.
  destruct H1;subst.
  inv H. inv H6. inv H9;try contradiction.
  {
    destruct i;simpl in H4;try unfold exec_load_TSO,exec_store_TSO,tso_goto_label in H4;ex_match;inv H4;try contradiction.
    all: try apply tsostorev_memunchg in Hx;simpl in *;try congruence.
    apply mem_storev_fleq in Hx0;rewrite Hx0; exists m;econstructor;eauto.
    apply mem_storev_fleq in Hx2;rewrite Hx2; exists m;econstructor;eauto.
    apply mem_storev_fleq in Hx1;rewrite Hx1; exists m;econstructor;eauto.
  }
  apply tsoalloc_memunchg in H3. apply tsostorev_memunchg in H5. apply tsostorev_memunchg in H6.  simpl in *;congruence.

  apply tsoalloc_memunchg in H1. apply store_args_fmem_memunchg in H3;simpl in *;congruence.
Qed.
Lemma embed_back_preserve:
  forall ge fl c bf gm fp c' bf' gm',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    forall fl2 fm,
      disj fl fl2->
      embed gm' fl2 fm ->
      exists fm0,embed gm fl2 fm0.
Proof.
  intros.
  destruct (eff_chg bf bf') eqn:?.
  {
    apply eff_chg_t in Heqb as [];subst.
    exploit img_eff. eapply TSO_eff;eauto.
    all: simpl;eauto;intro.
    destruct H2.
    eapply disjoint_fl_memeq in H3;eauto.
    inv H1. apply FreelistEq_comm in H3.
    eapply FreelistEq_mem_fl_wd in H3.
    eexists. eapply gmem_fl_wd_embed with (wd:=H3);eauto.

    eapply validity_preserve;eauto.
  }
  {
    apply eff_chg_f in Heqb.
    exploit mem_unchg. eapply TSO_eff;eauto.
    destruct Heqb;auto.
    intro;subst;eauto.
  }
Qed.
Lemma embed_preserve2:
  forall ge fl c bf gm fp c' bf' gm',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    forall fl2 fm,
      disj fl fl2->
      embed gm fl2 fm ->
      exists fm0,embed gm' fl2 fm0.
Proof.
  intros.
  destruct (eff_chg bf bf') eqn:?.
  {
    apply eff_chg_t in Heqb as [];subst.
    exploit img_eff. eapply TSO_eff;eauto.
    all: simpl;eauto;intro.
    destruct H2.
    eapply disjoint_fl_memeq in H3;eauto.
    inv H1. 
    eapply FreelistEq_mem_fl_wd in H3.
    eexists. eapply gmem_fl_wd_embed with (wd:=H3);eauto.

    eapply validity_preserve;eauto.
  }
  {
    apply eff_chg_f in Heqb.
    exploit mem_unchg. eapply TSO_eff;eauto.
    destruct Heqb;auto.
    intro;subst;eauto.
  }
Qed.
Ltac inv_next :=
  match goal with
  | H : Next _ _ = Next _ _ |- _ => inv H; subst; eauto
  end.
Ltac ex_match3:=
  match goal with
    H: ?x = ?y |- context [?x] => rewrite H
  end.
Lemma get_block_exists:
  forall fl n,
  exists b,get_block fl n = b.
Proof. eauto. Qed.
Lemma fmem_eq':
  forall fm fm',
    Mem.mem_contents fm = Mem.mem_contents fm' ->
    Mem.validblocks fm = Mem.validblocks fm' ->
    Mem.freelist fm = Mem.freelist fm' ->
    Mem.mem_access fm = Mem.mem_access fm' ->
    fm = fm'.
Proof.
  destruct fm,fm';simpl;intros;subst.
  assert(nextblockid = nextblockid0).
  {
    revert valid_wd valid_wd0;clear;intros.
    pose proof Nat.lt_total nextblockid nextblockid0.
    destruct H as [|[|]];auto.
    pose proof get_block_exists freelist0 nextblockid.
    Hsimpl.
    exploit valid_wd;eauto.
    exploit valid_wd0;eauto.
    intros. rewrite H2 in H1.
    apply H1 in H.
    apply Nat.lt_neq in H. contradiction.
    
    pose proof get_block_exists freelist0 nextblockid0.
    Hsimpl.
    exploit valid_wd;eauto.
    exploit valid_wd0;eauto.
    intros. rewrite H2 in H1.
    apply H1 in H. apply Nat.lt_neq in H. contradiction.
  }
  subst.
  pose proof proof_irr access_max access_max0.
  pose proof proof_irr freelist_wd freelist_wd0.
  pose proof proof_irr valid_wd valid_wd0.
  pose proof proof_irr invalid_noaccess invalid_noaccess0.
  pose proof proof_irr contents_default contents_default0.
  congruence.
Qed.
Lemma embed_eq:
  forall gm fl fm fm',
    embed gm fl fm->
    embed gm fl fm'->
    fm = fm'.
Proof.
  intros.
  inv H;inv H0.
  destruct fm,fm'.
  unfold strip in *. simpl in *.
  inv H1.
  eapply fmem_eq';eauto.
Qed.
Lemma cmpu_bool_fp_eq:
  forall m c v1 v2, 
    Cop_fp.cmpu_bool_fp_total m c v1 v2= of_optfp (Cop_fp.cmpu_bool_fp m c v1 v2).
Proof.
  unfold Cop_fp.cmpu_bool_fp,Cop_fp.cmpu_bool_fp_total;intros;ex_match2;auto.
Qed.
Lemma GMem_eq:
  forall m m', GMem.eq m m' <-> GMem.eq' m m'.
Proof. split;inversion 1;subst;econstructor;eauto. Qed.
Lemma storev_eq:
  forall chunk addr v m m' m'',
    Mem.storev chunk m addr v = Some m->
    Mem.storev chunk m' addr v = Some m'' ->
    unchanged_content (belongsto (FP.writes (storev_fp chunk addr))) (strip m)(strip m')->
    GMem.eq (strip m')(strip m'').
Proof.
  intros.
  apply GMem_eq.
  eapply unchanged_content_memeq with(l:=(FP.writes (storev_fp chunk addr)));eauto.
  eapply unchanged_content_trans;eauto. apply unchanged_content_comm;eauto.
  {
    unfold Mem.storev in *;ex_match.
    unfold Mem.store in *. ex_match2. inv H. inv H0.
    unfold strip. simpl. clear - v1 v0 H1.
    gmem_unfolds;Esimpl;intros;auto;try solve[eapply H1;eauto].
    unfold belongsto,range_locset in H. Locs.unfolds.  ex_match2.
    destruct zle;inv H. destruct zlt;inv H3.
    rewrite !PMap.gss.
    apply setN_geteq2;auto. rewrite size_chunk_conv in l0.
    rewrite encode_val_length. auto.
  }
  {
    apply mem_storev_eff in H0 as [[? _ _ _] _].
    unfold effects in MemContentPreserve.
    assert(FP.frees (storev_fp chunk addr) = Locs.emp).
    unfold storev_fp. ex_match2;auto.
    rewrite H0,Locs.locs_union_emp in MemContentPreserve.
    auto.
  }
Qed.

Lemma eval_builtin_args_locality:
  forall args tm ge (rs:Asm.preg->val) v vargs,
    eval_builtin_args ge rs v tm args vargs->
    forall tm0 fp,
      MemPre (strip (fmemory tm))(strip (fmemory tm0)) fp ->
      buffer_safe (tbuffer tm0) (strip (fmemory tm0))->
      tbuffer tm = tbuffer tm0->
      MemOpFP.eval_builtin_args_fp ge rs v args fp->
      eval_builtin_args ge rs v tm0 args vargs.
Proof.
  unfold eval_builtin_args.
  induction args;intros.
  inv H. constructor.
  inv H.
  inv H3. apply MemPre_split in H0 as [].
  exploit IHargs;eauto. intro.
  constructor;auto.

  clear H3 H8 H7 H0 IHargs args.
  generalize dependent tm0.
  generalize dependent fp1.
  induction H6;intros;inv H5;try solve[constructor].

  econstructor;eauto.
  unfold tsoloadv in *. ex_match.
  unfold tsoload in *. ex_match.
  simpl in *. destruct tm0.
  destruct H1 . simpl in *.
  ex_match3. subst.
  exploit MemPre_apply_buffer_preserve.
  apply H0. apply Hx1. apply H1. intro.
  eapply load_locality;eauto.

  econstructor;eauto.
  unfold tsoloadv in *. ex_match.
  unfold tsoload in *. ex_match.
  simpl in *. destruct tm0.
  destruct H1 . simpl in *. ex_match3. subst.
  exploit MemPre_apply_buffer_preserve.
  apply H0. apply Hx1. apply H1. intro.
  eapply load_locality;eauto.

  apply MemPre_split in H as [].
  eapply IHeval_builtin_arg1 in H4;eauto.
  eapply IHeval_builtin_arg2 in H6;eauto.
  econstructor;eauto.
Qed.
Lemma extcall_arg_locality:
  forall m rs l b,
    extcall_arg rs m l b ->
    forall fp m2,
      tbuffer m = tbuffer m2 ->
      buffer_safe (tbuffer m2)(strip (fmemory m2))->
      MemPre (strip (fmemory m))(strip (fmemory m2)) fp->
      extcall_arg_fp rs l fp->
      extcall_arg rs m2 l b.
Proof.
  intros.
  inv H;try econstructor;eauto.
  eapply tsoloadv_locality1;eauto. inv H3;auto.
Qed.
Lemma extcall_args_locality:
  forall sig args tm (rs:Asm.preg->val),
    extcall_arguments rs tm sig args->
    forall tm0 fp,
      MemPre (strip (fmemory tm))(strip (fmemory tm0)) fp ->
      buffer_safe (tbuffer tm0) (strip (fmemory tm0))->
      tbuffer tm = tbuffer tm0->
      extcall_arguments_fp rs sig fp->
      extcall_arguments rs tm0 sig args.
Proof.
  unfold extcall_arguments,extcall_arguments_fp.
  intro sig. generalize (loc_arguments sig).
  clear sig.
  induction l;intros.
  inv H. econstructor.

  inv H3.
  inv H.
  econstructor;eauto.
  {
    inv H5;constructor.
    inv H6.
    apply MemPre_split in H0 as [].
    eapply extcall_arg_locality;try apply H0;auto.
    apply MemPre_split in H0 as [].
    inv H6.
    apply MemPre_split in H0 as [].
    eapply extcall_arg_locality;try apply H0;eauto.

    inv H6.
    apply MemPre_split in H0 as [].
    apply MemPre_split in H0 as [].
    eapply extcall_arg_locality;try apply H5;eauto.
  }
  {
    eapply IHl;try apply H7;eauto.
    apply MemPre_split in H0 as [];eauto.
  }
Qed.
Lemma store_stack_fmem_locality:
  forall fm fm',
    tbuffer fm = tbuffer fm'->
    forall v z a ty fm1,
      store_stack_fmem fm v ty z a = Some fm1 ->
      exists fm2, store_stack_fmem fm' v ty z a = Some fm2 /\
             tbuffer fm1 = tbuffer fm2.
Proof.
  intros.
  unfold store_stack_fmem in *.
  unfold tsostorev in *. ex_match.
  unfold tsostore in *. eexists;split;eauto.
  inv_some. simpl. congruence.
Qed.
Lemma store_args_fmem_locality:
  forall m b stk tys m',
    store_args_fmem m stk b tys = Some m' ->
    forall m0,
      tbuffer m0 = tbuffer m ->
      exists m1,
        store_args_fmem m0  stk b tys = Some m1 /\ tbuffer m1 = tbuffer m'.
Proof.
  unfold store_args_fmem.
  generalize dependent 0.
  intros until b.
  revert z m;induction b;intros.
  {
    simpl in *. ex_match. inv_some.
    eexists. split;eauto.
  }
  {
    simpl in *;ex_match.
    all: try solve[eapply IHb in H;eauto;simpl;congruence].
  }
Qed.
Section AUX_TSOSTEP.
  Context {ge:Genv.t F V}.
  Definition notlock_instr i:=
    match i with
    | Plock_xchg _ _ => false
    | Plock_cmpxchg _ _ => false
    | Plock_dec _ => false
    | _ => true
    end.
  Inductive tso_lock_fstep:
    core -> tsofmem -> FP.t -> core -> tsofmem -> Prop :=
   |make_lock_step: forall b ofs (f: function) i rs bm rs' bm' lf fp,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i -> not_alloc_instr i -> notlock_instr i = false ->
      exec_instr_TSO ge f i rs bm = Next rs' bm' ->
      exec_instr_TSO_fp ge f i rs bm = fp ->
      tso_lock_fstep (Core_State rs lf) bm fp (Core_State rs' lf) bm'.
  Inductive tso_notlock_fstep:
  core -> tsofmem -> FP.t -> core -> tsofmem -> Prop :=
| tso_exec_step_internal:
    forall b ofs (f: function) i rs bm rs' bm' lf fp,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i -> not_alloc_instr i -> notlock_instr i = true ->
      exec_instr_TSO ge f i rs bm = Next rs' bm' ->
      exec_instr_TSO_fp ge f i rs bm = fp ->
      tso_notlock_fstep (Core_State rs lf) bm fp (Core_State rs' lf) bm'

| tso_exec_step_internal_allocframe :
    forall b ofs (f : function) (rs:regset) bm rs' bm' bm2 bm3
      stk lf fp sz ofs_ra ofs_link sp
      (Hrs': rs' = nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) =
      Some (Pallocframe sz ofs_ra ofs_link) ->
      tsoalloc bm 0 sz (bm', stk) -> sp = Vptr stk Ptrofs.zero ->
      tsostorev Mptr bm' (Val.offset_ptr sp ofs_link) rs#RSP = Some bm2 ->
      tsostorev Mptr bm2 (Val.offset_ptr sp ofs_ra) rs#RA = Some bm3 ->
      fp = FP.union (tsoalloc_fp stk 0 sz)
                    (FP.union (storev_fp Mptr (Val.offset_ptr sp ofs_link))
                              (storev_fp Mptr (Val.offset_ptr sp ofs_ra))) ->
      tso_notlock_fstep (Core_State rs lf) bm fp (Core_State rs' lf) bm3
                 
| tso_exec_step_builtin:
    forall b ofs f ef args fp res rs bm vargs vres rs' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      rs RSP <> Vundef->
      eval_builtin_args ge rs (rs RSP) bm args vargs ->
      MemOpFP.eval_builtin_args_fp ge rs (rs RSP) args fp ->
      helpers.i64ext_sem ef vargs vres ->
      rs' = nextinstr_nf
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      tso_notlock_fstep (Core_State rs lf) bm fp (Core_State rs' lf) bm
               
| tso_exec_step_to_external:
    forall b ef args rs bm lf fp,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs bm (ef_sig ef) args ->
      extcall_arguments_fp rs (ef_sig ef) fp ->
      tso_notlock_fstep (Core_State rs lf) bm fp (Core_CallstateOut ef args rs lf) bm

| tso_exec_step_i64ext:
    forall b ef args res rs bm rs' lf,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      helpers.i64ext_sem ef args res ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
      tso_notlock_fstep (Core_CallstateOut ef args rs lf) bm FP.emp (Core_State rs' lf) bm

(*NOTE [loader]*)
| exec_initialize_call: 
    forall bm args tys retty bm1 stk bm2 fb z fp1 fp2 fp,
      args_len_rec args tys = Some z -> 
      tsoalloc bm 0 (4*z) (bm1, stk) ->
      tsoalloc_fp stk 0 (4*z) = fp1 ->
      store_args_fmem bm1 stk args tys = Some bm2 ->
      store_args_fp stk tys = fp2 ->
      FP.union fp1 fp2 = fp ->
      let rs0 := (Pregmap.init Vundef) 
                   #PC <- (Vptr fb Ptrofs.zero)
                   #RA <- Vzero 
                   #RSP <- (Vptr stk Ptrofs.zero) in
      tso_notlock_fstep (Core_CallstateIn fb args tys retty) bm 
           fp (Core_State rs0 (mk_load_frame stk retty)) bm2
  .
  Lemma tsofstep_lock_or_notlock:
    forall s m b s' m',
      tsofstep ge s m b s' m' ->
      tso_lock_fstep s m b s' m' \/ tso_notlock_fstep s m b s' m'.
  Proof.
    inversion 1;subst.
    destruct (notlock_instr i) eqn:?;[right|left];econstructor;eauto.
    right;econstructor 2;eauto.
    right;econstructor 3;eauto.
    right;econstructor 4;eauto.
    right;econstructor 5;eauto.
    right;econstructor 6;eauto.
  Qed.
  Lemma lock_step_tsofstep:
    forall s m b s' m',
      tso_lock_fstep s m b s' m'->
      tsofstep ge s m b s' m'.
  Proof. inversion 1;subst;econstructor;eauto. Qed.
  Lemma not_lock_step_tsofstep:
    forall s m b s' m',
      tso_notlock_fstep s m b s' m'->
      tsofstep ge s m b s' m'.
  Proof.
    inversion 1;subst.
    econstructor;eauto.
    econstructor 2;eauto.
    econstructor 3;eauto.
    econstructor 4;eauto.
    econstructor 5;eauto.
    econstructor 6;eauto.
  Qed.

  Lemma lock_step_buffer_nil:
    forall s m b s' m',
      tso_lock_fstep s m b s' m'->
      tbuffer m = nil /\ tbuffer m' = nil.
  Proof.
    inversion 1;subst.
    unfold notlock_instr in H4;ex_match;inv H4;
      unfold exec_instr_TSO in H5;ex_match; inv_next.
  Qed.
  Lemma not_lock_step_mem_ung:
    forall s m b s' m',
      tso_notlock_fstep s m b s' m'->
      strip (fmemory m) = strip (fmemory m').
  Proof.
    inversion 1;subst;auto.
    {
      unfold notlock_instr in H4;ex_match;inv H4.
      all: unfold exec_instr_TSO,exec_load_TSO,exec_store_TSO,tso_goto_label in H5;ex_match;try inv_next.
      all:try solve[eapply tsostorev_memunchg;eauto].
      apply tsofree_memunchg in Hx2;auto.
    }
    {
      apply tsostorev_memunchg in H5.
      apply tsostorev_memunchg in H6.
      apply tsoalloc_memunchg in H3.
      congruence.
    }
    {
      apply tsoalloc_memunchg in H1.
      apply store_args_fmem_memunchg in H3.
      congruence.
    }
  Qed.
  Inductive tso_lock_step:freelist->core -> buffer * gmem -> FP.t -> core -> buffer * gmem -> Prop :=
  |LockStep:
     forall fl c  gm fm fp c' m'  gm',
       embed gm fl fm ->
       tso_lock_fstep c {|tbuffer:=nil;fmemory:=fm|} fp c' m' ->
       gm' = strip (fmemory m') ->
       nil = tbuffer m' ->
       tso_lock_step fl c (nil,gm) fp c' (nil,gm').

  Lemma tso_lock_step_locality:
    forall fl c gm fp c' gm' ,
      tso_lock_step fl c (nil,gm) fp c' (nil,gm') ->
      forall gm0 fm0,
        embed gm0 fl fm0 ->
        LPre gm gm0 fp fl ->
        exists m1,
          tso_lock_step fl c (nil,gm0) fp c' (nil,m1) /\  LPost gm'  m1  fp fl.
  Proof.
    intros fl c gm fp c' gm' STEP gm0 fm0 EMBED1 PRE1.
    inv STEP. inv H1. inv EMBED1.
    inv H2.
    destruct PRE1 as [MEMPRE FLEQ].
    unfold notlock_instr in H5;ex_match;simpl in *;ex_match;try inv_next.
    {
      apply MemPre_split in MEMPRE as [PRE1 PRE2].
      eapply MemPre_mem_loadv_eq with(Fleq:=FLEQ) in Hx0 as R;eauto.
      eapply LPre_mem_storev_LPost with(Fleq:=FLEQ) in Hx1 as ?;eauto.
      Hsimpl.
      eexists. split.
      econstructor 1 with(fm:= (combine (strip fm0) (Mem.freelist fm) (Mem.nextblockid fm)(FreelistEq_mem_fl_wd fm (strip fm0) FLEQ))).
      econstructor;eauto.
      econstructor;eauto. simpl. do 2 ex_match3. eauto.
      eauto.
      auto.
      simpl.
      destruct H6;split;auto.
      apply MemPost_union;auto.
      apply MemPost_effect_emp.
      unfold loadv_fp,load_fp,effects;ex_match2;simpl;rewrite Locs.locs_union_emp;apply Locs.eq_refl.
    }
    {
      apply MemPre_split in MEMPRE as [PRE1 PRE2].
      apply MemPre_split in PRE2 as [PRE2 PRE3].
      eapply MemPre_mem_loadv_eq with(Fleq:=FLEQ) in Hx0 as R;eauto.
      assert(strip fm0= strip (combine (strip fm0) (Mem.freelist fm) (Mem.nextblockid fm)(FreelistEq_mem_fl_wd fm (strip fm0) FLEQ))). rewrite strip_combine;auto.
      rewrite H2 in PRE2.
      rewrite <-cmpu_bool_fp_eq in PRE2.
      erewrite MemPre_cmpu_valid_pointer_ceq in Hx1;eauto.
      eapply LPre_mem_storev_LPost with(Fleq:=FLEQ) in Hx3 as ?;eauto.
      Hsimpl.
      exists (strip x).
      split.
      econstructor 1 with(fm:= (combine (strip fm0) (Mem.freelist fm) (Mem.nextblockid fm)(FreelistEq_mem_fl_wd fm (strip fm0) FLEQ))).
      econstructor;eauto.
      econstructor;eauto. simpl. do 3 ex_match3. eauto.
      simpl. repeat ex_match3. rewrite LPre_cmpu_bool_fp_eq;auto.
      rewrite <- cmpu_bool_fp_eq. auto.
      auto.
      auto.
      destruct H7;split;auto.
      apply MemPost_union. apply MemPost_effect_emp.
      unfold loadv_fp,load_fp,effects;ex_match2;simpl;rewrite Locs.locs_union_emp;apply Locs.eq_refl.
      apply MemPost_union;auto. apply MemPost_effect_emp.
      apply cmpu_bool_fp_effemp0.
    }
    {
      apply MemPre_split in MEMPRE as [PRE1 PRE2].
      eapply MemPre_mem_loadv_eq with(Fleq:=FLEQ) in Hx0 as R;eauto.
      assert(strip fm0= strip (combine (strip fm0) (Mem.freelist fm) (Mem.nextblockid fm)(FreelistEq_mem_fl_wd fm (strip fm0) FLEQ))). rewrite strip_combine;auto.
      rewrite H2 in PRE2.
      rewrite <-cmpu_bool_fp_eq in PRE2.
      erewrite MemPre_cmpu_valid_pointer_ceq in Hx1;eauto.
      eexists.
      split.
      econstructor 1 with(fm:= (combine (strip fm0) (Mem.freelist fm) (Mem.nextblockid fm)(FreelistEq_mem_fl_wd fm (strip fm0) FLEQ))).
      econstructor;eauto.
      econstructor;eauto. simpl. do 3 ex_match3;eauto.
      simpl. do 2 ex_match3.  rewrite LPre_cmpu_bool_fp_eq;auto.
      rewrite <- cmpu_bool_fp_eq. auto.
      eauto. eauto.
      split;auto.
      apply MemPost_union;apply MemPost_effect_emp.
      unfold loadv_fp,load_fp,effects;ex_match2;simpl;try rewrite Locs.locs_union_emp;try apply Locs.eq_refl.
      apply cmpu_bool_fp_effemp0.
    }
    {
      apply MemPre_split in MEMPRE as [PRE1 PRE2].
      eapply MemPre_mem_loadv_eq with(Fleq:=FLEQ) in Hx0 as R;eauto.
      eapply LPre_mem_storev_LPost with(Fleq:=FLEQ) in Hx2 as ?;eauto.
      Hsimpl.
      eexists. split.
      econstructor 1 with(fm:= (combine (strip fm0) (Mem.freelist fm) (Mem.nextblockid fm)(FreelistEq_mem_fl_wd fm (strip fm0) FLEQ))).
      econstructor;eauto.
      econstructor;eauto. simpl. do 2 ex_match3. eauto.
      eauto.
      auto.
      simpl.
      destruct H6;split;auto.
      apply MemPost_union;auto.
      apply MemPost_effect_emp.
      unfold loadv_fp,load_fp,effects;ex_match2;simpl;rewrite Locs.locs_union_emp;apply Locs.eq_refl.
    }
  Qed.

  Inductive tso_not_lock_step:freelist->core -> buffer * gmem -> FP.t -> core -> buffer * gmem -> Prop :=
  |NotLockStep:
     forall fl c b gm fm fp c' m' b'  gm',
       embed gm fl fm ->
       tso_notlock_fstep c {|tbuffer:=b;fmemory:=fm|} fp c' m' ->
       gm' = strip (fmemory m') ->
       b' = tbuffer m' ->
       tso_not_lock_step fl c (b,gm) fp c' (b',gm').
  Lemma tso_not_lock_step_memung:
    forall fl c b gm fp c' b' gm',
      tso_not_lock_step fl c (b,gm) fp c' (b',gm') ->
      gm = gm'.
  Proof.
    inversion 1;subst.
    apply not_lock_step_mem_ung in H9.
    simpl in *. inv H6. auto.
  Qed.


  Lemma tso_valid_pointer_locality:
    forall x y bf fm fm' ,
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm')->
      MemPre (strip fm)(strip fm')(valid_pointer_fp x y) ->
      tso_valid_pointer m x y = tso_valid_pointer m' x y.
  Proof.
    intros.
    unfold tso_valid_pointer.
    unfold m,m'.
    destruct H,H0.
    do 2 ex_match3.
    eapply MemPre_apply_buffer_preserve in H1;try exact H;try exact H0;eauto.
    destruct H1 as [_ [_ R] _].
    unfold valid_pointer_fp,GMem.eq_perm,GMem.perm in R.
    simpl in *.
    do 2 destruct perm_dec;try discriminate;auto;contradict n;
    eapply R;eauto;apply range_locset_belongsto;split;auto;split;omega.
  Qed.
   Lemma tso_weak_valid_pointer_fp_locality:
    forall x y bf fm fm' ,
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm') ->
      MemPre (strip fm)(strip fm')(tso_weak_valid_pointer_fp m x y) ->
      tso_weak_valid_pointer_fp m x y = tso_weak_valid_pointer_fp m'  x y.
  Proof.
    unfold tso_weak_valid_pointer_fp;intros.
    ex_match2.
    eapply tso_valid_pointer_locality in H1;eauto.
    congruence.
    erewrite tso_valid_pointer_locality in Hx;eauto.
    congruence.
    eapply MemPre_subset;eauto.
    econstructor;try apply Locs.subset_refl.
    simpl.
    eapply range_locset_expend1_subset.
  Qed.
  Definition tso_weak_valid_pointer (tfm : tsofmem) (b : block) (ofs : Z) : bool :=
    tso_valid_pointer tfm b ofs || tso_valid_pointer tfm b (ofs-1).
  Lemma tso_weak_valid_pointer_locality:
    forall x y bf fm fm' ,
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm') ->
      MemPre (strip fm)(strip fm')(tso_weak_valid_pointer_fp m x y) ->
      tso_weak_valid_pointer m x y = tso_weak_valid_pointer m'  x y.
  Proof.
    unfold tso_weak_valid_pointer_fp,tso_weak_valid_pointer;intros.
    ex_match2.
    eapply tso_valid_pointer_locality in H1;eauto. rewrite <-H1,Hx. auto.
    exploit tso_valid_pointer_locality.
    exact H. exact H0. eapply MemPre_subset;try exact H1.
    unfold valid_pointer_fp. econstructor;try apply Locs.subset_refl.
    simpl. apply range_locset_expend1_subset.
    intro.
    rewrite H2 in Hx. rewrite Hx.

    exploit tso_valid_pointer_locality.
    exact H. exact H0. eapply MemPre_subset;try exact H1.
    econstructor;try apply Locs.subset_refl.
    simpl. instantiate(1:=y-1). instantiate(1:=x).
    Locs.unfolds. unfold range_locset. intros;ex_match.
    apply andb_true_iff in H3 as []. apply andb_true_iff;split;auto.
    do 2 destruct zlt;auto. omega.
    intro. rewrite H3. auto.
  Qed.
  
  
  Lemma tso_cmpu_bool_fp_locality:
    forall x y bf fm fm' c,
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm') ->
      MemPre (strip fm)(strip fm')(tso_cmpu_bool_fp_total m c x y) ->
      tso_cmpu_bool_fp_total m c x y = tso_cmpu_bool_fp_total m' c x y.
  Proof.
    unfold tso_cmpu_bool_fp_total.
    intros. ex_match2.
    1,2:eapply tso_weak_valid_pointer_fp_locality;eauto.
    apply MemPre_split in H1 as [].
    eapply tso_weak_valid_pointer_fp_locality in H1;eauto.
    eapply tso_weak_valid_pointer_fp_locality in H2;eauto.
    congruence.
  Qed.
  Lemma tso_cmpu_bool_locality:
    forall x y bf fm fm' c,
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm') ->
      MemPre (strip fm)(strip fm')(tso_cmpu_bool_fp_total m c x y) ->
      Val.cmpu (tso_valid_pointer m) c x y = Val.cmpu (tso_valid_pointer m') c x y.
  Proof.
    unfold Val.cmpu,tso_cmpu_bool_fp_total.
    intros.
    f_equal.
    unfold Val.cmpu_bool.
    ex_match2;compute ["&&"] in *.
    all: try solve[
               eapply tso_weak_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence].
    {
      apply MemPre_split in H1 as [H1 H2].
      ex_match2.
      eapply tso_weak_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
      eapply tso_weak_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
    }
    { apply MemPre_split in H1 as [H1 H2].
      ex_match2.
      eapply tso_weak_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
      eapply tso_weak_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
    }
    {
      apply MemPre_split in H1 as [H1 H2].
      ex_match2.
      eapply tso_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
      eapply tso_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
    }
    {
      apply MemPre_split in H1 as [H1 H2].
      ex_match2.
      eapply tso_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
      eapply tso_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
    }
  Qed.
  Lemma compare_ints_TSO_fp_locality:
    forall x y bf fm fm',
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm')->
      MemPre (strip fm)(strip fm')(compare_ints_TSO_fp x y m) ->
      compare_ints_TSO_fp x y m = compare_ints_TSO_fp x y  m'.
  Proof.
    unfold compare_ints_TSO_fp.
    intros.
    apply MemPre_split in H1 as [].
    f_equal; eapply tso_cmpu_bool_fp_locality;eauto.
  Qed.
  Lemma compare_ints_TSO_locality:
    forall x y bf fm fm' rs,
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm')->
      MemPre (strip fm)(strip fm')(compare_ints_TSO_fp x y m) ->
      compare_ints_TSO x y rs m = compare_ints_TSO x y rs m'.
  Proof.
    intros.
    unfold compare_ints_TSO_fp in H1.
    unfold compare_ints_TSO.
    apply MemPre_split in H1 as [].
    f_equal. f_equal. f_equal. f_equal.
    eapply tso_cmpu_bool_locality;eauto.
    f_equal. eapply tso_cmpu_bool_locality;eauto.
  Qed.
  Lemma exec_load_TSO_buffer_unchg:
    forall chunk m addr rs p rs' m',
      exec_load_TSO ge chunk m addr rs p = Next rs' m'->
      tbuffer m = tbuffer m'.
  Proof. unfold exec_load_TSO;intros;ex_match. Qed.
  Lemma exec_load_TSO_locality:
    forall chunk m addr rs p rs' m',
      exec_load_TSO ge chunk m addr rs p = Next rs' m'->
      forall m0,
        tbuffer m = tbuffer m0 ->
        buffer_safe (tbuffer m0)(strip (fmemory m0))->
        MemPre (strip (fmemory m))(strip (fmemory m0))(exec_load_fp ge chunk addr rs) ->
        exec_load_TSO ge chunk m0 addr rs p = Next rs' m0.
  Proof.
    unfold exec_load_TSO;intros;ex_match;inv_next.
    eapply tsoloadv_locality1 in Hx;eauto.
    ex_match3. eauto.
  Qed.
  Lemma exec_store_TSO_memunchg:
    forall chunk m addr rs p lp rs' m',
      exec_store_TSO ge chunk m addr rs p lp = Next rs' m'->
      strip (fmemory m) = strip (fmemory m').
  Proof.
    unfold exec_store_TSO;intros;ex_match;inv_next.
    eapply tsostorev_memunchg;eauto.
  Qed.
  Lemma exec_store_TSO_locality:
    forall chunk m addr rs p lp rs' m',
      exec_store_TSO ge chunk m addr rs p lp = Next rs' m'->
      forall m0,
        exists m0',
          exec_store_TSO ge chunk m0 addr rs p lp= Next rs' m0'.
  Proof.
    unfold exec_store_TSO,exec_store_fp;intros;ex_match;inv_next.
    unfold tsostorev in *.
    ex_match.
    unfold tsostore in *.
    inv_some. eauto.
  Qed.
  Lemma exec_store_TSO_locality2:
    forall chunk m addr rs p lp rs' m',
      exec_store_TSO ge chunk m addr rs p lp = Next rs' m'->
      forall m0,
        tbuffer m = tbuffer m0 ->
        exists m0',
          exec_store_TSO ge chunk m0 addr rs p lp= Next rs' m0' /\ tbuffer m' = tbuffer m0'.
  Proof.
    unfold exec_store_TSO,exec_store_fp;intros;ex_match;inv_next.
    unfold tsostorev in *.
    ex_match.
    unfold tsostore in *.
    inv_some. eexists;split;eauto.
    unfold buffer_insert. simpl.
    congruence.
  Qed.
  Lemma tsofmem_eq:
    forall m, m = {|tbuffer:=tbuffer m;fmemory:=fmemory m|}.
  Proof. destruct m;auto. Qed.
  Lemma fleq_nextblockideq:
    forall m m' fl,
      FreelistEq m m' fl ->
      forall fm fm',
        embed m fl fm ->
        embed m' fl fm' ->
        Mem.nextblockid fm = Mem.nextblockid fm'.
  Proof.
    unfold FreelistEq.
    intros.
    inv H0;inv H1.
    unfold strip,GMem.valid_block in H. simpl in H.
    unfold in_fl in H.
    assert(forall b n, get_block (Mem.freelist fm) n = b ->    In b (Mem.validblocks fm) <-> In b (Mem.validblocks fm')).
    intros. eapply H;eauto.
    clear H.
    destruct fm,fm'. simpl in *; subst.

    revert H1 valid_wd valid_wd0.
    clear. intros.
    pose proof Nat.lt_total nextblockid nextblockid0.
    destruct H as [|[|]];auto.
    pose proof get_block_exists freelist nextblockid as [].
    eapply valid_wd0 in H;eauto.
    eapply H1 in H;eauto.
    eapply valid_wd in H;eauto.
    omega.

    pose proof get_block_exists freelist nextblockid0 as [].
    eapply valid_wd in H;eauto.
    eapply H1 in H;eauto.
    eapply valid_wd0 in H;eauto.
    omega.
  Qed.

  Definition buffer_fl_embed bf fl m:=
    exists m', apply_buffer bf m = Some m' /\ exists fm', embed m' fl fm'.
  Definition buffer_fl_embed_rel bf fl m m':=
    buffer_fl_embed bf fl m ->
    buffer_fl_embed bf fl m'.
  Lemma alloc_buffer_fl_embed_rel:
    forall bf fl m fm fm2 b lo hi,
      embed m fl fm ->
      tsoalloc ({|tbuffer:=bf;fmemory:=fm|}) lo hi (fm2,b) ->
      buffer_fl_embed bf fl m.
  Proof.
    intros.
    inv H. inv H0.
    unfold buffer_fl_embed.
    Esimpl;eauto.
  Qed.

  Lemma check_compare_ints_TSO_locality:
    forall x y bf fm fm',
      let m := {|tbuffer:=bf;fmemory:=fm|} in
      let m' := {|tbuffer:=bf;fmemory:=fm'|} in
      buffer_safe bf (strip fm) ->
      buffer_safe bf (strip fm')->
      MemPre (strip fm)(strip fm')(compare_ints_TSO_fp x y m) ->
      check_compare_ints_TSO x y m = check_compare_ints_TSO x y m'.
  Proof.
    intros. unfold check_compare_ints_TSO.
    assert (Val.cmpu_bool (tso_valid_pointer m) Ceq x y = Val.cmpu_bool (tso_valid_pointer m') Ceq x y).
    { unfold compare_ints_TSO_fp in H1.
      apply MemPre_split in H1. destruct H1 as [H1 _].
      unfold Val.cmpu, tso_cmpu_bool_fp_total in *.
      unfold Val.cmpu_bool.
      ex_match2;compute ["&&"] in *; subst m m'.
      all: try solve[
                 eapply tso_weak_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence].
      {
        apply MemPre_split in H1 as [H1 H2].
        ex_match2.
        eapply tso_weak_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
        eapply tso_weak_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
      }
      { apply MemPre_split in H1 as [H1 H2].
        ex_match2.
        eapply tso_weak_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
        eapply tso_weak_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
      }
      {
        apply MemPre_split in H1 as [H1 H2].
        ex_match2.
        eapply tso_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
        eapply tso_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
      }
      {
        apply MemPre_split in H1 as [H1 H2].
        ex_match2.
        eapply tso_valid_pointer_locality in H2;eauto;unfold tso_weak_valid_pointer in H2;congruence.
        eapply tso_valid_pointer_locality in H1;eauto;unfold tso_weak_valid_pointer in H1;congruence.
      }
    }
    rewrite H2. auto.
  Qed.
  Lemma not_lock_step_locality':
    forall fl c gm bf fp c' bf',
      buffer_safe bf gm ->
      tso_not_lock_step fl c (bf,gm) fp c' (bf',gm) ->
      forall gm0 fm0 (FLEMBEDREL:buffer_fl_embed_rel bf fl gm gm0),
        embed gm0 fl fm0 ->
        LPre gm gm0 fp fl->
        buffer_safe bf gm0->
        tso_not_lock_step fl c (bf,gm0) fp c' (bf',gm0).
  Proof.
    intros.
    inv H1. destruct H2 as [MEMPRE FLEQ].
    inv H0. inv H8.
    remember {| tbuffer := bf; fmemory := fm0 |} as m0 in *.
    try replace fm0 with (fmemory m0) in * by (rewrite Heqm0 ;auto).
    try replace bf with (tbuffer m0) in * by (rewrite Heqm0 ;auto).
    clear fm0 bf Heqm0.
    rewrite <- H1 in *.
    inv H11.
    {
      unfold notlock_instr in H7;ex_match;simpl in H8,MEMPRE;ex_match;try inv_next.
      Ltac triv:=
        econstructor;[econstructor;reflexivity|econstructor;eauto;simpl;eauto|auto|auto].
      all: try solve[triv].
      all: try solve[eapply exec_load_TSO_locality with(m0:=m0) in H8 as ?;eauto;triv;[rewrite <-tsofmem_eq;auto|eapply exec_load_TSO_buffer_unchg in H8;eauto]].
      all: try solve[eapply exec_store_TSO_locality2 with(m0:=m0) in H8 as R;eauto;
                     destruct R as [?[]];triv;eapply exec_store_TSO_memunchg;eauto].
      all: try solve[triv; repeat ex_match3; rewrite<- !tsofmem_eq; auto].
      all: try solve[triv;[ex_match3;erewrite <- tsofmem_eq,compare_ints_TSO_locality,<- tsofmem_eq;eauto|erewrite <-compare_ints_TSO_fp_locality;eauto]].
      all: try solve[unfold tso_goto_label in H8;ex_match;inv H2;inv_next;triv;
                     unfold tso_goto_label;repeat ex_match3; rewrite <- tsofmem_eq; auto].
      {
        triv.
        
        ex_match3. erewrite <- check_compare_ints_TSO_locality. rewrite Hx1. all: auto.
        erewrite <- tsofmem_eq,compare_ints_TSO_locality,<- tsofmem_eq;eauto.
        erewrite <-compare_ints_TSO_fp_locality;eauto.
      }
      {
        triv. ex_match3. erewrite <- check_compare_ints_TSO_locality. rewrite Hx1. all: auto.
        erewrite <- tsofmem_eq,compare_ints_TSO_locality,<- tsofmem_eq;eauto.
        erewrite <-compare_ints_TSO_fp_locality;eauto.
      }
      {
        assert(strip fm = strip (fmemory {|tbuffer := tbuffer m0; fmemory := fm|})).
        auto.
        rewrite H8 in MEMPRE.
        apply MemPre_split in MEMPRE as [PRE1 PRE2].
        apply MemPre_split in PRE1 as [PRE0 PRE1].
        eapply tsoloadv_locality1 in PRE1;eauto.
        eapply tsoloadv_locality1 in PRE0;eauto.
        econstructor.
        Focus 2. econstructor;try eassumption. simpl.
        rewrite <-!tsofmem_eq. repeat ex_match3. eauto.
        simpl. ex_match3. f_equal. econstructor;eauto. auto. auto.
      }
      eapply exec_load_TSO_locality with(m0:=m0) in H8 as ?;eauto.
      triv. rewrite <- Hx0, <-tsofmem_eq;auto.
      eapply exec_load_TSO_buffer_unchg in H8;eauto. simpl in H8. congruence.
      rewrite Hx0. unfold buffer_safe. eexists;simpl;eauto.
    }
    {
      (* need FLEMBED*)
      assert(exists m0',tsoalloc m0 0 sz (m0',stk)/\tbuffer m0' = tbuffer bm').
      {
        eapply alloc_buffer_fl_embed_rel in H6 as?;eauto.
        Focus 2. econstructor;eauto.
        unfold buffer_fl_embed_rel in FLEMBEDREL.
        rewrite H1 in FLEMBEDREL.
        apply FLEMBEDREL in H7 as FLEMBED.
        clear H7.
        destruct FLEMBED as [?[?[]]].
        inversion H6;subst.
        eapply Fleq_apply_buffer_preserve in FLEQ as FLEQ2;eauto.
        eapply fleq_nextblockideq in FLEQ2 as ?;eauto;[|rewrite <- H0;eauto].
        destruct m0.
        assert(Mem.nextblock fm' = Mem.nextblock x0).
        unfold Mem.nextblock;f_equal;auto. inv H10;inv H18; congruence.
        rewrite H12. eexists. split. econstructor;eauto.
        auto.
      }
      destruct H7 as [m1[]].
      unfold tsostorev in *;ex_match.
      econstructor.
      Focus 2.
      econstructor 2. eauto. eauto. eauto. eauto.
      rewrite <- tsofmem_eq. eauto. eauto. 
      unfold tsostorev. ex_match3. unfold tsostore. eauto.
      unfold tsostorev. ex_match3. unfold tsostore. eauto.
      congruence.
      econstructor;eauto.
      simpl. inv H7. auto.
      simpl. unfold tsostore in *. do 2 inv_some.
      simpl. congruence.
    }
    {
      econstructor. econstructor;reflexivity.
      econstructor 3;eauto.
      eapply eval_builtin_args_locality;eauto.
      auto. auto.
    }
    {
      econstructor. econstructor;reflexivity.
      econstructor 4;eauto.
      eapply extcall_args_locality;eauto.
      auto. auto.
    }
    {
      econstructor. econstructor;reflexivity.
      econstructor 5;eauto.
      auto. auto.
    }
    {
      (* need FLEMBED*)
      assert(exists m0',tsoalloc m0 0 (4*z) (m0',stk)/\tbuffer m0' = tbuffer bm1).
      {  
        eapply alloc_buffer_fl_embed_rel in H4 as?;eauto.
        Focus 2. econstructor;eauto.
        unfold buffer_fl_embed_rel in FLEMBEDREL.
        rewrite H1 in FLEMBEDREL.
        apply FLEMBEDREL in H5 as FLEMBED.
        clear H5.
        destruct FLEMBED as [?[?[]]].
        inversion H4;subst.
        eapply Fleq_apply_buffer_preserve in FLEQ as FLEQ2;eauto.
        eapply fleq_nextblockideq in FLEQ2 as ?;eauto;[|rewrite <- H0;eauto].
        destruct m0.
        assert(Mem.nextblock fm' = Mem.nextblock x0).
        unfold Mem.nextblock;f_equal;auto. inv H7;inv H15; congruence.
        rewrite H9. eexists. split. econstructor;eauto.
        auto.
      }
      destruct H5 as [?[]].
      eapply store_args_fmem_locality in H6 as ?;eauto.
      Hsimpl.
      econstructor. econstructor;reflexivity.
      econstructor 6;try rewrite <- tsofmem_eq;eauto.
      apply store_args_fmem_memunchg in H8.
      apply tsoalloc_memunchg in H5.
      apply tsoalloc_memunchg in H4. simpl in *. congruence.
      congruence.
    }
  Qed.
  Lemma not_lock_step_locality:
    forall fl c gm bf fp c' bf',
      buffer_safe bf gm ->
      tso_not_lock_step fl c (bf,gm) fp c' (bf',gm) ->
      forall gm0 fm0 (FLEMBED:buffer_fl_embed bf fl gm0),
        embed gm0 fl fm0 ->
        LPre gm gm0 fp fl->
        buffer_safe bf gm0->
        tso_not_lock_step fl c (bf,gm0) fp c' (bf',gm0).
  Proof.
    intros.
    assert(buffer_fl_embed_rel bf fl gm gm0). unfold buffer_fl_embed_rel. intro;auto.
    eapply not_lock_step_locality' in H4;eauto.
  Qed.
End AUX_TSOSTEP.
Lemma tsostep_lock_or_notlock:
  forall ge fl c bf gm fp c' bf' gm',
    tsostep ge fl c (bf,gm) fp c' (bf',gm')->
    @tso_lock_step ge fl c (bf,gm) fp c' (bf',gm') \/
    @tso_not_lock_step ge fl c (bf,gm) fp c' (bf',gm').
Proof.
  intros.
  inv H. apply tsofstep_lock_or_notlock in H8 as [|].
  left. apply lock_step_buffer_nil in H as ?. destruct H0;simpl in *;subst.
  rewrite H1. econstructor;eauto.
  right. econstructor;eauto.
Qed.
Lemma lock_step_tsostep:
  forall ge fl c bf gm fp c' bf' gm',
    @tso_lock_step ge fl c (bf,gm) fp c' (bf',gm')->
    tsostep ge fl c (bf,gm) fp c' (bf',gm').
Proof.
  inversion 1;subst;econstructor;eauto.
  eapply lock_step_tsofstep;eauto.
Qed.
Lemma not_lock_step_tsostep:
  forall ge fl c bf gm fp c' bf' gm',
    @tso_not_lock_step ge fl c (bf,gm) fp c' (bf',gm')->
    tsostep ge fl c (bf,gm) fp c' (bf',gm').
Proof.
  inversion 1;subst;econstructor;eauto.
  eapply not_lock_step_tsofstep;eauto.
Qed.
Lemma exec_load_fp_eq_emp:
  forall ge chunk r rs,
    eff_eq FP.emp (exec_load_fp ge chunk r rs).
Proof.
  unfold exec_load_fp,loadv_fp,load_fp.
  intros.
  ex_match2;try apply eff_eq_refl.
  constructor;auto.
Qed.
Lemma tso_cmpu_bool_fp_eq_emp:
  forall x y c bm,
    eff_eq FP.emp (tso_cmpu_bool_fp_total bm c x y).
Proof.
  unfold tso_cmpu_bool_fp_total.
  intros.
  ex_match2;try apply eff_eq_refl;
    unfold tso_weak_valid_pointer_fp,valid_pointer_fp;ex_match2;try constructor;auto.
Qed.
Lemma tso_cmplu_bool_fp_eq_emp:
  forall x y c bm,
    eff_eq FP.emp (tso_cmplu_bool_fp_total bm c x y).
Proof.
  unfold tso_cmplu_bool_fp_total.
  intros.
  ex_match2;try apply eff_eq_refl;
    unfold tso_weak_valid_pointer_fp,valid_pointer_fp;ex_match2;try constructor;auto.
Qed.
Lemma compare_ints_TSO_fp_eq_emp:
  forall x y bm,
    eff_eq FP.emp (compare_ints_TSO_fp x y bm).
Proof.
  unfold compare_ints_TSO_fp.
  rewrite <- FP.fp_union_emp with(fp:=FP.emp).
  intros. apply eff_eq_union;apply tso_cmpu_bool_fp_eq_emp.
Qed.
Lemma compare_longs_TSO_fp_eq_emp:
  forall x y bm,
    eff_eq FP.emp (compare_longs_TSO_fp x y bm).
Proof.
  unfold compare_longs_TSO_fp.
  rewrite <- FP.fp_union_emp with(fp:=FP.emp).
  intros. apply eff_eq_union;apply tso_cmplu_bool_fp_eq_emp.
Qed.
Lemma tso_not_lock_step_bufeff:
  forall ge fl c b gm fp c' b' gm',
    @tso_not_lock_step ge fl c (b,gm) fp c' (b',gm') ->
    BufferEff b b' fp fl.
Proof.
  intros.
  eapply not_lock_step_tsostep in H as ?.
  destruct (eff_chg b b') eqn:?.
  apply eff_chg_t in Heqb0 as [];subst.
  unfold BufferEff.
  exists nil. split. auto. split.
  {
    clear H0.
    inv H. inv H9.
    {
      unfold notlock_instr in H3. ex_match2;simpl in H4;try inv_next;simpl;try apply eff_eq_refl.
      all: try apply exec_load_fp_eq_emp;try apply compare_ints_TSO_fp_eq_emp;try apply compare_longs_TSO_fp_eq_emp.
      all: try solve[unfold exec_store_TSO in H4; ex_match2;inv_next;
        unfold tsostorev,tsostore in *; ex_match2; inv_some;
          inv H11].
      ex_match2;inv_next. simpl. inv H11.
    }
    {
      unfold tsostorev,tsostore in H5. ex_match.
      inv H5. simpl in H11.
      contradict H11. apply app_cons_not_nil.
    }
    {
      simpl.
      revert H4;clear. induction 1.
      apply eff_eq_refl.
      rewrite H0.
      rewrite <- FP.fp_union_emp with(fp:=FP.emp).
      apply eff_eq_union;auto.
      clear IHeval_builtin_args_fp H4 H0 fp2 fp.
      induction H;try apply eff_eq_refl.
      unfold loadv_fp. ex_match2;try apply eff_eq_refl.
      unfold load_fp. split;auto.
      unfold loadv_fp. ex_match2;try apply eff_eq_refl.
      unfold load_fp. split;auto.
      rewrite <- FP.fp_union_emp with(fp:=FP.emp),<- H1.
      apply eff_eq_union;auto.
    }
    {
      simpl.
      revert H2;clear. induction 1.
      apply eff_eq_refl.
      rewrite <-H0.
      rewrite <- FP.fp_union_emp with(fp:=FP.emp).
      apply eff_eq_union;auto.
      clear IHload_arguments_fp H2 H0 fp2 fp.
      inv H. inv H0. apply eff_eq_refl.
      unfold loadv_fp. ex_match2;try apply eff_eq_refl.
      unfold load_fp. split;auto.
      inv H0;inv H1;try rewrite !FP.fp_union_emp;try rewrite !FP.emp_union_fp.
      apply eff_eq_refl.
      
      unfold loadv_fp. ex_match2;try apply eff_eq_refl.
      unfold load_fp. split;auto.
      unfold loadv_fp. ex_match2;try apply eff_eq_refl.
      unfold load_fp. split;auto.

      rewrite <- FP.fp_union_emp with(fp:=FP.emp).
      apply eff_eq_union;auto.
      unfold loadv_fp. ex_match2;try apply eff_eq_refl.
      unfold load_fp. split;auto.
      unfold loadv_fp. ex_match2;try apply eff_eq_refl.
      unfold load_fp. split;auto.
    }
    apply eff_eq_refl.
    {
      apply store_args_fmem_bf_app in H2. Hsimpl.
      rewrite H1 in H11.
      inv H0. simpl in *.
      inv H11.
    }
  }
  {
    unfold buffer_local_alloc. intros.
    inv H1.
  }
  eapply TSO_bfeff;eauto.
Qed.    
Definition bi_disj_fl bi fl:=
  match bi with
  | BufferedAlloc b _ _ => ~ in_fl fl b
  | _ => True
  end.
Lemma bi_disj_fl_freelisteq:
  forall m fl bi m',
      bi_disj_fl bi fl ->
      apply_buffer_item bi m = Some m'->
      FreelistEq m m' fl.
Proof.
  destruct bi;unfold FreelistEq;simpl;intros.
  unfold alloc in H0. inv_some. unfold GMem.valid_block;simpl.
  split;intro;auto. destruct H0;try congruence.
  unfold free in H0. ex_match. inv_some. tauto.
  unfold store in H0;ex_match;inv_some. tauto.
Qed.
Lemma freelisteq_embed:
  forall m fl m' fm,
    embed m fl fm ->
    FreelistEq m m' fl ->
    exists fm', embed m' fl fm'.
Proof.
  intros. inv H; eapply FreelistEq_mem_fl_wd in H0.
  eexists. eapply gmem_fl_wd_embed with(wd:=H0).
Qed.
Lemma buffer_item_local_alloc_disj:
  forall bi fl fl',
    disj fl fl'->
    buffer_item_local_alloc bi fl ->
    bi_disj_fl bi fl'.
Proof.
  unfold buffer_item_local_alloc,bi_disj_fl;intros.
  ex_match2.
  inv H. unfold in_fl in *.
  destruct H0.
  intros [].
  eapply H1;eauto.
  rewrite H,H0. auto.
Qed.
Lemma apply_buffer_item_tsostep_exchage:
  forall ge fl c bf gm fp c' bf' gm',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    buffer_safe bf gm ->
    forall fl' bi gm'',
      ~ FP.conflict (bi_footprint bi) fp ->
      apply_buffer_item bi gm' = Some gm''->
      buffer_item_local_alloc bi fl' ->
      disj fl fl' ->
      buffer_fl_embed bf fl gm'' ->
      exists gm1, apply_buffer_item bi gm = Some gm1 /\
             exists gm2, tsostep ge fl c (bf,gm1) fp c' (bf',gm2) /\
                    GMem.eq gm'' gm2.
Proof.
  intros.
  apply tsostep_lock_or_notlock in H as [|].
  {
    assert(bf = nil /\ bf' = nil).
    inv H;auto. destruct H6;subst.
    assert(LEffect gm gm' fp fl).
    apply lock_step_tsostep in H as ?.
    apply TSO_eff in H6.
    eapply H6;eauto.

    apply FP.smile_conflict_compat in H1.
    apply FPLemmas.fpsmile_sym in H1.
    eapply LEffect_fpsmile_LPre_Rule in H6 as ?;eauto.
    destruct H7.
    eapply buf_item_unbuf_locality_1 in H7 as ?;eauto.
    Hsimpl.
    exists x. split;auto.
    eapply Fleq_apply_buffer_item_preserve in H8 as ?;eauto.

    apply apply_buffer_item_eff in H9 as ?.
    apply FPLemmas.fpsmile_sym in H1.
    eapply MemEffect_fpsmile_MemPre_Rule in H12 as ?;eauto.
    assert(FreelistEq gm x fl).
    eapply bi_disj_fl_freelisteq;eauto.
    eapply buffer_item_local_alloc_disj;eauto.
    apply disj_comm;auto.
    assert(LPre gm x fp fl).
    split;auto. apply MemPre_comm;auto.
    assert(exists fm, embed gm fl fm). inv H;eauto.
    Hsimpl.
    eapply freelisteq_embed in H14 as ?;eauto.
    Hsimpl.
    eapply tso_lock_step_locality in H15;eauto.
    Hsimpl.
    assert(LEffect x x2 fp fl).
    apply lock_step_tsostep in H15.
    apply TSO_eff in H15.
    eapply H15;eauto.
    apply lock_step_tsostep in H15. Esimpl;eauto.
    apply GMem.eq_sym.
    apply GMem_eq.
    eapply LEffect_LPost_fpsmile_memeq with(m0:=gm)(m1:=gm')(m2:=gm'')(m1':=x)(m2':=x2);eauto.
    split. eapply apply_buffer_item_eff;eauto.
    eapply buffer_item_local_alloc_local_alloc;eauto.
    apply FPLemmas.fpsmile_sym;auto.

    split;auto. eapply buffer_item_local_alloc_local_alloc;eauto.
    split;auto.
  }
  {
    apply tso_not_lock_step_memung in H as ?;subst.
    exists gm''. split;auto.
    exists gm''. split;[|apply GMem.eq_refl].
    apply not_lock_step_tsostep.
    inversion H5 as [?[?[]]].
    assert(exists fm,embed gm' fl fm).
    inv H;eauto.
    destruct H8.
    eapply buffer_item_local_alloc_disj in H3 as ?;eauto;[|apply disj_comm;eauto].
    eapply bi_disj_fl_freelisteq in H9 as ?;eauto.
    eapply freelisteq_embed in H8 as ?;eauto.
    Hsimpl.
    eapply not_lock_step_locality;eauto.

    apply LPre_comm.
    eapply LEffect_fpsmile_LPre_Rule;eauto.
    apply disj_comm;eauto.
    split. eapply apply_buffer_item_eff;eauto.
    eapply buffer_item_local_alloc_local_alloc;eauto.
    eapply FP.smile_conflict_compat;eauto.

    eexists;eauto.
  }
Qed.   
Lemma TSO_step_access_validity_preserve:
  forall ge fl bf bf' c gm fp c' gm',
    tsostep ge fl c (bf,gm) fp c' (bf',gm') ->
    GMem.mem_access gm = GMem.mem_access gm' /\
    GMem.validblocks gm = GMem.validblocks gm'.
Proof.
  intros.
  inv H. inv H5. inv H8.
  {
    destruct i;inv H3;unfold exec_load_TSO,exec_store_TSO,tso_goto_label in *;ex_match;try inv H5;try solve[split;auto].
    all: try (apply tsostorev_memunchg in Hx;simpl in Hx;rewrite Hx;split;auto).
    all: unfold Mem.storev,Mem.store in *;ex_match;inv Hx1;inv Hx2;try inv Hx3;auto.
  }
  apply tsoalloc_memunchg in H2.
  apply tsostorev_memunchg in H4.
  apply tsostorev_memunchg in H5.
  simpl in *|- . rewrite H2,H4,H5. split;auto.

  simpl;split;auto.
  simpl;split;auto.
  simpl;split;auto.
  apply tsoalloc_memunchg in H0.
  apply store_args_fmem_memunchg in H2.
  simpl in H0.
  rewrite H0,H2;split;auto.
Qed.
Lemma access_validity_eq_fmem_nextblockid_eq:
  forall gm gm',
    GMem.validblocks gm = GMem.validblocks gm'->
    forall fl fm,
      embed gm fl fm ->
      exists fm', embed gm' fl fm' /\ Mem.nextblockid fm = Mem.nextblockid fm'.
Proof.
  intros.
  assert(FreelistEq gm gm' fl).
  unfold FreelistEq;intros.
  unfold GMem.valid_block. rewrite H. tauto.
  inv H0.
  apply FreelistEq_mem_fl_wd in H1.
  eexists. split. eapply gmem_fl_wd_embed with(wd:=H1).
  auto.
Qed.
Lemma apply_buffer_item_validity_preserve:
  forall bf gm1 gm gm',
    GMem.validblocks gm = GMem.validblocks gm' ->
    GMem.mem_access gm = GMem.mem_access gm' ->
    apply_buffer_item bf gm = Some gm1->
    exists gm1', apply_buffer_item bf gm' = Some gm1' /\
            GMem.mem_access gm1 = GMem.mem_access gm1' /\
            GMem.validblocks gm1 = GMem.validblocks gm1'.
Proof.
  destruct bf;simpl;intros.
  unfold alloc in *;try (inv H1;simpl;Esimpl;eauto;simpl;eauto; try congruence;fail).
  unfold free in *. ex_match.
  assert(range_perm gm' b z z0 Max Freeable).
  unfold range_perm;intros. rewrite<- H0;eapply r;eauto.
  ex_match2.
  unfold unchecked_free in *;inv H1;Esimpl;eauto;simpl;try congruence.
  rewrite H0. auto.

  unfold store in *.
  ex_match2. inv H1;Esimpl;eauto;simpl;eauto.
  clear Hx0. contradict n.
  destruct v0;split;auto.
  unfold range_perm;intros;rewrite <- H0;eapply r;eauto.
Qed.
Lemma apply_buffer_validity_preserve:
  forall bf gm1 gm gm',
    GMem.validblocks gm = GMem.validblocks gm' ->
    GMem.mem_access gm = GMem.mem_access gm' ->
      apply_buffer bf gm = Some gm1->
      exists gm1', apply_buffer bf gm' = Some gm1' /\
              GMem.mem_access gm1 = GMem.mem_access gm1' /\
              GMem.validblocks gm1 = GMem.validblocks gm1'.
Proof.
  induction bf;intros. simpl in H1. inv H1.
  Esimpl;eauto. simpl;auto.

  simpl in H1. unfold optbind in H1;ex_match.
  eapply apply_buffer_item_validity_preserve in Hx as ?;eauto.
  Hsimpl.

  exploit IHbf;eauto.
  intros. Hsimpl.
  Esimpl;eauto.
  simpl;unfold optbind. ex_match3. auto.
Qed.
Lemma apply_buffer_validity_preserve2:
  forall bf gm gm',
    GMem.validblocks gm = GMem.validblocks gm' ->
    GMem.mem_access gm = GMem.mem_access gm' ->
    apply_buffer bf gm = None ->
    apply_buffer bf gm' = None.
Proof.
  induction bf;intros. inv H1.
  simpl in *. unfold optbind in *. ex_match.
  exploit apply_buffer_item_validity_preserve;eauto.
  intros;Hsimpl. ex_match3. eapply IHbf;eauto.
  ex_match2. symmetry in H,H0.
  exploit apply_buffer_item_validity_preserve;eauto.
  intros;Hsimpl. congruence.
Qed.
Definition access_validity_eq gm gm':=
  GMem.validblocks gm = GMem.validblocks gm' /\  GMem.mem_access gm = GMem.mem_access gm'.

Lemma access_validity_eq_comm:
  forall m1 m2,
    access_validity_eq m1 m2 -> access_validity_eq m2 m1.
Proof. destruct 1;split;auto. Qed.
Lemma access_validity_eq_fl_embed_rel:
  forall m m',
    access_validity_eq m m' ->
    forall bf fl,
      buffer_fl_embed_rel bf fl m m'.
Proof.
  intros.
  unfold buffer_fl_embed_rel,buffer_fl_embed;intros.
  Hsimpl. destruct H.
  eapply apply_buffer_validity_preserve in H2;eauto.
  Hsimpl.
  eexists;split;eauto.
  eapply access_validity_eq_fmem_nextblockid_eq in H1;eauto.
  Hsimpl;eauto.
Qed.

Lemma access_validity_buffer_safe_preserve:
  forall gm gm' bf,
    access_validity_eq gm gm' ->
    buffer_safe bf gm ->
    buffer_safe bf gm'.
Proof.
  unfold buffer_safe;intros.
  destruct H. Hsimpl.
  exploit apply_buffer_validity_preserve;eauto.
  intros. Hsimpl;eauto.
Qed.
Lemma lock_step_LEffect:
  forall ge fl c b m fp c' b' m',
    @tso_lock_step ge fl c (b,m) fp c' (b',m')->
    LEffect m m' fp fl.
Proof.
  inversion 1;subst.
  eapply img_eff. eapply TSO_eff. eapply lock_step_tsostep;eauto.
  eauto. eauto.
Qed.
Lemma TSO_one_step_reorder':
  forall ge ge1 fl c gm bf fp c' gm' bf' fl1 c1 c1' bf1 fp1 bf1' gm''
    (STEP1:tsostep ge fl c (bf,gm) fp c' (bf',gm'))
    (STEP2:tsostep ge1 fl1 c1 (bf1,gm') fp1 c1' (bf1',gm''))
    (BUS1: buffer_safe bf gm'')
    (BUS2:buffer_safe bf1 gm)
    (DISJFL:disj fl fl1)
    (FPSMILE:FP.smile fp fp1)
    ,
      exists gm1,
        tsostep ge1 fl1 c1 (bf1,gm) fp1 c1' (bf1',gm1)/\
        exists gm2,
          tsostep ge fl c (bf,gm1) fp c' (bf',gm2) /\
          GMem.eq gm'' gm2.
Proof.
  intros.
  apply tsostep_lock_or_notlock in STEP1 as R1.
  apply tsostep_lock_or_notlock in STEP2 as R2.
  destruct R1 as [R1|R1],R2 as [R2|R2].
  {
    assert(bf = nil /\ bf' = nil /\ bf1 = nil /\ bf1' = nil).
    inv R1;inv R2;auto. Hsimpl;subst.

    assert(exists fm, embed gm' fl1 fm). inv R2;eauto.
    Hsimpl. eapply embed_back_preserve in H;eauto.
    Hsimpl.
    exploit @tso_lock_step_locality;eauto.
    eapply LEffect_fpsmile_LPre_Rule;eauto.
    eapply lock_step_LEffect;eauto.
    intro;Hsimpl.

    assert(exists fm,embed gm fl fm). inv R1;eauto.
    Hsimpl. apply disj_comm in DISJFL.
    apply lock_step_tsostep in H0 as ?.
    eapply embed_preserve2 in H2;try exact DISJFL;eauto.
    Hsimpl.
    exploit @tso_lock_step_locality.
    exact R1. eauto.
    apply LPre_comm.
    eapply LEffect_fpsmile_LPre_Rule;eauto.
    eapply lock_step_LEffect;eauto.
    apply fpsmile_sym;auto.
    intro;Hsimpl.

    apply lock_step_tsostep in H4 as ?.
    Esimpl;eauto.

    apply GMem.eq_sym.
    apply GMem_eq.
    eapply LEffect_LPost_fpsmile_memeq with(m0:=gm)(m1:=gm')(m2:=gm'')(m1':=x1)(m2':=x4);eauto;try eapply lock_step_LEffect;eauto.
  }
  {
    assert(gm'' = gm'). inv R2.
    eapply not_lock_step_mem_ung in H8;eauto.
    simpl in *. inv H5. congruence.
    subst.

    assert(access_validity_eq gm gm').
    apply TSO_step_access_validity_preserve in STEP1 as [];split;auto.
    assert(exists fm, embed gm' fl1 fm). inv R2;eauto.
    Hsimpl. eapply embed_back_preserve in H0;try exact DISJFL;eauto.
    Hsimpl.
    exploit @not_lock_step_locality';try exact R2;eauto.
    eapply access_validity_buffer_safe_preserve;eauto.
    eapply access_validity_eq_fl_embed_rel;apply access_validity_eq_comm;eauto.
    eapply LEffect_fpsmile_LPre_Rule;eauto.
    eapply lock_step_LEffect;eauto.

    intro.
    apply not_lock_step_tsostep in H1 as ?.
    eexists;split;eauto.
    Esimpl;eauto.
    apply GMem.eq_refl.
  }
  {
    assert(gm' = gm). inv R1.
    eapply not_lock_step_mem_ung in H8;eauto.
    simpl in *. inv H5. congruence.
    subst.

    eexists. split;eauto.

    assert(access_validity_eq gm gm'').
    apply TSO_step_access_validity_preserve in STEP2 as [];split;auto.
    assert(exists fm, embed gm fl fm). inv R1;eauto.
    Hsimpl. eapply embed_preserve2 in H0;try apply disj_comm;try exact DISJFL;eauto.
    Hsimpl.
    exploit @not_lock_step_locality';try exact R1;eauto.
    eapply access_validity_buffer_safe_preserve;eauto;apply access_validity_eq_comm;auto.
    eapply access_validity_eq_fl_embed_rel;eauto.
    apply LPre_comm.
    eapply LEffect_fpsmile_LPre_Rule;eauto. apply disj_comm;eauto.
    eapply lock_step_LEffect;eauto.
    apply fpsmile_sym;auto.

    intro.
    apply not_lock_step_tsostep in H1 as ?.
    eexists;split;eauto.
    Esimpl;eauto.
    apply GMem.eq_refl.
  }
  {
    assert(gm = gm').
    inv R1. apply not_lock_step_mem_ung in H8. simpl in *. inv H5;congruence.
    assert(gm' = gm'').
    inv R2. apply not_lock_step_mem_ung in H9;inv H6;simpl in *;congruence.
    subst.

    Esimpl;eauto. apply GMem.eq_refl.
  }
Qed.

Lemma apply_buf_item_MemEffect :
  forall bi m m',
    apply_buffer_item bi m = Some m' ->
    MemEffect m m' (bi_footprint bi).
Proof.
  intros.
  destruct bi; simpls.
  (** alloc *)
  {
    eapply alloc_eff; eauto.
  }
  (** free *)
  {
    eapply free_eff; eauto.
  }
  (** store *)
  {
    eapply store_eff; eauto.
  }
Qed.

Lemma apply_buf_item_outside_stable :
  forall bi bi' m m',
    apply_buffer_item bi m = Some m' ->
    FP.smile (bi_footprint bi) (bi_footprint bi') ->
    MemPre m m' (bi_footprint bi').
Proof. 
  intros.
  eapply MemPre_comm.
  eapply MemEffect_fpsmile_MemPre_Rule; eauto.
  eapply apply_buf_item_MemEffect; eauto.
Qed.
