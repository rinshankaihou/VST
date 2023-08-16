Require Import Blockset Footprint GMemory Injections InteractionSemantics GlobDefs GAST ETrace NPSemantics GDefLemmas.

Require Import Classical_Prop Arith GSimDefs GlobSim GlobUSim NPDRF Init.
(** This file contains proof of DRF-preservation*)
Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:=D|} (at level 72,right associativity).
Local Notation "{-| PC , T }" := 
  ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |})  (at level 70,right associativity).
  Lemma conflict_union:
    forall fp1 fp2 fp3,
      FP.conflict fp1 fp2->FP.conflict (FP.union fp1 fp3) fp2.
  Proof.
    intros.
    destruct fp1,fp2,fp3.
    inversion H; [apply FP.conflict_cf | apply FP.conflict_rf | apply FP.conflict_wf | apply FP.conflict_ff |  apply FP.conflict_rw |  apply FP.conflict_ww];simpl; simpl in H0;Locs.unfolds;destruct H0 as [b[ofs]];exists b,ofs;
      [destruct (cmps b ofs),(frees b ofs),(cmps0 b ofs),(frees0 b ofs),(cmps1 b ofs),(frees1 b ofs)|
       destruct (reads b ofs),(frees b ofs),(reads0 b ofs),(frees0 b ofs),(reads1 b ofs),(frees1 b ofs)|
       destruct (writes b ofs),(frees b ofs),(writes0 b ofs),(frees0 b ofs),(writes1 b ofs),(frees1 b ofs)|
       destruct (frees b ofs),(frees0 b ofs),(frees1 b ofs) |
       destruct (reads b ofs),(writes b ofs),(reads0 b ofs),(writes0 b ofs),(reads1 b ofs),(writes1 b ofs)|
       destruct (writes b ofs),(writes0 b ofs),(writes1 b ofs)];
      auto with bool.
  Qed.
  Corollary conflict_union_ano :
    forall fp1 fp2 fp3,
      FP.conflict fp1 fp2->FP.conflict fp1 (FP.union fp2 fp3).
  Proof.
    intros.
    apply FP.conflict_sym.
    apply FP.conflict_sym in H.
    eapply conflict_union;eauto.
  Qed.

  Local Notation " A |+| B" := (Locs.union A B)  (at level 70,right associativity).
  Local Notation "A |<=| B" := (Locs.subset A B) (at level 70,right associativity).

  Local Ltac clearfp:=
    repeat rewrite FP.fp_union_emp in *;repeat rewrite FP.emp_union_fp in *;
    repeat rewrite FP.fp_union_assoc in *.
  Local Hint Resolve  Locs.locs_eq Locs.union_incr Locs.union_subset Locs.union_assoc Locs.union_sym .
  Lemma locs_union_assoc:
    forall l1 l2 l3,(l1 |+| l2 |+| l3) = ((l1|+|l2) |+| l3).
  Proof. auto. Qed.
  Lemma locs_union_sym:
    forall l1 l2,(l1 |+| l2) = (l2 |+| l1).
  Proof. auto. Qed.
  Local Hint Resolve locs_union_assoc locs_union_sym.
  Corollary UnionSubset4:
    forall l1 l2 l3 l4,
      l1 |<=| (l1|+|l2|+|l3|+|l4) /\
      l2 |<=| (l1|+|l2|+|l3|+|l4) /\
      l3 |<=| (l1|+|l2|+|l3|+|l4) /\
      l4 |<=| (l1|+|l2|+|l3|+|l4).
  Proof.
    intros.
    split;auto.
    split. rewrite locs_union_assoc. rewrite locs_union_sym with(l1 := l1). rewrite <-locs_union_assoc. auto.
    split. rewrite locs_union_assoc. rewrite locs_union_sym. rewrite <- locs_union_assoc. auto.
    rewrite locs_union_assoc.  rewrite locs_union_assoc. rewrite locs_union_sym. auto.
  Qed.
  Corollary subset_belongsto:
    forall x y,
      Locs.subset x y ->
      forall b ofs,
        Locs.belongsto x b ofs
        -> Locs.belongsto y b ofs.
  Proof. intros. eapply Locs.belongsto_subset;eauto. Qed.
  Definition LocG (l:Locs.t) (Shared:Bset.t)(ge:GlobEnv.t)(t:tid) : Prop :=
    forall b ofs,
      Locs.belongsto l b ofs ->
      (Bset.belongsto Shared b \/ FLists.bbelongsto (GlobEnv.freelists ge) t b).
  Lemma fpGtoLocG:
    forall fp Shared ge t,
      fpG fp Shared ge t ->
      LocG fp.(FP.cmps) Shared ge t /\ LocG fp.(FP.reads) Shared ge t /\
      LocG fp.(FP.writes) Shared ge t /\ LocG fp.(FP.frees) Shared ge t.
  Proof.
    intros.
    destruct H; destruct fp; simpl;simpl in H.
    specialize (UnionSubset4 cmps reads writes frees) as[L1 [L2 [L3 L4]]] .
    remember (cmps |+| reads |+| writes |+| frees) as U4.
    specialize (subset_belongsto cmps U4 L1) as S1.
    specialize (subset_belongsto reads U4 L2) as S2.
    specialize (subset_belongsto writes U4 L3) as S3.
    specialize (subset_belongsto frees U4 L4) as S4.
    assert(Refine:forall b ofs,
              Locs.belongsto U4 b ofs ->
              Bset.belongsto Shared b \/ FLists.bbelongsto (GlobEnv.freelists ge) t b
          ).
    intros;subst;eapply H;auto; rewrite <- locs_union_assoc;eauto.
    unfold LocG.
    
    split;try split;try split;intros;eapply Refine;eauto.
  Qed.
    
  Lemma Locemp:
    forall x,
    (forall b ofs ,~ Locs.belongsto x b ofs) <-> Locs.eq x Locs.emp.
  Proof.
    split;intros.
    unfold Locs.belongsto in H.
    unfold Locs.eq.
    intros.
    specialize (H b ofs).
    unfold Locs.emp.
    destruct (x b ofs);auto;contradiction.

    apply Locs.locs_eq in H.
    subst.
    compute.
    intro.
    inversion H.
  Qed.
  Lemma loc_belongsto_intersect:
    forall l1 l2 b ofs,
      Locs.belongsto (Locs.intersect l1 l2) b ofs ->
      Locs.belongsto l1 b ofs /\ Locs.belongsto l2 b ofs.
  Proof.
    unfold Locs.belongsto.
    intros.
    unfold Locs.intersect in H.
    destruct (l1 b ofs);destruct(l2 b ofs);auto.
  Qed.
  Lemma LocMatch_smile_preservation:
    forall mu ge l1 l2 l3 l4 t1 t2,
      GlobEnv.wd ge ->
      LocMatch mu l1 l2 -> LocMatch mu l3 l4 ->
      LocG l2 mu.(SharedTgt) ge t1 ->
      LocG l4 mu.(SharedTgt) ge t2 ->
      t1 <> t2 -> Bset.inj_inject (inj mu) ->
      Locs.smile l1 l3 ->
      Locs.smile l2 l4.
  Proof. {
    intros until t2.
    intro wd.
    destruct mu;simpl.
    intros.
    
    unfold Bset.inj_inject in H4.
    unfold Locs.smile in H5.
    unfold Locs.smile.
    unfold LocG in H1,H2.
    destruct H,H0.
    simpl in H,H0,H1,H2.
    apply Locemp .
    
    unfold Locs.eq. unfold Locs.eq in H5.
    unfold Locs.emp in H5.
    intros.
    intro.
    apply loc_belongsto_intersect in H6 as[].
    pose proof H6 as L;pose proof H7 as R.
    apply H1 in H6 as [];apply H2 in H7 as [];try(
      apply H in L as [x[]];apply H0 in R as [y[]];auto;
      unfold Bset.inject_block in H8,H10;
      eapply H4 in H8;eauto;subst;
      unfold Locs.belongsto in H9,H11;
      specialize (H5 x ofs);
      unfold Locs.intersect in H5;
      rewrite H9 in H5;rewrite H11 in H5; inversion H5).
    clear H H0 H1 H2 H4.
    destruct H6,H7.
    destruct H as [],H0 as [].
    rewrite <- H0 in H;clear H0.
    unfold FLists.get_tfblock in H.
    unfold FLists.get_block in H.
    unfold FLists.get_tfl in H.
    unfold FLists.get_fl in H.
    unfold FLists.get_tfid in H.
    destruct ge.
    destruct freelists.
    simpl in H.
    destruct wd as [wd _ _].
    destruct wd as [_ wd _ wd2].
    simpl in wd,wd2.
    specialize (wd2 t1 t2 x x0 H3).
    apply wd in wd2.
    destruct wd2.
    apply H0 in H.
    auto.
    }
  Qed.

  
  Lemma LFPG_smile_preservation:
    forall mu ge id id' fp1 fp2 fp3 fp4,
      GlobEnv.wd ge -> 
      LFPG mu ge id fp1 fp2 -> LFPG mu ge id' fp3 fp4 -> FP.smile fp1 fp3 ->
      id <> id' -> Bset.inj_inject (inj mu) ->
      FP.smile fp2 fp4.
  Proof.
    intros.
    destruct H0,H1,H2.
    destruct H0,H1.
    apply fpGtoLocG in H5 as [S1[S2[S3 S4]]].
    apply fpGtoLocG in H6 as [W1[W2[W3 W4]]].
    destruct smile_cf,smile_rf,smile_rw,smile_wf.
    constructor;try split;try eapply LocMatch_smile_preservation;eauto.
    all: unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes, FP.ge_frees;
      repeat apply Locs.smile_union; apply Locs.smile_sym; repeat apply Locs.smile_union;
        auto using Locs.smile_sym.
  Qed.

  Corollary smile_conflict:
    forall fp1 fp2, FP.conflict fp1 fp2 <-> ~ FP.smile fp1 fp2.
  Proof.
    split; intros.
    intro.
    apply FP.smile_conflict_compat in H0.
    contradiction.

    assert(FP.conflict fp1 fp2 \/ ~ FP.conflict fp1 fp2). apply classic.
    destruct H0;auto.
    apply FP.smile_conflict_compat in H0.
    contradiction.
  Qed.
  Corollary LFPG_conflict_backwards_preservation :
    forall mu ge id id' fp1 fp2 fp3 fp4,
      GlobEnv.wd ge -> 
      LFPG mu ge id fp1 fp2 -> LFPG mu ge id' fp3 fp4 -> FP.conflict fp2 fp4 ->
      id <> id' -> Bset.inj_inject (inj mu) ->
      FP.conflict fp1 fp3.
  Proof.
    intros.
    apply smile_conflict.
    apply smile_conflict in H2.
    intro.
    eapply LFPG_smile_preservation in H5;eauto.
  Qed.

  Theorem GloblUSimulation_tau_step_backwards_progress :
    forall sge tge I ord match_state i mu spc tpc fpS fpT tpc1 fpT1,
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu fpS fpT spc tpc ->
      np_step tpc tau fpT1 tpc1 ->
      atom_bit tpc = atom_bit tpc1 ->
      exists spce tpce fpSe fpTe,
        tau_star np_step spc fpSe spce /\
        tau_star np_step tpc1 fpTe tpce /\
        atom_bit spc = atom_bit spce /\
        atom_bit tpc = atom_bit tpce /\
        LFPG mu tge tpc.(cur_tid) (FP.union fpS fpSe)(FP.union fpT (FP.union fpT1 fpTe)).
  Proof. {
    intros until fpT1.
    intros GUSim match1 step1 biteq1.
    inversion GUSim.
    revert spc tpc fpS fpT tpc1 fpT1 match1 step1 biteq1.
    induction i using(well_founded_induction index_wf).
    intros.
    pose proof match1 as Tmp1.
    eapply match_tau_step in Tmp1 ;eauto.
    destruct Tmp1 as [[spce[fpSe[j[plus1[lfpg match2]]]]]|[j[ordji match2]]].
    {
      exists spce,tpc1,fpSe,FP.emp.
      apply tau_plus2star in plus1.
      assert(tau_star np_step tpc1 FP.emp tpc1). constructor.
      assert(atom_bit spc = atom_bit spce).
      apply match_tp in match2 as[_[_[_[Eq _]]]].
      inversion Eq;clear Eq;subst.
      apply match_tp in match1 as[_[_[_[Eq _]]]].
      inversion Eq;clear Eq;subst.
      congruence.
      rewrite FP.fp_union_emp.
      auto.
    }
    {
      assert(cur_tid tpc = cur_tid tpc1). eapply GlobSim.tau_step_tid_preservation;eauto.
      pose proof match_abort j mu fpS (FP.union fpT fpT1) spc tpc1 match2 as [_].
      apply GlobSim.safe_rule in H1.
      destruct H1 as [final|[label[fpT2[tpc2 step2]]]].
      {
        eapply match_final in final as [spce[fpSe[S1[S2[S3 S4]]]]];eauto.
        exists spce,tpc1,fpSe,FP.emp.
        assert(tau_star np_step tpc1 FP.emp tpc1). constructor.
        rewrite H0.
        rewrite FP.fp_union_emp.
        auto.        
      }
      {
        assert(L:label = tau \/ label <> tau). apply classic.
        destruct L as [|ntau];subst.
        {
          assert(L:atom_bit tpc1 = atom_bit tpc2 \/ atom_bit tpc1 <> atom_bit tpc2).
          apply classic.
          destruct L as [eq|neq].
          {
            pose proof eq as Tmp1.
            eapply H in Tmp1;eauto.
            destruct Tmp1 as [spce[tpce[fpSe[fpTe[S1[S2[S3[S4 S5]]]]]]]].
            exists spce,tpce,fpSe,(FP.union fpT2 fpTe).
            apply tau_plus_1 in step2;apply tau_plus2star in step2.
            eapply tau_star_star in S2;try apply step2.
            rewrite<- biteq1 in S4.
            rewrite H0.
            rewrite FP.fp_union_assoc.
            auto.
          }
          {
            pose proof neq as Tmp1.
            eapply match_ent_atom in Tmp1;eauto.
            destruct Tmp1 as [fpSe[spce[fpS''[spc''[m[S1[S2[S3[S4 S5]]]]]]]]].
            exists spce,tpc1,fpSe,FP.emp.
            rewrite FP.fp_union_emp.
            split;auto.
            split;constructor;auto.
            split;auto.
            assert(fpS'' =FP.emp).
            inversion S3;subst;auto;try contradiction.
            simpl in S1,S2.
            apply match_tp in match1 as [_[_[_ [Eq _]]]].
            inversion Eq;subst.
            eapply GlobSim.EntAx_bit_rule in neq as [];eauto.
            rewrite H2 in biteq1.
            rewrite biteq1 in H1.
            apply match_tp in S5 as [_[_[_[Eq2 _]]]].
            inversion Eq2;subst.
            simpl in H4.
            rewrite H1 in H4.
            rewrite H3 in H4.
            inversion H4.
            subst.
            rewrite FP.fp_union_emp in S4.
            assert(fpT2=FP.emp).
            inversion step2;subst;auto.
            contradiction .
            subst.
            rewrite FP.fp_union_emp in S4.
            rewrite H0.
            auto.
          }
        }
        {
          pose proof ntau as Tmp1.
          eapply match_npsw_step in Tmp1;eauto.
          destruct Tmp1 as [fpS'[spc'[fpS''[spc''[t[S1[S2[S3[S4 S5]]]]]]]]].
          specialize (S5 t S3) as [S5 [S6[k S7]]].
          exists spc',tpc1,fpS',FP.emp.
          GlobSim.clearfp.
          rewrite H0.
          split;auto.
          split;constructor;auto.
          split;auto.
          assert(fpS'' = FP.emp).
          inversion S4;subst;auto;try contradiction.
          assert(fpT2 = FP.emp).
          inversion step2;subst;auto;try contradiction.
          subst. GlobSim.clearfp;auto.
        }
      }
    }
    }
  Qed.              

  Theorem GloblUSimulation_tau_N_backwards_progress :
    forall sge tge I ord match_state k i mu spc tpc fpS fpT tpc1 fpT1,
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu fpS fpT spc tpc ->
      tau_N np_step k tpc fpT1 tpc1 ->
      atom_bit tpc = atom_bit tpc1 ->
      exists spce tpce fpSe fpTe,
        tau_star np_step spc fpSe spce /\
        tau_star np_step tpc1 fpTe tpce /\
        atom_bit spc = atom_bit spce /\
        atom_bit tpc = atom_bit tpce /\
        LFPG mu tge tpc.(cur_tid) (FP.union fpS fpSe)(FP.union fpT (FP.union fpT1 fpTe)).
  Proof.
    induction k.
    {
      intros until fpT1.
      intros GUSim match_spc_tpc nonsense _.
      inversion GUSim as[wf _ _ _ _ _ safe].
      inversion nonsense;clear nonsense;subst.
      specialize (safe i mu fpS fpT spc tpc1 match_spc_tpc) as [_ safe].
      apply GlobSim.safe_rule in safe as [final|[l[fpT1[tpc2 stepT1]]]].
      {
        inversion GUSim as [_ _ _ _ _ L _].
        specialize (L i mu fpS fpT spc tpc1 match_spc_tpc final) as[spc1[fpS1[star_spc_spc1[biteq1 [lfpg finals]]]]].
        exists spc1,tpc1,fpS1,FP.emp.
        rewrite FP.fp_union_emp.
        assert(tau_star np_step tpc1 FP.emp tpc1). constructor.
        assert(atom_bit tpc1 = atom_bit tpc1). auto. 
        firstorder.
      }
      {
        assert(L:l=tau\/l<>tau). apply classic.
        destruct L as[|non_tau];subst.
        {
          intros.
          assert (L:atom_bit tpc1 = atom_bit tpc2 \/ atom_bit tpc1 <> atom_bit tpc2).
          apply classic.
          destruct L.
          {
            revert spc tpc1 fpS fpT fpT1 tpc2 match_spc_tpc stepT1 H.
            induction i using (well_founded_induction wf).
            inversion GUSim as[_ _ Rule _ _ _ _].
            intros.
            assert(cur_tid tpc1 = cur_tid tpc2).
            eapply GlobSim.tau_step_tid_preservation;eauto.
            specialize (Rule  i mu fpS fpT spc tpc1 match_spc_tpc tpc2 fpT1 stepT1 H0) as[[spce[fpSe[j[plus_spc_spce[lfpg match']]]]] |[j[ordji match']]].
            {
              exists spce,tpc2,fpSe,fpT1.
              apply tau_plus_1 in stepT1.
              apply tau_plus2star in stepT1.
              apply tau_plus2star in plus_spc_spce.
              assert(atom_bit spc = atom_bit spce).
              inversion GUSim as [_ Rule _ _ _ _ _].
              pose proof Rule as Rule1.
              specialize (Rule j mu (FP.union fpS fpSe) (FP.union fpT fpT1) spce tpc2 match') as[_[_[_[Eq _]]]].
              inversion Eq;clear Eq;subst.
              rewrite H2.
              rewrite<- H0.
              specialize (Rule1  i mu fpS fpT spc tpc1 match_spc_tpc) as [_[_[_[Eq _]]]].
              inversion Eq;try congruence.
              rewrite FP.emp_union_fp.
              firstorder.
            }
            {
              inversion  GUSim as [_ _ _ _ _ _ Safe].
              specialize (Safe j mu fpS (FP.union fpT fpT1) spc tpc2 match') as [_ Safe].
              apply GlobSim.safe_rule in Safe as [final|[label[fpT2[tpc3 stepT2]]]].
              {
                inversion GUSim as [_ _ _ _ _ P _].
                eapply P in final as [spce[fpSe[S1[S2[S3 S4]]]]];eauto.
                exists spce,tpc2,fpSe,fpT1.
                split;auto.
                split. apply tau_plus2star;constructor;auto.
                split;auto.
                split;auto.
                rewrite H1.
                rewrite FP.emp_union_fp;auto.
              }
              {
                 assert(L:label = tau \/ label <> tau). apply classic.
                 destruct L.
                 {
                   subst.
                   assert(L:atom_bit tpc2 = atom_bit tpc3 \/ atom_bit tpc2 <> atom_bit tpc3). apply classic.
                   destruct L.
                   {
                     eapply  GloblUSimulation_tau_step_backwards_progress in match';eauto.
                     destruct match' as [spce[tpce[fpSe[fpTe[S1[S2[S3[S4 S5]]]]]]]].
                     exists spce,tpce,fpSe,(FP.union fpT1 (FP.union fpT2 fpTe)).
                     split;auto.
                     split.
                     apply tau_plus_1 in stepT1;apply tau_plus2star in stepT1.
                     apply tau_plus_1 in stepT2;apply tau_plus2star in stepT2.
                     eapply tau_star_star in stepT2;eauto.
                     eapply tau_star_star in S2;eauto.
                     rewrite FP.fp_union_assoc.
                     auto.
                     split;auto.
                     split. try congruence.
                     rewrite H1.
                     rewrite FP.emp_union_fp.
                     rewrite FP.fp_union_assoc.
                     auto.
                   }
                   {
                     inversion GUSim as [_ _ _ R _ _ _].
                     pose proof H2 as Tmp1.
                     eapply R in Tmp1;eauto;clear R.
                     destruct Tmp1 as [fpSe[spce[fpS'[spc'[m[S1[S2[S3[S4 S5]]]]]]]]].
                     assert(fpT2=FP.emp).
                     inversion stepT2;subst;auto;try contradiction.
                     assert(atom_bit spce <> atom_bit spc').
                     inversion GUSim as [_ L _ _ _ _ _].
                     apply L in S5 as [_[_[_ [EQ _]]]];apply L in match' as [_[_[_[EQ2 _]]]];
                       inversion EQ2;inversion EQ;clear L EQ EQ2;subst.
                     rewrite H7;rewrite <- S2;rewrite H4;auto.
                     exists spce,tpc2,fpSe,fpT1.
                     rewrite H0.
                     assert(fpS'=FP.emp).
                     inversion S3;subst;auto;try contradiction.
                     subst.
                     repeat rewrite FP.fp_union_emp in S4.
                     rewrite FP.emp_union_fp .
                     rewrite H1.
                     apply tau_plus_1 in stepT1;apply tau_plus2star in stepT1.
                     auto.
                   }
                 }
                 {
                   assert(fpT2 = FP.emp).
                   inversion stepT2;subst;auto;try contradiction.
                   subst.
                   pose proof H2 as neq.
                   inversion GUSim as [_ _ _ _ R _ _].
                   eapply R in H2 ;eauto;clear R.
                   destruct H2 as [fpSe[spce[fpS'[spc'[m[S1[S2[S3 [S4 S5]]]]]]]]].
                   specialize (S5 m S3) as [S7[S5[k S6]]].
                   exists spce,tpc2,fpSe,fpT1.
                   split;auto.
                   split. apply tau_plus2star;constructor;auto.
                   split;auto.
                   split;auto.
                   rewrite H1.
                   assert(fpS'=FP.emp).
                   inversion S7;subst;auto;try contradiction.
                   subst.
                   GlobSim.clearfp;auto.
                 }
              }            
            }
          }
          {
            inversion GUSim as [_ _ _ R _ _ _].
            pose proof H as Tmp1;eapply R in Tmp1;eauto;clear R.
            destruct Tmp1 as [fpSe[spce[fpS'[spc'[l[S1[S2[S3[S4 S5]]]]]]]]].
            exists spce,tpc1,fpSe,FP.emp.
            split;auto.
            split;constructor;auto.
            split;auto.
            rewrite FP.fp_union_emp.
            assert(atom_bit spce <> atom_bit spc').
            inversion GUSim as [_ R _ _ _ _ _].
            apply R in S5 as [_[_[_[Eq _]]]];apply R in match_spc_tpc as [_[_[_[Eq2 _]]]];inversion Eq;inversion Eq2;subst;clear Eq Eq2 R.
            rewrite <-S2;rewrite H3;rewrite H0;auto.
            assert(fpS'=FP.emp). inversion S3;subst;auto;try contradiction.
            assert(fpT1=FP.emp). inversion stepT1;subst;auto;try contradiction.
            subst.
            repeat rewrite FP.fp_union_emp in S4.
            auto.
          }
        }
        {
          inversion GUSim as [_ _ _ _ R _ _].
          pose proof stepT1 as Tmp1.
          eapply R in Tmp1;eauto;clear R.
          destruct Tmp1 as [fpSe[spce[fpS'[spc'[t[S1[S2[SR [S3 S4] ]]]]]]]].
          specialize (S4 t SR) as [S4[S5[j S6]]].
          exists spce,tpc1,fpSe,FP.emp.
          split;auto.
          split;constructor;auto.
          split;auto.
          rewrite FP.fp_union_emp.
          assert(fpS' = FP.emp).
          inversion S4;subst;auto;try contradiction.
          assert(fpT1 = FP.emp).
          inversion stepT1;subst;auto;try contradiction.
          subst.
          repeat rewrite FP.fp_union_emp in S5.
          auto.
        }
      }
    }
    {
      intros until fpT1.
      intros GUSim match_spc_tpc N1 biteq.
      inversion N1;subst.
      pose GlobSim.tau_N_tau_step_bit_rule.
      specialize (e k tge tpc s' tpc1 fp fp' H0 H1 biteq).
      pose proof e as f.
      inversion GUSim as [_ _ R _ _ _ _].
      eapply R in f;eauto;clear R.
      destruct f as [[spce[fpSe[f[S1[S2 S3]]]]] | [f[ordf S1]]].
      {
        rewrite e in biteq.
        specialize (IHk f mu spce s' (FP.union fpS fpSe) (FP.union fpT fp) tpc1 fp' GUSim S3 H1 biteq).
        destruct IHk as [spce0[tpce0[fpSe0[fpTe0[Q1[Q2[Q3[Q4 Q5]]]]]]]].
        exists spce0,tpce0,(FP.union fpSe fpSe0),fpTe0.
        split. apply tau_plus2star in S1;eapply tau_star_star;eauto.
        split;auto.
        inversion GUSim as [_ R _ _ _ _ _ ].
        apply R in match_spc_tpc as [_[_[_[Eq _]]]];apply R in S3 as [_[_[_[Eq2 _]]]];inversion Eq;inversion Eq2;subst;clear Eq Eq2 R.
        split. congruence.
        split. congruence.
        assert(cur_tid tpc = cur_tid s').
        inversion H0;subst;auto;try contradiction.
        rewrite H2.
        repeat rewrite FP.fp_union_assoc.
        repeat rewrite FP.fp_union_assoc in Q5.
        auto.
      }
      {
        pose proof S1 as Tmp1.
        eapply IHk in Tmp1;eauto.
        destruct Tmp1 as [spce[tpce[fpSe[fpTe[Q1[Q2[Q3 [Q4 Q5]]]]]]]].
        exists spce,tpce,fpSe,fpTe.
        assert(cur_tid tpc = cur_tid s').
        inversion H0;subst;auto;contradiction.
        rewrite H.
        repeat rewrite FP.fp_union_assoc.
        repeat rewrite FP.fp_union_assoc in Q5.
        rewrite<- e in Q4.
        auto.
        rewrite <- biteq.
        symmetry.
        eapply GlobSim.tau_N_tau_step_bit_rule;eauto.
      }
    }
  Qed.

  Lemma tau_star_to_star:
    forall ge pc fp pc1,
      tau_star (@np_step ge) pc fp pc1 -> exists l,star np_step pc l fp pc1.
  Proof.
    intros.
    induction H.
    exists nil;constructor.
    destruct IHtau_star as [l star1].
    exists (cons tau l).
    econstructor 2;eauto.
  Qed.
  Lemma cons_star_step:
    forall ge pc fp pc1 fp1 pc2 l1 o,
      star (@np_step ge) pc l1 fp pc1 ->
      np_step pc1 o fp1 pc2 ->
      star np_step pc (app l1 (cons o nil)) (FP.union fp fp1) pc2.
  Proof.
    intros.
    induction H.
    rewrite FP.emp_union_fp;rewrite <- FP.fp_union_emp with(fp:=fp1).
    econstructor 2;eauto. constructor.
    apply IHstar in H0.
    assert((app (cons e l)(cons o nil)) = (cons e (app l (cons o nil))));auto.
    rewrite H2.
    rewrite <- FP.fp_union_assoc.
    econstructor;eauto.
  Qed.  
      
  Theorem GlobUSimulation_tau_N_EntAtom_progress:
    forall sge tge I ord match_state k i mu spc tpc fpS fpT tpc1 fpT1 tpc2,
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu fpS fpT spc tpc ->
      tau_N np_step k tpc fpT1 tpc1 ->
      atom_bit tpc1 = O ->
      np_step tpc1 tau FP.emp tpc2 ->
      atom_bit tpc2 = GlobDefs.I ->
      exists spc1 spce fpS1 j,
        tau_star np_step spc fpS1 spc1 /\
        atom_bit spc1 = O /\
        np_step spc1 tau FP.emp spce /\
        atom_bit spce = GlobDefs.I /\
        LFPG mu tge tpc.(cur_tid)(FP.union fpS fpS1)(FP.union fpT fpT1) /\
        match_state j mu FP.emp FP.emp spce tpc2.
  Proof.
    induction k.
    {
      intros.
      inversion H.
      inversion H1;clear H1;subst.
      assert(atom_bit tpc1 <> atom_bit tpc2). rewrite H2;rewrite H4. intro. inversion H1.
      pose proof H3 as L.
      eapply match_ent_atom in L;eauto;destruct L as [fpS'[spc'[fpS''[spc''[j[S1[S2[S3[S4 S5]]]]]]]]].
      assert(atom_bit spc'<>atom_bit spc'').
      apply match_tp in S5 as [_[_[_[eq _]]]];apply match_tp in H0 as [_[_[_ [eq2 _]]]]; inversion eq;inversion eq2;clear eq eq2;subst.
      rewrite H0;rewrite <- S2;rewrite H7;auto.
      assert(fpS''=FP.emp). inversion S3;subst;auto;contradiction.
      subst.
      eapply GlobSim.EntAx_bit_rule in H5 as [];eauto.
      rewrite FP.fp_union_emp.
      repeat rewrite FP.fp_union_emp in S4.
      
      exists spc',spc'',fpS',j.
      firstorder.
    }
    {
      intros.
      inversion H1;subst.
      pose GlobSim.tau_N_bit_backwards_preservation.
      pose proof e (S k) tge tpc tpc1 (FP.union fp fp') H1 H2.
      assert(atom_bit s' = O). eapply GlobSim.tau_N_tau_step_bit_rule in H6;eauto. congruence.
      assert(atom_bit tpc=atom_bit s'). congruence.
      inversion H as [_ _ R _ _ _ _].
      eapply R in H9;eauto;clear R;destruct H9 as [[spc'[fpS'[i'[N1[N2 N3]]]]]  |[t[ordt match'']]].
      {
        specialize (IHk i' mu spc' s'  (FP.union fpS fpS') (FP.union fpT fp ) tpc1 fp' tpc2 H N3 H7 H2 H3 H4) as [spc1[spce[fpS1[j[S1[S2[S3[S4[S5 S6]]]]]]]]].
        exists spc1,spce,(FP.union fpS' fpS1),j.
        apply tau_plus2star in N1;eapply tau_star_star in S1;eauto.
        assert(cur_tid tpc = cur_tid s') . inversion H6;subst;auto;contradiction.
        rewrite H9.
        repeat rewrite<- FP.fp_union_assoc in S5.
        firstorder.
      }
      {
        eapply IHk in match'' as [spc1[spce[fpS1[j[S1[S2[S3[S4[S5 S6]]]]]]]]];eauto.
        assert(cur_tid tpc = cur_tid s') . inversion H6;subst;auto;contradiction.
        rewrite H9.
        rewrite <- FP.fp_union_assoc in S5.
        exists spc1,spce,fpS1,j.
        firstorder.
      }
    }
  Qed.

 

  Lemma tau_N_OIsplit:
    forall ge k pc fp pc1,
      tau_N (@np_step ge) k pc fp pc1 -> atom_bit pc <> atom_bit pc1 ->
      exists i j pc' pc'' fp1 fp2,
        tau_N np_step i pc fp1 pc' /\ atom_bit pc' = O /\
        np_step pc' tau FP.emp pc'' /\ atom_bit pc'' = GlobDefs.I /\
        tau_N np_step j pc'' fp2 pc1 /\ FP.union fp1 fp2 = fp /\ i+j+1=k.
  Proof.
    induction k;intros.
    inversion H;subst;contradiction.
    inversion H;subst.
    assert(atom_bit pc = O /\ atom_bit pc1 = I).
    eapply GlobSim.tau_N_bit_rule in H as [[]|[[]|[]]];subst;auto;rewrite H in H0;rewrite H1 in H0;contradiction.
    destruct H1.
    destruct (atom_bit s') eqn:eq.
    {
      assert(atom_bit s' <> atom_bit pc1).
      rewrite H4;rewrite eq;auto.
      intro;inversion H5.
      eapply IHk in H5;eauto.
      destruct H5 as [i[j[pc'[pc''[fp1[fp2[N1[b1[step1[b2[N2[]]]]]]]]]]]].
      exists (S i),j,pc',pc'',(FP.union fp0 fp1),fp2.
      split. econstructor 2;eauto.
      split;[auto|split];auto.
      split;[auto|split];auto.
      split;auto.
      rewrite <- FP.fp_union_assoc.
      rewrite H5.
      reflexivity.
      rewrite<- H6.
      auto.
    }
    {
      assert(fp0=FP.emp). inversion H2;subst;auto;try contradiction.
      compute in H1,eq. rewrite H1 in eq. inversion eq.
      subst.
      exists 0,k,pc,s',FP.emp,fp'.
      clearfp.
      split;constructor;auto;constructor;auto;constructor;auto;constructor;auto;constructor;auto.
      Lia.lia.
    }
  Qed.
  Corollary tau_star_OIsplit:
    forall ge pc fp pc1,
      tau_star (@np_step ge) pc fp pc1 -> atom_bit pc <> atom_bit pc1 ->
      exists  pc' pc'' fp1 fp2,
        tau_star np_step pc fp1 pc' /\ atom_bit pc' = O /\
        np_step pc' tau FP.emp pc'' /\ atom_bit pc'' = I /\
        tau_star np_step pc'' fp2 pc1 /\ FP.union fp1 fp2 = fp.
  Proof.
    intros.
    apply tau_star_tau_N_equiv in H as [].
    apply tau_N_OIsplit in H;auto.
    destruct H as [i[j[pc'[pc''[fp1[fp2[S1[S2[S3[S4[S5[S6 _]]]]]]]]]]]].
    exists pc',pc'',fp1,fp2.
    split. apply tau_star_tau_N_equiv;eauto.
    split;auto.
    split;auto.
    split;auto.
    split;auto. apply tau_star_tau_N_equiv;eauto.
  Qed.

  Lemma USim_fpsconflict_backwards_preservation_case1:
    forall sge tge I ord match_state i mu spc tpc,
      GlobEnv.wd tge ->
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu FP.emp FP.emp spc tpc ->
      forall I2 ord2 match_state2 i2 id,
        @GConfigUSim sge tge I2 ord2 match_state2->
        match_state2 i2 mu FP.emp FP.emp ({-|spc,id})({-|tpc,id}) ->
        cur_tid tpc <> id ->
        forall tpc1 fpT1 tpcid fpTid,
          tau_star np_step tpc fpT1 tpc1 ->
          atom_bit tpc = atom_bit tpc1 ->
          tau_star np_step ({-|tpc,id}) fpTid tpcid ->
          atom_bit tpc = atom_bit tpcid ->
          FP.conflict fpT1 fpTid ->
          exists spc1 fpS1 spcid fpSid,
            (
              tau_star np_step spc fpS1 spc1 /\ atom_bit spc = atom_bit spc1 /\
              tau_star np_step ({-|spc,id}) fpSid spcid /\ atom_bit spc = atom_bit spcid /\
              FP.conflict fpS1 fpSid).
  Proof. {
    intros until id.
    intro wd.
    intros.
    apply tau_star_tau_N_equiv in H4 as [].
    apply tau_star_tau_N_equiv in H6 as [].
    eapply GloblUSimulation_tau_N_backwards_progress with(I:=I) in H4;eauto.
    eapply GloblUSimulation_tau_N_backwards_progress with(I:=I2)in H6;eauto.
    destruct H4 as [spc1[tpc'[fpS1[fpT'[star1[star2[b1[b2 lfpg]]]]]]]].
    destruct H6 as [spc'[tpc''[fpS'[fpT''[star3[star4[b3[b4 lfpg2]]]]]]]].
    clearfp.
    assert(FP.conflict (FP.union fpT1 fpT')(FP.union fpTid fpT'')).
    apply conflict_union. apply conflict_union_ano. auto.
    eapply LFPG_conflict_backwards_preservation in H4;eauto.
    exists spc1,fpS1,spc',fpS'.
    auto.
    inversion H .
    eapply match_mu_wd;eauto.
    }
  Qed.

  Lemma USim_fpsconflict_backwards_preservation_case2:
    forall sge tge I ord match_state i mu spc tpc,
      GlobEnv.wd tge ->
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu FP.emp FP.emp spc tpc ->
      forall I2 ord2 match_state2 i2 id,
        @GConfigUSim sge tge I2 ord2 match_state2 ->
        match_state2 i2 mu FP.emp FP.emp ({-|spc,id})({-|tpc,id}) ->
        cur_tid tpc <> id ->
        forall tpc1 fpT1 tpc2 tpc3 fpT2 tpcid fpTid,
          tau_star np_step tpc fpT1 tpc1 ->
          atom_bit tpc = atom_bit tpc1 ->
          np_step tpc1 tau FP.emp tpc2 -> atom_bit tpc1 <> atom_bit tpc2 ->
          tau_star np_step tpc2 fpT2 tpc3 ->
          atom_bit tpc2 = atom_bit tpc3 ->
          tau_star np_step ({-|tpc,id}) fpTid tpcid ->
          atom_bit tpc = atom_bit tpcid ->
          FP.conflict fpT2 fpTid ->
          exists spc1 fpS1 spc2 spc3 fpS2 spcid fpSid,
            tau_star np_step spc fpS1 spc1 /\ atom_bit spc = atom_bit spc1 /\
            np_step spc1 tau FP.emp spc2 /\ atom_bit spc1 <> atom_bit spc2 /\
            tau_star np_step spc2 fpS2 spc3 /\
            tau_star np_step ({-|spc,id}) fpSid spcid /\ atom_bit spc = atom_bit spcid /\
            FP.conflict fpS2 fpSid.
  Proof. {
    intros.
    assert(R:cur_tid tpc = cur_tid tpc2).
    apply GlobSim.tau_star_tid_preservation in H5.
    apply GlobSim.tau_step_tid_preservation in H7.
    congruence.
    apply tau_star_tau_N_equiv in H5 as [].
    apply tau_star_tau_N_equiv in H11 as [].
    eapply GloblUSimulation_tau_N_backwards_progress with(I:=I2) in H11;eauto.
    destruct H11 as [spc'[tpc''[fpS'[fpT''[star3[star4[b3[b4 lfpg2]]]]]]]].
    eapply GlobUSimulation_tau_N_EntAtom_progress with(I0:=I) in H5;eauto.
    destruct H5 as [spc1[spce[fpS1[j[S1[S2[S3[S4[S5 S6]]]]]]]]].
    pose proof H9 as H9'.
    apply tau_star_tau_N_equiv in H9.
    destruct H9 as [y L].
    eapply GloblUSimulation_tau_N_backwards_progress with(I:=I)in L;eauto.
    destruct L as [spce0[tpce[fpSe[fpTe[Q1[Q2[Q3[Q4 Q5]]]]]]]].
    exists spc1,fpS1,spce,spce0,fpSe,spc',fpS'.
    clearfp.
    split;auto.
    split;auto.
    apply tau_star_tau_N_equiv in S1 as [].
    eapply GlobSim.tau_N_bit_backwards_preservation in H5;eauto.
    congruence.
    split;auto.
    split;auto.
    rewrite S2;rewrite S4.
    intro.
    inversion H5.
    split;auto.
    split;auto.
    split;auto.
    eapply LFPG_conflict_backwards_preservation;eauto.
    apply conflict_union. apply conflict_union_ano. auto.
    rewrite<- R.
    auto.
    inversion H0.
    eapply match_mu_wd;eauto.
    inversion H7;subst;auto;try contradiction.
    inversion H7;subst;auto;try contradiction.
    }
  Qed.

  Inductive np_race_config_base {ge}(pc:@ProgConfig ge):Prop:=
  | race_tau:
      forall id1 id2 fp1 fp2 pc1 pc2,
        pc_valid_tid pc id1 -> pc_valid_tid pc id2 -> id1<>id2 -> atom_bit pc = O ->
        tau_star np_step ({-|pc,id1}) fp1 pc1 -> atom_bit pc = atom_bit pc1 ->
        tau_star np_step ({-|pc,id2}) fp2 pc2 -> atom_bit pc = atom_bit pc2 ->
        FP.conflict fp1 fp2 -> np_race_config_base pc
  | race_atom_1:
      forall id1 id2 fp1 fp10 fp2 pc1 pc10 pc11 pc2,
        pc_valid_tid pc id1 -> pc_valid_tid pc id2 -> id1<>id2 ->
        tau_star np_step ({-|pc,id1}) fp1 pc1 -> atom_bit pc = atom_bit pc1 -> atom_bit pc = O ->
        np_step pc1 tau FP.emp pc10 -> atom_bit pc1 <> atom_bit pc10 ->
        tau_star np_step pc10 fp10 pc11 -> atom_bit pc10 = atom_bit pc11 ->
        tau_star np_step ({-|pc,id2}) fp2 pc2 -> atom_bit pc = atom_bit pc2 ->
        FP.conflict fp10 fp2 -> np_race_config_base pc.

  Definition np_race_config_0 {NL}{L:@langs NL}{gm}{ge}(p:prog L)(pc:@ProgConfig ge):Prop:=
    init_config p gm ge pc pc.(cur_tid) /\ np_race_config_base pc.
  Definition np_race_config_1 {ge}(o:glabel)(pc0 pc:@ProgConfig ge):Prop:=
    np_step pc0 o FP.emp pc /\ o <> tau /\ np_race_config_base pc.

  Lemma swid_valid_tid_preservation:
    forall ge pc id t,
      @pc_valid_tid ge pc id ->
      pc_valid_tid ({-|pc,t}) id.
  Proof.
    destruct pc.
    unfold pc_valid_tid.
    simpl.
    auto.
  Qed.

  Lemma GUSim_nprace_preservation_1:
    forall sge tge I ord i match_state mu fpS fpT spc tpc,
      GlobEnv.wd tge ->
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu fpS fpT spc tpc ->
      forall o tpc1,
        np_race_config_1 o tpc tpc1 ->
        exists spc1 fpS1 spc2,
          tau_star np_step spc fpS1 spc1 /\
          np_race_config_1 o spc1 spc2.
  Proof. {
    intros.
    unfold np_race_config_1 in *.
    destruct H2 as [step[ntau race]].
    inversion H0 as [_ _ _ _ R _ _ _].
    specialize (R i mu fpS fpT spc tpc H1 o tpc1 FP.emp ntau step) as [fpS1[spc1[fpS2[spc2[id[S1[S2[S3[S4 S5]]]]]]]]].
    assert(fpS2=FP.emp).
    specialize (S5 id S3) as [S5 _]. inversion S5;subst;auto;contradiction.
    subst. clearfp.
    assert(pc_valid_tid spc2 spc2.(cur_tid)).
    inversion S4;subst;try contradiction;unfold pc_valid_tid;auto.
    pose proof S5 spc2.(cur_tid) H2 as [S8[S6[j S7]]].
    exists spc1,fpS1,spc2.
    split;auto.
    split;auto.
    assert(forall t,pc_valid_tid tpc1 t-> pc_valid_tid spc2 t).
    {
      intros.
      inversion H0 as [_ R _ _ _ _ _ _].
      apply R in S7 as [E1[E2[E3 _]]].
      eapply GlobSim.thrddom_eq'_valid_tid_preservation in H3;eauto.
      apply GlobSim.thrddom_eq_comm.
      destruct spc2,tpc1;inversion E3;subst;econstructor;simpl in *;eauto.
    }
    inversion race;subst.
    {
      pose proof H3 id1 H4 as L1.
      pose proof S5 id1 L1 as [Sq1[Sq2[kq Sq3]]].
      pose proof H3 id2 H5 as L2.
      pose proof S5 id2 L2 as [Sr1[Sr2[Kr Sr3]]].
      pose USim_fpsconflict_backwards_preservation_case1.
      specialize (e sge tge I ord match_state kq mu ({-|spc2, id1}) ({-|tpc1, id1}) H H0 Sq3 I ord match_state Kr id2 H0 Sr3 H6 pc1 fp1 pc2 fp2 H8 H9 H10 H11 H12).
      destruct e as [s1[f1[s2[f2[Q1[Q2[Q3[Q4 Q5]]]]]]]].
      econstructor;eauto.
      apply H3 in H4.
      apply H3 in H5.
      econstructor 1 with(id1:=id1)(id2:=id2);eauto.
      inversion H0.
      apply match_tp in Sr3.
      destruct Sr3 as [_[_[_[Eq _]]]].
      inversion Eq;subst.
      destruct spc2.
      simpl in *.
      congruence.
    }
    {
      pose proof H3 id1 H4 as L1.
      pose proof S5 id1 L1 as [Sq1[Sq2[kq Sq3]]].
      pose proof H3 id2 H5 as L2.
      pose proof S5 id2 L2 as [Sr1[Sr2[Kr Sr3]]].
      pose USim_fpsconflict_backwards_preservation_case2.
      specialize (e sge tge I ord match_state kq mu ({-|spc2, id1}) ({-|tpc1, id1}) H H0 Sq3 I ord match_state Kr id2 H0 Sr3 H6 pc1 fp1 pc10 ).
      specialize (e pc11 fp10 pc2 fp2 H7 H8 H10 H11 H12 H13 H14 H15 H16).
      destruct e as [s1[f1[s2[s3[f2[s4[f4[Q1[Q2[Q3[Q4[Q5[Q6[Q7 Q8]]]]]]]]]]]]]].
      split;auto.
      assert(atom_bit spc2 = O).
      inversion Sr1;subst;try contradiction;auto.
      econstructor 2 with(id1:=id1)(id2:=id2);eauto.
      eapply GlobSim.EntAx_bit_rule in Q4 as [];eauto.
      apply tau_star_tau_N_equiv in Q5 as [].
      eapply GlobSim.tau_N_bit_I_preservation in H19 as L;eauto.
      congruence.
    }
    }
  Qed.
  Lemma GUSim_progress:
    forall sge tge I ord i match_state mu fpS fpT spc tpc l fpT' tpc',
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu fpS fpT spc tpc ->
      np_step tpc l fpT' tpc' ->
      exists fpS' spc' l' j fp1 fp2,
        match_state j mu fp1 fp2 spc' tpc' /\
        star np_step spc l' fpS' spc'.
  Proof. {
    intros until tpc'.
    intro GUSim.
    inversion GUSim.
    intros match_spc_tpc step1.
    assert(l=tau\/l<>tau). apply classic.
    destruct H .
    {
      subst.
      assert(atom_bit tpc = atom_bit tpc'\/atom_bit tpc <> atom_bit tpc').
      apply classic.
      destruct H.
      {
        eapply match_tau_step in H;eauto.
        destruct H as [[spc1[fpS1[j[S1[S2 S3]]]]]|[j[S1 S2]]].
        + apply tau_plus2star in S1;apply tau_star_to_star in S1 as [].
          exists fpS1,spc1,x,j,(FP.union fpS fpS1), (FP.union fpT fpT');auto.
        + exists FP.emp,spc,nil,j,fpS,(FP.union fpT fpT').
          constructor;auto. constructor.
      }
      {
        eapply match_ent_atom in H;eauto.
        destruct H as [fpS1[spc1[fpS2[spc2[j[S1[S2[S3[S4 S5]]]]]]]]].
        apply tau_star_to_star in S1 as [].
        exists (FP.union fpS1 fpS2),spc2,(app x (cons tau nil)),j,FP.emp,FP.emp.
        split;auto.
        eapply cons_star_step;eauto.
      }
    }
    {
      pose proof H as L.
      eapply match_npsw_step in H;eauto.
      destruct H as [fpS1[spc1[fpS2[spc2[id[S1[S2[S3[S4 S5]]]]]]]]].      
      assert (pc_valid_tid ({-|tpc',id}) tpc'.(cur_tid)).
      inversion step1;subst;try contradiction;unfold pc_valid_tid;auto.
      pose proof S5 id S3 as [_[_[i' H']]].
      pose proof match_tp i' mu FP.emp FP.emp ({-|spc2, id}) ({-|tpc', id}) H' as [E1[E2[E3 _]]].
      eapply GlobSim.match_tp_ano' in E3;eauto.
      assert(pc_valid_tid spc2 (cur_tid tpc')).
      auto.
      specialize (S5 tpc'.(cur_tid) H0) as [Q1[Q2 [j Q3]]].
      apply tau_star_to_star in S1 as [].
      exists (FP.union fpS1 fpS2), ({-|spc2, cur_tid tpc'}),(app x (cons l nil)),j,FP.emp,FP.emp.
      assert(({-|tpc',cur_tid tpc'})=tpc').
      destruct tpc';auto.
      rewrite <- H2.
      split;auto.
      rewrite H2.
      eapply cons_star_step;eauto.
    }
    }
  Qed.    

  Lemma cons_star_star:
    forall ge pc0 pc1 pc2 fp1 fp2 l1 l2,
      star (@np_step ge) pc0 l1 fp1 pc1->
      star np_step pc1 l2 fp2 pc2 ->
      star np_step pc0 (app l1 l2)(FP.union fp1 fp2) pc2.
  Proof.
    intros.
    induction H.
    clearfp;auto.
    apply IHstar in H0.
    assert(app (cons e l) l2 = cons e (app l l2)). auto.
    rewrite H2.
    rewrite <- FP.fp_union_assoc.
    econstructor 2 ;eauto.
  Qed.
  
  Lemma GUSim_star_progress:
    forall sge tge I ord i match_state mu fpS fpT spc tpc l fpT' tpc',
      @GConfigUSim sge tge I ord match_state ->
      match_state i mu fpS fpT spc tpc ->
      star np_step tpc l fpT' tpc' ->
      exists fpS' spc' l' j fp1 fp2,
        match_state j mu fp1 fp2 spc' tpc' /\
        star np_step spc l' fpS' spc'.
  Proof.
    intros.
    revert H H0.
    revert I ord match_state i mu fpS fpT spc.
    induction H1;intros.
    exists FP.emp,spc,nil,i,fpS,fpT;split;auto;constructor.
    eapply GUSim_progress in H;eauto.
    destruct H as [fpS1[spc1[l'[j[fp1'[fp2'[]]]]]]].
    eapply IHstar in H;eauto.
    destruct H as [fpS2[spc2[l2[j2[fp12[fp22[]]]]]]].
    exists (FP.union fpS1 fpS2),spc2,(app l' l2),j2,fp12,fp22.
    split;auto.
    eapply cons_star_star ;eauto.
  Qed.    

  Lemma GUSim_star_nprace_preservation_1:
    forall sge tge  I ord i match_state mu fpS fpT spc tpc ,
          GlobEnv.wd tge ->
          @GConfigUSim sge tge I ord match_state ->
          match_state i mu fpS fpT spc tpc ->
          forall l fp1 tpc1 o tpc2,
            star np_step tpc l fp1 tpc1 ->
            np_race_config_1 o tpc1 tpc2 ->
          exists l2 fpS0 spc1 spc2,
            star np_step spc l2 fpS0 spc1 /\
            np_race_config_1 o spc1 spc2.
  Proof.
    intros.
    eapply GUSim_star_progress in H2;eauto.
    destruct H2 as [fpS'[spc'[l'[j'[fp1'[fp2'[]]]]]]].
    eapply GUSim_nprace_preservation_1 in H3;eauto.
    destruct H3 as [spc1[fpS1[spc2[]]]].
    apply tau_star_to_star in H3 as [].
    eapply cons_star_star in H3;eauto.
    exists (app l' x),(FP.union fpS' fpS1) ,spc1,spc2;auto.
  Qed.    



  Definition init_rel {NL}{L:@langs NL}(sp tp:prog L):Prop:=
    forall tgm tge tpc,
      init_config tp tgm tge tpc tpc.(cur_tid) ->
      exists mu sgm sge spc,
        InitRel mu sge tge sgm tgm /\
        init_config sp sgm sge spc tpc.(cur_tid).

 Lemma GUSim_nprace_preservation_2':
   forall NL L mu sp tp tgm tge tpc sgm sge spc
     (H:True)
     (H0:GlobUSim sp tp)
     (H1:@np_race_config_0 NL L tgm tge tp tpc)
     (H3:InitRel mu sge tge sgm tgm)
     (H4:@init_config NL L sp sgm sge spc tpc.(cur_tid)),
     @np_race_config_0 NL L sgm sge sp spc.
  Proof. {
    intros. destruct H1.
    unfold np_race_config_0.
    assert(cur_tid tpc = cur_tid spc).
    inversion H4;auto.
    rewrite <- H5;split;auto.

    unfold GlobUSim in H0.
    assert(thrddom_eq' spc tpc).
    eapply H0 in H4 as [I[ord[i[match_state[]]]]];eauto.
    inversion H4;apply match_tp in H6 as [E1[E2[]]];auto.
    pose proof H4 as L1.
    pose proof H1 as L2.
    apply GlobSim.init_config_inv_thp in L1 .
    apply GlobSim.init_config_inv_thp in L2.
    assert(forall id,pc_valid_tid tpc id ->
                exists I ord match_state i,
                  GConfigUSim I ord match_state /\
                  match_state i mu FP.emp FP.emp ({-|spc,id})({-|tpc,id})).
    intros; eapply init_free in H1;try apply H7.

    eapply GlobSim.match_tp_ano' in H6;try apply H7;auto.
    rewrite H5 in H4.
    eapply init_free in H4;try apply H6.
    eapply H0 in H4;eauto.
    
    assert(wd:GlobEnv.wd tge).
    inversion H1;inversion H8;auto.
    
    inversion H2;subst.
    {
      pose proof H7 id1 H8 as [I1[ord1[match1[i1[]]]]].
      pose proof H7 id2 H9 as [I2[ord2[match2[i2[]]]]].
      pose USim_fpsconflict_backwards_preservation_case1.
      eapply USim_fpsconflict_backwards_preservation_case1 with(I:=I1)(I2:=I2) in H16;eauto.
      destruct H16 as [spc1[fpS1[spc2[fpS2[S1[S2[S3[S4 S5]]]]]]]].
      econstructor 1;eauto;try eapply GlobSim.match_tp_ano';eauto.
      clear e.
      inversion H19 as [_ R _ _ _ _ _ _ ].
      apply R in H20 as [_[_[_[Eq _]]]];inversion Eq;subst.
      destruct tpc,spc;simpl in *;try congruence.
    }
    {
      pose proof H7 id1 H8 as [I1[ord1[match1[i1[]]]]].
      pose proof H7 id2 H9 as [I2[ord2[match2[i2[]]]]].
      eapply  USim_fpsconflict_backwards_preservation_case2 with(I:=I1)(I2:=I2) in H20;eauto.
      destruct H20 as [spc1[fpS1[spc2[spc3[fpS2[spc''[fpS''[S1[S2[S3[S4[S5[S6[S7 S8]]]]]]]]]]]]]].
      econstructor 2;eauto;try eapply GlobSim.match_tp_ano';eauto.
      eapply match_tp in H24;eauto.
      destruct H24 as (_&_&_&?&_). inversion H20;subst. simpl in H24. congruence.
      eapply GlobSim.EntAx_bit_rule in S4 as [];eauto.
      apply tau_star_tau_N_equiv in S5 as [x S5];eapply GlobSim.tau_N_bit_I_preservation in S5;eauto.
      congruence.
    }
    }
  Qed.
Lemma GUSim_nprace_preservation_2:
    forall NL L sp tp,
      init_rel sp tp ->
      GlobUSim sp tp ->
      forall tgm tge tpc,
        @np_race_config_0 NL L tgm tge tp tpc ->
        exists sgm sge spc, @np_race_config_0 NL L sgm sge sp spc.
  Proof. {
    intros.
    destruct H1.
    pose proof H1 as Tmp1;eapply H in Tmp1;try apply H;eauto.
    destruct Tmp1 as [mu[sgm0[sge0[spc0 []]]]].
    exists sgm0,sge0,spc0.
    unfold np_race_config_0.
    assert(cur_tid tpc = cur_tid spc0).
    inversion H4;auto.
    rewrite <- H5;split;auto.

    unfold GlobUSim in H0.
    assert(thrddom_eq' spc0 tpc).
    eapply H0 in H4 as [I[ord[i[match_state[]]]]];eauto.
    inversion H4;apply match_tp in H6 as [E1[E2[]]];auto.
    pose proof H4 as L1.
    pose proof H1 as L2.
    apply GlobSim.init_config_inv_thp in L1 .
    apply GlobSim.init_config_inv_thp in L2.
    assert(forall id,pc_valid_tid tpc id ->
                exists I ord match_state i,
                  GConfigUSim I ord match_state /\
                  match_state i mu FP.emp FP.emp ({-|spc0,id})({-|tpc,id})).
    intros; eapply init_free in H1;try apply H7.

    eapply GlobSim.match_tp_ano' in H6;try apply H7;auto.
    rewrite H5 in H4.
    eapply init_free in H4;try apply H6.
    eapply H0 in H4;eauto.
    
    assert(wd:GlobEnv.wd tge).
    inversion H1;inversion H8;auto.
    
    inversion H2;subst.
    {
      pose proof H7 id1 H8 as [I1[ord1[match1[i1[]]]]].
      pose proof H7 id2 H9 as [I2[ord2[match2[i2[]]]]].
      pose USim_fpsconflict_backwards_preservation_case1.
      eapply USim_fpsconflict_backwards_preservation_case1 with(I:=I1)(I2:=I2) in H16;eauto.
      destruct H16 as [spc1[fpS1[spc2[fpS2[S1[S2[S3[S4 S5]]]]]]]].
      econstructor 1;eauto;try eapply GlobSim.match_tp_ano';eauto.
      clear e.
      inversion H19 as [_ R _ _ _ _ _ _ ].
      apply R in H20 as [_[_[_[Eq _]]]];inversion Eq;subst.
      destruct tpc,spc0;simpl in *;try congruence.
    }
    {
      pose proof H7 id1 H8 as [I1[ord1[match1[i1[]]]]].
      pose proof H7 id2 H9 as [I2[ord2[match2[i2[]]]]].
      eapply  USim_fpsconflict_backwards_preservation_case2 with(I:=I1)(I2:=I2) in H20;eauto.
      destruct H20 as [spc1[fpS1[spc2[spc3[fpS2[spc''[fpS''[S1[S2[S3[S4[S5[S6[S7 S8]]]]]]]]]]]]]].
      econstructor 2;eauto;try eapply GlobSim.match_tp_ano';eauto.
      eapply match_tp in H24;eauto.
      destruct H24 as (_&_&_&?&_). inversion H20;subst. simpl in H24. congruence.
      eapply GlobSim.EntAx_bit_rule in S4 as [];eauto.
      apply tau_star_tau_N_equiv in S5 as [x S5];eapply GlobSim.tau_N_bit_I_preservation in S5;eauto.
      congruence.
    }
    }
  Qed.
  Definition nprace_prog {NL}{L:@langs NL}(sp:prog L):Prop:=
    exists gm ge pc,
      init_config sp gm ge pc pc.(cur_tid) /\
      (
        @np_race_config_0 NL L gm ge sp pc \/
        exists l fp pc' o pce,
          star np_step pc l fp pc' /\ np_race_config_1 o pc' pce
      ).
  Lemma inv_thdp_gettop_valid_tid:
    forall ge pc c,
      ThreadPool.inv pc.(thread_pool) ->
      ThreadPool.get_top pc.(thread_pool) pc.(cur_tid) = Some c->
      @pc_valid_tid ge pc pc.(cur_tid).
  Proof.
    intros until c.
    intros H H_tp_core.
    destruct pc as [thdp t gm bit].
    unfold ThreadPool.valid_tid;split.
    {
      assert(Coqlib.Plt t thdp.(ThreadPool.next_tid) \/ BinPos.Pge t thdp.(ThreadPool.next_tid)).
      apply classic.
      destruct H0;auto.
      inversion H as [tp_finite _ _ _].
      apply tp_finite in H0. simpl in H0.
      clear tp_finite.
      inversion H_tp_core.
      unfold ThreadPool.get_top in H2.
      unfold ThreadPool.get_cs in H2.
      rewrite H0 in H2.
      inversion H2.
    }
    {
      intro.
      inversion H0;subst.
      inversion H_tp_core.
      unfold ThreadPool.get_top in H4.
      simpl in *.
      rewrite H1 in H4.
      inversion H2;subst.
      inversion H4.
    }
  Qed.
  Lemma inv_step_valid_tid:
    forall ge pc fp pc1 o,
      (@np_step ge) pc o fp pc1->
      ThreadPool.inv pc.(thread_pool) ->
      pc_valid_tid pc pc.(cur_tid).
  Proof.
    intros.
    inversion H;subst;eapply inv_thdp_gettop_valid_tid;eauto.
  Qed.

  Lemma tau_star_valid_tid:
    forall ge pc fp pc1,
      ThreadPool.inv pc.(thread_pool) ->
      tau_star (@np_step ge) pc fp pc1 ->
      fp<> FP.emp ->
      pc_valid_tid pc pc.(cur_tid).
  Proof.
    intros.
    inversion H0;subst;try contradiction.
    eapply inv_step_valid_tid;eauto.
  Qed.
  Lemma np_predict_valid_tid:
    forall ge pc id fp1 fp2 ,
      ThreadPool.inv pc.(thread_pool) ->
      @np_predict ge pc id fp1 fp2 ->
      fp2<>FP.emp ->
      pc_valid_tid ({-|pc,id}) id.
  Proof.
    intros.
    inversion H0;subst.
    inversion H2;subst;try contradiction.
    inversion H2;subst.
    inversion H3;subst.
    eapply inv_step_valid_tid;eauto.
    inversion H4;subst;try contradiction.
    inversion H3;subst;eapply inv_step_valid_tid;eauto.
  Qed.    

  Lemma np_predict_half:
    forall ge pc id fp1 fp2,
      @np_predict ge pc id fp1 fp2 ->
      exists pc1,tau_star np_step ({-|pc,id}) fp1 pc1 /\ atom_bit pc1 = O /\ atom_bit ({-|pc,id}) = atom_bit pc1. 
  Proof. intros;inversion H;subst;auto;apply np_normal_iff_tau_star_bitpreservation in H0 as [Eq1[_[_ star1]]];exists pc'; auto. Qed.
    
  Lemma np_race_config_np_race_config_base_equiv:
    forall ge pc,
      ThreadPool.inv (thread_pool pc ) ->
      ( (@np_race_config ge pc) <-> np_race_config_base pc).
  Proof.
    intros ge pc invpc.
    split;intro.
    {
      destruct H.
      inversion H2;clear H2;subst.
      {
        pose proof FP.emp_never_conflict fp10 fp20 H4 as [].
        apply np_predict_half in H0 as [s1[star1[]]];apply np_predict_half in H1 as [s2[star2[]]].
        assert(invs1:ThreadPool.inv ({-|s,t1}).(thread_pool) /\ ThreadPool.inv ({-|s,t2}).(thread_pool)).
        destruct s;simpl in *;auto.
        destruct invs1 as [invs1 invs2].
        pose proof H2 as L;eapply tau_star_valid_tid with(pc:=({-|s,t1})) in L;eauto.
        pose proof H3 as R;eapply tau_star_valid_tid in R;eauto.
        econstructor 1 with(id1:=t1)(id2:=t2);simpl;eauto.
        apply tau_star_tau_N_equiv in star1 as [].
        apply GlobSim.tau_N_bit_backwards_preservation in H7;auto.
      }
      {
        pose proof FP.emp_never_conflict fp11 fp20 H4 as [].
        inversion H0;subst. contradiction.
        apply np_normal_iff_tau_star_bitpreservation in H5.
        apply np_normal_iff_tau_star_bitpreservation in H7.
        destruct H5 as [biteq[_[_ star1]]].
        destruct H7 as [biteq2[bit1[tid1 star2]]].
        apply np_predict_half in H1 as [].
        destruct H1 as [star'[bit2 biteq3]].
        apply np_ent_atom_tau_step_bitchange in H6 as [step1[]].
        econstructor 2;simpl;eauto;try eapply np_predict_valid_tid in H0;eauto.
        eapply tau_star_valid_tid in star';eauto.
      }
      {
        pose proof FP.emp_never_conflict fp10 fp21 H4 as [].
        inversion H1;subst;try contradiction.
        apply np_normal_iff_tau_star_bitpreservation in H5.
        apply np_normal_iff_tau_star_bitpreservation in H7.
        destruct H5 as [biteq[_[_ star1]]].
        destruct H7 as [biteq2[bit1[tid1 star2]]].
        apply np_predict_half in H0 as [].
        destruct H0 as [star'[bit2 biteq3]].
        apply np_ent_atom_tau_step_bitchange in H6 as [step1[]].
        apply FP.conflict_sym in H4.
        econstructor 2 with(id1:=t2);eauto;try eapply np_predict_valid_tid in H1;eauto.
        eapply tau_star_valid_tid in star';eauto.
      }
    }
    {
      intros.
      inversion H.
      {
        destruct pc as [tgp id gm bit]. simpl in *;subst.
        apply tau_star_tau_N_equiv in H4 as [].
        apply tau_star_tau_N_equiv in H6 as [].
        apply tau_N_bitpreservation_np_normal_tau in H4;auto.
        apply tau_N_bitpreservation_np_normal_tau in H3;auto.
        simpl in H3,H4.
        eapply np_predict_only_tau with(i':=id) in H4;eauto.
        eapply np_predict_only_tau with(i':=id) in H3;eauto.
        econstructor;eauto.
        constructor;auto.
      }
      {
        destruct pc as [tgp id gm bit]. simpl in *.
        assert(T:cur_tid pc1 = id1).
        apply GlobSim.tau_star_tid_preservation in H3;auto.
        assert(T2:cur_tid pc1 = cur_tid pc10).
        inversion H6;subst;auto;contradiction.
        apply tau_star_tau_N_equiv in H3 as [].
        apply tau_star_tau_N_equiv in H8 as [].
        apply tau_star_tau_N_equiv in H10 as [].
        apply tau_N_bitpreservation_np_normal_tau in H3;auto.
        apply tau_N_bitpreservation_np_normal_tau in H8;auto.
        apply tau_N_bitpreservation_np_normal_tau in H10;auto.
        simpl in *.
        pose proof H7 as L;eapply GlobSim.EntAx_bit_rule in H7 as [];eauto.
        subst.
        rewrite H7 in *.
        rewrite H13 in *.
        rewrite <-T2 in *.
        rewrite <-H7 in L;rewrite <- H13 in L.
        apply tau_step_bitchange_np_ent_atom in H6;auto.
        eapply np_predict_with_atom with(i':=id) in H3;eauto.
        eapply np_predict_only_tau with(i':=id) in H10;eauto.
        econstructor ;eauto.
        constructor 2;auto.
      }
    }
  Qed.

  Lemma np_star_race_config_np_race_config_1_equiv:
    forall ge pc0,
      GlobEnv.wd ge ->
      ThreadPool.inv (thread_pool pc0 ) ->
     ( exists l fp o pc1 pc, star (@np_step ge) pc0 l fp pc1 /\ np_race_config_1 o pc1 pc) <-> np_star_race_config pc0.      
  Proof.
    intros ge pc0 wd invpc.
    split;intro.
    {
      destruct H as [l[fp[o[pc1[pc2[]]]]]].
      induction H.
      {
        inversion H0.
        destruct H1.
        apply np_race_config_np_race_config_base_equiv in H2.
        econstructor;eauto.
        eapply GlobSim.thp_inv_preservation;eauto.
      }
      {
        apply IHstar in H0.
        econstructor 2;eauto.
        eapply GlobSim.thp_inv_preservation;eauto.
      } 
    }
    {
      induction H.
      {
        assert(fp=FP.emp).
        inversion H;subst;auto;contradiction.
        exists nil,FP.emp,l,s,s';subst.
        split;constructor;auto.
        split;auto.
        apply np_race_config_np_race_config_base_equiv;auto.
        eapply GlobSim.thp_inv_preservation;eauto.
      }
      {
        destruct IHnp_star_race_config as [ls[fp1[o[pc1[pc[]]]]]].
        eapply GlobSim.thp_inv_preservation;eauto.
        exists (cons l ls),(FP.union fp fp1),o,pc1,pc.
        split;try econstructor 2;eauto.
      }      
    }
  Qed.

  Lemma np_race_prog_nprace_prog_equiv:
    forall NL L p,
      @np_race_prog NL L p <-> nprace_prog p.
  Proof.
    split.
    {
      intro.
      destruct H.
      {
        unfold nprace_prog.
        exists gm,ge,s.
        assert(t=cur_tid s ).
        inversion H;auto.
        split;try congruence.
        left.
        unfold np_race_config_0.
        apply np_race_config_np_race_config_base_equiv in H0.
        split;try congruence.
        eapply GlobSim.init_config_inv_thp;eauto.
      }
      {
        unfold nprace_prog.
        exists gm,ge,s.
        assert(t=cur_tid s ).
        inversion H;auto.
        split;try congruence.
        right.
        apply np_star_race_config_np_race_config_1_equiv in H0 as [l[fp[o[pc1[pc2]]]]].
        exists l,fp,pc1,o,pc2;auto.
        inversion H;subst.
        inversion H3;auto.
        eapply GlobSim.init_config_inv_thp;eauto.
      }
    }
    {
      intro.
      unfold nprace_prog in H.
      destruct H as [gm[ge[pc[init[race|[l[fp[pc'[o[pce[]]]]]]]]]]].
      destruct race as [_].
      apply np_race_config_np_race_config_base_equiv in H.
      econstructor;eauto.
      eapply GlobSim.init_config_inv_thp;eauto.

      assert(exists l fp o pc1 pc2,star np_step pc l fp pc1 /\ np_race_config_1 o pc1 pc2).
      exists l,fp,o,pc',pce;auto.
      apply np_star_race_config_np_race_config_1_equiv in H1.
      econstructor 2;eauto.
      inversion init;subst.
      inversion H3;auto.
      eapply GlobSim.init_config_inv_thp;eauto.
    }
  Qed.

  Lemma GUSim_nprace_prog_preservation:
    forall NL L sp tp,
      @GlobUSim NL L sp tp ->
      init_rel sp tp ->
      nprace_prog tp ->
      nprace_prog sp.
  Proof.
    intros.
    unfold nprace_prog in *.
    destruct H1 as [tgm[tge[tpc[init_tpc race_tpc]]]].
    destruct race_tpc as [race_tpc| [l[fpT1[tpc1[o[tpc2[star1 race_tpc2]]]]]]].
    {
      
      eapply GUSim_nprace_preservation_2 in race_tpc as[sgm[sge[spc]]];eauto.
      exists sgm,sge,spc.
      inversion H1;auto.
    }
    {
      pose proof init_tpc as Tmp;eapply H0 in Tmp;eauto.
      destruct Tmp as [mu[sgm[sge[spc[]]]]].
      exists sgm,sge,spc.
      assert(cur_tid spc = cur_tid tpc).
      inversion H2;auto.
      rewrite H3;split;auto.
      right.
      pose proof init_tpc as Tmp;eapply H in Tmp as [I[ord[match_state[i[]]]]];eauto.
      eapply GUSim_star_nprace_preservation_1 in race_tpc2;eauto.
      destruct race_tpc2 as [l2[fpS2[spc1[spc2[]]]]].
      exists l2,fpS2,spc1,o,spc2.
      auto.
      inversion init_tpc.
      inversion H6;auto.
    }
  Qed.


  Lemma GUSim_DRF_preservation:
    forall NL L sp tp,
      @GlobUSim NL L sp tp ->
      init_rel sp tp ->
      npdrf sp ->
      npdrf tp.
  Proof.
    intros.
    unfold npdrf in *.
    intro.
    apply np_race_prog_nprace_prog_equiv in H2.
    eapply GUSim_nprace_prog_preservation in H2;eauto.
    apply np_race_prog_nprace_prog_equiv in H2.
    contradiction.
  Qed.
  