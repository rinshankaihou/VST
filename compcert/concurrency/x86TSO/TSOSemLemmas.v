From mathcomp.ssreflect Require Import fintype ssrnat.    
Require Import Coqlib Maps Axioms LibTactics.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import CUAST.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset.

Require Import Languages.
Require Import GlobSemantics TSOGlobSem RGRels ClientSim ObjectSim.

Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.
Require Import InteractionSemantics.

Require Import FMemLemmas TSOMemLemmas TSOAuxDefs TSOStepAuxLemmas.

Local Transparent Mem.load Mem.alloc Mem.store Mem.free.

Section BUFFER.

  Definition fconflict bi1 bi2:=
    let fp1 := bi_footprint bi1 in
    let fp2 := bi_footprint bi2 in
    match bi1 with
    | BufferedStore chunk b ofs _ => match bi2 with
                              | BufferedAlloc b2 lo hi =>
                                FP.conflict fp1 fp2 /\
                                ~ Locs.subset (FMemOpFP.range_locset b ofs (size_chunk chunk))(FMemOpFP.range_locset b2 lo (hi - lo))
                              | BufferedFree _ _ _ => FP.conflict fp1 fp2
                              | _ => False
                              end
    | BufferedFree b lo hi => FP.conflict fp1 fp2 /\
                           match bi2 with
                           | BufferedAlloc b2 lo2 hi2 =>
                             ~ Locs.subset (FMemOpFP.range_locset b lo (hi - lo))(FMemOpFP.range_locset b2 lo2 (hi2-lo2))
                           | _ => True
                           end
    | BufferedAlloc b lo hi => match bi2 with
                              | BufferedFree b2 lo2 hi2 =>
                                FP.conflict fp1 fp2 /\ ~ Locs.subset (FMemOpFP.range_locset b2 lo2 (hi2-lo2))(FMemOpFP.range_locset b lo (hi-lo))
                            | BufferedStore chunk b2 ofs _ => FP.conflict fp1 fp2 /\ ~ Locs.subset (FMemOpFP.range_locset b2 ofs (size_chunk chunk))(FMemOpFP.range_locset b lo (hi-lo))
                            | _ => False
                            end
    end.

  Lemma fpsmile_nfconflict:
    forall bi1 bi2,
      FP.smile (bi_footprint bi1)(bi_footprint bi2) ->
      ~ fconflict bi1 bi2.
  Proof.
    intros.
    apply FP.smile_conflict_compat in H.
    intro;contradict H.
    unfold fconflict in H0.
    ex_match2;Hsimpl;auto.
  Qed.
  Lemma fpsmile_nfconflict_2:
    forall bi bf,
      FP.smile (bi_footprint bi)(bf_footprint bf) ->
      forall bi',
        In bi' bf ->
        ~ fconflict bi bi'.
  Proof.
    induction bf;intros.
    inv H0.
    inv H0. eapply fpsmile_nfconflict;eauto.
    simpl in H. eapply FPLemmas.fpsmile_union_elim;eauto.
    simpl in H. eapply IHbf;eauto. eapply FPLemmas.fpsmile_union_elim2;eauto.
  Qed.
  Lemma fpsmile_nfconflict_3:
    forall bf1 bf2,
      FP.smile (bf_footprint bf1)(bf_footprint bf2) ->
      forall bi bi',
        In bi bf1 ->
        In bi' bf2 ->
        ~ fconflict bi bi'.
  Proof.
    induction bf1;intros.
    inv H0.
    simpl in *. inv H0.
    eapply fpsmile_nfconflict_2;eauto.
    apply FPLemmas.fpsmile_sym. apply FPLemmas.fpsmile_sym in H.
    eapply FPLemmas.fpsmile_union_elim;eauto.

    eapply IHbf1;eauto.
    apply FPLemmas.fpsmile_sym. apply FPLemmas.fpsmile_sym in H.
    eapply FPLemmas.fpsmile_union_elim2;eauto.
  Qed.
  Lemma fconflict_comm:
    forall bi1 bi2,
      fconflict bi1 bi2 -> fconflict bi2 bi1.
  Proof.
    unfold fconflict;intros;ex_match2;auto.
    all: Hsimpl;Esimpl;auto;try apply FP.conflict_sym;auto.
  Qed.
  Lemma nfconflict_comm:
    forall bi1 bi2,
      ~fconflict bi1 bi2 -> ~fconflict bi2 bi1.
  Proof.
    intros;intro;contradict H. eapply fconflict_comm;eauto.
  Qed.
        
  Lemma apply_buffer_item_fconflict:
    forall bi1 bi2,
      ~ fconflict bi1 bi2 ->
      forall m m1 m2,
        apply_buffer_item bi1 m = Some m1 ->
        apply_buffer_item bi2 m = Some m2 ->
        exists m', apply_buffer_item bi2 m1 = Some m'.
  Proof.
    destruct bi2;intros.
    simpl;unfold alloc;eauto.
    {
      destruct bi1.
      {
        apply Classical_Prop.not_and_or in H.
        destruct H.
        {
          apply FP.smile_conflict_compat in H.
          apply apply_buf_item_MemEffect in H0.
          eapply MemEffect_fpsmile_MemPre_Rule in H0;eauto.
          apply MemPre_comm in H0.
          eapply buf_item_unbuf_locality_1 in H0;eauto.
          Hsimpl;Esimpl;eauto.
        }
        {
          apply Classical_Prop.NNPP in H.
          simpl in *.
          unfold free in *.
          ex_match2;eauto.

          clear Hx0 Hx H1.
          contradict n.
          unfold alloc in H0.
          inv_some.
          unfold range_perm in *.
          simpl.
          intros.
          apply r in H0 as ?;clear r.
          Locs.unfolds.
          assert(z<=ofs<z+(z0-z)). Lia.lia.
          eapply range_locset_belongsto2 with(b:=b) in H2.
          unfold belongsto in H2. Locs.unfolds.
          apply H in H2.
          apply range_locset_belongsto in H2 as [].
          subst.
          rewrite PMap.gss;auto.
          destruct zle,zlt;try Lia.lia;simpl;auto.
          constructor.
        }
      }
      {
        apply Classical_Prop.not_and_or in H.
        destruct H.
        {
          apply FP.smile_conflict_compat in H.
          apply apply_buf_item_MemEffect in H0.
          eapply MemEffect_fpsmile_MemPre_Rule in H0;eauto.
          apply MemPre_comm in H0.
          eapply buf_item_unbuf_locality_1 in H0;eauto.
          Hsimpl;Esimpl;eauto.
        }
        {
          contradiction.
        }
      }
      {
         apply FP.smile_conflict_compat in H.
         apply apply_buf_item_MemEffect in H0.
         eapply MemEffect_fpsmile_MemPre_Rule in H0;eauto.
         apply MemPre_comm in H0.
         eapply buf_item_unbuf_locality_1 in H0;eauto.
         Hsimpl;Esimpl;eauto.
      }
    }
    {
      destruct bi1.
      {
        apply Classical_Prop.not_and_or in H.
        destruct H.
        {
          apply FP.smile_conflict_compat in H.
          apply apply_buf_item_MemEffect in H0.
          eapply MemEffect_fpsmile_MemPre_Rule in H0;eauto.
          apply MemPre_comm in H0.
          eapply buf_item_unbuf_locality_1 in H0;eauto.
          Hsimpl;Esimpl;eauto.
        }
        {
          apply Classical_Prop.NNPP in H.
          simpl in *.
          unfold store in *.
          ex_match2;eauto.

          clear Hx0 Hx H1.
          contradict n.
          destruct v0;split;auto.
          clear H2.
          unfold alloc in H0.
          inv_some.
          unfold range_perm in *.
          simpl.
          intros.
          apply H1 in H0 as ?;clear H1.
          Locs.unfolds.
          assert(z<=ofs<z+size_chunk m). Lia.lia.
          eapply range_locset_belongsto2 with(b:=b) in H1.
          unfold belongsto in H1. Locs.unfolds.
          apply H in H1.
          apply range_locset_belongsto in H1 as [].
          subst.
          rewrite PMap.gss;auto.
          destruct zle,zlt;try Lia.lia;simpl;auto.
          constructor.
        }
      }
      {
        apply Classical_Prop.not_and_or in H as [];try contradiction.
        apply FP.smile_conflict_compat in H.
        apply apply_buf_item_MemEffect in H0.
        eapply MemEffect_fpsmile_MemPre_Rule in H0;eauto.
        apply MemPre_comm in H0.
        eapply buf_item_unbuf_locality_1 in H0;eauto.
        Hsimpl;Esimpl;eauto.
      }
      {
        simpl in *.
        unfold store in*;ex_match2;eauto.
        exfalso.
        clear Hx Hx1 Hx0.
        contradict n.
        clear H1.
        destruct v1,v2. split;auto.
        inv_some.
        unfold range_perm in *;simpl;intros; eauto.
      }
    }
  Qed.

  Lemma bi_bf_nfconflict_1:
    forall bi bf,
      (forall bi', In bi' bf -> ~fconflict bi bi') ->
      forall m m1 m2,
        apply_buffer_item bi m = Some m1 ->
        apply_buffer bf m = Some m2 ->
        exists m',apply_buffer_item bi m2 = Some m'.
  Proof.
    induction bf;intros.
    simpl in H1. inv_some. eauto.
    {
      simpl in *.
      unfold optbind in *.
      ex_match.

      eapply apply_buffer_item_fconflict in H0 as ?;try exact Hx;[|apply nfconflict_comm;eauto].
      Hsimpl.

      eapply IHbf in H1;try exact H2;eauto.
    }
  Qed.
    
  Lemma emp_intersect_locs:

    forall l, Locs.intersect Locs.emp l = Locs.emp.
  Proof.
    intros.
    apply Locs.locs_eq.
    Locs.unfolds. auto with bool.
  Qed.
  Lemma add_minus_eq:
    forall a b,
      b = a + ( b - a).
  Proof.
    intros;Lia.lia.
  Qed.
  Definition bi_eff bi m m':Prop :=
    match bi with
    | BufferedStore chunk b ofs v => GMem.mem_access m = GMem.mem_access m' /\ GMem.validblocks m = GMem.validblocks m' /\ valid_access m chunk b ofs Memperm.Writable
                                    
    | BufferedFree b lo hi =>
      exists locs, Locs.subset locs  (FMemOpFP.range_locset b lo (hi-lo)) /\
              unchanged_perm (notbelongsto locs) m m' /\
              range_perm m b lo hi Memperm.Max Memperm.Freeable
    | BufferedAlloc b lo hi =>
      (forall b0 ofs k p,
        ~ GMem.perm m' b0 ofs k p ->
        GMem.perm m b0 ofs k p ->
        b0 = b /\ (lo > ofs \/ ofs >= hi)) /\
      ( forall b0 ofs k p,
        GMem.perm m' b0 ofs k p ->
        ~ GMem.perm m b0 ofs k p ->
        b0 = b /\ (lo <= ofs  < hi))
    end.
  Lemma bi_eff_applyable:
    forall bi m m',
      bi_eff bi m m' ->
      exists m1, apply_buffer_item bi m = Some m1.
  Proof.
    destruct bi.
    simpl;unfold alloc;eauto.
    simpl. unfold free;intros. Hsimpl. ex_match2. eauto.
    simpl;unfold store;intros;Hsimpl;ex_match2;eauto.
  Qed.
  Lemma bi_bi_eff:
    forall bi m m',
      apply_buffer_item bi m = Some m' ->
      bi_eff bi m m'.
  Proof.
    destruct bi;simpl;intros.
    {
      unfold alloc in H; inv_some; simpl in *.
      unfold GMem.perm in *. simpl in *.
      split;intros; rewrite PMap.gsspec in *;ex_match2.
      contradict H. constructor.

      destruct zle,zlt;auto. inv Hx0.
      destruct zle,zlt;auto; inv Hx0.
    }
    {
      apply free_eff in H as ?;Hsimpl.
      destruct H0.
      Esimpl. apply Locs.subset_refl.
      eauto.
      unfold free in H;ex_match2. auto.
    }
    {
      unfold store in H;ex_match;inv_some. auto.
    }
  Qed.

  Lemma bi_eff_progress:
    forall bi m m' bi' m1,
      bi_eff bi m m'->
      ~fconflict bi' bi ->
      apply_buffer_item bi' m = Some m1 ->
      exists m2,
        apply_buffer_item bi' m' = Some m2 /\
        bi_eff bi m1 m2.
  Proof.
    intros.
    destruct bi,bi'.
    {
      simpl in *.
      unfold alloc in *. inv_some. simpl in *.
      unfold GMem.perm in *. simpl in *.
      Esimpl;eauto;simpl;intros;
        rewrite PMap.gsspec in H1,H2;ex_match2;
          eapply H;eauto.
    }
    {
      simpl in H,H1|-*.
      unfold free in *.
      ex_match2.
      {
        Esimpl;eauto; inv_some;
          unfold unchecked_free,GMem.perm;simpl;intros;
            rewrite PMap.gsspec in *; ex_match2;subst;
              eapply H;eauto.
      }
      {
        clear Hx0 Hx H1.
        exfalso.
        unfold range_perm in *;intros.
        contradict n. intros.
        apply Classical_Prop.NNPP.
        intro.
        apply r in H1 as ?.
        eapply H in H2;eauto.
        Hsimpl. subst.
        contradict H0.
        simpl. unfold FMemOpFP.free_fp,FMemOpFP.uncheck_alloc_fp.
        split.
        eapply FP.conflict_ff;simpl.
        unfold FMemOpFP.range_locset;Locs.unfolds.
        exists b ofs. ex_match2. destruct zle,zlt;auto;try Lia.lia.
        
        unfold FMemOpFP.range_locset.
        Locs.unfolds.
        rewrite <-!add_minus_eq.
        intro.
        specialize (H0 b ofs).
        ex_match2. destruct H4,zle,zlt,zle,zlt;try Lia.lia;simpl in *;exploit H0;auto.
      }
    }
    {
      simpl in H,H1|- *.
      unfold store in *.
      ex_match2.
      {
        inv_some. Hsimpl.
        Esimpl;eauto.
      }
      {
        clear Hx0 Hx H1.
        contradict n.
        destruct v0;split;auto.
        unfold range_perm in *.
        intros. specialize (H1 _ H3).
        apply Classical_Prop.NNPP;intro.
        eapply H in H4 as ?;eauto.
        contradict H0. simpl.
        split. unfold FMemOpFP.store_fp,FMemOpFP.uncheck_alloc_fp.
        apply FP.conflict_wf;simpl.
        rewrite !emp_intersect_locs,!Locs.locs_union_emp.
        Locs.unfolds. unfold FMemOpFP.range_locset.
        exists b ofs. destruct H5;subst. ex_match2.
        destruct zle,zlt;auto;try Lia.lia.

        destruct H5;subst.
        intro. unfold FMemOpFP.range_locset in H0;Locs.unfolds.
        specialize (H0 b ofs).
        ex_match2. destruct zle,zlt,zle,zlt;try Lia.lia;exploit H0;eauto.
      }
    }
    {
      simpl in H1|-*.
      eexists;split.
      unfold alloc in *;eauto.
      simpl in H. Hsimpl.
      exists x. split;auto.
      unfold alloc in H1;inv_some.
      unfold range_perm,GMem.perm;simpl.
      split.
      {
        gmem_unfolds. Hsimpl.
        split;intros.
        eapply H1 in H4. split;intros[];auto;right;apply H4;auto.

        rewrite !PMap.gsspec. ex_match2;try tauto;eauto.
      }
      {
        rewrite PMap.gsspec.
        intros.
        ex_match2. constructor.
        {
          contradict H0.
          split;simpl.
          unfold FMemOpFP.uncheck_alloc_fp,FMemOpFP.free_fp.
          eapply FP.conflict_ff;simpl. Locs.unfolds.
          exists b ofs. unfold FMemOpFP.range_locset;ex_match2;auto.
          rewrite <-add_minus_eq.
          destruct zle,zlt,zle,zlt;try Lia.lia;auto.

          unfold FMemOpFP.range_locset. Locs.unfolds.
          intro.
          specialize (H0 b ofs). subst.
          ex_match2.
          rewrite <-!add_minus_eq in H0.
          destruct zle,zlt,zle,zlt;try Lia.lia;exploit H0;eauto.
        }
        {
          eapply H3;eauto.
        }
      }
    }
    {
      simpl in *.
      unfold free in *;ex_match2.
      {
        inv_some.
        Hsimpl;Esimpl;eauto.
        {
          gmem_unfolds.
          Hsimpl;split;auto.
          intros. rewrite! PMap.gsspec. ex_match2;subst;try tauto;eauto.
        }
        {
          unfold unchecked_free,range_perm in *.
          simpl.
          rewrite PMap.gsspec. ex_match2;eauto. subst.
          intros. apply H2 in H3 as ?.
          ex_match2.
          destruct zle,zlt;try Lia.lia;inv Hx2.

          contradict H0.
          split;auto.
          unfold FMemOpFP.free_fp;apply FP.conflict_ff;simpl;Locs.unfolds.
          exists b0 ofs. apply andb_true_iff;split;auto;unfold FMemOpFP.range_locset;ex_match2;rewrite <- add_minus_eq;destruct zle,zlt;try Lia.lia;auto.
        }
      }
      {
        clear Hx0 H1 Hx. contradict n.
        unfold range_perm in *. intros.
        specialize (r _ H1).
        Hsimpl.
        apply H3;auto.
        unfold notbelongsto.
        destruct x eqn:?;auto.
        contradict H0.
        split;auto.
        apply FP.conflict_ff. unfold FMemOpFP.free_fp;simpl;Locs.unfolds.
        apply H in Heqt.
        do 2 eexists. apply andb_true_iff;split;eauto.
        unfold FMemOpFP.range_locset;ex_match2.
        rewrite <- add_minus_eq.
        destruct zle,zlt;try Lia.lia;auto.
      }
    }
    {
      simpl in *.
      unfold store in *.
      ex_match2.
      {
        inv_some.
        Hsimpl.
        Esimpl;eauto.
      }
      {
        clear Hx0 Hx H1.
        contradict n.
        inv v0;split;auto.
        Hsimpl.
        unfold range_perm.
        intros.
        apply H1 in H5 as ?.
        eapply H3;eauto.
        unfold notbelongsto.
        destruct x eqn:?;auto.
        contradict H0.
        unfold FMemOpFP.store_fp,FMemOpFP.free_fp.
        apply FP.conflict_wf. simpl.
        rewrite !emp_intersect_locs,Locs.locs_union_emp.
        Locs.unfolds. apply H in Heqt.
        do 2 eexists. apply andb_true_iff. split;eauto.
        unfold FMemOpFP.range_locset;ex_match2.
        destruct zle,zlt;try Lia.lia;auto.
      }
    }
    {
      simpl in *. Hsimpl.
      unfold alloc in *.
      inv_some.
      Esimpl;eauto;simpl;try congruence.
      destruct H3;split;auto.
      unfold range_perm;simpl. rewrite H;eauto.
      intros. apply H1 in H4 as ?.
      rewrite PMap.gsspec. ex_match2. constructor.
      subst. contradict H0.
      split. unfold FMemOpFP.uncheck_alloc_fp,FMemOpFP.store_fp;apply FP.conflict_wf;simpl;rewrite !emp_intersect_locs,!Locs.emp_union_locs.
      Locs.unfolds. exists b0 ofs. apply andb_true_iff;split. unfold FMemOpFP.range_locset. ex_match2. clear Hx0. destruct zle,zlt;try Lia.lia;auto. ex_match2.

      unfold FMemOpFP.range_locset. intro.
      Locs.unfolds. specialize (H0 b0 ofs). ex_match2.
      rewrite <- add_minus_eq in H0.
      assert(zle z0 ofs && zlt ofs z1 = true).
      apply H0. clear H0 Hx0. destruct zle,zlt;auto;Lia.lia.
      congruence.
    }
    {
      simpl in *. Hsimpl.
      unfold free in *.
      ex_match2.
      {
        inv_some.
        Esimpl;eauto.
        unfold unchecked_free. simpl. rewrite H. auto.
        destruct H3;split;auto.
        unfold unchecked_free,range_perm;simpl.
        intros.
        apply H1 in H4 as ?.
        rewrite PMap.gsspec;ex_match2;auto.
        subst. contradict H0.
        split;auto.
        apply FP.conflict_wf.
        unfold FMemOpFP.store_fp,FMemOpFP.free_fp,FMemOpFP.range_locset;simpl;rewrite !emp_intersect_locs,!Locs.emp_union_locs. Locs.unfolds.
        exists b0 ofs.
        ex_match2. rewrite <-add_minus_eq,Hx2.
        clear Hx2. destruct zle,zlt;auto;try Lia.lia.
      }
      {
        clear Hx Hx0 H1.
        contradict n.
        unfold range_perm in *.
        rewrite <-H. auto.
      }
    }
    {
      simpl in *. Hsimpl.
      unfold store in *. ex_match2.
      inv_some. Esimpl;eauto.

      clear H1 Hx Hx0. contradict n.
      destruct v1;split;auto.
      unfold range_perm in *;rewrite <- H;auto.
    }
  Qed.
  Lemma bi_eff_progress2:
    forall bi m m' bi' m1 m2,
      bi_eff bi m m'->
      ~fconflict bi' bi ->
      apply_buffer_item bi' m' = Some m1 ->
      apply_buffer_item bi' m = Some m2 ->
      bi_eff bi m2 m1.
  Proof.
    intros.
    eapply bi_eff_progress in H;eauto.
    Hsimpl. rewrite H1 in H;inv_some. congruence.
  Qed.
  Lemma bi_eff_star_progress:
    forall bf bi m m' m1,
      bi_eff bi m m' ->
      (forall bi', In bi' bf -> ~fconflict bi' bi) ->
      apply_buffer bf m = Some m1 ->
      exists m2, apply_buffer bf m' = Some m2 /\
            bi_eff bi m1 m2.
  Proof.
    induction bf;intros;simpl in *.
    inv_some. Esimpl;eauto.

    unfold optbind in *.
    ex_match.

    eapply bi_eff_progress in Hx as ?;eauto;Hsimpl.
    eapply IHbf in H3 as ?;eauto;Hsimpl.
    ex_match3.
    Esimpl;eauto.
  Qed.

  Lemma bi_bf_nfconflict_2:
    forall bi bf,
      (forall bi', In bi' bf -> ~fconflict bi bi') ->
      forall m m1 m2,
        apply_buffer_item bi m = Some m1 ->
        apply_buffer bf m = Some m2 ->
        exists m',apply_buffer bf m1 = Some m'.
  Proof.
    intros.
    apply bi_bi_eff in H0.
    eapply bi_eff_star_progress in H1;eauto.
    Hsimpl;eauto.
    intros;apply nfconflict_comm;eauto.
  Qed.
  Lemma buffer_safe_exchangable_nfconflict:
    forall m bi1 bi2,
      buffer_safe (bi1::bi2::nil) m ->
      buffer_safe (bi2::bi1::nil) m ->
      ~ fconflict bi1 bi2.
  Proof.
    destruct bi1 eqn:?,bi2 eqn:?;simpl;auto;unfold buffer_safe,apply_buffer,optbind;simpl;intros;ex_match2;Hsimpl;repeat inv_some;unfold free,store,alloc in *;ex_match2;repeat inv_some;try clear Hx1 Hx2;intro; unfold range_perm in *;simpl in *;unfold FMemOpFP.uncheck_alloc_fp,FMemOpFP.free_fp,FMemOpFP.store_fp in *.
    {
      destruct H.
      pose proof Locs.locs_emp.
      inv H;simpl in *;try rewrite !emp_intersect_locs,Locs.locs_union_emp in *;try contradiction.
      clear H1.
      Locs.unfolds.
      Hsimpl. ex_match2. subst.
      simpl in H. unfold FMemOpFP.range_locset in H. ex_match2;subst.
      contradict H0.
      intros.

      apply range_locset_belongsto in H0 as [].
      subst.
      rewrite <-add_minus_eq in H1.

      apply r in H1 as ?.
      apply r0 in H1 as ?.
      rewrite PMap.gss in H2.
      ex_match2.
      unfold FMemOpFP.range_locset.
      ex_match2.
      rewrite <- add_minus_eq.
      congruence.
    }
    {
      destruct v0 as [? _], v1 as [? _].
      unfold range_perm in *;simpl in *.
      destruct H.
      pose proof Locs.locs_emp.
      inv H;simpl in *;try rewrite !emp_intersect_locs,!Locs.locs_union_emp,!Locs.emp_union_locs,!Locs.locs_intersect_emp in *;try contradiction.
      Focus 2.
      rewrite !Locs.locs_intersect_emp in *;try contradiction.
      
      Locs.unfolds.
      Hsimpl. simpl in H.
      unfold FMemOpFP.range_locset in H.
      assert( zle z1 x0 && zlt x0 (z1 + size_chunk m0) = true /\ b0 = x /\ b = x).
      ex_match2;subst;auto.
      apply andb_true_iff in H as [];auto.
      apply andb_true_iff in H as [];auto. congruence.
      clear H.
      Hsimpl;subst.
      contradict H2.
      intros.
      
      apply range_locset_belongsto in H2 as [].
      subst.
      apply H0 in H4 as ?.
      apply H1 in H4 as ?.
      rewrite PMap.gsspec in H5.
      ex_match2.
      unfold FMemOpFP.range_locset.
      ex_match2.
      rewrite <- add_minus_eq;congruence.
    }
    {
      destruct H.
      pose proof Locs.locs_emp.
      inv H;simpl in *;try rewrite !emp_intersect_locs,Locs.locs_union_emp in *;try contradiction.
      clear H1.
      Locs.unfolds.
      Hsimpl. ex_match2. subst.
      simpl in H. unfold FMemOpFP.range_locset in H. ex_match2;subst.
      contradict H0.
      intros.

      apply range_locset_belongsto in H0 as [].
      subst.
      rewrite <-add_minus_eq in H1.

      apply r in H1 as ?.
      apply r0 in H1 as ?.
      rewrite PMap.gss in H0.
      ex_match2.
      unfold FMemOpFP.range_locset.
      ex_match2.
      rewrite <- add_minus_eq.
      congruence.
      apply andb_true_iff in H as [];congruence.

    }
    {
      destruct H.
      pose proof Locs.locs_emp.
      inv H;simpl in *;try rewrite !emp_intersect_locs,Locs.locs_union_emp in *;try contradiction.
      clear H1.
      Locs.unfolds.
      Hsimpl. ex_match2. subst.
      simpl in H.
      apply andb_true_iff in H as [].
      apply range_locset_belongsto in H as [];subst.
      apply range_locset_belongsto in H1 as [];subst.
      rewrite <-!add_minus_eq in *.

      exploit r1;eauto.
      exploit r2;eauto.
      exploit r;eauto.
      exploit r0;eauto.
      intros.
      rewrite !PMap.gss in *.
      ex_match2.
      destruct zle,zlt,zle,zlt;auto with bool; Lia.lia.
    }
    {
      clear Hx3 Hx4 Hx5 Hx6.
      destruct v0 as [? _],v1 as [? _].
      destruct H as [? _].
      pose proof Locs.locs_emp.
      inv H;simpl in *;try rewrite !emp_intersect_locs,!Locs.locs_union_emp,!Locs.emp_union_locs,!Locs.locs_intersect_emp in *;try contradiction.
      Focus 2.

      rewrite Locs.locs_intersect_emp in H3. contradiction.

      clear H2.
      rewrite !emp_intersect_locs,Locs.emp_union_locs in H3.
      Locs.unfolds.
      Hsimpl.
      apply andb_true_iff in H as [].
      apply range_locset_belongsto in H as [].
      apply range_locset_belongsto in H2 as [];subst.
      rewrite <- add_minus_eq in H4.
      exploit r0;eauto.
      exploit r;eauto.
      exploit H0;eauto.
      exploit H1;eauto.
      intros;clear r r0 H0 H1.
      
      unfold unchecked_free in H. simpl in H.
      rewrite PMap.gsspec in H. ex_match2.
      destruct zle,zlt;auto with bool;try Lia.lia.
    }
    {
      destruct v0 as [? _],v1 as [? _].
      destruct H as [? R].
      pose proof Locs.locs_emp.
      inv H;simpl in *;try rewrite !emp_intersect_locs,!Locs.locs_union_emp,!Locs.emp_union_locs,!Locs.locs_intersect_emp in *;try contradiction.
      Focus 2.
      rewrite Locs.locs_intersect_emp in H3. contradiction.

      clear H2.
      rewrite !emp_intersect_locs,Locs.locs_union_emp in H3.
      Locs.unfolds.
      Hsimpl.
      apply andb_true_iff in H as [].
      apply range_locset_belongsto in H as []. subst.
      ex_match2;subst.
      exploit H0;eauto.
      exploit H1;eauto;simpl.
      intros.
      rewrite PMap.gss in H4. ex_match2.

      contradict R;intros.
      apply range_locset_belongsto in H5 as [];subst.
      exploit H0;eauto.
      exploit H1;eauto.
      simpl. intros.
      rewrite PMap.gsspec in H7. 
      unfold FMemOpFP.range_locset.
      ex_match2.
      rewrite <- add_minus_eq. auto.
    }
    {
      clear Hx5 Hx4 Hx3 Hx6.
      destruct v0 as [? _ ],v1 as [? _ ].
      pose proof Locs.locs_emp.
      inv H;simpl in *;try rewrite !emp_intersect_locs,!Locs.locs_union_emp,!Locs.emp_union_locs,!Locs.locs_intersect_emp in *;try contradiction.
      Focus 2.
      rewrite Locs.locs_intersect_emp in H3. contradiction.

      rewrite !emp_intersect_locs,Locs.locs_union_emp in H3.
      clear H2.
      Locs.unfolds. Hsimpl. apply andb_true_iff in H as [].
      apply range_locset_belongsto in H as [];subst.
      apply range_locset_belongsto in H2 as [];subst.
      rewrite <- add_minus_eq in H2.
      exploit r;eauto.
      exploit H0;eauto.
      exploit H1;eauto.
      intros;clear r H0 H1.
      unfold unchecked_free in *. simpl in *.
      rewrite PMap.gss in H4. ex_match2.
      destruct zle,zlt;auto with bool;try Lia.lia.
    }
  Qed.
 Lemma unbuffer_safe_apply_buffer':
    forall m,
      unbuffer_safe m->
      forall t bf ls,
        tso_buffers m t = bf++ls ->
        (exists gm, apply_buffer bf (memory m ) = Some gm) /\
        forall gm,
          apply_buffer bf (memory m) = Some gm ->
          unbuffer_safe (tsoupd m t ls gm).
  Proof.
    intros.
    split.
    {
      destruct m;simpl in *.
      eapply unbuffer_safe_apply_buffer in H;eauto.
      rewrite H0 in H. Hsimpl.
      apply apply_buffer_split in H;Hsimpl;eauto.
    }
    {
      destruct m;simpl in *.
      generalize dependent memory.
      generalize dependent tso_buffers.
      generalize dependent t.
      induction bf.
      {
        intros.
        simpl in *. inv_some.
        unfold tsoupd. simpl. rewrite tupdate_same_eq;auto.
      }
      {
        intros.
        simpl in H1. unfold optbind in H1. ex_match.
        inv H. eapply UNBS in Hx as ?;eauto.
        clear UNBS ABIS.
        simpl in *.
        eapply IHbf with(t:=t) in H;eauto.
        unfold tsoupd in *;simpl in *.
        rewrite tupdate_same_tid_eq in H;auto.
        rewrite tupdate_b_get;auto.
      }
    }
  Qed.
  Lemma unbuffer_safe_apply_buffer:
    forall m,
      unbuffer_safe m->
      forall t bf,
        tso_buffers m t = bf ->
        (exists gm, apply_buffer bf (memory m ) = Some gm) /\
        forall gm,
          apply_buffer bf (memory m) = Some gm ->
          unbuffer_safe (tsoupd m t nil gm).
  Proof.
    assert(forall A (bf:list A),bf = bf ++ nil).
    induction bf;auto. simpl.  congruence.
    intros.
    eapply unbuffer_safe_apply_buffer';eauto.
    congruence.
  Qed.
  Lemma unbuffer_safe_nfconflict:
    forall m,
      unbuffer_safe m ->
      forall t bi,
        In bi (tso_buffers m t) ->
        forall t',
          t' <> t ->
          forall bi2,
            In bi2 (tso_buffers m t') ->
            ~ fconflict bi2 bi.
  Proof.
    intros. 
    apply in_split in H0.
    apply in_split in H2.
    Hsimpl.

    eapply unbuffer_safe_apply_buffer' in H0 as ?;eauto.
    Hsimpl.
    specialize (H4 _ H3).
    eapply unbuffer_safe_apply_buffer' with(t:=t') in H4 as ?;eauto.
    Focus 2. simpl. rewrite tupdate_not_eq_get;eauto.
    Hsimpl.
    specialize (H6 _ H5).

    clear H4 H5 H3 H.
    remember (tsoupd (tsoupd m t (bi :: x2) x3) t' (bi2 :: x0) x4) as tm.
    assert(tso_buffers tm t = bi::x2).
    rewrite Heqtm. simpl. rewrite tupdate_not_eq_get,tupdate_b_get;auto.

    assert(tso_buffers tm t' = bi2 :: x0).
    rewrite Heqtm. simpl. rewrite tupdate_b_get;auto.
    clear H0 H2 Heqtm.

    eapply  buffer_safe_exchangable_nfconflict;try instantiate(1:=memory tm);unfold buffer_safe;simpl;unfold optbind.

    inv H6.
    eapply ABIS in H3 as ?;eauto. Hsimpl. ex_match3.
    eapply UNBS in H0;eauto.
    inv H0. simpl in *.
    edestruct ABIS0. instantiate(3:=t). rewrite tupdate_not_eq_get;eauto.
    ex_match3. eauto.

    inv H6.
    eapply ABIS in H as ?;eauto. Hsimpl. ex_match3.
    eapply UNBS in H0;eauto.
    inv H0. simpl in *.
    edestruct ABIS0. instantiate(3:=t'). rewrite tupdate_not_eq_get;eauto.
    ex_match3. eauto.
  Qed.
    

    
  Lemma apply_buffer_split_2:
     forall bi bf m m',
      apply_buffer (bi::bf) m = Some m' ->
      exists m1, apply_buffer_item bi m = Some m1 /\ apply_buffer bf m1 = Some m'.
  Proof.
    intros.
    assert((bi::nil)++bf = bi::bf). auto.
    rewrite <- H0 in H.
    apply apply_buffer_split in H as [?[]].
    unfold apply_buffer,optbind in H;ex_match.
    eauto.
  Qed.
  Lemma buffer_safe_exchangable_nfconflict_2:
    forall m bi1 bi2,
      buffer_safe (bi1::bi2::nil) m ->
      ~ fconflict bi1 bi2->
      buffer_safe (bi2::nil) m ->
      buffer_safe (bi2::bi1::nil) m.
  Proof.
    destruct 1.
    apply apply_buffer_split_2 in H;Hsimpl.
    simpl in H0. unfold optbind in H0;ex_match.
    inv_some.
    
    intros.
    destruct H1.
    simpl in H1. unfold optbind in H1;ex_match. inv_some.
    apply nfconflict_comm in H0.
    eapply apply_buffer_item_fconflict in H as ?;eauto.
    Hsimpl.
    unfold buffer_safe.
    exists x2.
    simpl;unfold optbind. do 2 ex_match3. eauto.
  Qed.

  
  Record mem_sim (R:bool->buffer_item->tid->tsomem->tsomem->Prop):Prop:=
    {
      match_buffer_1:
        forall b bi t m1 m2,
          R b bi t m1 m2 ->
          forall t',
            t' <> t ->
            tso_buffers m1 t' = tso_buffers m2 t';
      match_buffer_2:
        forall b bi t m1 m2,
          R b bi t m1 m2 ->
          b = true ->
          tso_buffers m1 t = tso_buffers m2 t /\
          tso_buffers m1 t = nil;
      match_buffer_3:
        forall b bi t m1 m2,
          R b bi t m1 m2 ->
          b = false->
          (tso_buffers m1 t)++(bi::nil)=tso_buffers m2 t;
      match_apply_buffer_item:
        forall b bi t m1 m2,
          R b bi t m1 m2 ->
          forall t',
            t <> t'->
            forall bi' ls,
              tso_buffers m1 t' = bi'::ls ->
              forall m1',
                apply_buffer_item bi' (memory m1) = Some m1' ->
                exists m2', apply_buffer_item bi' (memory m2) = Some m2' /\
                       R b bi t(tsoupd m1 t' ls m1')(tsoupd m2 t' ls m2');
      match_apply_buffer_item_2:
        forall b bi t m1 m2,
          R b bi t m1 m2->
          b = false->
          tso_buffers m1 t = nil ->
          exists m2', apply_buffer_item bi (memory m2) = Some m2' /\
                 R true bi t m1 (tsoupd m2 t nil m2');
      match_apply_buffer_item_3:
        forall b bi t m1 m2,
          R b bi t m1 m2 ->
          b = false ->
          forall bi2 ls,
            tso_buffers m1 t = bi2::ls ->
            forall m1',
              apply_buffer_item bi2 (memory m1) = Some m1' ->
              exists m2', apply_buffer_item bi2 (memory m2) = Some m2' /\
                     R false bi t(tsoupd m1 t ls m1')(tsoupd m2 t (ls++(bi::nil)) m2')
    }.

  Lemma unbuffer_safe_preserve:
    forall m ,
      unbuffer_safe m ->
      forall m' b bi t (R:bool->buffer_item->tid->tsomem->tsomem->Prop) (Rel:R b bi t m m')
        (SIM:mem_sim R),
    unbuffer_safe m'.
  Proof.
    induction 1;intros.
    econstructor.
    {
      intros.
      destruct  (peq t0 t).
      {
        destruct b.
        subst. exploit match_buffer_2;eauto;intros[].
        congruence.
        subst. exploit match_buffer_3;eauto;intro.
        rewrite <- H1 in *.
        destruct (tso_buffers tso t) eqn:?.
        {
          simpl in *.
          exploit match_apply_buffer_item_2;eauto.
          intro. Hsimpl. inv H0;eauto.
        }
        {
          simpl in *.
          inv H0.
          eapply ABIS in Heqb as ?;eauto.
          Hsimpl.
          exploit match_apply_buffer_item_3;eauto.
          intro. Hsimpl;eauto.
        }
      }
      {
        exploit match_buffer_1;eauto. intro.
        rewrite <-H1 in *.
        apply ABIS in H0 as ?. Hsimpl.
        exploit match_apply_buffer_item;eauto.
        intros;Hsimpl;eauto.
      }
    }
    {
      intros.
      destruct (peq t t0).
      {
        subst. destruct b.
        {
          exploit match_buffer_2;eauto;intros[].
          congruence.
        }
        {
          exploit match_buffer_3;eauto;intro.
          rewrite <- H2 in *.
          destruct (tso_buffers tso t0) eqn:?.
          {
            simpl in *.
            exploit match_apply_buffer_item_2;eauto.
            intros. Hsimpl.
            constructor;simpl;intros.
            {
              
              unfold tupdate in H5. ex_match2.
              exploit match_buffer_1;eauto.
              intro. simpl in H6.  rewrite tupdate_not_eq_get in H6;eauto.
              exploit ABIS;eauto. rewrite H6. simpl;eauto.
              intro.  Hsimpl.
              inv H0.
              exploit match_apply_buffer_item;try exact H4;eauto.
              rewrite H6;eauto.
              intro. Hsimpl. simpl in *.
              rewrite H1 in H3;inv_some.
              Esimpl;eauto.
            }
            {
              unfold tupdate in H5. ex_match2. clear Hx.
              inv H0.
              exploit match_buffer_1;eauto;intro.
              simpl in H0;unfold tupdate in H0;ex_match2.
              rewrite <- H0 in *.
              exploit ABIS;eauto;intro;Hsimpl.
              exploit match_apply_buffer_item;eauto;intro;Hsimpl.
              simpl in *.
              rewrite H3 in H1;inv_some.

              exploit H. exact H5. eauto. eauto. eauto.
              intro.
              rewrite H6 in H8;inv_some.
              auto.
            }
          }
          {
            simpl in *. inv H0.
            exploit ABIS;eauto;intros;Hsimpl.
            exploit match_apply_buffer_item_3;eauto;intro;Hsimpl.
            rewrite H1 in H3;inv_some.
            econstructor;simpl;intros.
            {
              unfold tupdate in H3;ex_match2;subst.
              {
                destruct b1 eqn:?.
                {
                  simpl in *. inv H3.
                  exploit match_apply_buffer_item_2;eauto.
                  simpl. rewrite tupdate_b_get;auto.
                  intro;Hsimpl.
                  Esimpl;eauto.
                }
                {
                  simpl in *;inv H3.
                  exploit H;eauto.
                  intro.
                  inv H3.
                  simpl in ABIS0.
                  eapply ABIS0;eauto.
                  rewrite tupdate_b_get;eauto.
                }
              }
              {
                exploit UNBS;try exact H1;eauto;intro.
                exploit match_buffer_1;eauto;intro;Hsimpl.

                inv H5. simpl in *.
                exploit ABIS0.  rewrite H6.
                unfold tupdate;ex_match2;eauto.
                intro;Hsimpl.
                
                exploit match_apply_buffer_item;eauto.
                simpl.
                rewrite H6. unfold tupdate;ex_match2;eauto.
                intro;Hsimpl;eauto.
              }
            }
            {
              unfold tupdate in H3;ex_match2;subst.
              {
                destruct b1 eqn:?.
                {
                  simpl in *. inv H3.
                  exploit match_apply_buffer_item_2;eauto.
                  simpl. rewrite tupdate_b_get;auto.
                  intro;Hsimpl.
                  simpl in H3.
                  rewrite H3 in H5;inv_some.
                  eapply H;eauto.
                }
                {
                  simpl in *;inv H3.
                  exploit H;eauto.
                  intro.
                  inv H3.
                  eapply UNBS0;eauto.
                  simpl. unfold tupdate. ex_match2;eauto.
                }
              }
              {
                eapply H in H4 as ?;eauto.
                unfold tsoupd in H6.
                inv H6.
                eapply UNBS0;eauto.
                simpl. unfold tupdate. ex_match2.
              }
            }
          }
        }
      }
      {
        inv H0.
        exploit match_buffer_1;eauto;intro;Hsimpl.
        rewrite <- H0 in *.
        exploit ABIS;eauto;intro;Hsimpl.
        exploit match_apply_buffer_item;eauto;intro;Hsimpl.
        rewrite H1 in H4;inv_some.
        eapply H;eauto.
      }
    }
  Qed.
    
  Definition inv_bi bi t m :=
    forall t',
      t' <> t ->
      forall bi',
        In bi' (tso_buffers m t') ->
        ~ fconflict bi bi'.

  Inductive match_mem :bool->buffer_item->tid->tsomem->tsomem->Prop:=
  | bi_exists:
      forall m bi t,
        unbuffer_safe m ->
        inv_bi bi t m ->
        buffer_safe ((tso_buffers m t)++(bi::nil)) (memory m)->
        match_mem false bi t m (tsoupd m t ((tso_buffers m t)++(bi::nil)) (memory m))
  | bi_use:
      forall m bi t m' m'',
        match_mem false bi t m m'->
        tso_buffers m' t = bi::nil ->
        apply_buffer_item bi (memory m') = Some m''->
        match_mem true bi t m (tsoupd m' t nil m'')
  | matched_progress:
      forall b m bi t m',
        match_mem b bi t m m' ->
        forall t' bi2 ls m1 m2,
          t' <> t ->
          tso_buffers m t' = bi2::ls ->
          apply_buffer_item bi2 (memory m) = Some m1->
          apply_buffer_item bi2 (memory m') = Some m2 ->
          match_mem b bi t (tsoupd m t' ls m1)(tsoupd m' t' ls m2)
  | matched_progress2:
      forall b m bi bi2 ls t m' m1 m2,
        match_mem b bi t m m' ->
        b = false ->
        tso_buffers m t = bi2::ls ->
        apply_buffer_item bi2 (memory m) = Some m1->
        apply_buffer_item bi2 (memory m') = Some m2 ->
        match_mem b bi t (tsoupd m t ls m1)(tsoupd m' t (ls++(bi::nil)) m2).
  Lemma match_mem_match_buffer1:
    forall b bi t m1 m2,
        match_mem b bi t m1 m2 ->
        forall t',
          t' <> t ->
          tso_buffers m1 t' = tso_buffers m2 t'.
  Proof.
    induction 1;intros.
    simpl. rewrite tupdate_not_eq_get;auto.
    simpl. rewrite tupdate_not_eq_get;auto.
    simpl. unfold tupdate;ex_match2;auto.
    simpl. rewrite! tupdate_not_eq_get;auto.
  Qed.
  Lemma match_mem_match_buffer3:       
   forall b bi t m1 m2,
     match_mem b bi t m1 m2 ->
     b = false->
     (tso_buffers m1 t)++(bi::nil)=tso_buffers m2 t.
 Proof.
   induction 1;intros.
   simpl. rewrite tupdate_b_get. auto.
   congruence.
   specialize (IHmatch_mem H4).
   simpl. rewrite! tupdate_not_eq_get;auto.
   simpl. rewrite!tupdate_b_get;auto.
 Qed.
 Lemma match_mem_match_buffer2:
   forall b bi t m1 m2,
     match_mem b bi t m1 m2 ->
     b = true ->
     tso_buffers m1 t = tso_buffers m2 t /\
     tso_buffers m1 t = nil.
 Proof.
   induction 1;intros.
   congruence.
   apply match_mem_match_buffer3 in H;auto.
   rewrite H0 in H.
   destruct (tso_buffers m t)eqn:?.
   split;auto. simpl. rewrite tupdate_b_get;auto.
   inv H. apply app_eq_nil in H5 as [];subst.
   symmetry in H3. contradict H3.
   apply nil_cons.

   specialize (IHmatch_mem H4) as [].
   simpl. rewrite ! tupdate_not_eq_get;auto.
   congruence.
 Qed.
 Lemma match_mem_false_memeq:
   forall bi b t m1 m2,
     match_mem b bi t m1 m2 ->
     b = false ->
     memory m1 = memory m2.
 Proof.
   induction 1;intros;eauto.
   congruence.
   simpl. rewrite IHmatch_mem in H2;auto. rewrite H2 in H3;inv_some;auto.
   simpl. apply IHmatch_mem in H4. rewrite H4 in H2. rewrite H2 in H3;inv_some;auto.
 Qed.
 Lemma match_mem_inv_bi:
   forall bi b t m1 m2,
     match_mem b bi t m1 m2 ->
     inv_bi bi t m1.
 Proof.
   induction 1;intros;auto.
   {
     unfold inv_bi in *.
     simpl;intros.
     unfold tupdate in H5;ex_match2;eauto.
     eapply IHmatch_mem;eauto. subst. rewrite H1;right;eauto.
   }
   {
     unfold inv_bi in *.
     simpl;intros.
     unfold tupdate in H5;ex_match2.
     eapply IHmatch_mem;eauto.
   }
 Qed.
 Lemma match_mem_unbuffer_safe_1:
   forall bi b t m1 m2,
     match_mem b bi t m1 m2 ->
     unbuffer_safe m1.
 Proof.
   induction 1;intros;auto.
   {
     inv IHmatch_mem.
     eapply UNBS;eauto.
   }
   {
     inv IHmatch_mem.
     eapply UNBS;eauto.
   }
 Qed.
 Lemma match_mem_true_buffers_t_nil:
   forall bi b t m1 m2,
     match_mem b bi t m1 m2 ->
     b = true ->
     tso_buffers m1 t= nil /\ tso_buffers m2 t= nil.
 Proof.
   induction 1;intros;auto.
   congruence.
   eapply match_mem_match_buffer3 in H;eauto.
   rewrite H0 in H.
   assert(tso_buffers m t = nil). destruct (tso_buffers m t);auto.
   simpl in H. inv H.
   apply app_eq_nil in H5 as [].
   symmetry in H3. contradict H3.
   apply nil_cons. split;auto.
   simpl. rewrite tupdate_b_get;auto.

   apply IHmatch_mem in H4 as ?;Hsimpl.
   simpl. rewrite! tupdate_not_eq_get;auto.

   simpl in *. apply IHmatch_mem in H4. Hsimpl.
   congruence.
 Qed.

 Lemma in_app_or:
   forall (A : Type) (l m : list A) (a : A),In a (l++m) -> In a l \/ In a m.
 Proof.
   induction l;intros.
   auto.
   simpl in *. destruct H;auto.
   apply IHl in H as [];auto.
 Qed.
 Lemma match_mem_buffer_safe_1:
   forall bi b t m1 m2,
     match_mem b bi t m1 m2 ->
     buffer_safe (tso_buffers m2 t) (memory m1).
 Proof.
   induction 1;intros.
   simpl. rewrite tupdate_b_get;auto.
   simpl. rewrite tupdate_b_get. eexists;simpl;eauto.
   simpl. rewrite tupdate_not_eq_get;auto.
   destruct b.
   {
     apply match_mem_true_buffers_t_nil in H as ?;auto.
     Hsimpl.
     rewrite H5. eexists;split;auto.
   }
   apply match_mem_false_memeq in H as ?;auto.
   rewrite H4 in *. rewrite H2 in H3;inv_some.
   apply match_mem_inv_bi in H as ?.
   rewrite <- H4 in *.
   apply match_mem_unbuffer_safe_1 in H as ?.
   apply match_mem_match_buffer3 in H as ?;auto.
   rewrite <- H6 in *.

   destruct IHmatch_mem.
   eapply bi_bf_nfconflict_2 in H2;eauto.
   apply match_mem_inv_bi in H.
   unfold inv_bi in H.
   specialize (H t' H0).
   intros.

   apply in_app_or in H8.
   destruct H8.
   {
     eapply unbuffer_safe_nfconflict;eauto.
     rewrite H1. left;auto.
   }
   simpl in H8. destruct H8;try contradiction. subst.
   apply nfconflict_comm. apply H. rewrite H1;left;auto.

   simpl. rewrite tupdate_b_get.   subst.
   apply match_mem_match_buffer3 in H as ?;auto.
   rewrite H1 in H0. simpl in *.
   rewrite <-H0 in IHmatch_mem.
   destruct IHmatch_mem. apply apply_buffer_split_2 in H4.
   Hsimpl. rewrite H2 in H4. inv_some.
   eexists;eauto.
 Qed.   
 Lemma match_mem_match_apply_buffer_item1_false:
   forall b bi t m1 m2,
     match_mem b bi t m1 m2 ->
     b = false ->
     forall t' : tid,
       t <> t' ->
       forall (bi' : buffer_item) (ls : list buffer_item),
         tso_buffers m1 t' = bi' :: ls ->
         forall m1' : gmem,
           apply_buffer_item bi' (memory m1) = Some m1' ->
           exists m2',
             apply_buffer_item bi' (memory m2) = Some m2' /\
             match_mem b bi t (tsoupd m1 t' ls m1') (tsoupd m2 t' ls m2').
 Proof.
   induction 1;simpl;intros.
   {
     Esimpl;eauto.
     econstructor;eauto.
     econstructor;eauto.
   }
   congruence.
   {
     subst.
     apply match_mem_false_memeq in H as ?;auto. rewrite H4 in *.
     rewrite H2 in H3;inv_some.
     unfold tupdate in H6. ex_match2;subst.
     {
       exploit IHmatch_mem;eauto.
       intro;Hsimpl.
       rewrite H2 in H3;inv_some.
       Esimpl;eauto.
       econstructor;eauto.
       simpl. rewrite tupdate_b_get. auto.
     }
     {
       Esimpl;eauto. econstructor;eauto.
       econstructor;eauto.
       congruence.
       simpl. rewrite tupdate_not_eq_get;auto.
     }
   }
   {
     apply match_mem_false_memeq in H as ?;auto. rewrite H8 in *.
     rewrite H2 in H3. inv_some.
     unfold tupdate in H6;ex_match2.
     Esimpl;eauto. econstructor;eauto. econstructor;eauto.
     congruence.
     simpl. rewrite tupdate_not_eq_get;auto.
   }
 Qed.

 Lemma match_mem_true_bi_eff:
   forall b bi t m1 m2,
     match_mem b bi t m1 m2 ->
     b = true ->
     bi_eff bi (memory m1)(memory m2).
 Proof.
   induction 1;intros.
   congruence.
   apply bi_bi_eff in H1. simpl.
   apply match_mem_false_memeq in H;auto. congruence.

   specialize (IHmatch_mem H4).
   
   eapply bi_eff_progress in IHmatch_mem as ?;eauto.
   Hsimpl. rewrite H3 in H5. inv_some. simpl. auto.

   eapply match_mem_inv_bi in H.
   unfold inv_bi in H.
   apply nfconflict_comm.
   eapply H;eauto.
   rewrite H1. left;auto.

   congruence.
 Qed.
 Lemma match_mem_match_apply_buffer_item1_true:
   forall b bi t m1 m2,
     match_mem b bi t m1 m2 ->
     b = true ->
     forall t' : tid,
       t <> t' ->
       forall (bi' : buffer_item) (ls : list buffer_item),
         tso_buffers m1 t' = bi' :: ls ->
         forall m1' : gmem,
           apply_buffer_item bi' (memory m1) = Some m1' ->
           exists m2',
             apply_buffer_item bi' (memory m2) = Some m2' /\
             match_mem b bi t (tsoupd m1 t' ls m1') (tsoupd m2 t' ls m2').
 Proof.
   intros.
   subst.
   apply match_mem_true_bi_eff in H as ?;auto.
   eapply bi_eff_progress in H0 as ?;eauto.
   Hsimpl. Esimpl;eauto. econstructor;eauto.
   apply match_mem_inv_bi in H. unfold inv_bi in H.
   apply nfconflict_comm. eapply H;eauto.
   rewrite H2;left;auto.
 Qed.

 Lemma match_mem_sim:
   mem_sim match_mem.
 Proof.
   constructor.
   apply match_mem_match_buffer1.
   apply match_mem_match_buffer2.
   apply match_mem_match_buffer3.
   {
     destruct b;intros.
     eapply match_mem_match_apply_buffer_item1_true;eauto.
     eapply match_mem_match_apply_buffer_item1_false;eauto.
   }
   {
     intros.
     subst.
     apply match_mem_buffer_safe_1 in H as ?.
     apply match_mem_match_buffer3 in H as ?;auto.
     rewrite H1 in H2. simpl in H2.
     rewrite <- H2 in H0. destruct H0.
     simpl in H0. unfold optbind in H0. ex_match. inv_some.
     apply match_mem_false_memeq in H as ?;auto.
     rewrite <- H0 in *.
     Esimpl;eauto. econstructor 2;eauto. congruence.
   }
   {
     intros. subst.
     apply match_mem_false_memeq in H as ?;auto.
     rewrite <- H0 in *.
     Esimpl;eauto.

     econstructor 4;eauto.
     congruence.
   }
 Qed.

 Lemma unbuffer_safe_append_preserve:
   forall m,
     unbuffer_safe m ->
     forall t bi,
       buffer_safe (tso_buffers m t++bi::nil) (memory m) ->
       inv_bi bi t m ->
       unbuffer_safe (tsoupd m t (tso_buffers m t ++ bi::nil) (memory m)).
 Proof.
   intros. pose proof match_mem_sim.
   eapply unbuffer_safe_preserve with(R:=match_mem);eauto.
   econstructor 1;eauto.
 Qed.

 Lemma unbuffer_safe_append_bf_preserve:
   forall bf t m,
     unbuffer_safe m ->
     buffer_safe (tso_buffers m t ++ bf) (memory m) ->
     (forall bi, In bi bf -> inv_bi bi t m) ->
     unbuffer_safe (tsoupd m t (tso_buffers m t++bf) (memory m)).
 Proof.
   induction bf;intros.
   rewrite app_nil_r.
   unfold tsoupd. rewrite tupdate_same_eq;auto. destruct m;auto.

   pose proof H0 as R.
   destruct H0.
   apply apply_buffer_split in H0;Hsimpl.
   apply apply_buffer_split_2 in H2;Hsimpl.

   assert(buffer_safe ((tso_buffers m t)++(a::nil))(memory m)).
   eexists. erewrite apply_buffer_app_eq;eauto. simpl. unfold optbind. rewrite H2. eauto.
   eapply unbuffer_safe_append_preserve in H4;eauto.
   Focus 2. eapply H1;eauto. left;auto.

   assert(R2:tso_buffers m t ++ a::bf = (tso_buffers m t ++ a::nil)++bf).
   clear. generalize dependent (tso_buffers m t).
   revert bf a. induction b. auto.
   simpl. congruence.
   remember (tsoupd m t (tso_buffers m t ++ a::nil)(memory m)) as m'.
   eapply IHbf with(t:=t) in H4;eauto.
   rewrite Heqm' in H4;simpl in H4.
   unfold tsoupd in H4. simpl in H4.
   unfold tsoupd.
   rewrite tupdate_same_tid_eq,tupdate_b_get in H4.
   congruence.
   rewrite Heqm'. simpl.
   rewrite tupdate_b_get.  congruence.

   unfold inv_bi in *;intros.
   rewrite Heqm' in H7. simpl in H7.
   rewrite tupdate_not_eq_get in H7;eauto.
   eapply H1;eauto. right;auto.
 Qed.

 Lemma unbuffer_safe_globstep_preserve:
   forall tge pc l fp pc',
     @tso_globstep tge pc l fp pc'->
     unbuffer_safe (tm pc)->
     unbuffer_safe (tm pc').
 Proof.
   inversion 1;subst;auto.
   inversion 1;subst.
   unfold unbuffer in H_unbuf;ex_match;inv_some.
   simpl in *.
   eapply UNBS in Hx0;eauto.
 Qed.

 Lemma non_conflict_access_unbuffer_safe':
  forall tm ge fl tc t fp tc' b' m' m'',
    unbuffer_safe tm ->
    tsostep ge fl tc (tso_buffers tm t, memory tm) fp tc' (b', m') ->
    apply_buffer b' m' = Some m'' ->
    ~ conflictc t fp (tso_buffers tm) ->
    unbuffer_safe (tsoupd tm t b' m').
 Proof.
   intros.
   apply TSO_eff in H0 as EFF1.
   destruct EFF1.
   destruct (eff_chg (tso_buffers tm t) b') eqn:?.
   apply eff_chg_t in Heqb as [];subst.
   unfold tsoupd. rewrite tupdate_same_eq;auto.
   eapply unbuffer_safe_mem_access_same_stable with(m1:=memory tm);eauto.
   destruct tm;auto.
   eapply TSO_step_access_validity_preserve in H0;Hsimpl;auto.

   apply eff_chg_f in Heqb. clear bf_chg. unfold BufferEff in bf_eff. Hsimpl.
   subst.
   
   eapply unbuffer_safe_append_bf_preserve;eauto.
   eexists;eauto.

   revert H4 H2. clear.

   unfold inv_bi;intros.
   apply fpsmile_nfconflict.   
   apply FP.smile_conflict_compat;intro.
   assert(FP.conflict fp (bi_footprint bi')).
   assert(forall bi bf, In bi bf -> FP.subset (bi_footprint bi)(bf_footprint bf)).
   {
     clear;induction bf;intros;inv H;auto.
     simpl. apply FP.union_subset. Hsimpl.
     simpl. rewrite FP.union_comm_eq.  apply FP.subset_union_subset;auto.
   }
   specialize (H5 _ _ H).
   apply USimDRF.smile_conflict.
   apply USimDRF.smile_conflict in H3.
   intro. contradict H3.
   apply FPLemmas.fpsmile_sym.
   eapply FPLemmas.fpsmile_subset;eauto.
   apply FPLemmas.fpsmile_sym.
   eapply fpsmile_eff_eq_trans;eauto.
   destruct H4;split;auto.
   apply bf_footprint_reads_emp.
   apply bf_footprint_cmps_emp.

   clear H3.
   contradict H2.
   econstructor;eauto.
 Qed.   
End BUFFER.
(*
Ltac unfold_unchanged_perm :=
  unfolds unchanged_perm;
  unfolds unchanged_validity; unfolds GMem.eq_perm;
  unfolds GMem.valid_block; unfolds GMem.perm.

Ltac unfold_belongsto :=
  unfolds belongsto; unfolds Locs.belongsto.

Ltac unfold_effects :=
  unfolds effects; do 4 unfolds Locs.union. 

Lemma buf_item_unbuf_locality_1 :
  forall bi m m',
    unbuf_locality_1 bi m m'.
Proof.
  intros.
  unfolds unbuf_locality_1; intros.
  destruct bi; simpls.
  
  (** alloc *)
  {
    unfolds alloc.
    inv H.
    eexists; split; eauto.
    unfold MemPost, unchanged_content; simpls.
    split.
    {
      inv H0.
      unfold_unchanged_perm; simpls.
      unfolds FMemOpFP.uncheck_alloc_fp.
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
      unfolds GMem.perm; simpls.
      intros.
      unfold_belongsto.
      unfold_effects; simpls.
      ex_match2; subst.
      rewrite PMap.gss in H1; eauto.
      ex_match2; tryfalse.
      do 2 rewrite PMap.gss; eauto.
    }
  }
  (** free *)
  {
    unfolds free.
    inv H0. 
    ex_match2; inv H.
    {
      eexists; split; eauto.
      unfold MemPost, unchanged_content, unchecked_free; simpls.
      unfold_belongsto; unfold_effects; simpls.
      unfolds FMemOpFP.range_locset.
      split.
      {
        unfold_unchanged_perm; simpls.
        split; intros.
        ex_match2; subst.
        unfolds range_perm.
        rewrite Zplus_minus in H.
        destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse.
        assert (z <= ofs < z0); eauto.
        split; intros.
        { 
          clear - r0 H H0.
          eapply r0 in H0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m0))); eauto.
          eapply GMem.invalid_noaccess with (ofs := ofs) (k := Memperm.Max) in H1.
          unfolds Mem.perm_order'.
          rewrite H1 in H0; simpls; tryfalse.
        }
        {
          clear - r H H0.
          eapply r in H0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m))); eauto.
          eapply GMem.invalid_noaccess with (ofs := ofs) (k := Memperm.Max) in H1.
          unfolds Mem.perm_order'.
          rewrite H1 in H0; simpls; tryfalse.
        }
        
        ex_match2; subst.
        rewrite Zplus_minus in H.
        do 2 rewrite PMap.gss; eauto. 
        destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse.
        split; intro; tryfalse.
      }
      {
        intros.
        unfolds GMem.perm; simpls.
        ex_match2; subst.
        rewrite PMap.gss in H0; simpls.
        rewrite Zplus_minus in H.
        destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse.
      }
    }
    {
      contradiction n; clear - r EffectPermEqPre.
      unfolds range_perm; intros.
      lets Hrange : H.
      eapply r in H.
      specialize (EffectPermEqPre b ofs).
      unfold_belongsto.
      unfold_effects; simpls.
      assert (FMemOpFP.range_locset b z (z0 - z) b ofs = true).
      {
        unfold FMemOpFP.range_locset.
        ex_match2; subst; rewrite Zplus_minus.
        destruct (zle z ofs); destruct (zlt ofs z0); simpls;
          tryfalse; try Lia.lia; eauto.
      }
      {
        clear - H0 H EffectPermEqPre.
        unfolds Mem.perm_order'.
        unfolds GMem.perm.
        ex_match2; tryfalse.
        eapply EffectPermEqPre in H0; clear EffectPermEqPre.
        unfolds Memperm.perm_order'.
        rewrite Hx in H0.
        rewrite Hx0 in H0.
        eapply H0 in H; eauto.
        eapply EffectPermEqPre in H0; clear EffectPermEqPre.
        unfolds Memperm.perm_order'.
        rewrite Hx in H0; rewrite Hx0 in H0.
        eapply H0; eauto.
      }
    }
  }
  (** store *)
  {
    inv H0.
    unfolds store.
    ex_match2.
    {
      eexists; split; eauto.
      inv H; simpls.
      unfold MemPost, unchanged_content; simpls.
      split.
      {
        unfold_unchanged_perm; simpls.
        split; intros; eauto.
        unfold_belongsto.
        unfold_effects.
        unfolds FMemOpFP.store_fp; simpls.
        unfolds FMemOpFP.range_locset.
        ex_match2; subst.
        unfolds Locs.emp; simpls.
        destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m1));
          simpls; tryfalse.
        split; intros; eauto.
        { 
          clear - v1 l l0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m0))); eauto.
          unfolds valid_access, range_perm.
          destruct v1.
          assert (z <= ofs < z + size_chunk m1); eauto.
          eapply H0 in H2.
          unfolds Mem.perm_order'.
          eapply GMem.invalid_noaccess in H.
          rewrite H in H2; simpls; tryfalse.
        }
        { 
          clear - v0 l l0.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks m))); eauto.
          unfolds valid_access, range_perm.
          destruct v0.
          assert (z <= ofs < z + size_chunk m1); eauto.
          eapply H0 in H2.
          eapply GMem.invalid_noaccess in H.
          unfolds Mem.perm_order'.
          rewrite H in H2; simpls; tryfalse.
        }
      }
      {
        intros.
        unfolds GMem.perm; simpls.
        unfold_belongsto.
        unfold_effects; simpls.
        unfolds FMemOpFP.range_locset.
        ex_match2; subst.
        destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m1));
          simpls; tryfalse.
        assert (z <= ofs < z + size_chunk m1); eauto.
        do 2 rewrite PMap.gss; eauto.
        eapply setN_geteq2; eauto.
        rewrite encode_val_length.
        rewrite <- size_chunk_conv; eauto.
      }
    }
    {
      inv H. 
      contradiction n; clear - v0 EffectPermEqPre.
      unfolds valid_access, range_perm; simpls.
      destruct v0.
      split; eauto.
      intros.
      lets Hrange : H1.
      eapply H in H1.
      specialize (EffectPermEqPre b ofs).
      unfold_belongsto.
      unfold_effects; simpls.
      unfolds FMemOpFP.range_locset.
      ex_match2; subst.
      destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m1));
        tryfalse; try Lia.lia; simpls.
      assert (true = true); eauto.
      eapply EffectPermEqPre in H2.
      unfolds GMem.perm.
      eapply H2; eauto.
    }
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
Qed.*)
Lemma fmem_eq :
  forall m1 m2,
    Mem.mem_contents m1 = Mem.mem_contents m2 ->
    Mem.mem_access m1 = Mem.mem_access m2 ->
    Mem.validblocks m1 = Mem.validblocks m2 ->
    Mem.freelist m1 = Mem.freelist m2 ->
    Mem.nextblockid m1 = Mem.nextblockid m2 ->
    m1 = m2.
Proof.
  destruct m1,m2;simpl.
  intros. subst.
  rewrite proof_irr with(a1:=valid_wd)(a2:=valid_wd0).
  rewrite proof_irr with(a1:=access_max)(a2:=access_max0).
  rewrite proof_irr with(a1:=contents_default)(a2:=contents_default0).
  rewrite proof_irr with(a1:=invalid_noaccess)(a2:=invalid_noaccess0).
  rewrite proof_irr with(a1:=freelist_wd)(a2:=freelist_wd0).
  auto.
Qed.

Lemma getblock_always_success :
  forall n fl,
  exists b, MemAux.get_block fl n = b.
Proof.
  induction n; intros; simpls; eauto.
Qed.
  
(** * Reordering Lemmas *)
Section Reordering.
  
  Variable TGE: TSOGlobEnv.t.

  Definition normal_tsoglabel (l: tsoglabel) : Prop :=
    match l with
    | tau | evt _ => True
    | _ => False
    end.
  
  Inductive ub_star (t: tid) : @TSOProgConfig TGE -> @TSOProgConfig TGE -> Prop :=
  | ub_star_refl: forall tpc, ub_star t tpc tpc
  | ub_star_cons: forall tpc tpc' tpc'',
      tso_globstep tpc (ub t) FP.emp tpc' ->
      ub_star t tpc' tpc'' ->
      ub_star t tpc tpc''.

  (** equivalence between configurations *)
  Record eq_config (tpc1 tpc2: @TSOProgConfig TGE) : Prop :=
    {
      eq_thrdpool: thrdpool tpc1 = thrdpool tpc2;
      eq_cid: cid tpc1 = cid tpc2;
      eq_m: GMem.eq (memory (tm tpc1)) (memory (tm tpc2));
      eq_buffer: tso_buffers (tm tpc1) = tso_buffers (tm tpc2);
    }.

  Lemma eq_config_refl: forall tpc, eq_config tpc tpc.
  Proof. constructor; auto. apply GMem.eq_refl. Qed.
  
  Lemma eq_config_trans: forall tpc1 tpc2 tpc3, eq_config tpc1 tpc2 -> eq_config tpc2 tpc3 -> eq_config tpc1 tpc3.
  Proof. intros. inv H; inv H0. econstructor; eauto using GMem.eq_trans; congruence. Qed.
  
  Lemma eq_config_sym: forall tpc1 tpc2, eq_config tpc1 tpc2 -> eq_config tpc2 tpc1.
  Proof. intros. inv H. constructor; auto using GMem.eq_sym. Qed.

  (** equivalence between configurations but current tid *)
  Record eq_config_but_cid (tpc1 tpc2: @TSOProgConfig TGE) : Prop :=
    {
      eq_thrdpool': thrdpool tpc1 = thrdpool tpc2;
      eq_m': GMem.eq (memory (tm tpc1)) (memory (tm tpc2));
      eq_buffer': tso_buffers (tm tpc1) = tso_buffers (tm tpc2);
    }.
  
  Lemma eq_config_but_cid_refl: forall tpc, eq_config_but_cid tpc tpc.
  Proof. constructor; auto. apply GMem.eq_refl. Qed.
  
  Lemma eq_config_but_cid_trans:
    forall tpc1 tpc2 tpc3,
      eq_config_but_cid tpc1 tpc2 ->
      eq_config_but_cid tpc2 tpc3 ->
      eq_config_but_cid tpc1 tpc3.
  Proof. intros. inv H; inv H0. econstructor; eauto using GMem.eq_trans; congruence. Qed.
  
  Lemma eq_config_but_cid_sym:
    forall tpc1 tpc2, eq_config_but_cid tpc1 tpc2 -> eq_config_but_cid tpc2 tpc1.
  Proof. intros. inv H. constructor; auto using GMem.eq_sym. Qed.

  (** eq_config_but_cid could switch to eq_config *)
  Lemma eq_config_eq_config_but_cid:
    forall tpc tpc',
      eq_config tpc tpc' ->
      eq_config_but_cid tpc tpc'.
  Proof. clear; intros; inv H; constructor; auto. Qed.

  Lemma eq_config_eq_step:
    forall (tpc1 tpc2: @TSOProgConfig TGE) l fp tpc1',
      eq_config tpc1 tpc2 ->
      tso_globstep tpc1 l fp tpc1' ->
      exists tpc2', tso_globstep tpc2 l fp tpc2' /\ eq_config tpc1' tpc2'.
  Proof. 
    intros. inv H. destruct tpc1, tpc2. simpl in *. subst.
    inv H0.
    (* core step *)
    exploit gmem_buffer_eq_corestep_eq. eauto. eauto.
    intros (gm2' & Hcorestep & Heq).
    eexists. split. eapply TSOGlobSem.Corestep; eauto.
    rewrite <- eq_buffer0. eauto.
    unfold tsoupd in *. rewrite <- eq_buffer0. eapply gmem_eq_ub_safe_eq; eauto.
    econstructor; eauto. simpl. rewrite <- eq_buffer0; auto.
    (* ub step *)
    destruct tm, tm'.
    exploit gmem_eq_ub_gmem_eq; eauto. intros (gm2' & Hub & Heq).
    eexists; split. eapply TSOGlobSem.Unbuffer; eauto.
    destruct tm0. simpl in *. rewrite <- eq_buffer0. eauto.
    econstructor; eauto.
    (* call *)
    eexists. split. eapply TSOGlobSem.Call; eauto. econstructor; eauto.
    (* return *)
    eexists. split. eapply TSOGlobSem.Return; eauto. econstructor; eauto.
    (* halt *)
    eexists. split. eapply TSOGlobSem.Halt; eauto. econstructor; eauto.
    (* print *)
    eexists. split. eapply TSOGlobSem.EF_Print; eauto. econstructor; eauto.
    (* sw *)
    eexists. split. eapply TSOGlobSem.Switch; eauto. econstructor; eauto.
  Qed.
  
  Lemma merge_sw_steps:
    forall (tpc tpc' tpc'': @TSOProgConfig TGE),
      tso_globstep tpc sw FP.emp tpc' ->
      tso_globstep tpc' sw FP.emp tpc'' ->
      tso_globstep tpc sw FP.emp tpc''.
  Proof. intros. inv H. inv H0. constructor; auto. Qed.
  
  Lemma unbuffer_sw_step_reorder:
    forall (tpc tpc' tpc'': @TSOProgConfig TGE) t,
      tso_globstep tpc sw FP.emp tpc' ->
      tso_globstep tpc' (ub t) FP.emp tpc'' ->
      exists tpc0,
        tso_globstep tpc (ub t) FP.emp tpc0 /\
        tso_globstep tpc0 sw FP.emp tpc''.
  Proof.
    intros.
    inv H; inv H0.
    eexists; split.
    eapply TSOGlobSem.Unbuffer; eauto.
    eapply TSOGlobSem.Switch; eauto.
  Qed.
  
  Lemma same_thrd_normal_unbuffer_step_reorder:
    forall (tpc tpc' tpc'': @TSOProgConfig TGE) l fp,
      FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc) ->
      let t := cid tpc in
      tso_buffers (tm tpc) t <> nil ->
      normal_tsoglabel l ->
      tso_globstep tpc l fp tpc' ->
      tso_globstep tpc' (ub t) FP.emp tpc'' ->
      exists tpc0,
        tso_globstep tpc (ub t) FP.emp tpc0 /\
        tso_globstep tpc0 l fp tpc''.
  Proof.
    introv Hfls_embed; intros; subst. 
    inv H1; inv H2; simpls; tryfalse; subst t.
    (** Corestep *)
    { 
      lets Hbuf' : H_core_step.
      eapply tso_step_buf_add in Hbuf'; eauto.
      lets Hgm' : H_core_step.
      eapply tso_step_buf_not_empty_gm_stable in Hgm'; eauto; subst.
      destruct Hbuf' as [buf'' Hbuf']; subst.
      lets H_unbuf_safe' : H_unbuf_safe.
      eapply unbuffer_safe_addition_original_still in H_unbuf_safe'; eauto.
      lets H_unbuf' : H_unbuf.
      eapply unbuffer_upd_original_still in H_unbuf'; eauto.
      destruct H_unbuf' as [tm'' [H_unbuf' [Hmem Hbuf]]].
      eexists; split.
      econstructor; eauto. 
      eapply thrdpool_tupdate_valid_original_valid; eauto.
      eapply TSOGlobSem.Corestep; eauto.
      eapply tsostep_unbuffer_still; eauto.
      clear - Hmem Hbuf.
      destruct tm', tm''; simpls; subst.
      unfold tsoupd; simpls; eauto. 
      eapply unbuffer_safe_unbuffer_still with
      (tm := tsoupd tm t0 (tso_buffers tm t0 ++ buf'') (memory tm)); eauto.
    }
    (** Call *)
    {
      eexists.
      split.
      econstructor; eauto.
      eapply thrdpool_push_valid_original_valid; eauto.
      eapply TSOGlobSem.Call; eauto.
    }
    (** Return *)
    {
      eexists.
      split.
      econstructor; eauto.
      eapply thrdpool_pop_valid_original_valid; eauto.
      eapply thrdpool_tupdate_valid_original_valid; eauto.
      eapply TSOGlobSem.Return; eauto.
    }
    (** Halt *)
    {
      eexists.
      split.
      econstructor; eauto.
      eapply thrdpool_pop_valid_original_valid; eauto.
      eapply TSOGlobSem.Halt; eauto.
    }
    (** Print *)
    {
      eexists.
      split.
      econstructor; eauto.
      eapply thrdpool_tupdate_valid_original_valid; eauto.
      eapply TSOGlobSem.EF_Print; eauto.
    }
  Qed.


End Reordering.




(** * Prog config eq on individual thread *)
Definition eq_thrdp_tm TGE t
           (tpc: @TSOProgConfig TGE) tpc' : Prop :=
  (TSOThrdPool.next_tid (thrdpool tpc) = TSOThrdPool.next_tid (thrdpool tpc'))
  /\
  (TSOThrdPool.next_fmap (thrdpool tpc) t = TSOThrdPool.next_fmap (thrdpool tpc') t)
  /\
  (TSOThrdPool.content (thrdpool tpc)) !! t = (TSOThrdPool.content (thrdpool tpc')) !! t
  /\
  memory (tm tpc) = memory (tm tpc')
  /\
  tso_buffers (tm tpc) t = tso_buffers (tm tpc') t.

Lemma eq_thrdp_tm_refl:
  forall TGE t tpc, eq_thrdp_tm TGE t tpc tpc.
Proof. clear. unfold eq_thrdp_tm. intuition. Qed.

Lemma eq_thrdp_tm_sym:
  forall TGE t tpc tpc',
    eq_thrdp_tm TGE t tpc tpc' ->
    eq_thrdp_tm TGE t tpc' tpc.
Proof. clear. unfold eq_thrdp_tm. intuition. Qed.  

Lemma eq_thrdp_tm_trans:
  forall TGE t tpc1 tpc2 tpc3,
    eq_thrdp_tm TGE t tpc1 tpc2 ->
    eq_thrdp_tm TGE t tpc2 tpc3 ->
    eq_thrdp_tm TGE t tpc1 tpc3.
Proof. clear. unfold eq_thrdp_tm. firstorder; congruence. Qed.

Lemma eq_thrdp_tm_tau_step_sim:
  forall TGE tpc0 fp _tpc0 tpc1,
    cid tpc0 = cid _tpc0 ->
    (forall t', t' <> cid tpc0 ->
           (exists bis, tso_buffers (tm tpc0) t' = tso_buffers (tm _tpc0) t' ++ bis)) ->
    eq_thrdp_tm TGE (cid tpc0) tpc0 _tpc0 ->
    tso_globstep tpc0 tau fp tpc1 ->
    exists _tpc1, tso_globstep _tpc0 tau fp _tpc1 /\
             (forall t, eq_thrdp_tm TGE t tpc0 _tpc0 ->
                   eq_thrdp_tm TGE t tpc1 _tpc1).
Proof.  
  clear. unfold eq_thrdp_tm; firstorder.
  inv H1; destruct _tpc0; simpls; subst; simpls.
  inv H2; simpls. 
  (** Corestep *)
  eexists. split. econstructor; eauto.
  rewrite <- H4; eauto.
  rewrite <- H6, <- H5; eauto.
  econstructor; eauto.
  rewrite <- H4; eauto.
  clear - H0 H_unbuf_safe.
  eapply unbuffer_safe_addition_multi_thread_original_still; eauto.
  {
    intros.
    unfold tsoupd; simpls.
    unfold tupdate.
    ex_match2; subst; eauto.
    eexists nil. rewrite app_nil_r; eauto.
  }  
  simpl; intros.
  destruct H as (Hnxt_tid_eq & Hnxt_map_eq & Hcontent_eq & Hmem_eq & Ht_buf_eq).
  inv H_tp_upd; subst; simpls.
  repeat (split; eauto).
  destruct (peq t t0); subst; eauto.
  do 2 (rewrite PMap.gss; eauto).
  rewrite H_tp_core in H.
  inv H; eauto.
  do 2 (rewrite PMap.gso; eauto).
  unfold tupdate.
  ex_match2; subst; eauto.
  (** At external *)
  eexists.
  split.
  eapply TSOGlobSem.Call; eauto.
  rewrite <- H4; eauto.
  unfolds TSOThrdPool.push; simpls.
  rewrite H_tp_core in H_tp_push; simpls.
  inv H_tp_push; simpls.
  rewrite <- H4, H_tp_core; eauto.
  intros; simpls.
  destruct H as (Hnxt_tid_eq & Hnxt_map_eq & Hcontent_eq & Hmem_eq & Ht_buf_eq).
  unfolds TSOThrdPool.push.
  rewrite H_tp_core in H_tp_push; inv H_tp_push; simpls.
  repeat (split; eauto).
  ex_match2; subst; simpls; eauto.
  destruct (peq t t0); simpls; subst.
  do 2 (rewrite PMap.gss; eauto).
  rewrite Hnxt_map_eq; eauto.
  do 2 (rewrite PMap.gso; eauto).
  (** Return *) 
  eexists.
  split.
  eapply TSOGlobSem.Return.
  rewrite <- H4; eauto.
  eauto. 
  unfolds TSOThrdPool.pop. 
  rewrite H_tp_core in H_tp_pop.
  inv H_tp_pop. 
  rewrite <- H4, H_tp_core; simpl; eauto.
  eauto. eauto.
  unfolds TSOThrdPool.pop.
  rewrite H_tp_core in H_tp_pop; simpls.
  inv H_tp_pop; inv H_tp_upd.
  econstructor; simpls; eauto.
  rewrite PMap.gss; eauto.
  intros; simpls.
  destruct H as (Hnxt_tid_eq & Hnxt_map_eq & Hcontent_eq & Hmem_eq & Ht_buf_eq).
  unfolds TSOThrdPool.pop.
  rewrite H_tp_core in H_tp_pop.
  inv H_tp_pop; inv H_tp_upd; simpls.
  repeat (split; eauto).
  rewrite PMap.gss in H; simpls; inv H.
  do 2 rewrite PMap.set2.
  destruct (peq t t0); subst.
  do 2 rewrite PMap.gss; eauto.
  do 2 (try rewrite PMap.gso; eauto).
  (** Halt *)
  eexists.
  split.
  eapply TSOGlobSem.Halt; eauto.
  rewrite <- H4; eauto.
  unfolds TSOThrdPool.pop.
  rewrite H_tp_core in H_tp_pop.
  rewrite <- H4, H_tp_core.
  inv H_tp_pop; eauto.
  intros; simpls.
  destruct H as (Hnxt_tid_eq & Hnxt_map_eq & Hcontent_eq & Hmem_eq & Ht_buf_eq).
  unfolds TSOThrdPool.pop.
  rewrite H_tp_core in H_tp_pop.
  inv H_tp_pop; simpls.
  repeat (split; eauto).
  destruct (peq t t0); subst; eauto.
  do 2 (rewrite PMap.gss; eauto).
  do 2 (try rewrite PMap.gso; eauto).
Qed.

Lemma eq_thrdp_tm_ub_step_sim:
  forall TGE tpc tpc' t _tpc,
    tso_globstep tpc (ub t) FP.emp tpc' ->
    eq_thrdp_tm TGE t tpc _tpc ->
    exists _tpc',
      tso_globstep _tpc (ub t) FP.emp _tpc' /\
      (forall t', eq_thrdp_tm TGE t' tpc _tpc ->
             eq_thrdp_tm TGE t' tpc' _tpc').
Proof.
  intros.
  inv H; inv H0; simpls.
  destruct _tpc; simpls.
  destruct H1 as (Hnxt_map_eq & Hcontent_eq & Hmem_eq & Ht_buf_eq).
  unfolds unbuffer.
  ex_match2; simpls; tryfalse; simpls.
  inv H_unbuf; simpls.
  eexists.
  split.
  econstructor; eauto.
  unfolds TSOThrdPool.valid_tid.
  rewrite <- H; eauto.
  unfold unbuffer.
  rewrite <- Ht_buf_eq.
  rewrite <- Hmem_eq, Hx0.
  eauto.
  intros.
  unfolds eq_thrdp_tm; simpls.
  destruct H0 as
      (Hnxt_tid_eq' & Hnxt_map_eq' & Hcontent_eq' & Hmem_eq' & Ht_buf_eq').
  repeat (split; eauto).
  unfold tupdate.
  ex_match2; subst; eauto.
Qed.

Lemma eq_thrdp_tm_print_step_sim:
  forall TGE tpc0 v _tpc0 tpc1,
    cid tpc0 = cid _tpc0 ->
    eq_thrdp_tm TGE (cid tpc0) tpc0 _tpc0 ->
    tso_globstep tpc0 (evt v) FP.emp tpc1 ->
    exists _tpc1, tso_globstep _tpc0 (evt v) FP.emp _tpc1 /\
             (forall t, eq_thrdp_tm TGE t tpc0 _tpc0 ->
                   eq_thrdp_tm TGE t tpc1 _tpc1).
Proof.
  intros.
  inv H0; inv H1; simpls; subst; simpls.
  destruct H3 as (Hnxt_map_eq & Hcontent_eq & Hmem_eq & Ht_buf_eq).
  destruct _tpc0; simpls.
  inv H_tp_upd; simpls.
  eexists.
  split.  
  eapply TSOGlobSem.EF_Print; eauto.
  rewrite <- Hcontent_eq; eauto.
  econstructor; eauto.
  rewrite <- Hcontent_eq; eauto.
  rewrite H_tp_core in H.
  inv H; simpls.
  intros.
  unfolds eq_thrdp_tm; simpls.
  destruct H as
      (Hnxt_tid_eq' & Hnxt_map_eq' & Hcontent_eq' & Hmem_eq' & Ht_buf_eq').
  repeat (split; eauto).
  destruct (peq cid t); subst; eauto.
  do 2 rewrite PMap.gss; eauto.
  do 2 (try rewrite PMap.gso; eauto).
Qed.
  
Definition thrd_valid {TGE: TSOGlobEnv.t} (tpc: @TSOProgConfig TGE) (t: tid) : Prop :=
    TSOThrdPool.valid_tid (thrdpool tpc) t.
  
Definition thrd_not_halted {TGE: TSOGlobEnv.t} (tpc: @TSOProgConfig TGE) (t: tid) : Prop :=
  ~ TSOThrdPool.halted (thrdpool tpc) t.

Definition switchable {TGE: TSOGlobEnv.t} (tpc: @TSOProgConfig TGE) (t: tid) : Prop :=
  thrd_valid tpc t /\ thrd_not_halted tpc t.

Lemma eq_thrdp_tm_valid:
  forall TGE t tpc tpc',
    eq_thrdp_tm TGE t tpc tpc' ->
    thrd_valid tpc t ->
    thrd_valid tpc' t.
Proof.
  clear. unfold thrd_valid. intros. inv H. congruence.
Qed.

Lemma eq_thrdp_tm_halted:
  forall TGE t tpc tpc',
    eq_thrdp_tm TGE t tpc tpc' ->
    thrd_not_halted tpc t ->
    thrd_not_halted tpc' t.
Proof.
  clear. unfold thrd_not_halted. intros TGE t tpc tpc' H A C; apply A; clear A.
  destruct H. intuition. inv C; constructor. congruence.
Qed.
  
Lemma eq_thrdp_tm_sw_step_sim:
  forall TGE tpc0 fp _tpc0 tpc1,
    cid tpc0 = cid _tpc0 ->
    (forall t, switchable tpc0 t -> switchable _tpc0 t) ->
    tso_globstep tpc0 sw fp tpc1 ->
    exists _tpc1,
      cid tpc1 = cid _tpc1 /\
      tso_globstep _tpc0 sw fp _tpc1 /\
      (forall t, eq_thrdp_tm TGE t tpc0 _tpc0 -> eq_thrdp_tm TGE t tpc1 _tpc1).
Proof. 
  intros.
  inv H1; simpls; subst; simpls.
  destruct _tpc0; simpls.
  unfolds switchable; simpls.
  unfolds thrd_valid, thrd_not_halted; simpls.
  assert (TSOThrdPool.valid_tid thdp t' /\ ~ TSOThrdPool.halted thdp t').
  eauto.
  eapply H0 in H.
  destruct H.
  eexists.
  split.
  Focus 2.
  split.
  econstructor; eauto.
  intros.
  inv H2; simpls.
  destruct H4 as (Hnxt_map_eq' & Hcontent_eq' & Hmem_eq' & Ht_buf_eq').
  econstructor; simpls; eauto.
  eauto.
Qed.

Lemma buffer_insert_cid_label:
  forall TGE tpc0 tpc1 l0 fp0 t0 bis,
    @tso_globstep TGE tpc0 l0 fp0 tpc1 ->
    tso_buffers (tm tpc1) t0 = tso_buffers (tm tpc0) t0 ++ bis ->
    bis <> nil ->
    t0 = cid tpc0 /\ l0 = tau.
Proof.
  Ltac bis_nil :=
    match goal with
    | H : ?A = ?A ++ ?B |- _ =>
      eapply append_ls_still_nil in H;
      subst; simpls
    end.
  
  intros. inv H; simpls; eauto;
            try solve [bis_nil; tryfalse].
  split; eauto.
  unfolds tupdate.
  ex_match2; eauto.
  bis_nil; tryfalse.

  unfolds unbuffer.
  ex_match2; simpls.
  inv H_unbuf; simpls.
  unfolds tupdate.
  ex_match2; subst; eauto.
  assert (length (tso_buffers tm t') = length (b :: tso_buffers tm t' ++ bis)).
  rewrite <- Hx; eauto.
  simpls.
  rewrite app_length in H.
  Lia.lia.
  assert (length (tso_buffers tm t0) = length (tso_buffers tm t0 ++ bis)).
  rewrite <- H0; eauto.
  rewrite app_length in H.
  destruct bis; simpls; tryfalse.
  Lia.lia.
Qed.

Lemma subset_intersect_full_intersect :
  forall fp fp' fp0 b ofs,
    Locs.subset fp' fp0 ->
    Locs.intersect fp fp' b ofs = true ->
    Locs.intersect fp fp0 b ofs = true.
Proof.
  intros.
  unfolds Locs.subset, Locs.intersect.
  specialize (H b ofs).
  unfolds Locs.belongsto.
  destruct (fp b ofs) eqn:?; destruct (fp' b ofs) eqn:?; simpls; tryfalse.
  eauto.
Qed.

Lemma fp_subset_conflict_full_conflict :
  forall fp fp' fp0,
    FP.conflict fp fp' ->
    FP.subset fp' fp0 ->
    FP.conflict fp fp0.
Proof.
  intros.
  eapply USimDRF.smile_conflict in H.
  eapply USimDRF.smile_conflict.
  intro.
  contradiction H.
  eapply FPLemmas.fpsmile_subset; eauto.
Qed.

Lemma conflict_bi_subset_fp_conflict :
  forall bi fp fp0,
    conflict_bi fp bi ->
    FP.subset (bi_footprint bi) fp0 ->
    FP.conflict fp0 fp.
Proof.
  intros.
  unfolds conflict_bi.
  eapply FP.conflict_sym.
  eapply fp_subset_conflict_full_conflict; eauto.
Qed.

Lemma exec_store_TSO_bf_additional_subst_fp :
  forall ge rs bm rs' bm' bis bi c a rd ls,
    exec_store_TSO ge c bm a rs rd ls = Next rs' bm' ->
    tbuffer bm' = tbuffer bm ++ bis ->
    In bi bis ->
    FP.subset (bi_footprint bi) (exec_store_fp ge c a rs).
Proof.
  intros.
  unfolds exec_store_TSO, tsostorev, tsostore.
  ex_match2.
  inv Hx; inv_next.
  unfolds buffer_insert; simpls.
  eapply app_inv_head in H0; subst.
  simpls.
  destruct H1; subst; tryfalse.
  unfold exec_store_fp, FMemOpFP.storev_fp.
  rewrite Hx0.
  simpls.
  eapply FP.subset_refl; eauto.
Qed.
  
Lemma exec_instr_TSO_bf_additional_subst_fp :
  forall ge f i rs bm rs' bm' bis bi,
    exec_instr_TSO ge f i rs bm = Next rs' bm' ->
    tbuffer bm' = tbuffer bm ++ bis -> In bi bis ->
    FP.subset (bi_footprint bi) (exec_instr_TSO_fp ge f i rs bm).
Proof.
  intros.
  destruct i; simpls; ex_match2; try inv_next;
    try solve [eapply append_ls_still_nil in H0; simpls; subst; simpls; tryfalse];
    try solve [unfolds exec_load_TSO, tsoloadv; ex_match2; try inv_next;
               eapply append_ls_still_nil in H0; simpls; subst; tryfalse];
    try solve [eapply exec_store_TSO_bf_additional_subst_fp; eauto];
    try solve [unfolds tso_goto_label; ex_match2; inv_next;
               eapply append_ls_still_nil in H0; simpls; subst; simpls; tryfalse].
  unfolds tsoloadv, tsoload; ex_match2; simpls.
  eapply app_inv_head in H0; subst; simpls.
  destruct H1; subst; tryfalse.
  simpls.
  rewrite FP.union_comm_eq.
  eapply FP.union_subset; eauto.
Qed.

Lemma store_args_rec_fmem_apply_buf_subst :
  forall args bm bm' stk tys z,
    store_args_rec_fmem bm (Vptr stk (Ptrofs.repr 0)) z args tys = Some bm' ->
    exists bis, tbuffer bm' = tbuffer bm ++ bis /\
           (forall bi, In bi bis ->
                  FP.subset (bi_footprint bi)
                            (loadframe.store_args_rec_fp stk z tys)).
Proof.
  induction args; intros.
  {
    simpls.
    destruct tys; simpls; tryfalse.
    inv H.
    eexists nil.
    rewrite app_nil_r; eauto.
    split; eauto.
    intros; simpls; tryfalse.
  }
  { 
    simpls.
    destruct tys; simpls; tryfalse.
    destruct t; simpls;
      try eapply IHargs in H; unfolds buffer_insert; simpls;
        try solve [destruct H as (bis & Htbuf & Hbi_subset_fp);
                   rewrite app_assoc_reverse in Htbuf; simpls;
                   rewrite Htbuf;
                   eexists; split; eauto;
                   intros; simpls;
                   destruct H; subst; simpls; eauto;
                   [unfold loadframe.store_stack_fp; simpls;
                    unfold Ptrofs.zero;
                    eapply FP.union_subset; eauto;
                    eapply Hbi_subset_fp in H | 
                    rewrite FP.union_comm_eq;
                    eapply FP.subset_union_subset; eauto]].
    {
      ex_match2; simpls; subst; simpls.
      eapply IHargs in H; eauto; simpls.
      destruct H as (bis & Htbuf & Hbi_subset_fp).
      repeat (rewrite app_assoc_reverse in Htbuf); simpls.
      rewrite Htbuf.
      eexists.
      split; eauto.
      intros; simpls.
      destruct H; subst; simpls.
      rewrite <- GDefLemmas.fp_union_comm.
      unfold loadframe.store_stack_fp; simpls.
      rewrite FP.union_comm_eq.
      rewrite <- GDefLemmas.fp_union_comm.
      eapply FP.union_subset; eauto.
      destruct H; subst; simpls.
      rewrite <- GDefLemmas.fp_union_comm.
      unfolds loadframe.store_stack_fp.
      eapply FP.union_subset; eauto.
      eapply Hbi_subset_fp in H.
      rewrite FP.union_comm_eq.
      eapply FP.subset_union_subset; eauto.
    }
  }
Qed.

Lemma tsofstep_bf_addition_subst_fp :
  forall ge c bm c' bm' fp bi bis,
    tsofstep ge c bm fp c' bm' ->
    tbuffer bm' = tbuffer bm ++ bis ->
    In bi bis ->
    FP.subset (bi_footprint bi) fp.
Proof.
  intros. 
  inv H;
    try solve [eapply append_ls_still_nil in H0; simpls; subst; tryfalse].
  (** internal step *)
  {
    eapply exec_instr_TSO_bf_additional_subst_fp; eauto.
  }
  (** alloc step *)
  {
    inv H5.
    unfolds tsostorev, tsostore, buffer_insert.
    ex_match2; simpls.
    inv H7; inv H8; simpls.
    repeat (rewrite app_assoc_reverse in H0); simpls.
    eapply app_inv_head in H0; subst.
    clear - H1.
    simpls.
    destruct H1; subst; simpls.
    eapply FP.union_subset.
    destruct H; subst; simpls.
    rewrite FP.union_comm_eq.
    rewrite <- FP.fp_union_assoc.
    eapply FP.union_subset.
    destruct H; tryfalse; subst; simpls.
    rewrite FP.fp_union_assoc.
    rewrite FP.union_comm_eq.
    eapply FP.union_subset.
  }
  (** initialization *)
  {
    inv H3; simpls.
    unfolds store_args_fmem.
    unfold loadframe.store_args_fp.
    eapply store_args_rec_fmem_apply_buf_subst in H5; simpls.
    destruct H5 as [bis' [Hbuf Hsubset]].
    rewrite Hbuf in H0.
    rewrite app_assoc_reverse in H0.
    eapply app_inv_head in H0; subst.
    simpl in H1.
    destruct H1; subst; simpl.
    {
      unfold tsoalloc_fp.
      eapply FP.union_subset.
    }
    {
      rewrite FP.union_comm_eq.
      eapply FP.subset_union_subset.
      eapply Hsubset; eauto.
    }
  }
Qed.

Lemma bis_subst_fp :
  forall TGE tpc0 tpc1 l fp bi bis,
    @tso_globstep TGE tpc0 l fp tpc1 ->
    let t0 := cid tpc0 in
    tso_buffers (tm tpc1) t0 = tso_buffers (tm tpc0) t0 ++ bis ->
    In bi bis ->
    FP.subset (bi_footprint bi) fp.
Proof.
  intros. 
  inv H; simpls; subst t0;
    try solve [eapply append_ls_still_nil in H0; subst; tryfalse].
  (** Core Step *)
  {
    inv H_core_step; simpls.
    inv H6.
    rewrite tupdate_b_get in H0.
    eapply tsofstep_bf_addition_subst_fp; eauto.
  }
  (** Unbuffer *)
  {
    unfolds unbuffer.
    ex_match2.
    inv H_unbuf; simpls.
    unfolds tupdate.
    ex_match2; subst.
    assert (length (tso_buffers tm t') = length (b :: tso_buffers tm t' ++ bis)).
    rewrite <- Hx; eauto.
    simpls.
    rewrite app_length in H; Lia.lia.
    eapply append_ls_still_nil in H0; subst.
    simpls; tryfalse.
  }
Qed.
 
Lemma conflict_bi_conflict_fp:
  forall TGE tpc0 tpc1 l0 fp0 bi bis fp,
    @tso_globstep TGE tpc0 l0 fp0 tpc1 ->
    let t0 := cid tpc0 in
    tso_buffers (tm tpc1) t0 = tso_buffers (tm tpc0) t0 ++ bis ->
    In bi bis ->
    conflict_bi fp bi ->
    FP.conflict fp0 fp.
Proof.
  intros; subst t0.
  lets Hfp_subst : H.
  eapply bis_subst_fp in Hfp_subst; eauto.
  eapply conflict_bi_subset_fp_conflict; eauto.
Qed.

Lemma less_buffer_item_not_unbuffered_ub_sim:
  forall TGE tpc tpc' t head bi tail head' _tpc _tail,
    memory (tm tpc) = memory (tm _tpc) ->
    @tso_globstep TGE tpc (ub t) FP.emp tpc' ->
    tso_buffers (tm tpc) t = head ++ bi :: tail ->
    tso_buffers (tm tpc') t = head' ++ bi :: tail ->
    tso_buffers (tm _tpc) t = head ++ bi :: _tail ->
    (thrd_valid tpc t -> thrd_valid _tpc t) ->
    exists _tpc',
      @tso_globstep TGE _tpc (ub t) FP.emp _tpc' /\
      tso_buffers (tm _tpc') t = head' ++ bi :: _tail.
Proof.
  introv Hmem_eq; intros.
  inv H; simpls.
  unfolds thrd_valid; simpls.
  destruct _tpc; simpls.
  unfolds unbuffer.
  destruct head; simpls.
  {
    rewrite H0 in H_unbuf.
    ex_match2.
    inv H_unbuf; simpls.
    eexists.
    split.
    econstructor; eauto.
    unfold unbuffer.
    rewrite H2.
    rewrite <- Hmem_eq, Hx; eauto.
    simpls.
    rewrite tupdate_b_get in H1; subst.
    assert (length tail = length (head' ++ bi :: tail)).
    {
      rewrite <- H1; eauto.
    }
    rewrite app_length in H; simpls.
    Lia.lia.
  }
  {
    rewrite H0 in H_unbuf.
    ex_match2.
    inv H_unbuf; simpls.
    eexists.
    split.
    econstructor; eauto.
    unfold unbuffer.
    rewrite H2, <- Hmem_eq, Hx.
    eauto.
    simpls.
    try rewrite tupdate_b_get in *.
    eapply app_inv_tail in H1; subst; eauto.
  }
Qed.

Lemma ub_star_thdp_cid_unchg:
  forall TGE t tpc tpc',
    ub_star TGE t tpc tpc' ->
    thrdpool tpc' = thrdpool tpc /\ cid tpc' = cid tpc.
Proof. clear. induction 1; auto. inv H; auto. Qed.

Lemma glob_step_fp_smile_conflictc_preserve:
  forall TGE tpc l fp tpc' t0 fp0,
    @tso_globstep TGE tpc l fp tpc' ->
    FP.smile fp fp0 ->
    ~ conflictc t0 fp0 (tso_buffers (tm tpc)) ->
    ~ conflictc t0 fp0 (tso_buffers (tm tpc')).
Proof.
  intros.
  lets Hglob_step : H.
  inv H; simpls; eauto.
  (** CoreStep *)
  {
    intro.
    contradiction H1; clear H1.
    inv H.
    econstructor; eauto.
    lets Hbf : H_core_step.
    eapply tso_step_buf_add in Hbf.
    destruct Hbf as [buf'' Hbf]; subst.
    unfold tupdate in H2.
    ex_match2; subst.
    eapply in_or_app_rev in H2.
    destruct H2; eauto.
    unfolds conflict_bi.
    lets Hfp_bf_item_subset : Hglob_step.
    eapply bis_subst_fp in Hfp_bf_item_subset; eauto.
    Focus 2.
    simpls.
    rewrite tupdate_b_get; eauto.
    eapply conflict_bi_subset_fp_conflict in H3; eauto.
    eapply FP.smile_conflict_compat in H0; tryfalse.
  }
  (** Unbuffer *)
  {
    intro.
    contradiction H1; clear H1.
    inv H.
    econstructor; eauto.
    unfolds unbuffer.
    ex_match2; simpls.
    inv H_unbuf; simpls.
    unfold tupdate in H2.
    ex_match2; eauto; subst.
    rewrite Hx; simpls; eauto.
  }
Qed.

Lemma step_diff_tid_thrdp_eq:
  forall TGE tpc l fp tpc' t',
    cid tpc <> t' ->
    @tso_globstep TGE tpc l fp tpc' ->
    (TSOThrdPool.content (thrdpool tpc')) !! t' =
    (TSOThrdPool.content (thrdpool tpc)) !! t'.
Proof.
  intros.
  inv H0; simpls; eauto;
    try solve [inv H_tp_upd; simpls; rewrite PMap.gso; eauto].
  (** ext call *)
  unfolds TSOThrdPool.push; simpls.
  rewrite H_tp_core in H_tp_push; simpls.
  inv H_tp_push; simpls.
  rewrite PMap.gso; eauto. 
  (** return *)
  unfolds TSOThrdPool.pop.
  rewrite H_tp_core in H_tp_pop; simpls.
  inv H_tp_pop.
  inv H_tp_upd; simpls.
  rewrite PMap.gss in H0.
  inv H0.
  do 2 (rewrite PMap.gso; eauto).
  (** halt *)
  unfolds TSOThrdPool.pop.
  rewrite H_tp_core in H_tp_pop.
  inv H_tp_pop; simpls.
  rewrite PMap.gso; eauto.
Qed.
  
Lemma smile_sym:
  forall fp1 fp2, FP.smile fp1 fp2 -> FP.smile fp2 fp1.
Proof. eapply FPLemmas.fpsmile_sym; eauto. Qed.

Lemma evt_step_emp_fp:
  forall TGE tpc v fp tpc',
    @tso_globstep TGE tpc (evt v) fp tpc' ->
    fp = FP.emp.
Proof. clear. inversion 1; auto. Qed.


Lemma sw_step_eq_config_but_cid:
  forall TGE tpc tpc',
    @tso_globstep TGE tpc sw FP.emp tpc' ->
    eq_config_but_cid TGE tpc tpc'.
Proof. clear. inversion 1; constructor; simpl; auto using GMem.eq_refl. Qed.

Lemma ub_step_buffer_pop:
  forall TGE tpc t tpc',
    @tso_globstep TGE tpc (ub t) FP.emp tpc' ->
    exists bi, tso_buffers (tm tpc) t = bi :: tso_buffers (tm tpc') t.
Proof.
  clear. inversion 1. simpl. unfold unbuffer in *. subst.
  destruct (tso_buffers tm t). discriminate.
  destruct apply_buffer_item; inv H_unbuf.
  simpl. unfold tupdate. destruct peq. eauto. contradiction.
Qed.
 
Lemma eq_config_eq_ub_star:
  forall TGE tpc0 tpc1 tpc0' t,
    eq_config TGE tpc0 tpc0' ->
    ub_star TGE t tpc0 tpc1 ->
    exists tpc1', ub_star TGE t tpc0' tpc1' /\ eq_config TGE tpc1 tpc1'.
Proof.
  clear. intros. revert tpc0' H. induction H0.
  intros. exists tpc0'. split; [constructor | auto].
  intros. exploit eq_config_eq_step; eauto. intros (tpc1' & Hub0' & Heq).
  apply IHub_star in Heq. destruct Heq as (tpc2' & Hubstar' & Heq).
  exists tpc2'. split; auto. econstructor; eauto.
Qed.

Lemma non_conflicting_tau_step_buffer_fp_smile:
  forall TGE tpc fp tpc' t,
    @tso_globstep TGE tpc tau fp tpc' ->
    tso_buffers (tm tpc) (cid tpc) = nil ->
    ~ conflictc (cid tpc) fp (tso_buffers (tm tpc)) ->
    t <> cid tpc ->
    forall bi bi',
      In bi (tso_buffers (tm tpc') (cid tpc)) ->
      In bi' (tso_buffers (tm tpc') t) ->
      FP.smile (bi_footprint bi) (bi_footprint bi').
Proof.
  intros.
  eapply FP.smile_conflict_compat.
  intro.
  contradiction H1; clear H1.
  econstructor; eauto.
  instantiate (1 := bi').
  {
    inv H; simpls; eauto.
    clear - H4 H2.
    unfolds tupdate.
    ex_match2; eauto.
  }
  lets Hglob_step : H. 
  inv H; eauto; simpls; try solve [rewrite H0 in H3; simpls; tryfalse].
  (** Core Step *)
  {
    lets Hbf : H_core_step.
    eapply tso_step_buf_add in Hbf.
    destruct Hbf as [buf'' Hbf].
    rewrite H0 in Hbf; simpls; subst.
    lets Hfp_buf_subset : Hglob_step. 
    eapply bis_subst_fp in Hfp_buf_subset.
    Focus 2. simpls.
    unfold tupdate.
    ex_match2; subst; eauto.
    rewrite H0; simpl; eauto.
    Focus 2.
    instantiate (1 := bi).
    clear - H3.
    unfolds tupdate.
    ex_match2; subst; eauto.
    clear - H5 Hfp_buf_subset.
    eapply FP.conflict_sym in H5.
    eapply fp_subset_conflict_full_conflict in H5; eauto.
    unfold conflict_bi.
    eapply FP.conflict_sym; eauto.
  }
Qed.

Lemma ub_steps_reorder:
  forall TGE tpc1 tpc2 tpc3 t1 t2 bi1 bi2 tail1 tail2,
    tso_globstep tpc1 (ub t1) FP.emp tpc2 ->
    tso_globstep tpc2 (ub t2) FP.emp tpc3 ->
    t1 <> t2 ->
    tso_buffers (tm tpc1) t1 = bi1 :: tail1 ->
    tso_buffers (tm tpc1) t2 = bi2 :: tail2 ->
    FP.smile (bi_footprint bi1) (bi_footprint bi2) ->
    exists tpc2' tpc3',
      tso_globstep tpc1 (ub t2) FP.emp tpc2' /\
      tso_globstep tpc2' (ub t1) FP.emp tpc3' /\
      eq_config TGE tpc3 tpc3'.
Proof.
  intros.
  inv H; inv H0; simpls.
  unfolds unbuffer.
  rewrite H2 in H_unbuf.
  destruct (apply_buffer_item bi1 (memory tm)) eqn:Happly_buf1; simpls; tryfalse.
  inv H_unbuf; simpls.
  rewrite in_tbf_upd_oth_stillin in H_unbuf0; eauto.
  rewrite H3 in H_unbuf0.
  destruct (apply_buffer_item bi2 g) eqn:Happly_buf2; simpls; tryfalse.
  inv H_unbuf0; simpls.
  lets Happly_buf1' : Happly_buf1.
  eapply buf_item_unbuf_locality_1 in Happly_buf1'.
  lets Happly_buf2' : Happly_buf2.
  eapply buf_item_unbuf_locality_1 in Happly_buf2'. 
  assert (MemPre g (memory tm) (bi_footprint bi2)).
  {
    eapply MemPre_comm.
    eapply apply_buf_item_outside_stable; eauto.
  }
  eapply Happly_buf2' in H.
  destruct H as [gm1 [Happly_buf2'' HMemPost2]].
  assert (MemPre (memory tm) gm1 (bi_footprint bi1)).
  {
    eapply apply_buf_item_outside_stable; eauto.
    eapply FPLemmas.fpsmile_sym; eauto.
  }
  eapply Happly_buf1' in H.
  destruct H as [gm2 [Happly_buf1'' HMemPost1]].
  do 2 eexists.
  split.
  {
    econstructor; eauto.
    unfold unbuffer.
    rewrite H3; rewrite Happly_buf2''; eauto.
  }
  split.
  {
    econstructor; eauto.
    unfold unbuffer; simpls.
    rewrite tupdate_not_eq_get, H2, Happly_buf1''; eauto.
  }
  {
    econstructor; eauto; simpls.
    apply GMem_eq.
    eapply FPLemmas.MemEffect_MemPost_fpsmile_memeq. 
    3 : eapply FPLemmas.fpsmile_sym; eauto.
    4 : eapply unchanged_content_comm; eauto.
    5 : eapply unchanged_content_comm; eauto.
    eapply apply_buf_item_MemEffect; eauto.
    eapply apply_buf_item_MemEffect; eauto.
    eapply apply_buf_item_MemEffect; eauto.
    eapply apply_buf_item_MemEffect; eauto.
    rewrite tupdate_tid_neq_twice_rev; eauto.
  }
Qed.

Lemma ub_step_buffer_eq:
  forall TGE tpc t tpc' t',
    @tso_globstep TGE tpc (ub t) FP.emp tpc' ->
    t' <> t ->
    tso_buffers (tm tpc') t' = tso_buffers (tm tpc) t'.
Proof.
  clear. inversion 1. subst. simpl.
  unfold unbuffer in *. destruct (tso_buffers tm t); inv H_unbuf.
  destruct apply_buffer_item; inv H1.
  simpl. unfold tupdate.
  destruct peq; subst; auto. contradiction.
Qed.

Lemma ub_star_ub_step_reorder:
  forall TGE tpc1 tpc2 tpc3 t1 t2,
    ub_star TGE t1 tpc1 tpc2 ->
    tso_globstep tpc2 (ub t2) FP.emp tpc3 ->
    t1 <> t2 ->
    (forall bi1 bi2,
        In bi1 (tso_buffers (tm tpc1) t1) ->
        In bi2 (tso_buffers (tm tpc1) t2) ->
        FP.smile (bi_footprint bi1) (bi_footprint bi2)) ->
    exists tpc2' tpc3',
      tso_globstep tpc1 (ub t2) FP.emp tpc2' /\
      ub_star TGE t1 tpc2' tpc3' /\
      eq_config TGE tpc3 tpc3'.
Proof.
  intros. revert tpc3 H0 H2. induction H; intros.
  exists tpc3 tpc3. split. auto. split. constructor. auto using eq_config_refl.
  exploit IHub_star. eauto. intros.
  erewrite ub_step_buffer_eq in H5; eauto.
  exploit ub_step_buffer_pop. exact H. intros [bi1' Hbuffer].
  rewrite Hbuffer in H3. apply H3; auto. simpl. auto.
  intros (tpc2' & tpc3' & Hub2 & Hubstar1 & Heq).
  exploit ub_step_buffer_pop. exact H. intros [bi1' Hbuffer1].
  exploit ub_step_buffer_pop. exact Hub2. intros [bi2' Hbuffer2].
  erewrite ub_step_buffer_eq in Hbuffer2; eauto.
  exploit ub_steps_reorder. exact H. exact Hub2. auto. exact Hbuffer1. exact Hbuffer2.
  apply H3. rewrite Hbuffer1. simpl; auto. rewrite Hbuffer2; simpl; auto.
  intros (tpc2'' & tpc3'' & Hub2' & Hub1' & Heq').
  exploit eq_config_eq_ub_star. exact Heq'. eauto. intros (tpc3''' & Hubstar' & Heq'').
  exists tpc2'' tpc3'''. split. auto. split; eauto using eq_config_trans.
  econstructor; eauto.
Qed.

Lemma ub_evt_reorder:
  forall TGE (tpc0 tpc1 tpc2 tpc3: @TSOProgConfig TGE) t v,
    tso_globstep tpc0 (ub t) FP.emp tpc1 ->
    tso_globstep tpc1 sw FP.emp tpc2 ->
    tso_globstep tpc2 (evt v) FP.emp tpc3 ->
    exists _tpc1 _tpc2 _tpc3,
      tso_globstep tpc0 sw FP.emp _tpc1 /\
      cid _tpc1 = cid tpc2 /\
      tso_globstep _tpc1 (evt v) FP.emp _tpc2 /\
      tso_globstep _tpc2 (ub t) FP.emp _tpc3 /\
      eq_config_but_cid TGE tpc3 _tpc3.
Proof.
  intros.
  inv H; inv H0; inv H1; simpls.
  do 3 eexists.
  split.
  {
    econstructor.
    instantiate (1 := t'); eauto.
    eauto.
  }
  split; simpls; eauto.
  split.
  {
    econstructor; eauto.
  }
  split.
  {
    econstructor; eauto.
    eapply thrdpool_tupdate_valid_still_valid; eauto.
  }
  {
    econstructor; eauto.
    simpls.
    eapply GMem.eq_refl; eauto.
  }
Qed.

Lemma eq_config_but_cid_ub :
  forall TGE tpc t tpc' _tpc,
    eq_config_but_cid TGE tpc _tpc ->
    tso_globstep tpc (ub t) FP.emp tpc' ->
    exists _tpc', tso_globstep _tpc (ub t) FP.emp _tpc' /\
             eq_config_but_cid TGE tpc' _tpc'.
Proof.
  intros.
  inv H0; inv H; simpls.
  destruct _tpc; simpls; subst.
  destruct tm, tm'; simpls. 
  lets Hunbuf : eq_m'0; eapply gmem_eq_ub_gmem_eq in Hunbuf; eauto; simpls.
  destruct Hunbuf as [gm2' [Hunbuf' Hgmem_eq']].
  eexists.
  split.
  econstructor; eauto.
  instantiate (1 := {| tso_buffers := tso_buffers0; memory := gm2' |}).
  destruct tm0; simpls; subst; eauto.
  econstructor; eauto.
Qed.

Lemma eq_config_but_cid_ub_star:
  forall TGE tpc t tpc' _tpc,
    eq_config_but_cid TGE tpc _tpc ->
    ub_star TGE t tpc tpc' ->
    exists _tpc', ub_star TGE t _tpc _tpc' /\ eq_config_but_cid TGE tpc' _tpc'.
Proof.
  intros.
  generalize dependent _tpc.
  induction H0; simpls; intros; eauto.
  {
    exists _tpc.
    split.
    eapply ub_star_refl; eauto.
    eauto.
  }
  {
    eapply eq_config_but_cid_ub in H1; eauto.
    destruct H1 as (_tpc' & Hub_step & Heq_config).
    eapply IHub_star in Heq_config.
    destruct Heq_config as [_tpc'0 [Hub_star' Heq_config']].
    exists _tpc'0. split; eauto.
    eapply ub_star_cons; eauto.
  }
Qed.

Lemma ub_star_evt_reorder:
  forall TGE (tpc0 tpc1 tpc2 tpc3: @TSOProgConfig TGE) t v,
    ub_star TGE t tpc0 tpc1 ->
    tso_globstep tpc1 sw FP.emp tpc2 ->
    tso_globstep tpc2 (evt v) FP.emp tpc3 ->
    exists _tpc1 _tpc2 _tpc3,
      tso_globstep tpc0 sw FP.emp _tpc1 /\
      cid _tpc1 = cid tpc2 /\
      tso_globstep _tpc1 (evt v) FP.emp _tpc2 /\
      ub_star TGE t _tpc2 _tpc3 /\
      eq_config_but_cid TGE tpc3 _tpc3.
Proof.
  introv Hub_star.
  generalize dependent tpc2.
  generalize dependent tpc3.
  generalize dependent v.
  induction Hub_star; intros.
  {
    inv H; inv H0; simpls.
    do 3 eexists.
    split.
    econstructor; eauto.
    split; simpl; eauto.
    split.
    econstructor; eauto.
    split.
    eapply ub_star_refl; eauto.
    {
      econstructor; eauto; simpls.
      eapply GMem.eq_refl; eauto.
    }
  }
  {
    lets Hreorder : H0.
    eapply IHHub_star in Hreorder; eauto.
    destruct Hreorder as [_tcp1 [_tcp2 [_tcp3
                           [Hsw [Htid_eq [Hevt [Hub_star' Heq_config]]]]]]].
    lets Ht : H.
    eapply ub_evt_reorder with (v := v) in Ht; eauto.
    destruct Ht as [_tcp1' [_tcp2' [_tcp3' [Hsw1 [Htid_eq1
                               [Hevt1 [Hub_step1 Heq_config1]]]]]]].
    lets Heq_config1' : Heq_config1.
    eapply eq_config_but_cid_ub_star with (t := t) (tpc' := _tcp3) in Heq_config1';
      eauto.
    destruct Heq_config1' as [_tcp'' [Hub_star'' Heq_config']].
    exists _tcp1' _tcp2' _tcp''.
    split; eauto.
    split; eauto.
    inv Htid_eq; eauto.
    split; eauto.
    split.
    {
      clear - Hub_step1 Hub_star''.
      eapply ub_star_cons; eauto.
    }
    eapply eq_config_but_cid_trans; eauto.
  }
Qed.
Require ConflictReorder SmileReorder.
Lemma adjacent_sc_conflicting_step_race:
  forall SGE spc0 fp0 spc1 spc2 fp2 spc3,
    (* GE wd, thrdpool inv holds, spc0 safe *)
    (forall ix, mod_wd (GlobEnv.modules SGE ix)) ->
    GlobEnv.wd SGE->
    ThreadPool.inv spc0.(thread_pool) ->
    safe_state glob_step GlobSemantics.abort spc0 ->
    (* tau steps *)
    @glob_step SGE spc0 ETrace.tau fp0 spc1 ->
    @glob_step SGE spc1 ETrace.sw FP.emp spc2 ->
    @glob_step SGE spc2 ETrace.tau fp2 spc3 ->
    (* tid neq *)
    cur_tid spc0 <> cur_tid spc2 ->
    (* fp conflict *)
    FP.conflict fp0 fp2 ->
    (* either abort or race *)
    DRF.star_race_config spc0.
Proof.
  intros.
  apply FP.emp_never_conflict in H7 as ?;Hsimpl.
  apply TypedSemantics.type_glob_step_exists in H3 as [].
  destruct x;try(inv H3;contradiction).
  apply TypedSemantics.type_glob_step_exists in H5 as [].
  destruct x;try(inv H5;contradiction).

  assert(ConflictReorder.pc_valid_tid spc1 (cur_tid spc2)).
  inv H4. constructor;auto.
  exploit ConflictReorder.npnswstep_pc_valid_tid_backwards_preservation.
  left. apply H3. eauto.
  intro.
  assert(glob_step spc0 ETrace.sw FP.emp ({|thread_pool:= thread_pool spc0;cur_tid := cur_tid spc2;gm := gm spc0;atom_bit := atom_bit spc0 |})).
  inv H4. simpl.
  inv H3. inv H11. econstructor;eauto.

  inv H4.
  exploit ConflictReorder.corestep_conflict;eauto.
  rewrite SmileReorder.pc_cur_tid. eauto.
  eauto.
  intro.
  destruct H4.
  simpl in *.
  contradict H4. eapply H2;eauto.
  econstructor 2. eauto. constructor.

  inv H3.
  Hsimpl. simpl in *.
  unfold DRF.star_race_config.
  Esimpl;eauto. econstructor 2;eauto. constructor.
  econstructor.
  apply H6. econstructor;eauto.

  inv H3. econstructor;eauto.
  right;congruence.
  auto.
Qed.

Lemma apply_not_alloc_item_vb_eq :
  forall bi m m',
    ~ (exists b lo hi, bi = BufferedAlloc b lo hi) ->
    apply_buffer_item bi m = Some m' ->
    GMem.validblocks m = GMem.validblocks m'.
Proof.
  intros.
  destruct bi; simpls.
  contradiction H.
  eauto.
  unfolds free.
  ex_match2.
  unfolds unchecked_free.
  inv H0; simpls; eauto.
  unfolds store.
  ex_match2.
  inv H0; simpls; eauto.
Qed.

Lemma apply_buffer_cons :
  forall bf1 bf2 m m' m'',
    apply_buffer bf1 m = Some m'' -> apply_buffer bf2 m'' = Some m' ->
    apply_buffer (bf1 ++ bf2) m = Some m'.
Proof.
  induction bf1; intros; simpls.
  inv H; eauto.
  destruct (apply_buffer_item a m) eqn:?; simpls; tryfalse.
  eapply IHbf1 with (bf2 := bf2) in H; eauto.
Qed.

Lemma in_apply_bf_mvb_in_orgin_m_or_bf_alloc_rev :
  forall bf b m m',
    In b (GMem.validblocks m) \/ (exists lo hi, In (BufferedAlloc b lo hi) bf) ->
    apply_buffer bf m = Some m' ->
    In b (GMem.validblocks m').
Proof.
  induction bf; intros; simpls.
  inv H0; eauto.
  destruct H; eauto.
  destruct H as (lo & hi & contr); tryfalse.
  destruct (apply_buffer_item a m) eqn:?; simpls; tryfalse.
  eapply IHbf; eauto.
  destruct H.
  left.
  eapply apply_buffer_item_in_validbloks_stable; eauto.
  destruct H as (lo & hi & H).
  destruct H; subst.
  clear - Heqo; left.
  simpls.
  unfolds alloc.
  inv Heqo; simpls; eauto.
  right; eauto.
Qed.
  
Lemma valid_block_stable_embed_stable :
  forall m1 m2 fm1 fl,
    GMem.validblocks m1 = GMem.validblocks m2 ->
    embed m1 fl fm1 ->
    exists fm2, embed m2 fl fm2.
Proof.
  intros.
  inv H0.
  eexists
    (Mem.mkmem (GMem.mem_contents m2)
               (GMem.mem_access m2)
               (GMem.validblocks m2)
               (Mem.freelist fm1)
               (Mem.nextblockid fm1) _ _ _ _ _).
  econstructor; eauto.
  unfold strip; simpls.
  eapply gmem_eq; eauto.
  Unshelve.
  {
    intros.
    destruct fm1; eauto.
  }
  {
    destruct fm1; simpls.
    intros.
    eapply valid_wd in H0.
    rewrite <- H; eauto.
  }
  {
    intros.
    destruct m2; simpls; eauto.
    eapply access_max.
  }
  {
    intros.
    destruct m2; simpls; eauto.
  }
  {
    intros.
    destruct m2; simpls; eauto.
  }
Qed.

Lemma store_args_rec_fmem_add_store_buf_item' :
  forall args bm bm' sp ofs tys,
    store_args_rec_fmem bm sp ofs args tys = Some bm' ->
    exists bis, tbuffer bm' = tbuffer bm ++ bis /\ fmemory bm = fmemory bm' /\
           (forall bi, In bi bis -> (exists c b ofs v, bi = BufferedStore c b ofs v /\
           exists ofs0, sp = Vptr b ofs0)).
Proof.
  induction args; intros.
  eexists nil.
  simpls.
  ex_match2; subst.
  inv H.
  rewrite app_nil_r.
  repeat (split; eauto).
  intros; tryfalse.
  simpls.
  ex_match2;
  unfolds store_stack_fmem, tsostorev, tsostore, buffer_insert;
    ex_match2; inv_some;
      eapply IHargs in H; eauto; simpls;
        destruct sp; simpls; tryfalse;
          match goal with
          | H : Vptr _ _ = Vptr _ _ |- _ => inv H
          | _ => idtac
          end;
          destruct H as (bis & Hbuf & Hmem & store);
          try solve [eexists; rewrite Hbuf; rewrite app_assoc_reverse; simpl;
                     repeat (split; eauto); introv Ht; destruct Ht; subst; eauto;
                     repeat eexists].
  inv Hx2; simpls.
  rewrite Hbuf, Hmem.
  repeat (rewrite app_assoc_reverse); simpl.
  eexists.
  repeat (split; eauto).
  intros.
  simpl in H.
  inv Hx5. 
  repeat (destruct H; subst).
  do 4 eexists. split; eauto.
  do 4 eexists. split; eauto.
  eapply store; eauto.
Qed.

Lemma store_args_rec_fmem_add_store_buf_item :
  forall args bm bm' sp ofs tys,
    store_args_rec_fmem bm sp ofs args tys = Some bm' ->
    exists bis, tbuffer bm' = tbuffer bm ++ bis /\ fmemory bm = fmemory bm' /\
           (forall bi, In bi bis -> (exists c b ofs v, bi = BufferedStore c b ofs v)).
Proof.
  intros.
  eapply store_args_rec_fmem_add_store_buf_item' in H; eauto.
  destruct H as (bis & Hbuf & Hmem & Hstore).
  eexists.
  repeat (split; eauto).
  intros.
  eapply Hstore in H.
  destruct H as (c & b & ofs0 & v & Hbi & Hsp).
  subst; eauto.
Qed.

Lemma vb_subset_apply_buf_item_still :
  forall m m' m0 m'0 b bi,
    (forall b, In b (GMem.validblocks m) -> In b (GMem.validblocks m')) ->
    apply_buffer_item bi m = Some m0 ->
    apply_buffer_item bi m' = Some m'0 ->
    In b (GMem.validblocks m0) ->
    In b (GMem.validblocks m'0).
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inv H0; inv H1; simpls.
    destruct H2; eauto.
  }
  {
    unfolds free, unchecked_free; simpls.
    ex_match2.
    inv H0; inv H1; simpls.
    eauto.
  }
  {
    unfolds store.
    ex_match2.
    inv H0; inv H1; simpls.
    eauto.
  }
Qed.

Lemma vb_fl_apply_buf_item_still :
  forall m m' m0 m'0 b bi fl,
    (forall b, In b (GMem.validblocks m') ->
          ~ In b (GMem.validblocks m) -> exists n', MemAux.get_block fl n' = b) ->
    apply_buffer_item bi m = Some m0 ->
    apply_buffer_item bi m' = Some m'0 ->
    In b (GMem.validblocks m'0) ->
    ~ In b (GMem.validblocks m0) ->
    exists n', MemAux.get_block fl n' = b.
Proof.
  intros.
  destruct bi; simpls.
  (* alloc *)
  {
    unfolds alloc.
    inv H0; inv H1; simpls.
    destruct H2.
    contradiction H3; eauto.
    destruct (Classical_Prop.classic (In b (GMem.validblocks m))).
    contradiction H3; eauto.
    eauto.
  }
  (* free *)
  {
    unfolds free.
    ex_match2.
    unfolds unchecked_free.
    inv H0; inv H1; simpls.
    eauto.
  }
  (* store *)
  {
    unfolds store.
    ex_match2.
    inv H0; inv H1; simpls.
    eauto.
  }
Qed.

Lemma origin_embed_alloc_nextblock_embed_still :
  forall m fl fm m' lo hi,
    embed m fl fm ->
    alloc m (Mem.nextblock fm) lo hi = Some m' ->
    exists fm', embed m' fl fm'.
Proof.
  intros.
  inv H.
  eexists
    (Mem.mkmem (GMem.mem_contents m')
               (GMem.mem_access m')
               (GMem.validblocks m')
               (Mem.freelist fm) (Mem.nextblockid fm+1)%coq_nat _ _ _ _ _).
  econstructor; eauto.
  unfold strip; simpl.
  eapply gmem_eq; eauto.
  Unshelve.
  destruct fm; simpls; eauto.
  {
    unfolds alloc.
    inv H0; simpls.
    intros.
    destruct fm; simpls.
    unfold Mem.nextblock; simpls.
    split; intro.
    destruct H0; subst; eauto.
    destruct (Nat.eq_dec nextblockid n); subst.
    Lia.lia.
    lets Ht : n0.
    eapply freelist_wd in Ht; tryfalse.
    eapply valid_wd in H0; eauto.
    Lia.lia.
    eapply Nat.lt_exists_pred in H0.
    destruct H0 as [k [Ht Hle]].
    subst.
    rewrite Nat.add_1_r in Ht.
    eapply Nat.succ_inj in Ht; subst.
    eapply Nat.lt_eq_cases in Hle.
    destruct Hle; subst; eauto.
    right.
    eapply valid_wd in H; eauto.
  }
  destruct m'; simpls; eauto.
  destruct m'; simpls; eauto.
  destruct m'; simpls; eauto.
Qed.

Lemma embed_fl_disj_vb_ext_embed_still :
  forall m m' fm1 fm2 fl1 fl2,
    (forall b, In b (GMem.validblocks m) -> In b (GMem.validblocks m')) ->
    (forall b, In b (GMem.validblocks m') -> ~ In b (GMem.validblocks m) ->
          exists n', MemAux.get_block fl1 n' = b) ->
    MemAux.disj fl1 fl2 ->
    embed m fl2 fm2 ->
    embed m' fl1 fm1 ->
    exists fm, embed m' fl2 fm.
Proof.
  intros.
  inv H2; inv H3.
  eexists
    (Mem.mkmem (Mem.mem_contents fm1)
               (Mem.mem_access fm1)
               (Mem.validblocks fm1)
               (Mem.freelist fm2) (Mem.nextblockid fm2) _ _ _ _ _).
  econstructor; eauto.
  unfold strip; simpls.
  eapply gmem_eq; eauto.
  Unshelve.
  {
    destruct fm2; eauto.
  }
  {
    intros.
    split; intro.
    {
      destruct fm2; simpls.
      destruct (Classical_Prop.classic (In b validblocks)); eauto.
      eapply valid_wd; eauto.
      eapply H0 in H3; eauto.
      destruct H3.
      clear - H1 H2 H3.
      inv H1.
      unfolds MemAux.get_block.
      specialize (H x n).
      tryfalse.
    }
    {
      destruct fm2; simpls.
      eapply valid_wd in H3; eauto.
    }
  }
Qed.

Lemma embed_alloc_embed_still_nextblockid :
  forall m m' fl fm fm' n lo hi,
    embed m fl fm ->
    ~ In (MemAux.get_block fl n) (GMem.validblocks m) ->
    alloc m (MemAux.get_block fl n) lo hi = Some m' ->
    embed m' fl fm' ->
    n = Mem.nextblockid fm.
Proof.
  intros.
  inv H; inv H2.
  unfolds alloc.
  inv H1.
  destruct fm, fm'; subst; simpls; subst; simpls.
  clear access_max invalid_noaccess contents_default
        access_max0 invalid_noaccess0 contents_default0.
  pose proof Nat.lt_trichotomy.
  specialize (H n nextblockid).
  destruct H.
  {
    assert (MemAux.get_block freelist n = MemAux.get_block freelist n); eauto.
    eapply valid_wd in H1.
    eapply H1 in H; tryfalse.
  }
  destruct H; eauto.
  pose proof Nat.lt_trichotomy.
  specialize (H1 nextblockid nextblockid0).
  destruct H1.
  {
    assert (MemAux.get_block freelist nextblockid =
            MemAux.get_block freelist nextblockid); eauto.
    eapply valid_wd0 in H2.
    eapply H2 in H1; clear H2. 
    destruct H1.
    destruct (Nat.eq_dec n nextblockid); eauto.
    eapply freelist_wd in n0; tryfalse.
    eapply valid_wd in H1; eauto.
    Lia.lia.
  }
  destruct H1; subst.
  {
    assert (MemAux.get_block freelist n =
            MemAux.get_block freelist n); eauto.
    eapply valid_wd0 in H1.
    assert (MemAux.get_block freelist n = MemAux.get_block freelist n \/
            In (MemAux.get_block freelist n) validblocks); eauto.
    eapply H1 in H2.
    Lia.lia.
  }
  {
    lets Ht : H1.
    eapply valid_wd in H1; eauto.
    assert (MemAux.get_block freelist n =
            MemAux.get_block freelist nextblockid0 \/
            In (MemAux.get_block freelist nextblockid0) validblocks).
    eauto.
    eapply valid_wd0 in H2; eauto.
    Lia.lia.
  }
Qed.

Lemma vbeq_apply_buffer_embed_stable :
  forall bf m1 m2 m1' m2' fm1' fl,
    apply_buffer bf m1 = Some m1' ->
    GMem.validblocks m1 = GMem.validblocks m2 ->
    embed m1' fl fm1' ->
    apply_buffer bf m2 = Some m2' ->
    exists fm2', embed m2' fl fm2'.
Proof.
  intros.
  eexists
    (Mem.mkmem (GMem.mem_contents m2')
                     (GMem.mem_access m2')
                     (GMem.validblocks m2') fl (Mem.nextblockid fm1') _ _ _ _ _).
  econstructor; eauto.
  unfold strip; simpl; eauto.
  eapply gmem_eq; eauto.
  Unshelve.
  destruct fm1'; inv H1; eauto.

  intros.
  inv H1.
  lets Ht : H0.
  eapply in_valid_block_eq_apply_same_buf_still in Ht; eauto.
  split; intro.
  {
    rewrite <- Ht in H1.
    destruct fm1'; simpls.
    eapply valid_wd; eauto.
  }
  {
    destruct fm1'; simpls.
    rewrite <- Ht.
    eapply valid_wd; eauto.
  }
  
  destruct m2'; simpl; eauto.
  destruct m2'; simpl; eauto.
  destruct m2'; simpl; eauto.
Qed.

Lemma vbmore_out_fl_apply_buffer_embed_stable :
  forall bf m1 m2 m1' m2' fm1' fl,
    (forall b, In b (GMem.validblocks m1) -> In b (GMem.validblocks m2)) ->
    (forall b, In b (GMem.validblocks m2) -> ~ In b (GMem.validblocks m1) ->
          ~ (exists n', MemAux.get_block fl n' = b)) ->
    apply_buffer bf m1 = Some m1' ->
    embed m1' fl fm1' ->
    apply_buffer bf m2 = Some m2' ->
    exists fm2', embed m2' fl fm2'.
Proof.
  intros.
  eexists
    (Mem.mkmem (GMem.mem_contents m2')
               (GMem.mem_access m2')
               (GMem.validblocks m2') fl (Mem.nextblockid fm1') _ _ _ _ _). 
  econstructor; eauto.
  unfold strip; eauto.
  eapply gmem_eq; eauto.
  Unshelve.

  destruct fm1'; inv H2; eauto.

  intros.
  split; intro.
  {
    destruct (Classical_Prop.classic (In b (GMem.validblocks m1'))).
    {
      inv H2.
      destruct fm1'; simpls.
      eapply valid_wd; eauto.
    }
    { 
      lets Ht1 : H6.
      eapply not_in_apply_bf_vb_not_in_orign in H6; eauto.
      eapply apply_buffer_not_in_vb_not_alloc_in_bf in Ht1; eauto.
      eapply in_apply_bf_mvb_in_orgin_m_or_bf_alloc in H5; eauto.
      destruct H5.
      eapply H0 in H5; eauto.
      contradiction H5; eauto.
      contradiction Ht1; eauto.
    }
  }
  {
    inv H2.
    destruct fm1'; simpls.
    eapply valid_wd in H5; eauto.
    eapply in_apply_bf_mvb_in_orgin_m_or_bf_alloc in H1; eauto.
    destruct H1.
    eapply H in H1.
    eapply apply_buffer_in_validblocks_stable in H1; eauto.
    destruct H1 as (lo & hi & H1).
    eapply b_in_bf_alloc_in_apply_bf_m_vb in H1; eauto.
  }

  destruct m2'; eauto.
  destruct m2'; eauto.
  destruct m2'; eauto.
Qed.

Lemma embed_gm_forward_embed_stable :
  forall fl m m' fm fm' fm1 bi m0 m0',
    embed m fl fm ->
    (forall b, In b (GMem.validblocks m) -> In b (GMem.validblocks m')) ->
    (forall b, In b (GMem.validblocks m') -> ~ In b (GMem.validblocks m) ->
          exists n', MemAux.get_block fl n' = b) ->
    embed m' fl fm' ->
    apply_buffer_item bi m = Some m0 ->
    embed m0 fl fm1 ->
    apply_buffer_item bi m' = Some m0' ->
    exists fm2, embed m0' fl fm2.
Proof. 
  introv Hembed.
  intros. 
  inv H1; inv H3.
  destruct (Classical_Prop.classic (exists b0 lo hi, bi = BufferedAlloc b0 lo hi)).
  {
    destruct H3 as (b0 & lo & hi & Hbi); subst; simpls.
    destruct (Classical_Prop.classic
                (exists n, MemAux.get_block (Mem.freelist fm1) n = b0)).
    {
      destruct H3 as [n Hb0]; subst.
      destruct (Classical_Prop.classic
                  (In (MemAux.get_block (Mem.freelist fm1) n)
                      (Mem.validblocks fm'))).
      { eexists
          (Mem.mkmem (GMem.mem_contents m0')
                     (GMem.mem_access m0')
                     (GMem.validblocks m0')
                     (Mem.freelist fm') (Mem.nextblockid fm') _ _ _ _ _).
        econstructor; eauto.
        unfold strip; simpls.
        eapply gmem_eq; eauto.
        Unshelve.
        {
          intros.
          destruct fm'; simpls; eauto.
        }
        {
          intros.
          split; intro.
          {
            destruct fm'; simpls.
            lets Hvb : H5.
            eapply valid_wd in Hvb.
            eapply Hvb.
            clear - H4 H3 H6.
            unfolds strip; simpls.
            unfolds alloc; simpls.
            inv H4; simpls.
            destruct H6; subst; eauto.
          }
          {
            destruct fm'; simpls.
            lets Hvb : H5.
            eapply valid_wd in Hvb.
            eapply Hvb in H6.
            clear - H4 H3 H6.
            unfolds alloc, strip; simpls.
            inv H4; simpls.
            eauto.
          }
        }
        destruct m0'; simpls; eauto.
        destruct m0'; simpls; eauto.
        destruct m0'; simpls; eauto.
      }
      {
        assert (n = Mem.nextblockid fm).
        {
          eapply embed_alloc_embed_still_nextblockid with (m' := strip fm1); eauto.
          intro.
          contradiction H3; eauto.
          rewrite H1; eauto.
          rewrite <- H1; eauto.
          instantiate (1 := fm1).
          econstructor; eauto.
        }
        subst.
        assert (Mem.nextblockid fm = Mem.nextblockid fm').
        {
          inv Hembed.
          destruct fm, fm1; simpls.
          unfolds alloc, strip; simpls.
          inv H2; inv H4; simpls.
          clear invalid_noaccess0 access_max0 contents_default0
                invalid_noaccess access_max contents_default.
          destruct fm'; simpls.
          clear invalid_noaccess access_max contents_default.
          clear - freelist_wd freelist_wd0 freelist_wd1
                              valid_wd valid_wd1 H H0 valid_wd0 H3.
          assert ((nextblockid0 = nextblockid + 1)%coq_nat).
          {
            pose proof Nat.lt_trichotomy.
            specialize (H1 nextblockid0 (nextblockid + 1)%coq_nat).
            destruct H1.
            {
              assert (MemAux.get_block freelist nextblockid =
                      MemAux.get_block freelist nextblockid).
              eauto.
              eapply valid_wd0 in H2.
              assert (MemAux.get_block freelist nextblockid =
                      MemAux.get_block freelist nextblockid \/
                      In (MemAux.get_block freelist nextblockid) validblocks).
              eauto.
              eapply H2 in H4.
              clear - H1 H4.
              Lia.lia.
            }
            destruct H1; eauto.
            { 
              pose proof getblock_always_success.
              specialize (H2 (nextblockid + 1)%coq_nat freelist).
              destruct H2 as [b' H2].
              lets Ht : H2.
              eapply valid_wd0 in H2.
              eapply H2 in H1; clear H2. 
              destruct H1.
              subst. 
              assert ((nextblockid + 1)%coq_nat <> nextblockid).
              intro. Lia.lia.
              eapply freelist_wd1 in H1.
              tryfalse.
              eapply valid_wd in Ht.
              eapply Ht in H1.
              Lia.lia.
            }
          }

          subst.
          pose proof Nat.lt_trichotomy.
          specialize (H1 nextblockid nextblockid1).
          destruct H1.
          {
            assert (MemAux.get_block freelist nextblockid =
                    MemAux.get_block freelist nextblockid).
            eauto.
            eapply valid_wd1 in H2.
            eapply H2 in H1.
            tryfalse.
          }
          destruct H1; eauto.
          {
            assert (MemAux.get_block freelist nextblockid1 =
                    MemAux.get_block freelist nextblockid1).
            eauto.
            eapply valid_wd in H2.
            lets Ht : H1.
            eapply H2 in Ht.
            eapply H in Ht.
            eapply valid_wd1 in Ht; eauto.
            Lia.lia.
          }
        }
        eapply origin_embed_alloc_nextblock_embed_still with (m := strip fm'); eauto.
        instantiate (1 := fm').
        econstructor; eauto.
        unfold Mem.nextblock.
        rewrite <- H1, <- H5; eauto.
      }
    }
    {
      eexists
          (Mem.mkmem (GMem.mem_contents m0')
                     (GMem.mem_access m0')
                     (GMem.validblocks m0')
                     (Mem.freelist fm') (Mem.nextblockid fm') _ _ _ _ _).
      econstructor; eauto.
      unfold strip; simpl.
      eapply gmem_eq; eauto.
      Unshelve.
      intros; destruct fm'; simpls; eauto.
      {
        intros.
        destruct fm'; simpls.
        unfolds strip; simpls.
        unfolds alloc.
        inv H2; inv H4; simpls.
        split; intros.
        {
          destruct H1; subst.
          {
            contradiction H3; eauto.
          }
          {
            eapply valid_wd in H1; eauto.
          }
        }
        {
          eapply valid_wd in H1; eauto.
        }
      }
      destruct m0'; simpls; eauto.
      destruct m0'; simpls; eauto.
      destruct m0'; simpls; eauto.
    }
  }
  {
    eexists
      (Mem.mkmem (GMem.mem_contents m0')
                 (GMem.mem_access m0')
                 (GMem.validblocks m0')
                 (Mem.freelist fm') (Mem.nextblockid fm') _ _ _ _ _).
    econstructor; eauto.
    unfold strip; simpl.
    eapply gmem_eq; eauto.
    Unshelve.
    destruct fm'; simpls; eauto.
    {
      intros.
      destruct bi; simpls.
      contradiction H3; eauto.
      unfolds free, unchecked_free; simpls.
      ex_match2.
      inv H2; inv H4; simpls.
      destruct fm'; simpls; eauto.
      unfolds store.
      ex_match2.
      inv H2; inv H4; simpls; eauto.
      destruct fm'; simpls; eauto.
    }
    destruct m0'; simpls; eauto.
    destruct m0'; simpls; eauto.
    destruct m0'; simpls; eauto.
  }
Qed.

Lemma embed_apply_buf_gm_forward_embed_stable :
  forall bf fl m m' fm fm' m0 m0' fm0,
    (forall b, In b (GMem.validblocks m) -> In b (GMem.validblocks m0)) ->
    embed m fl fm ->
    apply_buffer bf m = Some m' ->
    embed m' fl fm' ->
    embed m0 fl fm0 ->
    apply_buffer bf m0 = Some m0' ->
    exists fm0', embed m0' fl fm0'.
Proof.
  intros.
  pose proof Nat.le_gt_cases. 
  specialize (H5 (Mem.nextblockid fm') (Mem.nextblockid fm0)).
  destruct H5.
  {
    eexists
      (Mem.mkmem (GMem.mem_contents m0')
                 (GMem.mem_access m0')
                 (GMem.validblocks m0')
                 fl (Mem.nextblockid fm0) _ _ _ _ _).
    econstructor; eauto.
    unfold strip; simpl; eauto.
    eapply gmem_eq; eauto.
    Unshelve.

    destruct fm; inv H0; eauto.

    intros. 
    split; intro.
    {
      inv H2; inv H3.
      destruct fm'; destruct fm0; simpls; subst.
      eapply valid_wd0; eauto.
      eapply in_apply_bf_mvb_in_orgin_m_or_bf_alloc in H7; eauto; simpls.
      destruct H7; eauto.
      destruct H2 as (lo & hi & H2).
      eapply b_in_bf_alloc_in_apply_bf_m_vb in H1; eauto; simpls.
      eapply valid_wd in H1; eauto.
      eapply valid_wd0; eauto.
      clear - H5 H1.
      Lia.lia.
    }
    {
      inv H2; inv H3.
      destruct fm'; destruct fm0; simpls; subst.
      eapply in_apply_bf_mvb_in_orgin_m_or_bf_alloc_rev; eauto; simpl.
      eapply valid_wd0 in H7; eauto.
    }

    destruct m0'; eauto.
    destruct m0'; eauto.
    destruct m0'; eauto.
  }
  {
    inv H2; inv H3.
    eexists
      (Mem.mkmem (GMem.mem_contents m0')
                 (GMem.mem_access m0')
                 (GMem.validblocks m0')
                 (Mem.freelist fm') (Mem.nextblockid fm') _ _ _ _ _).
    econstructor; eauto.
    unfold strip; simpl.
    eapply gmem_eq; eauto.
    Unshelve.
    
    destruct fm'; simpl; eauto.

    intros.
    destruct fm0; destruct fm'; simpls; subst.
    split; intro.
    {
      eapply in_apply_bf_mvb_in_orgin_m_or_bf_alloc in H2; eauto; simpls.
      destruct H2.
      {
        eapply valid_wd in H2; eauto.
        Lia.lia.
      }
      {
        destruct H2 as (lo & hi & H2).
        eapply valid_wd0; eauto.
        eapply b_in_bf_alloc_in_apply_bf_m_vb in H1; eauto.
      }
    }
    { 
      eapply valid_wd0 in H2; eauto.
      eapply in_apply_bf_mvb_in_orgin_m_or_bf_alloc in H1; eauto.
      destruct H1.
      eapply H in H1; eauto.
      eapply apply_buffer_in_validblocks_stable; eauto.
      eauto.
      destruct H1 as (lo & hi & H1).
      eapply alloc_in_buf_apply_buf_in_vb; eauto.
    }

    destruct m0'; eauto.
    destruct m0'; eauto.
    destruct m0'; eauto.
  }
Qed.

Lemma apply_buf_embed_apply_an_item_embed_apply_buf_embed_still :
  forall bf m m' m0 m1 fl bi fm' fm0 fm,
    embed m fl fm ->
    apply_buffer bf m =
    Some m' ->
    embed m' fl fm' ->
    apply_buffer_item bi m = Some m0 ->
    embed m0 fl fm0 ->
    apply_buffer bf m0 =
    Some m1 ->
    exists fm2, embed m1 fl fm2. 
Proof.
  intros.
  assert (GMem.validblocks m = GMem.validblocks m0 \/
          (exists b, b :: GMem.validblocks m = GMem.validblocks m0 /\
                exists lo hi, bi = BufferedAlloc b lo hi)).
  {
    clear - H2. 
    destruct bi; simpls.
    unfolds alloc.
    inv H2; simpls; eauto.
    right; eauto.
    unfolds free, unchecked_free.
    ex_match2; simpls; eauto.
    inv H2; simpl; eauto.
    unfolds store.
    ex_match2.
    inv H2; simpl; eauto.
  }
  destruct H5.
  {
    eapply vbeq_apply_buffer_embed_stable with (m1 := m) (m2 := m0); eauto.
  }
  destruct H5 as (b & Hvb & lo' & hi' & Hbf_alloc); subst.
  destruct (Classical_Prop.classic
              (exists n, MemAux.get_block fl n = b)).
  {
    eapply embed_apply_buf_gm_forward_embed_stable
    with (m := m) (m0 := m0) (bf := bf); eauto.
    intros.
    rewrite <- Hvb; simpl; eauto.
  }
  {
    eapply vbmore_out_fl_apply_buffer_embed_stable
    with (m1 := m) (m1' := m') (m2 := m0);
      eauto.
    intros.
    rewrite <- Hvb; simpl; eauto.
    intros.
    rewrite <- Hvb in H6.
    simpl in H6.
    destruct H6; subst; tryfalse.
    intro.
    destruct H6.
    contradiction H5; eauto.
  }
Qed.

Lemma FLs_embed_gm_forward_FLs_embed_stable :
  forall bfs m m' n fls fm',
    FLists.wd fls ->
    (forall b, In b (GMem.validblocks m) -> In b (GMem.validblocks m')) ->
    (forall b, In b (GMem.validblocks m') -> ~ In b (GMem.validblocks m) ->
          exists n', MemAux.get_block (FLists.get_fl fls n) n' = b) ->
    embed m' (FLists.get_fl fls n) fm' ->
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    FLs_embed fls {| tso_buffers := bfs; memory := m |} ->
    FLs_embed fls {| tso_buffers := bfs; memory := m' |}.
Proof.
  intros.
  remember {| tso_buffers := bfs; memory := m |} as tm.
  generalize dependent bfs. 
  generalize dependent m'. 
  generalize dependent n.
  generalize dependent m.
  generalize dependent fm'.
  induction H4; simpls; intros; subst; simpls; eauto.
  econstructor; intros; simpls; eauto.
  {
    subst fl.
    destruct (peq n flid); subst; eauto.
    specialize (Embed flid).
    destruct Embed as [fm1 Embed].
    eapply embed_fl_disj_vb_ext_embed_still; eauto.
    clear - H n0.
    inv H.
    eapply flist_disj; eauto.
  }
  { 
    inv H3; simpls.
    lets Happly_buf : H5. 
    eapply ABIS in Happly_buf.
    destruct Happly_buf as [m0 Happly_buf].
    lets Hcons : H5.
    assert (FLs_embed fls {| tso_buffers := bfs; memory := m |}).
    econstructor; eauto.
    inv H3; simpls.
    lets Hembed : Happly_buf.
    eapply UNBS1 in Hembed; eauto.
    inv Hembed; simpls.
    specialize (Embed1 n). 
    destruct Embed1 as [fm1 Embed1].
    assert (exists fm2, embed m'0 (FLists.flist_content fls n) fm2).
    {
      specialize (Embed0 n).
      destruct Embed0.
      eapply embed_gm_forward_embed_stable with (m' := m') (m := m); eauto.      
    }
    destruct H3 as [fm2 H3].
    eapply H0 in Hcons.
    2 : eauto.
    Focus 2.
    eapply UNBS0; eauto.
    5 : eauto.
    eauto.  
    Focus 3.
    instantiate (2 := n).
    instantiate (1 := fm2).
    eauto.
    clear - H1 H6 Happly_buf.
    intros.
    eapply vb_subset_apply_buf_item_still; eauto.
    clear - H2 H1 H6 Happly_buf.
    intros.
    eapply in_apply_bf_item_mvb_in_origin_or_item in H6; eauto.
    destruct H6.
    destruct (Classical_Prop.classic (In b (GMem.validblocks m))).
    eapply apply_buffer_item_in_validbloks_stable in H4; eauto.
    eauto.
    destruct H3 as [lo [hi H3]]; subst.
    simpls.
    clear - Happly_buf H0.
    unfolds alloc.
    inv Happly_buf; simpls.
    contradiction H0; eauto.
  }
Qed.

Lemma unbuffer_safe_additional_original_still' :
  forall bfs t bf m bf1,
    unbuffer_safe {| tso_buffers := tupdate t (bf1 ++ bf) bfs;
                     memory := m |} ->
    unbuffer_safe {| tso_buffers := tupdate t bf1 bfs; memory := m |}.
Proof.
  intros.
  eapply unbuffer_safe_addition_original_still; simpl.
  unfold tsoupd; simpl.
  rewrite tupdate_b_get.
  rewrite tupdate_same_tid_eq; eauto.
Qed.

Lemma FLs_embed_m_vbeq_ub_safe_FLs_embed_stable :
  forall fls bfs m m',
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    FLs_embed fls {| tso_buffers := bfs; memory := m |} ->
    GMem.validblocks m = GMem.validblocks m' ->
    FLs_embed fls {| tso_buffers := bfs; memory := m' |}.
Proof.
  intros. 
  remember {| tso_buffers := bfs; memory := m |} as tm.
  generalize dependent bfs.
  generalize dependent m.
  generalize dependent m'.
  induction H0; simpls; intros; subst; simpls.
  econstructor; intros; eauto.
  {
    subst fl; simpls.
    specialize (Embed flid).
    destruct Embed as [fm Embed].
    eapply valid_block_stable_embed_stable; eauto.
  }
  {
    simpls. 
    inv H; simpls.
    lets Happly_buf : H2.
    eapply ABIS in Happly_buf.
    destruct Happly_buf as [m2 Happly_buf].
    lets Hcons : H2.
    eapply H0 in Hcons.
    2 : eauto.
    eauto.
    3 : eauto.
    eapply UNBS0; eauto.
    eapply in_valid_block_eq_apply_same_buf_item_still; eauto.
  }
Qed.

Lemma FLs_embed_buf_tail_add_one_not_alloc_stable :
  forall fls bfs m t bi,
    unbuffer_safe {| tso_buffers := tupdate t (bfs t ++ bi :: nil) bfs;
                     memory := m |} ->
    FLs_embed fls {| tso_buffers := bfs; memory := m |} ->
    ~ (exists b lo hi, bi = BufferedAlloc b lo hi) ->
    FLs_embed fls {| tso_buffers := tupdate t (bfs t ++ bi :: nil) bfs;
                     memory := m |}.
Proof.
  intros.
  remember {| tso_buffers := bfs; memory := m |} as tm.
  generalize dependent bfs.
  generalize dependent m.
  generalize dependent t.
  generalize dependent bi.
  induction H0; simpls; intros; subst; simpls.
  econstructor; simpls; eauto.
  intros.
  unfold tupdate in H2.
  ex_match2; subst.
  {
    destruct (bfs t) eqn:?; simpls.
    {
      inv H2.
      rewrite tupdate_same_tid_eq. 
      rewrite tupdate_same_eq; eauto.
      assert (FLs_embed fls {| tso_buffers := bfs; memory := m |}).
      econstructor; eauto.
      eapply FLs_embed_m_vbeq_ub_safe_FLs_embed_stable; eauto.
      change (bi0 :: nil) with (nil ++ bi0 :: nil) in H0.
      eapply unbuffer_safe_additional_original_still' in H0.
      rewrite tupdate_same_eq in H0; eauto.
      eapply apply_not_alloc_item_vb_eq; eauto.
    }
    {
      inv H2.
      lets Hcons : Heql.
      eapply H in Hcons.
      2 : eauto.
      4 : eauto.
      rewrite tupdate_b_get in Hcons.
      try rewrite tupdate_same_tid_eq in *.
      eauto.
      eauto.
      rewrite tupdate_b_get.
      rewrite tupdate_same_tid_eq.
      clear - H0 Heql H3.
      inv H0; simpls.
      eapply UNBS in H3.
      rewrite tupdate_same_tid_eq in H3; eauto.
      rewrite tupdate_b_get; eauto.
    }
  }
  {
    eapply H with (t0 := t) in H2.
    2 : eauto.
    4 : eauto.
    rewrite tupdate_not_eq_get in H2; eauto.
    rewrite tupdate_tid_neq_twice_rev in H2; eauto.
    eauto.
    rewrite tupdate_not_eq_get; eauto.
    clear - H0 n H2 H3.
    inv H0; simpls.
    rewrite tupdate_tid_neq_twice_rev; eauto.
    eapply UNBS; eauto.
    rewrite tupdate_not_eq_get; eauto.
  }
Qed.

Lemma FLs_embed_buf_tail_add_not_alloc_stable :
  forall bis fls bfs m t,
    unbuffer_safe {| tso_buffers := tupdate t (bfs t ++ bis) bfs;
                     memory := m |} ->
    FLs_embed fls {| tso_buffers := bfs; memory := m |} ->
    (forall bi, In bi bis -> ~ (exists b lo hi, bi = BufferedAlloc b lo hi)) ->
    FLs_embed fls {| tso_buffers := tupdate t (bfs t ++ bis) bfs;
                     memory := m |}.
Proof.
  induction bis; intros.
  {
    try rewrite app_nil_r in *.
    rewrite buffer_unchange'; eauto.
  }
  {
    assert (FLs_embed fls {| tso_buffers := tupdate t (bfs t ++ a :: nil) bfs;
                             memory := m |}).
    {
      eapply FLs_embed_buf_tail_add_one_not_alloc_stable; eauto.
      assert (bfs t ++ a :: bis = (bfs t ++ a :: nil) ++ bis).
      {
        rewrite app_assoc_reverse; eauto.
      }
      rewrite H2 in H.
      eapply unbuffer_safe_additional_original_still' in H; eauto.
      specialize (H1 a).
      intro.
      assert (In a (a :: bis)); simpls; eauto.
      eapply H1 in H3; tryfalse.
    }
    eapply IHbis in H2; eauto.
    rewrite tupdate_b_get in H2.
    rewrite tupdate_same_tid_eq in H2.
    rewrite app_assoc_reverse in H2; simpls.
    eauto.
    rewrite tupdate_b_get.
    rewrite tupdate_same_tid_eq.
    rewrite app_assoc_reverse; eauto.
    intros.
    eapply H1; simpl; eauto.
  }
Qed.

Lemma FLs_embed_bf_tail_add_store_preserved :
  forall fls bfs m c b ofs v t,
    unbuffer_safe {| tso_buffers :=
                       tupdate t
                               (bfs t ++ BufferedStore c b ofs v :: nil) bfs;
                     memory := m |} ->
    FLs_embed fls {| tso_buffers := bfs; memory := m |} ->
    FLs_embed fls {| tso_buffers :=
                       tupdate t
                               (bfs t ++ BufferedStore c b ofs v :: nil) bfs;
                     memory := m |}.
Proof.
  intros.
  eapply FLs_embed_buf_tail_add_not_alloc_stable; eauto.
  intros; simpls.
  destruct H1; subst; tryfalse.
  intro.
  destruct H1 as [b0 [lo [hi Hcontr]]].
  tryfalse.
Qed.

Lemma FLs_embed_bf_tail_add_alloc_preserved :
  forall fls fl bfs m m' fm' t lo hi n n',
    FLists.wd fls -> fl = FLists.get_fl fls n ->
    unbuffer_safe {| tso_buffers :=
                       tupdate t
                               (bfs t ++ BufferedAlloc (MemAux.get_block fl n') lo hi
                                    :: nil) bfs;
                     memory := m |} ->
    apply_buffer (bfs t ++ BufferedAlloc (MemAux.get_block fl n') lo hi :: nil) m
    = Some m' ->
    embed m' fl fm' ->
    FLs_embed fls {| tso_buffers := bfs; memory := m |} ->
    FLs_embed fls {| tso_buffers :=
                       tupdate t
                               (bfs t ++ BufferedAlloc (MemAux.get_block fl n') lo hi
                                    :: nil) bfs;
                     memory := m |}.
Proof.
  intros. 
  remember {| tso_buffers := bfs; memory := m |} as tm.
  generalize dependent fl.
  generalize dependent bfs.
  generalize dependent m.
  generalize dependent m'.
  generalize dependent lo.
  generalize dependent hi.
  generalize dependent t.
  generalize dependent n.
  generalize dependent n'.
  generalize dependent fm'.
  induction H4; simpls; intros; subst; simpls.
  econstructor; eauto; simpls; intros.  
  unfold tupdate in H1. 
  ex_match2; subst.
  {  
    destruct (bfs t) eqn:?; simpls.
    {  
      inv H1. 
      rewrite tupdate_same_tid_eq; eauto.
      rewrite tupdate_same_eq; eauto.
      inv H3. 
      assert (FLs_embed fls {| tso_buffers := bfs; memory := m |}).
      {
        econstructor; eauto.
      }
      simpl in H5. 
      eapply FLs_embed_gm_forward_FLs_embed_stable with (m := m); eauto.
      { 
        clear - H5.
        intros.
        unfolds alloc.
        inv H5; simpl.
        eauto.
      }
      {
        intros.
        instantiate (1 := n).
        exists n'.
        unfolds alloc.
        inv H5; simpls.
        destruct H3; subst; tryfalse; eauto.
      }
      {
        instantiate (1 := fm').
        clear - H4 H5.
        unfolds alloc.
        inv H5; simpls.
        eauto.
      }
      {
        change (BufferedAlloc
                  (MemAux.get_block (FLists.get_fl fls n) n') lo hi
                  :: nil) with
        (nil ++ BufferedAlloc
             (MemAux.get_block (FLists.get_fl fls n) n') lo hi
             :: nil) in H2.
        eapply unbuffer_safe_additional_original_still' in H2.
        rewrite tupdate_same_eq in H2; eauto.
      }
    }
    {
      inv H1.
      rewrite tupdate_same_tid_eq.
      lets Hcons : Heql. 
      eapply H0 in Hcons.  
      3 : eauto.
      3 : eauto.
      2 : eauto.
      Focus 3.
      rewrite H5 in H3; simpl in H3.
      rewrite tupdate_b_get; eauto.
      rewrite tupdate_same_tid_eq in Hcons.
      rewrite tupdate_b_get in Hcons.
      eauto.
      rewrite tupdate_b_get; eauto.
      rewrite tupdate_same_tid_eq; eauto.
      clear - Heql H2 H5.
      inv H2; simpls.
      eapply UNBS in H5; eauto.
      rewrite tupdate_same_tid_eq in H5.
      eauto.
      rewrite tupdate_b_get; eauto.
      eauto.
    }
  }
  {
    assert (unbuffer_safe
              {|
                tso_buffers :=
                  tupdate t0 b
                  (tupdate t
                           (bfs t ++
                                BufferedAlloc
                                (MemAux.get_block (FLists.get_fl fls n) n') lo hi
                                :: nil)
                          bfs);
                memory := m'0 |}).
    {  
      clear - H1 H2 H5 n0.
      inv H2; simpls.
      eapply UNBS in H5; eauto.
      rewrite tupdate_not_eq_get; eauto.
    } 
    lets Happly_buf : H6. 
    rewrite tupdate_tid_neq_twice_rev in Happly_buf; eauto.
    eapply TSOMemLemmas.unbuffer_safe_apply_buffer in Happly_buf.
    rewrite tupdate_b_get in Happly_buf.
    destruct Happly_buf as [m'1 Happly_buf].
    assert (Htmp : exists fm2, embed m'1 (FLists.get_fl fls n) fm2).
    {
      specialize (Embed n).
      destruct Embed.
      lets Htt : H5.
      eapply UNBS in H5; eauto.
      inv H5; simpls.
      specialize (Embed n).
      destruct Embed.
      eapply apply_buf_embed_apply_an_item_embed_apply_buf_embed_still with
      (bi := bi) (m0 := m'0) (m := m); eauto.
    }
    destruct Htmp as [fm2 Htmp].
    lets Hcons : H1.   
    eapply H0 in Hcons. 
    3 : eauto.
    2 : eauto.
    2 : eauto.
    Focus 3.
    instantiate (6 := t).
    rewrite in_tbf_upd_oth_stillin; eauto.
    rewrite tupdate_not_eq_get in Hcons; eauto.
    rewrite tupdate_tid_neq_twice_rev in Hcons; eauto.
    rewrite tupdate_not_eq_get; eauto.
    rewrite tupdate_tid_neq_twice_rev; eauto.  
    specialize (Embed n).
    destruct Embed.
    lets Ht : H5.
    eapply UNBS in H5; eauto.
  }
Qed.

Lemma FLs_embed_exec_instr_TSO_preserved :
  forall ge f i rs tm fm rs' bm' fls n t,
    unbuffer_safe (tsoupd tm t (tbuffer bm') (strip (fmemory bm'))) ->
    FLs_embed fls tm ->
    Mem.freelist fm = FLists.get_fl fls n ->
    strip fm = memory tm ->
    exec_instr_TSO ge f i rs {| tbuffer := tso_buffers tm t; fmemory := fm |} = 
    Next rs' bm' ->
    FLs_embed fls (tsoupd tm t (tbuffer bm') (strip (fmemory bm'))).
Proof.
  intros.
  destruct i; simpls; try inv_next; simpls; unfolds tsoupd; simpls; try rewrite H2;
    try solve [rewrite tupdate_same_eq; eauto;
               destruct tm; simpls; eauto];
    try solve [unfolds exec_load_TSO, tsoloadv; ex_match2; try inv_next; simpls;
               rewrite tupdate_same_eq; eauto; destruct tm; simpls;
               try rewrite H2; eauto];
    try solve [unfolds exec_store_TSO, tsostorev, tsostore, buffer_insert;
               ex_match2; try inv_next; try inv_some; simpls; try rewrite H2 in *;
               destruct tm; simpls; eapply FLs_embed_bf_tail_add_store_preserved;
               eauto];
    try solve [unfolds tso_goto_label; ex_match2; try inv_next; simpls;
               try rewrite H2 in *; destruct tm; simpls; rewrite tupdate_same_eq;
               eauto].
  unfolds tsoloadv, tsoload.
  ex_match2; try inv_next; unfolds buffer_insert; simpls.
  try rewrite H2 in *. 
  eapply FLs_embed_buf_tail_add_one_not_alloc_stable; eauto.
  destruct tm; simpls; eauto.
  intro.
  destruct H3 as (b0' & lo & hi & Hcontr); tryfalse.

  ex_match2; try inv_next; simpls; try rewrite tupdate_same_eq in *; eauto.
  eapply FLs_embed_m_vbeq_ub_safe_FLs_embed_stable with (m := memory tm); eauto.
  eapply unbuffer_safe_mem_access_same_stable; eauto.
  unfolds Mem.storev, Mem.store; ex_match2.
  inv Hx1; simpls.
  rewrite Mem_GMem_access_eq, H2; eauto.
  destruct tm; simpls; eauto.
  unfolds Mem.storev, Mem.store; ex_match2.
  inv Hx1; simpls.
  rewrite mem_strip_gm_vb_eq, H2; eauto.

  ex_match2; try inv_next; simpls; try rewrite tupdate_same_eq in *; eauto.
  eapply FLs_embed_m_vbeq_ub_safe_FLs_embed_stable with (m := memory tm); eauto.
  eapply unbuffer_safe_mem_access_same_stable; eauto.
  unfolds Mem.storev, Mem.store; ex_match2.
  inv Hx3; simpls.
  rewrite Mem_GMem_access_eq, H2; eauto.
  destruct tm; simpls; eauto.
  unfolds Mem.storev, Mem.store; ex_match2.
  inv Hx3; simpls.
  rewrite mem_strip_gm_vb_eq, H2; eauto.
  rewrite H2; destruct tm; simpls; eauto.

  ex_match2; try inv_next; simpls; try rewrite tupdate_same_eq in *; eauto.
  eapply FLs_embed_m_vbeq_ub_safe_FLs_embed_stable with (m := memory tm); eauto.
  eapply unbuffer_safe_mem_access_same_stable; eauto.
  unfolds Mem.storev, Mem.store; ex_match2.
  inv Hx2; simpls.
  rewrite Mem_GMem_access_eq, H2; eauto.
  destruct tm; simpls; eauto.
  unfolds Mem.storev, Mem.store; ex_match2.
  inv Hx2; simpls.
  rewrite mem_strip_gm_vb_eq, H2; eauto.
Qed.  

Lemma FLs_embed_tau_step_preserved :
  forall fls ge fl c c' tm b' gm' fp t n,
    unbuffer_safe (tsoupd tm t b' gm') ->
    FLists.wd fls ->
    FLs_embed fls tm -> fl = FLists.get_fl fls n ->
    tsostep ge fl c (tso_buffers tm t, memory tm) fp c' (b', gm') ->
    FLs_embed fls (tsoupd tm t b' gm').
Proof.
  introv Hub_safe.
  intros; subst.
  inv H2.
  inv H7. 
  inv H10; simpls;
    try solve [rewrite H2; unfold tsoupd; rewrite tupdate_same_eq; eauto;
               destruct tm; simpls; eauto].
  (** normal step *)
  {
    eapply FLs_embed_exec_instr_TSO_preserved; eauto.
  }
  (** alloc frame *)
  {
    inv H6.
    unfolds tsostore.
    inv H8; inv H9.
    unfold buffer_insert; simpls.
    unfold tsoupd.
    rewrite H2. 
    assert (FLs_embed fls {| tso_buffers := tso_buffers tm;
                             memory := memory tm |}).
    destruct tm; simpls; eauto.
    rewrite H2 in H14, Hub_safe.
    lets Hub_safe1 : Hub_safe.
    unfold tsoupd in Hub_safe1.
    eapply unbuffer_safe_additional_original_still' in Hub_safe1.
    lets Hub_safe2 : Hub_safe1.
    eapply unbuffer_safe_additional_original_still' in Hub_safe2.
    lets Hub_safe3 : Hub_safe2.
    eapply unbuffer_safe_additional_original_still' in Hub_safe3.
    rewrite tupdate_same_eq in Hub_safe3; eauto.
    assert (Halloc : exists gm'', alloc gm' (Mem.nextblock fm') 0 sz = Some gm'').
    {
      unfold alloc; eauto.
    }
    lets Hembed : H16.
    inv Hembed.
    destruct Halloc as [gm'' Halloc].
    lets Hembed1 : Halloc.
    eapply origin_embed_alloc_nextblock_embed_still in Hembed1; eauto.
    destruct Hembed1.
    eapply FLs_embed_bf_tail_add_alloc_preserved
    with (t := t) (lo := 0%Z) (hi := sz) (m' := gm'') in H6; eauto. 
    eapply FLs_embed_bf_tail_add_store_preserved with (t := t) in H6.
    eapply FLs_embed_bf_tail_add_store_preserved with (t := t) in H6.
    repeat (rewrite tupdate_same_tid_eq in H6).
    repeat (rewrite tupdate_b_get in H6).  
    unfold Mem.nextblock; rewrite H7; eauto.
    repeat (rewrite tupdate_b_get).
    repeat (rewrite tupdate_same_tid_eq); eauto.
    unfolds Mem.nextblock; rewrite <- H7; eauto.
    repeat (rewrite tupdate_b_get).
    repeat (rewrite tupdate_same_tid_eq); eauto.
    unfolds Mem.nextblock; rewrite <- H7; eauto.
    unfolds Mem.nextblock; rewrite <- H7; eauto.
    eapply apply_buffer_cons; eauto.
    unfold apply_buffer, apply_buffer_item.
    unfolds Mem.nextblock.
    rewrite <- H7; rewrite Halloc; simpl; eauto.
  }
  (** initialization *)
  {
    inv H4.
    assert (Halloc1 : exists gm'', alloc gm' (Mem.nextblock fm') 0
                             match z with
                             | 0 => 0
                             | Z.pos y' => Z.pos y'~0~0
                             | Z.neg y' => Z.neg y'~0~0
                             end = Some gm'').
    {
      unfold alloc; eauto.
    }
    destruct Halloc1 as [gm'' Halloc1].
    assert (FLs_embed fls {| tso_buffers := tso_buffers tm;
                             memory := memory tm |}).
    destruct tm; simpls; eauto.
    unfolds tsoupd, store_args_fmem.
    try rewrite H2 in *.
    eapply store_args_rec_fmem_add_store_buf_item in H6. 
    destruct H6 as (bis & Hbf & Hmem & Hstore_item); simpls.
    lets Hembed1 : Halloc1.  
    eapply origin_embed_alloc_nextblock_embed_still in Hembed1; eauto.
    destruct Hembed1.
    eapply FLs_embed_bf_tail_add_alloc_preserved with (m' := gm'') in H4; eauto.
    eapply FLs_embed_buf_tail_add_not_alloc_stable in H4.
    repeat (rewrite tupdate_same_tid_eq in H4).
    repeat (rewrite tupdate_b_get in H4). 
    subst.
    rewrite H2.
    rewrite Hbf.
    repeat (rewrite app_assoc_reverse in * ).
    unfold Mem.nextblock.
    inv H13.
    rewrite <- H6 in H4; eauto.
    rewrite Hbf in Hub_safe; subst.
    rewrite H2 in Hub_safe.
    repeat (rewrite tupdate_b_get).
    repeat (rewrite tupdate_same_tid_eq); eauto.
    unfolds Mem.nextblock. 
    inv H13.
    rewrite <- H6; eauto.
    intros.
    eapply Hstore_item in H6.
    destruct H6 as (c & b & ofs & v & Hstore_item').
    intro.
    destruct H6 as (b' & lo & hi & Halloc).
    subst; tryfalse.
    rewrite Hbf in Hub_safe; subst.
    rewrite H2 in Hub_safe.
    eapply unbuffer_safe_additional_original_still' in Hub_safe; eauto.
    inv H13.
    rewrite <- H6.
    eauto.
    eapply apply_buffer_cons; eauto.
    unfold apply_buffer, apply_buffer_item.
    unfolds Mem.nextblock.
    inv H13.
    rewrite <- H6; rewrite Halloc1; simpl; eauto.
  }
Qed.

Lemma FLs_embed_preserved:
  forall TGE tpc l fp tpc',
    FLists.wd (TSOGlobEnv.freelists TGE) ->    
    FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc) ->
    @tso_globstep TGE tpc l fp tpc' ->
    FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc').
Proof.
  intros.
  inv H1; simpls; eauto.
  (** Core Step *)
  {
    lets Hub_safe' : H_core_step.
    eapply unbuffer_safe_after_tsostep_unbuffer_safe_original in Hub_safe';
      eauto.
    eapply FLs_embed_tau_step_preserved; eauto.
  }
  (** Unbuffer *)
  {
    inv H0.
    unfolds unbuffer.
    ex_match2; simpls.
    inv H_unbuf; simpls.
    eapply UNBS; eauto.
  }
Qed.
  
Lemma tsostep_buffered_alloc_in_fl:
  forall ge fl c buf gm fp c' buf' gm',
    tsostep ge fl c (buf, gm) fp c' (buf', gm') ->
    exists tail, buf' = buf ++ tail /\
            (forall b lo hi, In (BufferedAlloc b lo hi) tail ->
                        exists n, FLists.get_block fl n = b).
Proof.
  clear.
  intros.
  apply TSO_eff in H as [].
  destruct bf_chg.
  exists x;split;auto.
  intros.
  enough(buf<>nil\/buf<>buf'). apply bf_eff in H1.
  unfold BufferEff in H1. Hsimpl.
  rewrite H1 in H.
  apply app_inv_head in H. subst.
  unfold buffer_local_alloc,buffer_item_local_alloc in H3.
  apply H3 in H0. eauto.

  right. rewrite H. intro.
  assert(buf ++ nil = buf ++ x).
  rewrite <-app_nil_end. auto.
  apply app_inv_head in H2. subst. inv H0.
Qed.

Section normal_reorder.
  Variable TGE:TSOGlobEnv.t.
  Hypothesis FLISTWD: FLists.wd (TSOGlobEnv.freelists TGE).
  Local Notation "{ A , B , C  }" := {|thrdpool:=A;cid:=B;tm:=C|}(at level 70,right associativity).
  Local Notation "{-| PC , T }" := ({|thrdpool := thrdpool PC; cid := T;tm := tm PC;|}) (at level 70,right associativity).
  
  Ltac clear_get:=
    repeat (rewrite Maps.PMap.gsspec in *;(destruct Coqlib.peq;subst;try contradiction; simpl in *; subst)).
  Ltac clear_set:=
    repeat (rewrite Maps.PMap.set2 in *;(destruct Coqlib.peq;subst;try contradiction; simpl in *; subst)).
  
  Ltac solv_eq:=
    repeat
      ( match goal with
        | [H1: ?P = _, H2: ?P = _ |- _] =>
          rewrite H1 in H2; inversion H2; clear H1 H2
        | [H1: ?P = _ , H2: _ = ?P |- _] =>
          rewrite H1 in H2; inversion H2; clear H1 H2
        | [H1: _ = ?P, H2: _ = ?P |- _] =>
          rewrite <- H1 in H2; inversion H2; clear H1 H2
        end
      ); 
    try (trivial; fail).
  Ltac solv_thread:=
    repeat
      match goal with
      | H:TSOThrdPool.update _ _ _ _ |- _ => inv H
      | H:TSOThrdPool.halted _ _ |- _ => inv H
      end;
    unfold  TSOThrdPool.pop,  TSOThrdPool.push, TSOThrdPool.valid_tid  in *; simpl in *; subst;
    repeat (rewrite Maps.PMap.gsspec in *;(destruct Coqlib.peq;subst;try contradiction; simpl in *; subst));
    repeat 
      match goal with
        H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try (inversion H; fail)
      | H: Some _ = Some _ |- _ => inversion H; clear H; subst
      | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
      | H:?P = ?Q |- context [ ?P ] => rewrite H 
      end;
    simpl in *;
    solv_eq; eauto;
    clear_set;simpl in *.
  Record inv_cs (cs:  (list (@TSOCore.t TGE))) (i: tid) (next: nat) : Prop :=
    {
      (* - fid in cores belongsto thread i's fid map *)
      fid_belongsto: forall c,
        In c cs ->
        FLists.fbelongsto (TGE.(TSOGlobEnv.freelists)) i c.(TSOCore.F);
      (* - fid are valid w.r.t. [next] *)
      fid_valid: forall c,
          In c cs ->
          exists n, (n < next)%coq_nat /\
               FLists.get_tfid (TGE.(TSOGlobEnv.freelists)) i n = c.(TSOCore.F);
      (* - fid of each core are not equal *)
      fid_disjoint:
        forall n1 n2 (core1 core2: @TSOCore.t TGE),
          nth_error cs n1 = Some core1 ->
          nth_error cs n2 = Some core2 ->
          (TSOCore.F core1) = (TSOCore.F core2) ->
          n1 = n2;
    }.
  Lemma inv_cs_update:
    forall c cs cc c' i n,
      TSOCore.update c cc c'->
      inv_cs (c::cs) i n <->
      inv_cs (c'::cs) i n.
  Proof.
    split.
    {
      intro. inv H0. constructor;intros.
      + inv H0; inv H;simpl;auto;eapply fid_belongsto0;eauto;simpl;auto.
      + inv H0; inv H;simpl;auto;eapply fid_valid0;eauto;simpl;eauto.
      + assert(exists core3, nth_error (c::cs) n1 = Some core3 /\ TSOCore.F core1 = TSOCore.F core3).
        destruct n1. simpl in *. inv H0. exists c;split;auto. inv H;auto.
        simpl in *. exists core1;split;auto.
        assert(exists core4, nth_error (c::cs) n2 = Some core4 /\ TSOCore.F core2 = TSOCore.F core4).
        destruct n2. simpl in *. inv H1. exists c. split;auto.  inv H. auto.
        simpl in *. exists core2;split;auto.
        Hsimpl.
        eapply fid_disjoint0;eauto. congruence.
    }
    {
      intro. constructor;intros.
      - destruct H0 as [? _ _ ].
        destruct H1.
        + subst. specialize (fid_belongsto0 c'). inv H. apply fid_belongsto0;simpl;auto.
        + apply fid_belongsto0. right;auto.
      - destruct H0 as [_ ? _ ].
        destruct H1.
        + subst. specialize (fid_valid0 c'). destruct fid_valid0. left;auto.
          exists x. destruct H0;split;auto. inv H;auto.
        + apply fid_valid0. right;auto.
      - destruct H0 as [_ _ ?].
        assert(exists core3, nth_error (c'::cs) n1 = Some core3 /\ TSOCore.F core1 = TSOCore.F core3).
        destruct n1. simpl in *. inv H1. exists c';split;auto. inv H;auto.
        simpl in *. exists core1;split;auto.
        assert(exists core4, nth_error (c'::cs) n2 = Some core4 /\ TSOCore.F core2 = TSOCore.F core4).
        destruct n2. simpl in *. inv H2. exists c'. split;auto.  inv H. auto.
        simpl in *. exists core2;split;auto.
        Hsimpl.
        eapply fid_disjoint0;eauto. congruence.
    }
  Qed.
  Lemma inv_cs_pop:
    forall c cs i n,
      inv_cs (c::cs) i n->
      inv_cs cs i n.
  Proof.
    intros. constructor;intros.
    1,2:eapply H;right;eauto.
    enough(n1.+1=n2.+1).
    inv H3;auto.
    eapply H;eauto.
  Qed.
  Record inv (thdp: TSOThrdPool.t) : Prop :=
    {
      tp_finite: forall i,
        Pge i thdp.(TSOThrdPool.next_tid) -> PMap.get i thdp.(TSOThrdPool.content) = None;
      tp_valid: forall i,
          Plt i thdp.(TSOThrdPool.next_tid) -> exists cs, PMap.get i thdp.(TSOThrdPool.content) = Some cs;
      (* default val is none *)
      thdp_default: fst thdp.(TSOThrdPool.content) = None;
      (* inv on callstacks and freelists hold *)
      cs_inv: forall i cs,
          PMap.get i thdp.(TSOThrdPool.content) = Some cs ->
          inv_cs cs i (thdp.(TSOThrdPool.next_fmap) i);
    }.
  Lemma inv_update_preserve:
    forall thdp t c cs cc c' thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      TSOCore.update c cc c'->
      TSOThrdPool.update thdp t c' thdp'->
      inv thdp<->inv thdp'.
  Proof.
    split;intros.
    {
      solv_thread.
      inv H2;constructor;simpl;auto;intros.
      apply tp_finite0 in H1.
      rewrite PMap.gsspec. destruct peq;try congruence.
      apply tp_valid0 in H1 as [].
      rewrite PMap.gsspec. destruct peq;eauto.

      rewrite PMap.gsspec in H1.
      destruct peq;auto. subst. inv H1.
      eapply inv_cs_update in H0. apply H0;auto.
    }
    {
      solv_thread.
      inv H2;constructor;simpl;auto;intros;simpl in *.
      apply tp_finite0 in H1. rewrite PMap.gsspec in H1. ex_match.
      apply tp_valid0 in H1. Hsimpl. rewrite PMap.gsspec in H1;ex_match.
      inv H1;eauto. eauto.
      destruct (peq t i). subst. rewrite H in H1;inv H1.
      eapply inv_cs_update;eauto. eapply cs_inv0;eauto.
      rewrite PMap.gss;auto.

      apply cs_inv0. rewrite PMap.gso;auto.
    }
  Qed.
  Lemma inv_push_preserve:
    forall thdp t m sg cc thdp',
      TSOThrdPool.push thdp t m cc sg = Some thdp'->
      inv thdp ->inv thdp'.
  Proof.
    intros.
    {
      solv_thread.
      constructor;simpl;intros.
      - apply H0 in H. rewrite PMap.gsspec. ex_match2.
      - apply H0 in H as []. rewrite PMap.gsspec. ex_match2;eauto.
      - apply H0.
      - ex_match2.
        + subst. rewrite PMap.gss in H. inv H.
          apply H0 in Heqo as ?.
          constructor;intros.
          {
            inv H1. simpl. unfold FLists.fbelongsto. eauto.
            eapply H;eauto.
          }
          {
            inv H1;simpl. eexists;split;eauto. Lia.lia.
            eapply fid_valid in H;eauto.
            destruct H as [?[]]. exists x;split;eauto. Lia.lia.
          }
          {
            destruct n1,n2;simpl in *;auto.
            inv H1. simpl in H3.
            {
              edestruct fid_valid. apply H.
              eapply nth_error_in. eauto.
              destruct H1.
              rewrite <- H4 in H3.
              contradict H3.
              apply FLISTWD.
              Lia.lia.
            }
            {
              edestruct fid_valid. apply H.
              eapply nth_error_in. eauto.
              destruct H4. inv H2.
              rewrite <- H5 in H3. simpl in H3.
              contradict H3.
              apply FLISTWD.
              Lia.lia.
            }
            {
              f_equal. eapply H0;eauto.
            }
          }
        + rewrite PMap.gso in H;auto.
          eapply H0;eauto.
    }
  Qed.
  Lemma inv_pop_preserve:
    forall thdp t thdp',
      TSOThrdPool.pop thdp t = Some thdp'->
      inv thdp->inv thdp'.
  Proof.
    intros.
    solv_thread.
    constructor;simpl;intros.
    apply H0 in H. rewrite PMap.gsspec;ex_match2.
    apply H0 in H. rewrite PMap.gsspec;ex_match2. eauto.
    apply H0.
    rewrite PMap.gsspec in H;ex_match2. subst. inv H.
    apply H0 in Heqo. eapply inv_cs_pop;eauto.
    apply H0;auto.
  Qed.

  Lemma glob_step_inv_preserve:
    forall pc l fp pc',
      tso_globstep pc l fp pc' ->
      inv pc.(thrdpool) ->
      inv pc'.(thrdpool).
  Proof.
    intros.
    inv H;auto.
    eapply inv_update_preserve in H_tp_upd;eauto.
    apply H_tp_upd;auto.

    eapply inv_push_preserve in H_tp_push;eauto.
    eapply inv_pop_preserve in H_tp_pop as ?;eauto.
    eapply inv_update_preserve in H_tp_upd;eauto.
    eapply H_tp_upd;eauto.
    do 2 solv_thread.

    eapply inv_pop_preserve;eauto.
    eapply inv_update_preserve in H_tp_upd;eauto.
    apply H_tp_upd;auto.
  Qed.
  Definition thdp_valid_tid tp t :=
    @TSOThrdPool.valid_tid TGE tp t /\ ~ TSOThrdPool.halted tp t.
  Definition pc_valid_tid pc t:=
    let tp:=pc.(thrdpool) in
    thdp_valid_tid tp t.
  Lemma pc_valid_tid_switchable:
    forall pc t,
      pc_valid_tid pc t <->
      tso_globstep pc sw FP.emp ({-|pc,t}).
  Proof. split;inversion 1;subst. destruct pc;  econstructor;auto. split;auto. Qed.
  Lemma thrd_valid_tid_preserve:
    forall pc l fp pc',
      @tso_globstep TGE pc l fp pc' ->
      forall t,
        TSOThrdPool.valid_tid (thrdpool pc') t<->
        TSOThrdPool.valid_tid (thrdpool pc) t.
  Proof.
    split;intros;inv H;solv_thread.
  Qed.  
  Lemma halted_preserve:
    forall pc l fp pc',
      @tso_globstep TGE pc l fp pc'->
      forall t,
        TSOThrdPool.halted (thrdpool pc) t ->
        TSOThrdPool.halted (thrdpool pc') t.
  Proof. intros;inv H;solv_thread;econstructor;eauto;solv_thread. Qed.
  Lemma halted_preserve2:
    forall pc l fp pc',
      @tso_globstep TGE pc l fp pc'->
      forall t,
        t <> cid pc ->
        TSOThrdPool.halted (thrdpool pc) t <->
        TSOThrdPool.halted (thrdpool pc') t.
  Proof. split; intros;inv H;solv_thread;econstructor;eauto;solv_thread. Qed.
  Lemma pc_valid_tid_preserve:
    forall pc l fp pc',
      @tso_globstep TGE pc l fp pc'->
      forall t,
        t <> cid pc ->
        pc_valid_tid pc' t <-> pc_valid_tid pc t.
  Proof.
    unfold pc_valid_tid,thdp_valid_tid;split;intro;Hsimpl.
    1,2 :split;[eapply thrd_valid_tid_preserve in H;eauto;apply H;auto|intro;contradict H2; eapply halted_preserve2 in H;eauto;apply H;auto].
  Qed.
  Lemma pc_valid_tid_backwards_preserve:
    forall pc l fp pc',
      @tso_globstep TGE pc l fp pc'->
      forall t,
        pc_valid_tid pc' t -> pc_valid_tid pc t.
  Proof.
    unfold pc_valid_tid;intros;Hsimpl;split.
    eapply thrd_valid_tid_preserve in H;eauto. apply H;auto. destruct H0;auto.
    destruct H0.
    intro;contradict H1.  eapply halted_preserve in H;eauto.
  Qed.
  Lemma coreupdate_exists:
    forall c cc,exists c', @TSOCore.update TGE c cc c'.
  Proof. intros. eexists. econstructor;eauto. Qed.
  Lemma thrdpool_update_exists:
    forall thdp t c,
      inv thdp->
      thdp_valid_tid thdp t->
      exists thdp', @TSOThrdPool.update TGE thdp t c thdp'.
  Proof.
    unfold thdp_valid_tid.
    intros.
    Hsimpl.
    apply H in H0. Hsimpl.
    assert(x <> nil). intro;contradict H1;constructor;congruence.
    destruct x;try congruence.
    econstructor;eauto. econstructor;eauto.
  Qed.
  Lemma thrdpool_get_update_preserve:
    forall thdp t c thdp',
      @TSOThrdPool.update TGE thdp t c thdp'->
      forall t',
        t <> t' ->
        (TSOThrdPool.content thdp)!! t' = (TSOThrdPool.content thdp') !!t'.
  Proof. intros. solv_thread. Qed.
  Lemma inv_getable_valid:
    forall thdp t c cs,
      (TSOThrdPool.content thdp)!!t = Some (c::cs) ->
      inv thdp->
      thdp_valid_tid thdp t.
  Proof.
    intros.
    split.
    {
      inv H0.
      unfold TSOThrdPool.valid_tid.
      destruct (plt t (TSOThrdPool.next_tid thdp));auto.
      apply tp_finite0 in n. rewrite n in H;inv H.
    }
    {
      intro.
      inv H1. rewrite H in H2. inv H2.
    }
  Qed.

  Lemma tupdate_comm:
    forall bfs t bf' t' bf'',
      t <> t' ->
      tupdate t bf' (tupdate t' bf'' bfs) =
      tupdate t' bf'' (tupdate t bf' bfs).
  Proof.
    unfold tupdate;intros.
    apply functional_extensionality.
    intro.
    ex_match2;auto.
  Qed.
  Lemma ptree_set_sym:
    forall A i j m (v1 v2:A),
      i <> j ->
      Maps.PTree.set i v1 (Maps.PTree.set j v2 m) =
      Maps.PTree.set j v2 (Maps.PTree.set i v1 m).
  Proof. induction i;intros;destruct m,j;simpl;auto;try (rewrite IHi;auto;intro;subst);contradiction. Qed.
  Lemma pmap_set_sym:
    forall (A : Type) (i j : positive) (m : PMap.t A) (v1 v2 : A),
      i <> j -> PMap.set i v1 (PMap.set j v2 m) = PMap.set j v2 (PMap.set i v1 m).
  Proof. unfold Maps.PMap.set;simpl;intros;f_equal. eapply ptree_set_sym;eauto. Qed.
  Lemma update_update_sym:
    forall thdp t c cs cc c' thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      TSOCore.update c cc c' ->
      @TSOThrdPool.update TGE thdp t c' thdp' ->
      forall t0 c0 cs0 cc0 c0' thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0)->
        TSOCore.update c0 cc0 c0' ->
        TSOThrdPool.update thdp' t0 c0' thdp'' ->
        (TSOThrdPool.content thdp)!!t0 = Some (c0::cs0)/\
        exists thdp1, TSOThrdPool.update thdp t0 c0' thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs) /\
                 TSOThrdPool.update thdp1 t c' thdp''.
  Proof.
    intros;Esimpl;[|econstructor;eauto| |];solv_thread;solv_thread;eauto.
    destruct peq;congruence.
    econstructor;simpl;eauto. solv_thread.
    erewrite pmap_set_sym;eauto.
  Qed.
  Lemma update_push_sym:
    forall thdp t c cs cc c' thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      TSOCore.update c cc c' ->
      @TSOThrdPool.update TGE thdp t c' thdp' ->
      forall t0 c0 cs0 new_ix cc sg thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0) ->
        TSOThrdPool.push thdp' t0 new_ix cc sg = Some thdp''->
        (TSOThrdPool.content thdp)!!t0 = Some (c0::cs0) /\
        exists thdp1, TSOThrdPool.push thdp t0 new_ix cc sg = Some thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs) /\ 
                 TSOThrdPool.update thdp1 t c' thdp''.
  Proof.
    intros.
    Esimpl;solv_thread;solv_thread;eauto. econstructor;solv_thread;eauto.
    erewrite pmap_set_sym;eauto.
  Qed.

  Lemma update_pop_sym:
    forall thdp t c cs cc c' thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      TSOCore.update c cc c' ->
      @TSOThrdPool.update TGE thdp t c' thdp' ->
      forall t0 c0 cs0 thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0) ->
        TSOThrdPool.pop thdp' t0 = Some thdp''->
        (TSOThrdPool.content thdp)!!t0 = Some (c0::cs0) /\
        exists thdp1, TSOThrdPool.pop thdp t0 = Some thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs) /\ 
                 TSOThrdPool.update thdp1 t c' thdp''.
  Proof.
    intros.
    Esimpl;solv_thread;solv_thread;eauto.
    econstructor;eauto;solv_thread.
    erewrite pmap_set_sym;eauto.
  Qed.
  Lemma update__pop_update_sym:
    forall thdp t c cs cc c' thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      TSOCore.update c cc c' ->
      @TSOThrdPool.update TGE thdp t c' thdp' ->
      forall t0 c0 c1 cs0 thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::c1::cs0) ->
        TSOThrdPool.pop thdp' t0 = Some thdp''->
        forall cc1 c1' thdp''',
          TSOCore.update c1 cc1 c1'->
          TSOThrdPool.update thdp'' t0 c1' thdp'''->
          (TSOThrdPool.content thdp)!!t0 = Some (c0::c1::cs0) /\
          exists thdp1,
            TSOThrdPool.pop thdp t0 = Some thdp1 /\
            exists thdp2,
              TSOThrdPool.update thdp1 t0 c1' thdp2 /\
              (TSOThrdPool.content thdp2)!!t = Some (c::cs) /\
              TSOThrdPool.update thdp2 t c' thdp'''.
  Proof.
    intros.
    eapply update_pop_sym in H0 as ?;try exact H4;eauto.
    Hsimpl.
    assert((TSOThrdPool.content thdp'')!!t0=Some (c1::cs0)).
    revert H3 H4. clear. intros.
    solv_thread. solv_thread.
    eapply update_update_sym in H6 as ?;try exact H10;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.
  Lemma push_update_sym:
    forall thdp t c cs new_ix cc sg thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.push TGE thdp t new_ix cc sg = Some thdp'->
      forall t0 c0 cs0 cc0 c0' thdp'',
        t <> t0->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0) ->
        TSOCore.update c0 cc0 c0' ->
        @TSOThrdPool.update TGE thdp' t0 c0' thdp'' ->
        (TSOThrdPool.content thdp)!!t0 = Some (c0::cs0) /\
        exists thdp1, TSOThrdPool.update thdp t0 c0' thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs) /\ 
                 TSOThrdPool.push thdp1 t new_ix cc sg = Some thdp''.
  Proof.
    intros.
    Esimpl;[|econstructor;eauto| |]; solv_thread;eauto; solv_thread; eauto.
    erewrite pmap_set_sym;eauto.
  Qed.
  Lemma push_push_sym:
    forall thdp t c cs new_ix cc sg thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.push TGE thdp t new_ix cc sg = Some thdp'->
      forall t0 c0 cs0 new_ix0 cc0 sg0 thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0)->
        TSOThrdPool.push thdp' t0 new_ix0 cc0 sg0 = Some thdp''->
        (TSOThrdPool.content thdp)!!t0 = Some (c0::cs0) /\
        exists thdp1, TSOThrdPool.push thdp t0 new_ix0 cc0 sg0 = Some thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs)/\
                 TSOThrdPool.push thdp1 t new_ix cc sg = Some thdp''.
  Proof.
    intros.
    split. solv_thread. solv_thread.
    eexists. split. solv_thread;solv_thread.
    split;simpl; solv_thread. solv_thread.
    do 2 f_equal. destruct peq;try contradiction. rewrite pmap_set_sym;auto.
    apply functional_extensionality;intros.
    ex_match2. subst. contradiction.
  Qed.
  Lemma push_pop_sym:
    forall thdp t c cs new_ix cc sg thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.push TGE thdp t new_ix cc sg = Some thdp'->
      forall t0 c0 cs0 thdp'',
        t <> t0->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0)->
        TSOThrdPool.pop thdp' t0 = Some thdp''->
        (TSOThrdPool.content thdp)!!t0=Some (c0::cs0)/\
        exists thdp1, TSOThrdPool.pop thdp t0 = Some thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs) /\
                 TSOThrdPool.push thdp1 t new_ix cc sg = Some thdp''.
  Proof.
    intros.
    split. do 2 solv_thread.
    Esimpl. do 2 solv_thread. simpl. solv_thread.
    solv_thread.
    rewrite pmap_set_sym;auto.
  Qed.

  Lemma pop_update_sym:
    forall thdp t c cs thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.pop TGE thdp t= Some thdp'->
      forall t0 c0 cs0 cc0 c0' thdp'',
        t <> t0->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0) ->
        TSOCore.update c0 cc0 c0' ->
        @TSOThrdPool.update TGE thdp' t0 c0' thdp'' ->
        (TSOThrdPool.content thdp)!!t0 = Some (c0::cs0)/\
        exists thdp1, TSOThrdPool.update thdp t0 c0' thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs) /\ 
                 TSOThrdPool.pop thdp1 t = Some thdp''.
  Proof.
    intros.
    Esimpl;[|econstructor;eauto| |];do 2 solv_thread.
    rewrite pmap_set_sym;eauto.
  Qed.
  Lemma pop_push_sym:
    forall thdp t c cs thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.pop TGE thdp t= Some thdp'->
      forall t0 c0 cs0 new_ix0 cc0 sg0 thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0)->
        TSOThrdPool.push thdp' t0 new_ix0 cc0 sg0 = Some thdp''->
        (TSOThrdPool.content thdp)!!t0 = Some (c0::cs0) /\
        exists thdp1, TSOThrdPool.push thdp t0 new_ix0 cc0 sg0 = Some thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs)/\
                 TSOThrdPool.pop thdp1 t = Some thdp''.
  Proof.
    intros.
    Esimpl. do 2 solv_thread.
    do 2 solv_thread. simpl. solv_thread.
    solv_thread. rewrite pmap_set_sym;auto.
  Qed.
  Lemma pop_pop_sym:
    forall thdp t c cs thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.pop TGE thdp t= Some thdp'->
      forall t0 c0 cs0 thdp'',
        t <> t0->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::cs0)->
        TSOThrdPool.pop thdp' t0 = Some thdp''->
        (TSOThrdPool.content thdp)!!t0=Some (c0::cs0)/\
        exists thdp1, TSOThrdPool.pop thdp t0 = Some thdp1 /\
                 (TSOThrdPool.content thdp1)!!t = Some (c::cs) /\
                 TSOThrdPool.pop thdp1 t = Some thdp''.
  Proof.
    intros.
    Esimpl. do 2 solv_thread.
    do 2 solv_thread. simpl. solv_thread.
    solv_thread. rewrite pmap_set_sym;auto.
  Qed.
  Lemma push__pop_update_sym:
    forall thdp t c cs new_ix cc sg thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.push TGE thdp t new_ix cc sg = Some thdp'->
      forall t0 c0 c1 cs0 thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::c1::cs0) ->
        TSOThrdPool.pop thdp' t0 = Some thdp''->
        forall cc1 c1' thdp''',
          TSOCore.update c1 cc1 c1'->
          TSOThrdPool.update thdp'' t0 c1' thdp'''->
          (TSOThrdPool.content thdp)!!t0 = Some (c0::c1::cs0) /\
          exists thdp1,
            TSOThrdPool.pop thdp t0 = Some thdp1 /\
            exists thdp2,
              TSOThrdPool.update thdp1 t0 c1' thdp2 /\
              (TSOThrdPool.content thdp2)!!t = Some (c::cs) /\
              TSOThrdPool.push thdp2 t new_ix cc sg = Some thdp'''.
  Proof.
    intros.
    eapply push_pop_sym in H0 as ?;eauto.
    Hsimpl.
    assert( (TSOThrdPool.content thdp'') !! t0 = Some (c1 ::cs0)).
    revert H2 H3;clear;intros;do 2 solv_thread.
    eapply push_update_sym in H9;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.
  Lemma pop__pop_update_sym:
    forall thdp t c cs thdp',
      (TSOThrdPool.content thdp)!!t = Some (c::cs)->
      @TSOThrdPool.pop TGE thdp t = Some thdp'->
      forall t0 c0 c1 cs0 thdp'',
        t <> t0 ->
        (TSOThrdPool.content thdp')!!t0 = Some (c0::c1::cs0) ->
        TSOThrdPool.pop thdp' t0 = Some thdp''->
        forall cc1 c1' thdp''',
          TSOCore.update c1 cc1 c1'->
          TSOThrdPool.update thdp'' t0 c1' thdp'''->
          (TSOThrdPool.content thdp)!!t0 = Some (c0::c1::cs0) /\
          exists thdp1,
            TSOThrdPool.pop thdp t0 = Some thdp1 /\
            exists thdp2,
              TSOThrdPool.update thdp1 t0 c1' thdp2 /\
              (TSOThrdPool.content thdp2)!!t = Some (c::cs) /\
              TSOThrdPool.pop thdp2 t = Some thdp'''.
  Proof.
    intros.
    eapply pop_pop_sym in H3 as ?;try exact H0;eauto.
    Hsimpl.
    assert( (TSOThrdPool.content thdp'') !! t0 = Some (c1 ::cs0)).
    revert H2 H3;clear;intros;do 2 solv_thread.
    eapply pop_update_sym in H9;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.
  Lemma pop_update__update_sym:
    forall thdp t c0 c1 cs0 thdp',
      (TSOThrdPool.content thdp)!!t = Some (c0::c1::cs0)->
      TSOThrdPool.pop thdp t = Some thdp'->
      forall cc c1' thdp'',
        TSOCore.update c1 cc c1'->
        TSOThrdPool.update thdp' t c1' thdp''->
        forall t0 cc0 c cs c' thdp''',
          t <> t0->
          (TSOThrdPool.content thdp'')!!t0 = Some (c::cs)->
          TSOCore.update c cc0 c'->
          TSOThrdPool.update thdp'' t0 c' thdp'''->
          (TSOThrdPool.content thdp)!!t0 = Some (c::cs) /\
          exists thdp1,
            TSOThrdPool.update thdp t0 c' thdp1 /\
            (TSOThrdPool.content thdp1)!!t = Some(c0::c1::cs0)/\
            exists thdp2,
              TSOThrdPool.pop thdp1 t = Some thdp2 /\
              @TSOThrdPool.update TGE thdp2 t c1' thdp'''.
  Proof.
    intros.
    assert((TSOThrdPool.content thdp')!!t = Some (c1::cs0)).
    revert H H0;clear;intros;do 2 solv_thread.
    eapply update_update_sym in H6 as ?;try exact H2;eauto.
    Hsimpl.
    eapply pop_update_sym in H0 as ?;try exact H9;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.
  Lemma pop_update__push_sym:
    forall thdp t c0 c1 cs0 thdp',
      (TSOThrdPool.content thdp)!!t = Some (c0::c1::cs0)->
      TSOThrdPool.pop thdp t = Some thdp'->
      forall cc c1' thdp'',
        TSOCore.update c1 cc c1'->
        TSOThrdPool.update thdp' t c1' thdp''->
        forall t0 cc0 c cs new_ix sg thdp''',
          t <> t0->
          (TSOThrdPool.content thdp'')!!t0 = Some (c::cs)->
          TSOThrdPool.push thdp'' t0 new_ix cc0 sg = Some thdp'''->
          (TSOThrdPool.content thdp)!!t0 = Some (c::cs) /\
          exists thdp1,
            TSOThrdPool.push thdp t0 new_ix cc0 sg = Some thdp1 /\
            (TSOThrdPool.content thdp1)!!t = Some(c0::c1::cs0)/\
            exists thdp2,
              TSOThrdPool.pop thdp1 t = Some thdp2 /\
              @TSOThrdPool.update TGE thdp2 t c1' thdp'''.
  Proof.
    intros.
    assert((TSOThrdPool.content thdp')!!t = Some (c1::cs0)).
    revert H H0;clear;intros;do 2 solv_thread.
    eapply update_push_sym in H5 as ?;try exact H2;eauto.
    Hsimpl.
    eapply pop_push_sym in H0 as ?;try exact H9;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.
  Lemma pop_update__pop_sym:
    forall thdp t c0 c1 cs0 thdp',
      (TSOThrdPool.content thdp)!!t = Some (c0::c1::cs0)->
      TSOThrdPool.pop thdp t = Some thdp'->
      forall cc c1' thdp'',
        TSOCore.update c1 cc c1'->
        TSOThrdPool.update thdp' t c1' thdp''->
        forall t0 c cs thdp''',
          t <> t0->
          (TSOThrdPool.content thdp'')!!t0 = Some (c::cs)->
          TSOThrdPool.pop thdp'' t0 = Some thdp'''->
          (TSOThrdPool.content thdp)!!t0 = Some (c::cs) /\
          exists thdp1,
            TSOThrdPool.pop thdp t0 = Some thdp1 /\
            (TSOThrdPool.content thdp1)!!t = Some(c0::c1::cs0)/\
            exists thdp2,
              TSOThrdPool.pop thdp1 t = Some thdp2 /\
              @TSOThrdPool.update TGE thdp2 t c1' thdp'''.
  Proof.
    intros.
    assert((TSOThrdPool.content thdp')!!t = Some (c1::cs0)).
    revert H H0;clear;intros;do 2 solv_thread.
    eapply update_pop_sym in H5 as ?;try exact H2;eauto.
    Hsimpl.
    eapply pop_pop_sym in H8 as ?;try exact H0;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.
  Lemma pop_update__pop_update_sym:
    forall thdp t c0 c1 cs0 thdp',
      (TSOThrdPool.content thdp)!!t = Some (c0::c1::cs0)->
      TSOThrdPool.pop thdp t = Some thdp'->
      forall cc c1' thdp'',
        TSOCore.update c1 cc c1'->
        TSOThrdPool.update thdp' t c1' thdp''->
        forall t0 c2 c3 cs thdp''',
          t <> t0->
          (TSOThrdPool.content thdp'')!!t0 = Some (c2::c3::cs)->
          TSOThrdPool.pop thdp'' t0 = Some thdp'''->
          forall cc0 c3' thdp'''',
            TSOCore.update c3 cc0 c3'->
            @TSOThrdPool.update TGE thdp''' t0 c3' thdp''''->
            (TSOThrdPool.content thdp)!!t0 = Some (c2::c3::cs) /\
            exists thdp1,
              TSOThrdPool.pop thdp t0 = Some thdp1 /\
              exists thdp2, TSOThrdPool.update thdp1 t0 c3' thdp2 /\
                       (TSOThrdPool.content thdp2)!!t=Some(c0::c1::cs0) /\
                       exists thdp3,TSOThrdPool.pop thdp2 t = Some thdp3 /\
                               TSOThrdPool.update thdp3 t c1' thdp''''.
  Proof.
    intros.
    assert((TSOThrdPool.content thdp')!!t= Some (c1::cs0)).
    revert H H0;clear;intros;do 2 solv_thread.
    assert((TSOThrdPool.content thdp''')!!t0 = Some(c3::cs)).
    revert H4 H5;clear;intros;do 2 solv_thread.
    eapply update_pop_sym in H2 as ?;try exact H5;eauto.
    Hsimpl.
    eapply update_update_sym in H7 as ?;try exact H12;eauto.
    Hsimpl.

    eapply pop_pop_sym in H11 as ?;try exact H0;eauto.
    Hsimpl.
    eapply pop_update_sym in H21 as ?;try exact H15;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.
  Lemma eq_config_but_cid_idchange:
    forall pc t,
      @eq_config_but_cid TGE pc ({-|pc,t}).
  Proof. constructor;auto. apply GMem.eq_refl. Qed.

  Lemma diff_thrd_normal_step_reorder':
    forall (tpc1 tpc1' tpc2 tpc2': @TSOProgConfig TGE) l1 fp1 l2 fp2
      (INVTHDP1: inv tpc1.(thrdpool)),
      normal_tsoglabel l1 ->
      tso_globstep tpc1 l1 fp1 tpc1' ->
      cid tpc1' <> cid tpc2 ->
      tso_globstep tpc1' sw FP.emp tpc2 ->
      normal_tsoglabel l2 ->
      tso_globstep tpc2 l2 fp2 tpc2' ->
      FP.smile fp1 fp2 ->
      exists _tpc2 _tpc2' _tpc1 _tpc1',
        tso_globstep tpc1 sw FP.emp _tpc2 /\
        cid _tpc2 = cid tpc2 /\
        tso_globstep _tpc2 l2 fp2 _tpc2' /\
        tso_globstep _tpc2' sw FP.emp _tpc1 /\
        cid _tpc1 = cid tpc1 /\
        tso_globstep _tpc1 l1 fp1 _tpc1' /\
        @eq_config_but_cid TGE tpc2'  _tpc1'.
  Proof.
    {
      intros until fp2.
      intros INVTHDP1 ? ?.
      eapply glob_step_inv_preserve in INVTHDP1 as INVTHDP2 ;eauto.
      intros.
      pose proof H0 as STEP1. pose proof H4 as STEP2.
      inv H0;inv H2;inv H4;simpl in *;try contradiction.
      {
        (*core step*)
        exploit TSO_one_step_reorder'.
        exact H_core_step. exact H_core_step0.
        {
          eapply unbuffer_safe_buffer_safe with(t:=t) in H_unbuf_safe0 as R.
          simpl in R. unfold tupdate in R. ex_match2.
          
          apply TSO_bf_add in H_core_step as R1.
          destruct R1. rewrite H0 in R.
          destruct R. apply apply_buffer_split in H2. Hsimpl.
          exists x1. eauto.
        }
        {
          exploit unbuffer_safe_after_tsostep_unbuffer_safe_original.
          apply H_core_step. auto.
          intro.
          eapply unbuffer_safe_buffer_safe with(t:=t') in H0.
          simpl. unfold tupdate. ex_match2.
        }
        {
          exploit fid_belongsto.
          eapply INVTHDP1;eauto. simpl;auto.
          intro.
          exploit fid_belongsto.
          eapply INVTHDP2; eauto. simpl;auto.
          intro.
          unfold FLists.fbelongsto in H0,H2. Hsimpl.
          eapply FLISTWD. rewrite <-H0,<-H2.
          eapply FLISTWD;auto.
        }
        auto.
        intros. Hsimpl.
        unfold tsoupd in H0. simpl in H0.
        unfold tupdate in H0. ex_match2.
        assert(pc_valid_tid  ({thdp', t', tsoupd tm t buf' gm' }) t').
        split;auto.
        eapply pc_valid_tid_backwards_preserve in STEP1 as ?;eauto.
        pose proof thrdpool_update_exists thdp t' c'0 INVTHDP1 H7 as [thdp1 UPD1].
        set ({thdp,t',tm}) as _tpc0.
        set ({thdp1, t', tsoupd tm t' buf'0 x}) as _tpc0'.
        set ({thdp1, t, tsoupd tm t' buf'0 x}) as _tpc1.

        pose proof thrdpool_get_update_preserve thdp t' c'0 thdp1 UPD1 t n.
        rewrite H_tp_core in H8. symmetry in H8.
        exploit inv_update_preserve;try exact UPD1;eauto.
        solv_thread.
        intro R.
        apply R in INVTHDP1 as INVTHDP3.
        (*need to construct the second step first to prove unbuffer-safe*)
        pose proof inv_getable_valid _  _ _ _ H8 INVTHDP3.
        exploit thrdpool_update_exists.
        exact INVTHDP3. exact H9.
        instantiate(1:=c').
        intros[thdp2 UPD2].
        
        pose proof gmem_eq_ub_safe_eq _ _ _ H4 H_unbuf_safe0.
        simpl in H10. rewrite tupdate_comm in H10;auto.
        assert(tsoupd (tsoupd tm t' buf'0 x) t buf' x0 =
               {|
                 tso_buffers := tupdate t buf'
                                        (tupdate t' buf'0 (tso_buffers tm));
                 memory := x0 |}).
        auto.
        rewrite<- H11 in H10. clear H11.

        set ( {thdp2,t,tsoupd (tsoupd tm t' buf'0 x) t buf' x0}) as _tpc2.
        assert(tso_globstep _tpc1 tau fp1 _tpc2).
        {
          econstructor;eauto.
          unfold tsoupd. simpl.
          rewrite tupdate_not_eq_get;auto.
        }
        exploit unbuffer_safe_after_tsostep_unbuffer_safe_original.
        2: exact H10.
        simpl. unfold tupdate. destruct (peq t t');try contradiction; eauto.
        intro.
        exists _tpc0 _tpc0' _tpc1 _tpc2.
        split. unfold _tpc0. destruct H7; econstructor;eauto.
        split;auto.
        split.
        unfold _tpc0,_tpc0'.
        econstructor;eauto. solv_thread.
        split. destruct H9;unfold _tpc0',_tpc1;econstructor;eauto.
        split;auto.
        split;auto.
        unfold _tpc2.
        constructor;auto. simpl.
        clear Hx.
        revert UPD2 UPD1 H_tp_upd H_tp_upd0 n. clear.
        intros.
        solv_thread.
        rewrite pmap_set_sym;auto.
        simpl. rewrite tupdate_comm;auto.
      }
      {
        exploit update_push_sym;try exact H_core_upd;eauto.
        intro;Hsimpl.
        Esimpl.
        econstructor;eauto. solv_thread. intro;contradict H_not_halted;solv_thread.
        auto.
        eapply Call;eauto.
        apply pc_valid_tid_switchable.
        instantiate(1:=t).
        eapply inv_getable_valid;eauto.
        eapply inv_push_preserve;eauto.
        auto.
        econstructor;eauto.
        apply eq_config_but_cid_idchange.
      }
      {
        exploit update__pop_update_sym.
        exact H_tp_core.
        all: try eauto.
        intro;Hsimpl;Esimpl.
        econstructor;eauto. solv_thread. intro;contradict H_not_halted;solv_thread.
        auto.
        eapply Return;eauto.
        apply pc_valid_tid_switchable.
        instantiate(1:=t).
        eapply inv_getable_valid. simpl. eauto.
        assert((TSOThrdPool.content x)!!t'=Some (c'0::cs0)).
        revert H2 H0. clear. intros. solv_thread. solv_thread.
        eapply inv_update_preserve in H4;eauto.
        apply H4.
        eapply inv_pop_preserve;eauto.
        
        auto.
        econstructor;eauto. apply eq_config_but_cid_idchange.
      }
      {
        exploit update_pop_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable. eapply inv_getable_valid;eauto.
        auto.
        eapply Halt;eauto.
        apply pc_valid_tid_switchable. eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve;eauto.
        auto.
        econstructor;eauto. apply eq_config_but_cid_idchange.
      }
      {
        exploit update_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply EF_Print;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        econstructor;eauto. apply eq_config_but_cid_idchange.
      }
      {
        exploit push_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply Call;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit push_push_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Call;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_push_preserve in H2;eauto.
        auto.
        eapply Call;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit push__pop_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Return;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        assert((TSOThrdPool.content x)!!t' = Some (c'::cs0)).
        revert H0 H2;clear;intros;do 2 solv_thread.
        eapply inv_update_preserve in H4 as ?;eauto.
        apply H10;auto.
        auto.
        eapply Call;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit push_pop_sym.
        exact H_tp_core. all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Halt;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        auto.
        eapply Call;eauto. simpl;apply eq_config_but_cid_idchange.
      }
      {
        exploit push_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply Call;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_update__update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply Return;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_update__push_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Call;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_push_preserve in H2;eauto.
        auto.
        eapply Return;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_update__pop_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Return;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        assert((TSOThrdPool.content x)!!t' = Some (c'0::cs0)).
        revert H0 H2;clear;intros;do 2 solv_thread.
        eapply inv_update_preserve in H4 as ?;eauto.
        apply H11;auto.
        auto.
        eapply Return;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_update__pop_sym.
        exact H_tp_core. all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Halt;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        auto.
        eapply Return;eauto. simpl;apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_update__update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply Return;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply Halt;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_push_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Call;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_push_preserve in H2;eauto.
        auto.
        eapply Halt;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop__pop_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Return;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        assert((TSOThrdPool.content x)!!t' = Some (c'::cs)).
        revert H0 H2;clear;intros;do 2 solv_thread.
        eapply inv_update_preserve in H4 as ?;eauto.
        apply H10;auto.
        auto.
        eapply Halt;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_pop_sym.
        exact H_tp_core. all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Halt;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        auto.
        eapply Halt;eauto. simpl;apply eq_config_but_cid_idchange.
      }
      {
        exploit pop_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply Halt;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit update_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply EF_Print;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit update_push_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Call;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_push_preserve in H2;eauto.
        auto.
        eapply EF_Print;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit update__pop_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Return;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        assert((TSOThrdPool.content x)!!t' = Some (c'0::cs0)).
        revert H0 H2;clear;intros;do 2 solv_thread.
        eapply inv_update_preserve in H4 as ?;eauto.
        apply H10;auto.
        auto.
        eapply EF_Print;eauto. simpl. apply eq_config_but_cid_idchange.
      }
      {
        exploit update_pop_sym.
        exact H_tp_core. all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        eapply Halt;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_pop_preserve in H2 as ?;eauto.
        auto.
        eapply EF_Print;eauto. simpl;apply eq_config_but_cid_idchange.
      }
      {
        exploit update_update_sym.
        exact H_tp_core.
        all:eauto.
        intros;Hsimpl;Esimpl.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        auto.
        econstructor;eauto.
        apply pc_valid_tid_switchable;eapply inv_getable_valid;eauto.
        eapply inv_update_preserve in H2;eauto. apply H2;auto.
        auto.
        eapply EF_Print;eauto. simpl. apply eq_config_but_cid_idchange.
      }
    }
  Qed.
  Lemma FLs_embed_apply_buffer_preserve:
    forall tm fls,
      FLs_embed fls tm ->
      forall bf t gm,
        tso_buffers tm t = bf ->
        apply_buffer bf (memory tm) = Some gm->
        FLs_embed fls (tsoupd tm t nil gm).
  Proof.
    intros until t. revert tm fls H.
    induction bf;intros.
    simpl in *. inv_some.
    assert(tsoupd tm t nil (memory tm) = tm).
    unfold tsoupd,tupdate. destruct tm;simpl in *. f_equal.
    eapply functional_extensionality;intro.
    ex_match2. congruence.

    simpl in *. unfold optbind in H1. ex_match.
    inv H.
    eapply UNBS in Hx;eauto.
    assert(tso_buffers ({|tso_buffers:=tupdate t bf (tso_buffers tm);memory:=g|}) t = bf). unfold tupdate;simpl;ex_match2.
    eapply IHbf in H;eauto.
    simpl in *. unfold tsoupd in H|-*. simpl in *.
    rewrite tupdate_same_tid_eq in H.
    auto.
  Qed.
  Definition buffer_local_alloc (t:tid)(bf:buffer):=
    forall bi, In bi bf -> exists n, buffer_item_local_alloc bi (FLists.get_fl (TSOGlobEnv.freelists TGE)(FLists.thread_flmap (TSOGlobEnv.freelists TGE) t n)).
  Lemma thread_buffered_alloc_local_buffer_local_alloc:
    forall tm,
      (forall t b lo hi,
          In (BufferedAlloc b lo hi) (tso_buffers tm t) ->
          exists fn n,
            let fl := FLists.get_tfl  (TSOGlobEnv.freelists TGE) t fn in
            b = FLists.get_block fl n) ->
      forall t, buffer_local_alloc t (tso_buffers tm t).
  Proof.
    unfold buffer_local_alloc,buffer_item_local_alloc;intros.
    destruct bi.
    2,3: exists 0%nat;auto.
    apply H in H0. Hsimpl.
    unfold buffer_item_local_alloc.
    rewrite H0. exists x.
    unfold FLists.get_fl,FLists.get_tfl,FLists.get_block,MemAux.in_fl. eexists;eauto.
  Qed.
  Lemma buffer_local_alloc_preserve:
    forall t tpc fp tpc',
      tso_globstep tpc tau fp tpc'->
      buffer_local_alloc t (tso_buffers (tm tpc) t)->
      inv (thrdpool tpc)->
      FLists.wd (TSOGlobEnv.freelists TGE)->
      buffer_local_alloc t (tso_buffers (tm tpc') t).
  Proof.
    intros.
    inv H;auto.
    simpl in *.
    unfold tupdate;ex_match2;auto.
    subst.
    apply TSO_eff in H_core_step.
    destruct H_core_step.
    destruct (eff_chg (tso_buffers tm t0) buf') eqn:?.
    apply eff_chg_t in Heqb as [];subst;auto.
    apply eff_chg_f in Heqb. clear bf_chg.
    unfold BufferEff in bf_eff;Hsimpl;subst.
    revert H0 H4 H1 H_tp_core;clear.
    unfold buffer_local_alloc,TSOAuxDefs.buffer_local_alloc.
    intros.
    apply in_app_or in H. destruct H;eauto.
    specialize (H4 _ H).
    inv H1. specialize (cs_inv0 _ _ H_tp_core).
    inv cs_inv0.
    edestruct fid_valid0. left;eauto.
    Hsimpl. rewrite <- H2 in H4. eauto.
  Qed.
  Lemma diff_thrd_normal_unbuffer_step_reorder':
    forall (tpc tpc' tpc'': @TSOProgConfig TGE) l fp t'
      (FLEMBED:FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc))
      (INVTHDP1: inv tpc.(thrdpool))
      (LALLOC:buffer_local_alloc t' ((tpc'.(tm).(tso_buffers) t'))),
      let t := cid tpc in
      ~ conflictc t fp (tso_buffers (tm tpc)) ->
      normal_tsoglabel l ->
      tso_globstep tpc l fp tpc' ->
      t <> t' ->
      tso_globstep tpc' (ub t') FP.emp tpc'' ->
      exists tpc0 tpc1,
        tso_globstep tpc (ub t') FP.emp tpc0 /\
        tso_globstep tpc0 l fp tpc1 /\
        eq_config TGE tpc'' tpc1.
  Proof.
    intros.
    unfold t in *. clear t.
    pose proof H3 as STEP2.
    pose proof H1 as STEP1.
    inv H3;inv H1;tryfalse.
    {
      unfold unbuffer in H_unbuf.
      ex_match. inv_some.
      simpl in *.
      unfold tupdate in Hx.
      ex_match2.
      assert(FPNCFLICT:~ FP.conflict fp (bi_footprint b)).
      intro;contradict H.
      econstructor;eauto. rewrite Hx;left;auto.

      set (FLists.get_fl (TSOGlobEnv.freelists TGE)(TSOCore.F c)) as fl in *.
      set (TSOGlobEnv.modules TGE (TSOCore.i c)) as ge in *.
      apply tsostep_lock_or_notlock in H_core_step as R.
      destruct R.
      {
        assert(tso_buffers tm0 t = nil /\ buf' = nil). inv H1;auto.
        destruct H3;subst.
        rewrite H3 in *.
        assert(LEffect (memory tm0) gm' fp fl).
        apply TSO_eff in H_core_step as ?.
        eapply H4;eauto.
        destruct H4 as [EFF1 LOCALALLOC1].
        eapply MemEffect_fpsmile_MemPre_Rule in EFF1 as PRE1;[|apply FP.smile_conflict_compat;eauto].

        eapply buf_item_unbuf_locality_1 in PRE1 as UNBUF1;eauto.
        destruct UNBUF1 as [m1 [UB1 POST1]].

        apply apply_buf_item_MemEffect in UB1 as EFF2.
        eapply MemEffect_fpsmile_MemPre_Rule in EFF2 as PRE2;[|apply FPLemmas.fpsmile_sym;apply FP.smile_conflict_compat;eauto].

        assert(exists fm,embed m1 fl fm).
        inversion FLEMBED;subst.
        eapply UNBS in UB1 as ?;eauto.
        inv H4. eapply Embed0;eauto.
        Hsimpl.


        edestruct LALLOC as [? ITEMALLOC].
        unfold tupdate. ex_match2. rewrite Hx. left;eauto.
        set  (FLists.get_fl (TSOGlobEnv.freelists TGE)(FLists.thread_flmap (TSOGlobEnv.freelists TGE)t' x0)) as fl2 in *.
        assert(FLDISJ:MemAux.disj fl fl2).
        {
          eapply FLISTWD;eauto.
          assert(exists n,TSOCore.F c = FLists.thread_flmap (TSOGlobEnv.freelists TGE) t n).
          eapply INVTHDP1 in H_tp_core. inv H_tp_core.
          edestruct fid_valid0. left;eauto.
          destruct H5. eauto.
          destruct H5. rewrite H5.
          eapply FLISTWD;eauto.
        }
        enough(FLEQ: FreelistEq m1 (memory tm0) fl).
        assert(LPRE:LPre m1 (memory tm0) fp fl). split;auto.
        apply LPre_comm in LPRE.
        
        eapply tso_lock_step_locality in H1 as ?;eauto.
        Hsimpl. apply lock_step_tsostep in H5.
        assert(GMem.eq g x1).
        apply GMem.eq_sym.
        apply GMem_eq.
      
        
        eapply FPLemmas.LEffect_LPost_fpsmile_memeq with(m1:=gm')(m2:=g)(m1':=m1)(m2':=x1);eauto.
        split;eauto. split;eauto. eapply apply_buf_item_MemEffect;eauto.
        eapply buffer_item_local_alloc_local_alloc;eauto.
        apply FP.smile_conflict_compat;auto.

        split;auto. eapply buffer_item_local_alloc_local_alloc;eauto.
        split;auto. eapply Fleq_apply_buffer_item_preserve;eauto.
        apply FreelistEq_comm.
        eapply disjoint_fl_memeq;eauto.
        {
          revert H1;clear;intros.
          inv H1.  inv H4. unfold notlock_instr in H7;ex_match;simpl in *;ex_match;inv_next.
         
          all: try solve[unfold Mem.storev in *;ex_match;eapply store_forward;eauto].
          inv H3. simpl in *. congruence.
        }

        apply TSO_eff in H5. apply H5;auto.


        assert(unbuffer_safe  {|
             tso_buffers := tupdate t' b0 (tupdate t nil (tso_buffers tm0));
             memory := g |}).
        inv H_unbuf_safe.
        eapply UNBS;eauto.
        unfold tsoupd. simpl. unfold tupdate. ex_match2.
        eapply gmem_eq_ub_safe_eq in H8;eauto.
        
        Esimpl.
        econstructor;eauto.
        solv_thread. unfold unbuffer. do 2 ex_match3. eauto.
        econstructor. 
        2: simpl;unfold tupdate; ex_match2; rewrite H3; exact H5.
        all: eauto. 
        unfold tsoupd. simpl. rewrite tupdate_comm;auto.
        econstructor;eauto.
        simpl. rewrite tupdate_comm;auto.

        apply FPLemmas.disj_comm in FLDISJ.
        apply FreelistEq_comm.
        eapply disjoint_fl_memeq;eauto.
        eapply buffer_item_local_alloc_local_alloc;eauto.
        {
          revert UB1;clear;destruct b;simpl;unfold alloc,store,free;intros;ex_match;try inv_some;unfold GMem.valid_block;simpl;auto.
        }
      }
      {
        assert(memory tm0 = gm'). inv H1. apply not_lock_step_mem_ung in H12.
        simpl in H12. inv H9. congruence.
        subst.

        assert(exists fm,embed g fl fm).
        inversion FLEMBED;subst.
        eapply UNBS in Hx0 as ?;eauto.
        inv H3. eapply Embed0;eauto.
        Hsimpl.


        edestruct LALLOC as [? ITEMALLOC].
        unfold tupdate. ex_match2. rewrite Hx. left;eauto.
        set  (FLists.get_fl (TSOGlobEnv.freelists TGE)(FLists.thread_flmap (TSOGlobEnv.freelists TGE)t' x0)) as fl2 in *.
        assert(FLDISJ:MemAux.disj fl fl2).
        {
          eapply FLISTWD;eauto.
          assert(exists n,TSOCore.F c = FLists.thread_flmap (TSOGlobEnv.freelists TGE) t n).
          eapply INVTHDP1 in H_tp_core. inv H_tp_core.
          edestruct fid_valid0. left;eauto.
          destruct H4. eauto.
          destruct H4. rewrite H4.
          eapply FLISTWD;eauto.
        }
        
        assert(LPre (memory tm0) g fp fl).
        split. apply MemPre_comm. eapply MemEffect_fpsmile_MemPre_Rule. apply apply_buf_item_MemEffect;eauto. apply FPLemmas.fpsmile_sym. apply FP.smile_conflict_compat;auto.
        eapply disjoint_fl_memeq;eauto.
        apply FPLemmas.disj_comm;eauto.
        eapply buffer_item_local_alloc_local_alloc;eauto.
        {
          revert Hx0;clear;destruct b;simpl;unfold alloc,store,free;intros;ex_match;try inv_some;unfold GMem.valid_block;simpl;auto.
        }
        assert(  buffer_safe (tso_buffers tm0 t) (memory tm0)).
        {
           apply unbuffer_safe_buffer_safe with(t:=t) in H_unbuf_safe as R.
           simpl in R. unfold tupdate in R. ex_match2.
           apply TSO_bf_add in H_core_step as[];subst.
           destruct R as [? R]. 
           apply apply_buffer_split in R as[?[R1 R2]].
           eexists;eauto.
        }
        assert(  buffer_safe (tso_buffers tm0 t) g).
        {
           inv H_unbuf_safe.
           eapply UNBS in Hx0;eauto.
           Focus 2. instantiate(2:=t'). unfold tsoupd,tupdate;simpl;ex_match2;eauto.
           
           eapply unbuffer_safe_buffer_safe with(t:=t) in Hx0;eauto.
           simpl in Hx0. unfold tupdate in Hx0. ex_match2.
           apply TSO_bf_add in H_core_step as[];subst.
           destruct Hx0 as [? R]. 
           apply apply_buffer_split in R as[?[R1 R2]].
           eexists;eauto.
        }
        assert(  buffer_fl_embed (tso_buffers tm0 t) fl g).
        {
          destruct H6.
          eexists;split;eauto.
          inv FLEMBED.
          eapply UNBS in Hx0;eauto.
          clear Embed UNBS Hx1.
          revert H6 Hx0 n. clear.
          intros.
          set  {| tso_buffers := tupdate t' b0 (tso_buffers tm0); memory := g |} as tm in *.
          assert(memory tm = g). unfold tm;auto.
          rewrite <- H in *;clear H.
          eapply FLs_embed_apply_buffer_preserve in H6;eauto.
          inv H6. eapply Embed.
          instantiate(1:=t).
          unfold tm. simpl. unfold tupdate;ex_match2.
        }
        eapply not_lock_step_locality in H4;eauto.
        eapply not_lock_step_tsostep in H4 as ?.
        Esimpl. econstructor;eauto. solv_thread.
        unfold unbuffer. do 2 ex_match3. eauto.
        econstructor;eauto.  simpl. unfold tupdate;ex_match2. eauto.


        
        inv H_unbuf_safe.
        eapply UNBS in Hx0.
        Focus 2. instantiate(2:=t'). unfold tsoupd,tupdate;simpl.  ex_match2. eauto.
        unfold tsoupd. simpl. unfold tsoupd in Hx0. simpl in Hx0.
        rewrite tupdate_comm;auto.


        constructor;auto.
        simpl. apply GMem.eq_refl.
        simpl. rewrite tupdate_comm;auto.

       
      }
    }
    {
      do 2 eexists. split.
      econstructor;eauto.
      solv_thread.
      split. eapply Call;eauto.
      apply eq_config_refl.
    }
    {
      do 2 eexists. split.
      econstructor;eauto. solv_thread.
      split. eapply Return;eauto.
      apply eq_config_refl.
    }
    {
      do 2 eexists;split.
      econstructor;eauto. solv_thread.
      split. eapply Halt;eauto.
      apply eq_config_refl.
    }
    {
      do 2 eexists;split.
      econstructor;eauto. solv_thread.
      split. eapply EF_Print;eauto.
      apply eq_config_refl.
    }
  Qed.
  Lemma lock_step_access_eq:
    forall ge fl c bf m fp c' bf' m',
      @tso_lock_step ge fl c (bf,m) fp c' (bf',m') ->
      (GMem.mem_access) m = (GMem.mem_access) m'.
  Proof.
    Local Transparent Mem.store.
    intros. inv H. inv H9. inv H6.
    unfold notlock_instr in H3;ex_match;simpl in *;ex_match;inv_next.
    all:unfold Mem.storev in *; ex_match; unfold Mem.store in *; ex_match; inv_some; simpl in *;auto.
  Qed.
Lemma unbuf_locality :
  forall bf m m1,
    MemPre m m1 (bf_footprint bf) ->
    forall m',
      apply_buffer bf m = Some m'->
      exists m1', apply_buffer bf m1 = Some m1' /\
             MemPost m' m1' (bf_footprint bf).
Proof.
  induction bf;intros.
  simpl in *. inv_some; Esimpl;eauto. apply unchanged_content_emp.

  simpl in *. unfold optbind in *. ex_match.
  apply MemPre_split in H as ?. Hsimpl.
  eapply buf_item_unbuf_locality_1 in Hx as ?;eauto.
  specialize (H3 _ H1). Hsimpl. ex_match3.
  apply apply_buf_item_MemEffect in Hx as EFF1.
  apply apply_buf_item_MemEffect in H3 as EFF2.
  exploit IHbf.
  eapply MemPre_MemEffect_MemPost_Rule;eauto.
  eauto.
  intros. Hsimpl.
  Esimpl;eauto.
  eapply MemPost_MemEffect_MemPost_Rule;  eauto.
  eapply apply_buffer_eff;eauto.
  eapply apply_buffer_eff;eauto.
Qed.  
Definition ub_footprint (t:tid)(pc:@TSOProgConfig TGE):FP.t:=
  match tso_buffers (tm pc) t with
  | nil => FP.emp
  | b::ls => bi_footprint b
  end.
Lemma diff_thread_unbuffer_normal_step_reorder':
  forall (tpc tpc' tpc'': @TSOProgConfig TGE) l fp t'
    (UBS1:unbuffer_safe (tm tpc))
    (FLEMBED:FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc))
    (INVTHDP1: inv tpc.(thrdpool))
    (LALLOC:buffer_local_alloc t' ((tpc.(tm).(tso_buffers) t'))),
    let t := cid tpc in
    (*~ conflictc t fp (tso_buffers (tm tpc))*)
    ~ FP.conflict fp (ub_footprint t' tpc) ->
    normal_tsoglabel l ->
    tso_globstep tpc (ub t') FP.emp tpc' ->
    t <> t' ->
    tso_globstep tpc' l fp tpc'' ->
    exists tpc0 tpc1,
      tso_globstep tpc l fp tpc0 /\
      tso_globstep tpc0 (ub t') FP.emp tpc1 /\
      eq_config TGE tpc'' tpc1.
Proof.
  intros.
  unfold t in *. clear t.
  pose proof H3 as STEP2.
  pose proof H1 as STEP1.
  inv H3;inv H1;tryfalse.
  {
    unfold unbuffer in H_unbuf.
    ex_match. inv_some.
    simpl in *. 
    assert(FPSMILE:~ FP.conflict fp (bi_footprint b)).
    intro;contradict H. unfold ub_footprint;simpl. ex_match3. auto.
    apply FP.smile_conflict_compat in FPSMILE.
    
    edestruct LALLOC. rewrite Hx;left;eauto.
    set (FLists.get_fl (TSOGlobEnv.freelists TGE)(FLists.thread_flmap (TSOGlobEnv.freelists TGE) t' x)) as fl0 in *.
    set (FLists.get_fl (TSOGlobEnv.freelists TGE)(TSOCore.F c)) as fl in *.
    set (TSOGlobEnv.modules TGE (TSOCore.i c)) as ge in *.
    assert(FLDISJ:MemAux.disj fl fl0).
    {
      apply FLISTWD.
      eapply INVTHDP1 in H_tp_core. inv H_tp_core.
      edestruct fid_valid0. left;eauto.
      destruct H3. rewrite <- H4. eapply FLISTWD;eauto.
    }
    
    apply apply_buf_item_MemEffect in Hx0 as EFF1.
    eapply MemEffect_fpsmile_MemPre_Rule in EFF1 as PRE1;[|apply FPLemmas.fpsmile_sym;eauto].
    assert(FLEQ:FreelistEq g (memory tm0) fl).
    {
      apply FPLemmas.disj_comm in FLDISJ.
      apply FreelistEq_comm.
      eapply disjoint_fl_memeq;eauto.
      eapply buffer_item_local_alloc_local_alloc;eauto.
      { revert Hx0;clear;destruct b;simpl;unfold alloc,store,free;intros;ex_match;try inv_some;unfold GMem.valid_block;simpl;auto. }
    }
    assert(PRE1':LPre g (memory tm0) fp fl). split;auto.
    apply tsostep_lock_or_notlock in H_core_step as R.
    assert(exists fm,embed (memory tm0) fl fm).
    inv FLEMBED. eapply Embed.
    destruct H3 as [fm EMBED1].
    destruct R as [|].
    {
      assert(tupdate t' b0 (tso_buffers tm0) t = nil /\ buf' = nil).
      { inv H3;auto. }
      destruct H4;subst;rewrite H4 in *.
      unfold tupdate in H4;ex_match2.
      eapply tso_lock_step_locality in PRE1';eauto.
      Hsimpl.

      assert(EFF2:LEffect (memory tm0) x0 fp fl).
      {
        apply lock_step_tsostep in H5.
        apply TSO_eff in H5;eapply H5;eauto.
      }
      eapply LEffect_fpsmile_LPre_Rule in EFF2 as PRE2;eauto.
      inversion PRE2 as [MPRE2 ALL2].
      apply MemPre_comm in MPRE2.
      eapply buf_item_unbuf_locality_1 in MPRE2 as ?;eauto.
      Hsimpl.
      
      eapply unbuffer_safe_after_tsostep_unbuffer_safe_original in H_unbuf_safe as ?.
      Focus 2.
      simpl.  unfold tupdate. ex_match2. rewrite H4. eauto.
      assert(GMem.eq gm' x1).
      {
        apply GMem.eq_sym.
        apply GMem_eq.
        eapply FPLemmas.LEffect_LPost_fpsmile_memeq with(m1:=g)(m2:=gm')(m1':=x0)(m2':=x1).
        split. eauto. 
        eapply buffer_item_local_alloc_local_alloc;eauto.
        eapply TSO_eff in H_core_step. eapply H_core_step;eauto.
        apply FPLemmas.fpsmile_sym;auto.
        auto.
        auto.
        split;auto. eapply apply_buf_item_MemEffect;eauto.
        eapply buffer_item_local_alloc_local_alloc;eauto.
        split;auto. clear ALL2.
        eapply Fleq_apply_buffer_item_preserve;try exact H7;eauto.
        destruct PRE2. apply FreelistEq_comm;auto.
      }
      eapply gmem_eq_ub_safe_eq in H10 as UBS2;eauto.
      simpl in UBS2.
      
      Esimpl.
      econstructor;eauto. rewrite H4. eapply lock_step_tsostep;eauto.
      {
        apply lock_step_tsostep in H5.
        apply TSO_step_access_validity_preserve in H5 as [].
        eapply unbuffer_safe_mem_access_same_stable;eauto.
        rewrite tupdate_same_eq;auto.
        destruct tm0;auto.
      }
      econstructor;eauto. solv_thread.
      unfold unbuffer.
      simpl. rewrite tupdate_not_eq_get;auto. ex_match3.
      ex_match3. eauto.
      econstructor;eauto.
      simpl. rewrite tupdate_comm;auto.
    }
    {
      assert( g = gm'). inv H3. apply not_lock_step_mem_ung in H13;auto. inv H10.
      simpl in *. congruence.
      subst.
      eapply not_lock_step_locality in PRE1' as ?;eauto.
      {
        unfold tupdate in H4;ex_match2.

        set ({| tso_buffers := tupdate t' b0 (tso_buffers tm0); memory := gm' |}) as m in *.
        assert(memory m = gm'). unfold m;auto.
        assert(tso_buffers m t = (tupdate t' b0 (tso_buffers tm0) t)).
        unfold m;simpl;auto.
        rewrite <-H5,<-H6 in H_core_step.
        eapply unbuffer_safe_after_tsostep_unbuffer_safe_original in H_core_step as UBS0;eauto.

        eapply tso_not_lock_step_bufeff in H4 as ?.
        destruct H7;Hsimpl.
        subst buf'.

        assert(eff_eq fp (bf_footprint x0)).
        destruct H8;split;auto.
        eapply fpsmile_eff_eq_trans in H7 as ?;eauto.
        2: apply bf_footprint_reads_emp.
        2: apply bf_footprint_cmps_emp.

        apply FPLemmas.fpsmile_sym in H10.
        pose proof fpsmile_nfconflict_2 _ _ H10.
        apply not_lock_step_tsostep in H4 as ?.
        Esimpl.
        econstructor;eauto.
        Focus 2. econstructor;eauto. generalize dependent thdp'. revert H_tid_valid. clear;intros. solv_thread.
        unfold unbuffer. simpl. rewrite tupdate_not_eq_get;eauto. do 2  ex_match3. eauto.
        Focus 2.
        constructor;auto. apply GMem.eq_refl. simpl.
        rewrite tupdate_comm;auto.

        {
          eapply unbuffer_safe_append_bf_preserve;eauto.
          Focus 2. clear Hx1.
          revert Hx H_unbuf_safe H11 UBS0 H6 n.
          clear.
          intros.
          unfold inv_bi. intros.
          pose proof unbuffer_safe_nfconflict _ H_unbuf_safe.

          simpl in *.

          destruct (peq t'0 t').
          {
            subst.
            rewrite Hx in H1. inv H1.
            apply nfconflict_comm.
            eapply H11;eauto.

            eapply H2 with(t0:=t').
            rewrite tupdate_comm,tupdate_b_get;auto.
            eauto.
            rewrite tupdate_b_get;auto.
            apply List.in_or_app. right;auto.
          }
          {
            eapply H2.
            instantiate(1:=t'0).
            rewrite! tupdate_not_eq_get;auto.
            Focus 2.
            rewrite tupdate_b_get;auto. apply List.in_or_app;right;auto.
            auto.
          }
          Unfocus. clear Hx1.
          revert UBS1 UBS0 H_unbuf_safe Hx PRE1 n H8.
          clear; intros.
          eapply unbuffer_safe_buffer_safe with(t:=t) in UBS0 as R;eauto;simpl in R.
          rewrite tupdate_not_eq_get in R;auto.
          destruct R.
          eapply unbuffer_safe_buffer_safe with(t:=t) in UBS1.
          destruct UBS1.
          eapply MemPre_apply_buffer_preserve in PRE1;eauto.
          eapply unbuffer_safe_buffer_safe with(t:=t) in H_unbuf_safe as R;eauto.
          simpl in R. rewrite tupdate_b_get in R;auto.
          destruct R. apply apply_buffer_split in H1. Hsimpl.
          rewrite H1 in H;inv H.

          assert(MemPre x x1 (bf_footprint x0)).
          split. rewrite bf_footprint_reads_emp. apply unchanged_content_emp.
          rewrite bf_footprint_cmps_emp. apply unchanged_perm_emp.
          assert(forall fp1 fp2, eff_eq fp1 fp2 -> effects fp1 = effects fp2).
          destruct 1. unfold effects. congruence.
          erewrite H;eauto. destruct PRE1;auto.

          eapply unbuf_locality in H as ?;eauto.
          Hsimpl.
          eexists.
          erewrite apply_buffer_app_eq;eauto.
        }
      }
      {
        rewrite tupdate_not_eq_get;auto.
        eapply unbuffer_safe_buffer_safe with(t:=t) in H_unbuf_safe;eauto.
        simpl in H_unbuf_safe.
        rewrite tupdate_b_get in H_unbuf_safe.
        apply tso_not_lock_step_bufeff in H3 as R.
        destruct R;Hsimpl. subst.
        rewrite tupdate_not_eq_get in H_unbuf_safe;auto.
        destruct H_unbuf_safe.
        apply apply_buffer_split in H4;Hsimpl;eexists;eauto.
      }
      {
        unfold buffer_fl_embed.
        rewrite tupdate_not_eq_get;auto.
        eapply TSOMemLemmas.unbuffer_safe_apply_buffer' with(t:=t) in UBS1 as ?.
        Hsimpl. eexists;split;eauto.
        eapply FLs_embed_apply_buffer_preserve in H4;eauto.
        inv H4. eauto.
      }
      {
        rewrite tupdate_not_eq_get;auto.
        eapply TSOMemLemmas.unbuffer_safe_apply_buffer' with(t:=t) in UBS1 as ?.
        Hsimpl. esplit;eauto.
      }
    }
  }
  {
    Esimpl.
    eapply Call;eauto.
    econstructor;eauto. solv_thread.
    apply eq_config_refl.
  }
  {
    Esimpl.
    eapply Return;eauto.
    econstructor;eauto. solv_thread.
    apply eq_config_refl.
  }
  {
    Esimpl.
    eapply Halt;eauto.
    econstructor;eauto. solv_thread.
    apply eq_config_refl.
  }
  {
    Esimpl.
    eapply EF_Print;eauto.
    econstructor;eauto. solv_thread.
    apply eq_config_refl.
  }
Qed.
Inductive ubstarN (t:tid) :nat->@TSOProgConfig TGE->@TSOProgConfig TGE->Prop:=
| ubstarN_refl: forall tpc, ubstarN t Datatypes.O tpc tpc
| ubstarN_cons: forall i tpc tpc' tpc'',
    tso_globstep tpc (ub t) FP.emp tpc' ->
    ubstarN t i tpc' tpc'' ->
    ubstarN t (Datatypes.S i) tpc tpc''.
Lemma ubstarN_ubstar_equiv:
  forall t tpc tpc',
    ub_star TGE t tpc tpc' <-> exists n, ubstarN t n tpc tpc'.
Proof.
  split.
  induction 1. eexists;econstructor.
  Hsimpl. eexists;econstructor 2;eauto.

  intros. Hsimpl. induction H. constructor.
  econstructor;eauto.
Qed.
Lemma eq_config_eq_ub_starN:
  forall x tpc0 tpc1 tpc0' t,
    eq_config TGE tpc0 tpc0' ->
    ubstarN t x tpc0 tpc1 ->
    exists tpc1', ubstarN t x tpc0' tpc1' /\ eq_config TGE tpc1 tpc1'.
Proof.
  clear. intros. revert tpc0' H. induction H0.
  intros. exists tpc0'. split; [constructor | auto].
  intros. exploit eq_config_eq_step; eauto. intros (tpc1' & Hub0' & Heq).
  apply IHubstarN in Heq. destruct Heq as (tpc2' & Hubstar' & Heq).
  exists tpc2'. split; auto. econstructor; eauto.
Qed.
Lemma diff_thread_unbuffer_star_normal_step_reorder:
  forall (tpc tpc' tpc'': @TSOProgConfig TGE) l fp t'
    (UBS1:unbuffer_safe (tm tpc))
    (FLEMBED:FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc))
    (INVTHDP1: inv tpc.(thrdpool))
    (LALLOC:buffer_local_alloc t' ((tpc.(tm).(tso_buffers) t'))),
    let t := cid tpc in
    ~ FP.conflict fp (bf_footprint (tso_buffers (tm tpc) t'))->
    normal_tsoglabel l ->
    ub_star TGE t' tpc tpc' ->  
    t <> t' ->
    tso_globstep tpc' l fp tpc'' ->
    exists tpc0 tpc1,
      tso_globstep tpc l fp tpc0 /\
      ub_star TGE t' tpc0 tpc1 /\
      eq_config TGE tpc'' tpc1.
Proof.
  intros.
  apply ubstarN_ubstar_equiv in H1 as [].
  enough (exists tpc0 tpc1, tso_globstep tpc l fp tpc0 /\ ubstarN t' x tpc0 tpc1 /\ eq_config TGE tpc'' tpc1).
  Hsimpl. Esimpl;eauto. eapply ubstarN_ubstar_equiv;eauto.

  revert tpc tpc' tpc'' l fp t' t UBS1 FLEMBED INVTHDP1 LALLOC  H H0 H1 H2 H3.
  induction x;intros.
  {
    inversion H1;subst. Esimpl;eauto. constructor. apply eq_config_refl.
  }
  {
    inv H1.
    exploit IHx;try exact H6;eauto.
    {
      inv H5; unfold unbuffer in H_unbuf;ex_match;inv_some.
      inv UBS1. eapply UNBS;eauto.
    }
    {
      inv H5; unfold unbuffer in H_unbuf;ex_match;inv_some.
      inv FLEMBED. eapply UNBS;eauto.
    }
    {
      eapply glob_step_inv_preserve;eauto.
    }
    {
      inv H5; unfold unbuffer in H_unbuf;ex_match;inv_some.
      simpl.
      unfold buffer_local_alloc in *;intros.
      rewrite tupdate_b_get in H1. eapply LALLOC;eauto.
      simpl. rewrite Hx. right;auto.
    }
    {
      inv H5; unfold unbuffer in H_unbuf;ex_match;inv_some.
      simpl in *.
      intro;contradict H.
      rewrite tupdate_b_get in H1.
      rewrite Hx. simpl.
      rewrite FP.union_comm_eq.
      eapply USimDRF.conflict_union_ano;eauto.
    }
    {
      inv H5;auto.
    }

    intro. Hsimpl.
    clear H3 H6.

    exploit diff_thread_unbuffer_normal_step_reorder';try exact H5;try exact H1;auto.
    intro;contradict H.
    unfold ub_footprint in H3. ex_match2. simpl;auto.
    simpl. eapply USimDRF.conflict_union_ano;auto.
    
    intro;Hsimpl.
    eapply eq_config_eq_ub_starN in H8;eauto;Hsimpl.
    Esimpl. eauto. econstructor;eauto.
    eapply eq_config_trans;eauto.
  }
Qed.
Lemma unbuffer_switchable:
  forall (tpc tpc1 tpc2:@TSOProgConfig TGE) t,
    tso_globstep tpc (ub t) FP.emp tpc1 ->
    tso_globstep tpc1 sw FP.emp tpc2 ->
    tso_globstep tpc sw FP.emp ({-|tpc,cid tpc2}) /\
    tso_globstep  ({-|tpc,cid tpc2}) (ub t) FP.emp tpc2.
Proof.
  intros.
  inv H;inv H0.
  split;econstructor;eauto.
Qed.
Lemma ubstar_swtichable:
  forall (tpc tpc1 tpc2:@TSOProgConfig TGE) t,
    ub_star TGE t tpc tpc1 ->
    tso_globstep tpc1 sw FP.emp tpc2 ->
    tso_globstep tpc sw FP.emp ({-|tpc,cid tpc2}) /\
    ub_star TGE t ({-|tpc,cid tpc2}) tpc2.
Proof.
  induction 1;intros.
  inv H. Esimpl;eauto; econstructor;eauto.
  destruct IHub_star;auto.
  edestruct unbuffer_switchable;eauto.
  split;auto. econstructor;eauto.
Qed.
Lemma diff_thrd_normal_step_unbuffer_normal_step_reorder':
  forall (tpc1 tpc1' tpc1'' tpc2 tpc2': @TSOProgConfig TGE) l1 fp1 l2 fp2
    (*UBS1:unbuffer_safe (tm tpc1)*)
    (FLEMBED:FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc1))
    (INVTHDP1: inv tpc1.(thrdpool)),
    tso_buffers (tm tpc1) (cid tpc1) = nil ->
    (* t1 insert buffer and unbuffer *)
    normal_tsoglabel l1 ->
    tso_globstep tpc1 l1 fp1 tpc1' ->
    ub_star TGE (cid tpc1) tpc1' tpc1'' ->
    (* t2 normal step do not conflict with t1 insert buffer step *)
    cid tpc1 <> cid tpc2 ->
    tso_globstep tpc1'' sw FP.emp tpc2 ->
    normal_tsoglabel l2 ->
    tso_globstep tpc2 l2 fp2 tpc2' ->
    FP.smile fp1 fp2 ->
    (* t1 insert buffer and unbuffer steps could reorder with t2 normal step *)
    exists _tpc2 _tpc2' _tpc1 _tpc1' _tpc1'',
      tso_globstep tpc1 sw FP.emp _tpc2 /\
      cid _tpc2 = cid tpc2 /\
      tso_globstep _tpc2 l2 fp2 _tpc2' /\
      tso_globstep _tpc2' sw FP.emp _tpc1 /\
      cid _tpc1 = cid tpc1 /\
      tso_globstep _tpc1 l1 fp1 _tpc1' /\
      ub_star TGE (cid tpc1) _tpc1' _tpc1'' /\
      eq_config_but_cid TGE tpc2' _tpc1''.
 Proof.
   intros.
   assert(tso_buffers (tm tpc1')(cid tpc1') = nil \/ tso_buffers (tm tpc1')(cid tpc1') <> nil).
   destruct (tso_buffers (tm tpc1')(cid tpc1'));auto.
   right;intro;congruence.
   destruct H8 as [|R].
   {
     assert(cid tpc1 = cid tpc1'). inv H1;auto. inv H0.
     assert(tpc1' = tpc1'').
     revert H2 H8 H9;clear;intros.
     inv H2;auto. inv H. unfold unbuffer in H_unbuf. ex_match2. simpl in *.     congruence.
     subst.
     clear H2.

     exploit diff_thrd_normal_step_reorder'.
     eauto. exact H0. exact H1.
     rewrite <- H9.  exact H3.
     eauto. eauto. eauto. eauto.

     intro. Hsimpl.
     Esimpl;eauto. constructor.
   }
   enough(UBS1:unbuffer_safe (tm tpc1)).
   eapply unbuffer_safe_globstep_preserve in UBS1 as UBS2;eauto.
   edestruct ubstar_swtichable;eauto.
   clear H4 H2.
   exploit diff_thread_unbuffer_star_normal_step_reorder;try exact H9;eauto.
   simpl; eapply FLs_embed_preserved;eauto.
   simpl. eapply glob_step_inv_preserve;eauto.
   {
     simpl.
     revert H H1 INVTHDP1;clear;intros.
     assert(forall t, buffer_local_alloc t nil).
     unfold buffer_local_alloc;intros. inv H0.

     inv H1;try solve[simpl in *; rewrite H; eauto].
     apply tsostep_buffered_alloc_in_fl in H_core_step.
     Hsimpl. unfold buffer_local_alloc. simpl in *. rewrite tupdate_b_get.
     rewrite H1,H. intros. simpl in H3.
     unfold buffer_item_local_alloc. ex_match2.
     {
       eapply H2 in H3;Hsimpl.
       unfold FLists.get_block in H3. unfold MemAux.in_fl.
       eapply cs_inv in H_tp_core as ?;eauto.
       exploit fid_valid;eauto. left;eauto.
       intro. Hsimpl. exists x1 x0.
       rewrite <- H6 in H3. eauto.
     }
     exists Datatypes.O;auto.
     exists Datatypes.O;auto.
     simpl in *.
     unfold unbuffer in H_unbuf. ex_match2.
     inv_some;simpl. rewrite tupdate_not_eq_get,H;eauto.
     intro;subst;congruence.
   }
   {
     simpl.
     revert H H1 INVTHDP1 H7;clear;intros.
     inv H1;simpl in *.
     {
       rewrite tupdate_b_get.
       rewrite H in H_core_step.
       assert(buf' = nil \/ buf' <> nil).
       destruct buf';auto. right;intro;congruence.
       destruct H0;subst.
       intro R;apply FP.emp_never_conflict in R as [];contradiction.
       exploit bf_eff. eapply TSO_eff;eauto.
       right;intro;congruence.
       unfold BufferEff;intros;Hsimpl.
       simpl in *;subst. simpl in *.
       eapply FP.smile_conflict_compat.
       apply FPLemmas.fpsmile_sym.
       eapply fpsmile_eff_eq_trans ;eauto.
       destruct H2;split;auto. apply bf_footprint_reads_emp. apply bf_footprint_cmps_emp.
     }
     {
       unfold unbuffer in H_unbuf. ex_match2;inv_some.
       simpl. rewrite tupdate_not_eq_get.
       rewrite H. simpl. intro. apply FP.emp_never_conflict in H0 as [];contradiction.
       intro;subst;congruence.
     }
     rewrite H;intro R;apply FP.emp_never_conflict in R as [];contradiction.
     rewrite H;intro R;apply FP.emp_never_conflict in R as [];contradiction.
     rewrite H;intro R;apply FP.emp_never_conflict in R as [];contradiction.
     rewrite H;intro R;apply FP.emp_never_conflict in R as [];contradiction.
     rewrite H;intro R;apply FP.emp_never_conflict in R as [];contradiction.
   }

   intros. Hsimpl.
   assert(cid tpc1 = cid tpc1'). inv H1;auto. inv H0.
   exploit diff_thrd_normal_step_reorder'.
   exact INVTHDP1. exact H0. eauto.
   2: eauto. simpl. intro;congruence.
   eauto. eauto. eauto.

   intros;Hsimpl.
   eapply eq_config_but_cid_ub_star in H18 as ?;eauto;Hsimpl.
   eapply eq_config_but_cid_trans in H20;try apply eq_config_eq_config_but_cid;eauto.
   Esimpl;eauto.

   {
     revert H H0 H1 R;clear;intros.
     inv H1;simpl in *;try contradiction.
     eapply unbuffer_safe_after_tsostep_unbuffer_safe_original;eauto.
   }
 Qed.
 Lemma spawn_inv:
   forall tp mid c sg tp',
     TSOThrdPool.spawn tp mid c sg = tp' ->
     inv tp ->
     inv tp'.
 Proof.
   unfold TSOThrdPool.spawn; simpl. 
   intros. subst. inversion H0.
   constructor; subst; simpl in *; intros.
   { rewrite PMap.gsspec. destruct peq; subst. Lia.lia.
     apply tp_finite0. Lia.lia. }
   { rewrite PMap.gsspec. destruct peq; eauto.
     apply tp_valid0. apply Plt_succ_inv in H. destruct H; congruence. }
   { auto. }
   { rewrite PMap.gsspec in H. destruct peq; subst; auto.
     inv H. clear. constructor; simpl; intros; auto.
     inv H; simpl. unfold FLists.fbelongsto. eauto. inversion H0.
     inv H; simpl. unfold FLists.fbelongsto. eauto. inversion H0.
     do 2 try destruct n1; do 2 try destruct n2; simpl in *; auto; try discriminate.
   }
 Qed.
 
 Lemma init_inv:
   forall l thdp,
     TSOThrdPool.init l thdp->
     inv thdp.
 Proof.
   induction l;intros.
   {
     inv H. constructor;simpl;intros.
     rewrite PMap.gi;auto.
     exfalso. inv H. destruct i;inv H1.
     auto.
     rewrite PMap.gi in H. inv H.
   }
   {
     inv H.
     eapply IHl in H3.
     eapply spawn_inv;eauto.
   }
Qed.   
   
End normal_reorder.