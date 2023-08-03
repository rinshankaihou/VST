(** This file says that if [RespectPerm (Io, Ro, Go)] holds, then we can know  
that the following things hold : 
- client invariant [Ic] is stable under [Go] 
     (proved by [Lemma RP_Ic_Sta_Go]).
- object invariant [Io] is stable under [Gc]
     (proved by [Lemma RP_Io_Sta_Gc]).
- [Go] ====> [Rc]
     (proved by [Lemma RP_Go_Implies_Rc])
- [Gc] ====> [Ro]
     (proved by [Lemma RP_Gc_Implies_Ro])

Here, [RespectPerm (Io, Ro, Go)] is defined in /concurrency/x86TSO/ObjectSim
 *)
From mathcomp.ssreflect Require Import fintype ssrnat.                     
Require Import Coqlib Maps Axioms.  
Require Import AST Integers Floats Values Events Globalenvs Smallstep. 
Require Import Locations Stacklayout Conventions.
 
Require Import Asm. 

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Memdata Memperm MemAux FMemLemmas GMemory FMemory Footprint TSOMem.
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe.
 
Require CminorLang.  
Require SpecLang. 
Require Import ASM_local. 
Require Import AsmLang.
Require Import AsmTSO TSOMem.

Require Import Coq.Lists.Streams.

Require Import RGRels.
Require Import LibTactics.

Require Import code.
Require Import ObjectSim.
Require Import TSOGlobSem.
Require Import InvRG. 
Require Import AuxTacLemmas TSOMemLemmas MemLemmas.

Require Import ClientSim.

(** ** Auxiliary Lemmas *)
Section RP_RGI_Props.
  Variable Io: genv -> stInv.
  Variables Ro Go: genv -> tid -> stRel.
  Hypothesis HRP: RespectPerm Io Ro Go.

  (** [RespectPerm (Io, Ro, Go)] ======> [Sta (Ic, Go)] *)
  Lemma RP_Ic_Sta_Go:
    forall ge t, Sta Ic (Go ge t).
  Proof.
    intros. 
    inversion HRP; subst.
    unfold Sta.
    introv HIc HGo.
    clear - Gp HIc HGo.
    eapply Gp in HGo. 
    destruct HGo as [Henv_m [Hub_safe
                               [Hub_safe'
                                  [Hbf [Htm_vb_eq
                                          [Hm_access
                                             [Hobj_mem [Hcont_sm Hcont_tm]]]]]]]].
    destruct Hbf as [Hbf_eq | Hbf]; clear Gp.
    {
      unfolds obj_tau.
      destruct Hbf_eq as [Hgm_vb_eq Hbf_eq].
      inversion HIc; subst; clear HIc.
      econstructor; eauto.
      introv Ht_neq H_not_objm Hib_t1 Hib_t2.
      rewrite <- Hbf_eq in Hib_t1, Hib_t2.
      eapply Ic_no_conflict_bi; eauto.
      introv Happly_buf Hnot_in_objm Hnot_in_bf.
      rewrite <- Hbf_eq in Happly_buf.
      assert (Hnot_in_orig_objm : ~ obj_mem gm b ofs).
      {
        intro.
        contradiction Hnot_in_objm; eauto.
      }
      lets Happly_buf1 : Hub_safe.
      eapply unbuffer_safe_apply_buffer' with (t := t0) in Happly_buf1.
      destruct Happly_buf1 as [tgm Happly_buf1].
      lets Heq_loc : Happly_buf1. 
      eapply Ic_mem_eq in Heq_loc; eauto.
      2 : rewrite Hbf_eq; eauto.
      inversion Heq_loc; subst.
      assert (GMem.validblocks tgm = GMem.validblocks tgm').
      {
        eapply in_valid_block_eq_apply_same_buf_still; eauto.
      }
      assert (Hvb_eq : GMem.valid_block gm' b <-> GMem.valid_block tgm' b).
      {
        split; intros.
        { 
          unfolds GMem.valid_block.
          rewrite <- Hgm_vb_eq in H0.
          eapply eq_loc_validity in H0.
          rewrite <- H; eauto.
        }
        {
          unfolds GMem.valid_block.
          rewrite <- H in H0.
          eapply eq_loc_validity in H0.
          rewrite <- Hgm_vb_eq; eauto.
        }
      }
      econstructor; eauto.
      {
        intros. 
        specialize (eq_loc_perm k). 
        clear - Henv_m Happly_buf Hnot_in_orig_objm eq_loc_perm H
                       Happly_buf1 Hgm_vb_eq Htm_vb_eq Hm_access.
        unfolds env_m_stable. 
        destruct (Classical_Prop.classic (In b (GMem.validblocks gm))).
        {
          lets Hloc_stable : Hnot_in_orig_objm.
          eapply Henv_m in Hloc_stable; eauto.
          destruct Hloc_stable as [Hsm_loc_stable Htm_loc_stable].
          unfolds loc_stable.
          destruct Hsm_loc_stable as [_ Hsm_loc_perm].
          destruct Htm_loc_stable as [_ Htm_loc_perm].
          rewrite <- Hsm_loc_perm.
          eapply apply_same_bf_perm_eq_stable with
          (m2 := memory tm') (m2' := tgm') in Happly_buf1; eauto.
          rewrite <- Happly_buf1; eauto.
        }
        {  
          rewrite Hgm_vb_eq in H0.
          lets Ht : H0.
          eapply GMem.invalid_noaccess in Ht; eauto.
          rewrite Ht.
          rewrite <- Hgm_vb_eq in H0.
          eapply GMem.invalid_noaccess in H0.
          rewrite H0 in eq_loc_perm.
          eapply apply_buf_maccess_eq_still with (m2 := memory tm') in Happly_buf1;
            eauto.
          rewrite <- Happly_buf1.
          rewrite <- eq_loc_perm; eauto.
        }
      }
      {
        lets Hm_cont_eq : Hnot_in_orig_objm.
        unfolds env_m_stable.
        destruct (Classical_Prop.classic (In b (GMem.validblocks gm))).
        { 
          eapply Henv_m in Hm_cont_eq; eauto.
          destruct Hm_cont_eq as [H_sm_loc_stable H_tm_loc_stable].
          unfolds loc_stable.
          destruct H_sm_loc_stable as [Hsm_loc_cont_eq _].
          destruct H_tm_loc_stable as [Htm_loc_cont_eq _].
          rewrite Hsm_loc_cont_eq in eq_loc_content.
          eapply gm_cont_eq_apply_same_buf_stable with (m1' := tgm) (m2' := tgm')
            in Htm_loc_cont_eq; eauto.
          rewrite <- Htm_loc_cont_eq; eauto.
        }
        {
          lets Ht : H0.
          rewrite Hgm_vb_eq in Ht.
          eapply Hcont_sm in Ht; eauto.
          rewrite <- Ht.
          assert (~ In b (GMem.validblocks tgm')).
          {
            rewrite Hgm_vb_eq in H0.
            intro. 
            contradiction H0; eauto.
            eapply Hvb_eq; eauto.
          }
          eapply not_in_apply_bf_vb_not_in_orign in H1; eauto.
          eapply Hcont_tm with (ofs := ofs) in H1; eauto.
          eapply gm_cont_eq_apply_same_buf_stable with (m1' := tgm) (m2' := tgm')
            in H1; eauto.
          rewrite <- H1; eauto.
        }
      }

      clear - Htm_vb_eq Hbf_eq Ic_buf_alloc_invalid.
      unfolds buf_alloc_invalid.
      unfold GMem.valid_block.
      rewrite <- Htm_vb_eq, <- Hbf_eq.
      eauto.

      clear - Htm_vb_eq Hbf_eq Ic_buf_alloc_norep.
      unfolds buf_alloc_norep.
      rewrite <- Hbf_eq; eauto.
    }  
    destruct Hbf as [Hbf_obj_alloc | Hbf_upd_objm].
    {    
      unfolds obj_alloc_b.  
      destruct Hbf_obj_alloc as [stk [Hnew_b [Htm_upd_bf [Hnew_blk Hnb_valid]]]].
      destruct Htm_upd_bf as [lo [hi [Htm_upd_bf Halloc]]].
      lets HMem_vb : Halloc.
      symmetry in HMem_vb.
      eapply alloc_add_new_vb in HMem_vb.
      unfolds env_m_stable.
      inversion HIc; subst; clear HIc.
      econstructor; eauto.
      introv Ht_neq Hnot_objm Hib_t1 Hib_t2.  
      clear - Htm_upd_bf Ht_neq Hnot_objm Halloc Hnew_b
                         Hib_t1 Hib_t2 Ic_no_conflict_bi Hnew_blk Htm_upd_bf.
      rewrite <- Htm_upd_bf in Hib_t1, Hib_t2.
      unfolds tupdate.  
      dis_if_else; subst.
      dis_if_else; subst.
      tryfalse.
      eapply in_buffer_app_or in Hib_t2. 
      destruct Hib_t2 as [Hib_t2 | Hib_t2]; eauto.

      eapply Ic_no_conflict_bi; eauto.
      clear - Hnew_b Hnot_objm Halloc Hnew_blk Hib_t1 Hib_t2 Ht_neq.
      destruct (peq b stk).
      {
        intro; subst.
        unfold obj_mem in H.
        destruct gm; simpls.
        destruct H.
        eapply invalid_noaccess in Hnew_b.
        rewrite Hnew_b in H; tryfalse.
      }
      {
        intro; contradiction Hnot_objm; clear Hnot_objm.
        unfolds alloc, obj_mem; inv Halloc; simpls.
        rewrite PMap.gso; eauto.
      }
      
      inversion Hib_t2; subst.
      simpl in H1.
      destruct H1; subst; tryfalse.
      inversion H2; subst.
      unfolds get_tsom_b.
      destruct tm'; simpls.
      assert (tso_buffers t1 = TSOMem.tso_buffers tm t1).
      {
        rewrite <- Htm_upd_bf.
        ex_match2; eauto.
      }
      specialize (Hnew_blk t1).
      contradiction Hnew_blk; eauto.
      ex_match2; subst.
      (*
      assert (t <> t1); eauto.
      eapply Hnew_blk in H3.
      rewrite <- H1 in Hib_t1.
      clear - Hib_t1 H3 H1.
      inversion Hib_t1; subst.
      contradiction H3.
      rewrite <- H1; eauto.
      dis_if_else; subst; eauto.
      eapply Hnew_blk in Ht_neq; eauto.
      eapply in_buffer_app_or in Hib_t1. 
      destruct Hib_t1; eauto.*)

      assert (b <> stk).
      {
        intro; subst.
        specialize (Hnew_blk t2).
        contradiction Hnew_blk; eauto.
      }  
      eapply Ic_no_conflict_bi with (t1 := t) (t2 := t2); eauto.
      intro.  
      contradiction Hnot_objm; clear Hnot_objm. clear - H0 H1 Halloc.
      unfolds alloc, obj_mem.
      inv Halloc; simpls.
      rewrite PMap.gso; eauto.
      eapply in_buffer_app_or in Hib_t1.
      destruct Hib_t1; eauto.
      simpl in H1.
      inv H1; subst.
      simpl in H2. 
      destruct H2; tryfalse; subst.
      inv H3; tryfalse.
      
      eapply Ic_no_conflict_bi with (t1 := t1) (t2 := t2); eauto.
      intro.
      assert (b <> stk).
      { 
        intro; subst.
        clear - Hnew_b Halloc H0.
        unfolds alloc, obj_mem.
        inv Halloc; simpls.
        destruct gm; simpls.
        destruct H0.
        eapply invalid_noaccess in Hnew_b.
        rewrite Hnew_b in H; tryfalse.
      }
      contradiction Hnot_objm.
      clear - H0 H1 Halloc.
      unfolds obj_mem, alloc.
      inv Halloc; simpls.
      rewrite PMap.gso; eauto.
   
      intros.
      lets Happly_buf : Hub_safe.
      eapply unbuffer_safe_apply_buffer' with (t := t0) in Happly_buf.
      destruct Happly_buf as [tgm Happly_buf].
      assert (~ obj_mem gm b ofs).
      {
        intro.
        contradiction H0.
        eapply Hobj_mem; eauto.
      }
      lets HIc_mem_eq : Happly_buf.  
      eapply Ic_mem_eq in HIc_mem_eq; eauto; clear Ic_mem_eq.
      inversion HIc_mem_eq; subst.
      assert (Hgm_vb_eq : GMem.valid_block gm' b <-> GMem.valid_block tgm' b).
      { split; intros. 
        { 
          unfolds GMem.valid_block.
          rewrite <- HMem_vb in H3.
          simpl in H3.  
          destruct H3; subst.
          {
            destruct (peq t0 t); subst.
            {
              rewrite <- Htm_upd_bf in H.
              rewrite tupdate_b_get in H.
              eapply alloc_in_buf_apply_buf_in_vb in H; eauto.
              eapply in_or_app; simpl; eauto.
            }
            {
              assert (t <> t0); eauto.
              eapply H1 in H3; eauto.
              rewrite <- Htm_upd_bf in H3.
              contradiction H3.
              rewrite tupdate_b_get.
              eapply in_buffer_app_or_rev; eauto.
              right.
              econstructor; eauto.
              simpl; eauto.
              econstructor; eauto.
            }
          }
          {
            eapply eq_loc_validity in H3.
            rewrite <- Htm_upd_bf in H.
            destruct (peq t0 t); subst.
            {
              rewrite tupdate_b_get in H.
              eapply apply_sub_bf_orign_b_impl_stable; eauto.
            }
            {
              rewrite tupdate_not_eq_get in H; eauto.
              eapply in_valid_block_eq_apply_same_buf_still with
              (m2 := memory tm') (m2' := tgm') in Happly_buf; eauto.
              rewrite Happly_buf in H3; eauto.
            }
          }
        }
        {
          unfolds GMem.valid_block.
          rewrite <- HMem_vb.
          rewrite <- Htm_upd_bf in H.
          unfold tupdate in H.
          dis_if_else; subst.
          {
            lets Ht : H.
            eapply in_apply_bf_mvb_in_orgin_m_or_bf_alloc in Ht; eauto.
            destruct Ht as [Ht | Ht].
            {
              rewrite <- Htm_vb_eq in Ht.
              eapply apply_buffer_in_validblocks_stable in Ht; eauto.
              eapply eq_loc_validity in Ht; eauto.
              simpl; eauto.
            }
            {
              destruct Ht as [lo0 [hi0 Hin_bf]].
              eapply in_or_app_rev in Hin_bf.
              destruct Hin_bf as [Hin_bf | Hin_bf].
              {
                eapply alloc_in_buf_apply_buf_in_vb in Hin_bf; eauto.
                eapply eq_loc_validity in Hin_bf.
                simpl; eauto.
              }
              {
                clear - Hin_bf.
                simpls.
                destruct Hin_bf; tryfalse.
                inversion H; subst; eauto.
              }
            }
          }
          {
            clear - H Happly_buf eq_loc_validity H3 Htm_vb_eq.
            eapply in_valid_block_eq_apply_same_buf_still in Htm_vb_eq; eauto.
            rewrite <- Htm_vb_eq in H3.
            eapply eq_loc_validity in H3.
            simpl; eauto.
          }
        }
      }
      econstructor; eauto.
      { 
        intros.
        specialize (eq_loc_perm k).
        clear Ic_no_conflict_bi eq_loc_content eq_loc_validity HIc_mem_eq.
        rewrite <- Htm_upd_bf in H.
        unfold tupdate in H.
        destruct (Classical_Prop.classic (In b (GMem.validblocks gm))).
        {
          lets Hloc_stable : H3.
          eapply Henv_m in Hloc_stable; eauto.
          unfold loc_stable in Hloc_stable.
          split_and Hloc_stable.
          rewrite <- H7.
          rewrite eq_loc_perm.
          assert (Hb_not_newb : b <> stk).
          {
            intro; subst; tryfalse.
          }
          dis_if_else; subst.
          {
            clear - H Happly_buf H8 H Hb_not_newb.
            eapply apply_buf_alloc_mem_access_b_not_new_access_eq in H8; eauto.
            rewrite H8; eauto.
          }
          {
            eapply apply_buf_maccess_eq_still in Hm_access; eauto.
            rewrite Hm_access; eauto.
          }
        }
        {
          dis_if_else; subst.
          {
            destruct (peq b stk); subst.
            {
              clear - H Halloc.
              symmetry in Halloc.
              eapply alloc_nb_access in Halloc.
              rewrite Halloc.
              eapply apply_buf_tail_alloc_nb_access in H.
              rewrite H; eauto.
            }
            { 
              symmetry in Halloc.
              eapply alloc_not_nb_access_stable in Halloc; eauto.
              rewrite <- Halloc.
              assert ((GMem.mem_access (memory tm')) !! b ofs k =
                      (GMem.mem_access (memory tm)) !! b ofs k).
              {
                rewrite Hm_access; eauto.
              }
              eapply apply_buf_not_b_access_stable with (m1' := tgm') (m2' := tgm)
                in H5; eauto.
              rewrite H5; eauto.
            }
          }
          {
            destruct (peq b stk); subst.
            {
              clear - n H1 Htm_upd_bf.
              rewrite <- Htm_upd_bf in H1.
              assert (t <> t0); eauto.
              eapply H1 in H.
              contradiction H.
              econstructor.
              rewrite tupdate_b_get; eauto.
              eapply in_or_app.
              right; simpl; eauto.
              econstructor; eauto.
            }
            {
              symmetry in Halloc.
              eapply alloc_not_nb_access_stable in Halloc; eauto.
              rewrite <- Halloc.
              assert ((GMem.mem_access (memory tm)) !! b ofs =
                      (GMem.mem_access (memory tm')) !! b ofs).
              rewrite Hm_access; eauto.
              eapply apply_same_bf_perm_eq_stable in H5; eauto.
              rewrite <- H5; eauto.
            }
          }
        }
      }
      { 
        clear Ic_no_conflict_bi eq_loc_perm eq_loc_validity HIc_mem_eq.
        rewrite <- Htm_upd_bf in H.
        unfold tupdate in H.
        destruct (Classical_Prop.classic (In b (GMem.validblocks gm))).
        {
          lets Hm_cont : H3.
          eapply Henv_m in Hm_cont; eauto.
          unfolds loc_stable.
          split_and Hm_cont.
          rewrite <- H6.
          assert (Hb_not_newb : b <> stk).
          { 
            intro; subst; tryfalse.
          }
          dis_if_else; subst.
          {
            eapply apply_buf_alloc_mem_access_b_not_new_contents_eq
            with (m1' := tgm) (m2' := tgm') in H4; eauto.
            rewrite <- H4; eauto.
          }
          {
            eapply gm_cont_eq_apply_same_buf_stable
              with (m1' := tgm) (m2' := tgm') in H4; eauto.
            rewrite <- H4; eauto.
          }
        }
        {
          dis_if_else.
          {
            destruct (peq stk b); subst.
            {
              clear - H Halloc.
              symmetry in Halloc.
              eapply alloc_nb_content in Halloc.
              rewrite Halloc.
              eapply apply_buf_tail_alloc_nb_contents in H.
              rewrite H; eauto.
            }
            {
              assert (~ In b (GMem.validblocks gm')).
              {
                clear - n Halloc H3.
                unfolds alloc.
                inversion Halloc; subst; clear Halloc; simpls.
                intro.
                destruct H; subst; tryfalse.
              }
              eapply Hcont_sm in H5; eauto.
              rewrite <- H5.
              assert (~ In b (GMem.validblocks gm')).
              { 
                clear - H3 HMem_vb n.
                intro.
                contradiction H3.
                rewrite <- HMem_vb in H.
                simpl in H.
                destruct H; subst; tryfalse; eauto.
              }
              assert (~ In b (GMem.validblocks tgm')).
              {
                intro. 
                contradiction H6; eauto.
                eapply Hgm_vb_eq; eauto.
              }
              lets Happly_buf1 : H.
              eapply not_in_apply_bf_vb_not_in_orign in H; eauto.
              eapply Hcont_tm with (ofs := ofs) in H; eauto.
              eapply gm_cont_eq_apply_buf_not_alloc_stable
              with (m1' := tgm) (m2' := tgm') in H; eauto.
              rewrite <- H; eauto.
            }
          }
          {
            assert (b <> stk).
            {
              rewrite <- Htm_upd_bf in H1.
              intro; subst.
              assert (t <> t0); eauto.
              eapply H1 in H5.
              contradiction H5.
              rewrite tupdate_b_get; eauto.
              econstructor.
              eapply in_or_app; right; simpl; eauto.
              econstructor; eauto.
            }

            assert (~ In b (GMem.validblocks gm')).
            {
              clear - H3 H5 HMem_vb.
              intro.
              contradiction H3.
              rewrite <- HMem_vb in H.
              simpl in H.
              destruct H; subst; tryfalse.
            }

            lets Ht : H6.
            eapply Hcont_sm in H6.
            rewrite <- H6.

            assert (~ In b (GMem.validblocks tgm')).
            {
              clear - Hgm_vb_eq Ht.
              unfolds GMem.valid_block.
              intro.
              contradiction Ht.
              eapply Hgm_vb_eq; eauto.
            }

            lets Ht1 : H7.
            eapply not_in_apply_bf_vb_not_in_orign in H7; eauto.
            eapply Hcont_tm in H7; eauto.
            eapply gm_cont_eq_apply_same_buf_stable
            with (m1' := tgm) (m2' := tgm') in H7; eauto.
            rewrite <- H7; eauto.
          }
        }
      }
 
      rewrite <- Htm_upd_bf in H1.
      clear - H1.
      intros.
      lets Ht : H.
      eapply H1 in H.
      clear - H Ht.
      unfolds tupdate.
      dis_if_else; subst; eauto.
      {
        intro.
        eapply H.
        inversion H1; subst.
        econstructor; eauto.
        eapply in_or_app; eauto.
      }
      clear - Hnew_blk Htm_upd_bf Ic_buf_alloc_invalid Hnb_valid Htm_vb_eq.
      unfolds buf_alloc_invalid.
      intros.
      rewrite <- Htm_upd_bf in H.
      destruct (peq t t0) eqn:?; subst.
      {
        rewrite tupdate_b_get in H.
        unfold GMem.valid_block.
        rewrite <- Htm_vb_eq; eauto.
        eapply in_app in H.
        destruct H; eauto.
        unfold GMem.valid_block in Ic_buf_alloc_invalid; eauto.
        simpl in H.
        destruct H; tryfalse; subst.
        inv H; eauto.
      }
      {
        rewrite tupdate_not_eq_get in H;eauto.
        apply Ic_buf_alloc_invalid in H as ?.
        intro;contradict H0.
        unfold GMem.valid_block in *.
        congruence.
      }
      {
        destruct tm' as [bufs' tgm']. simpl in *. subst bufs'.
        eapply alloc_norep_preserve; eauto.
        intros. intro C. eapply Hnew_blk. eexists.
        econstructor. eauto. subst. constructor.
        Unshelve. auto. auto.
      }
    }
    {
      unfolds obj_upd_objm.
      (*
      destruct Hbf_upd_objm as
          [b [ofs [n [Hin_obj_mem [Hbf_upd_objm [Hvb_eq Hnot_in_oth_bf]]]]]].*)
      destruct Hbf_upd_objm as
          [b [ofs [n [Hin_obj_mem [Hbf_upd_objm Hvb_eq]]]]].
      unfolds env_m_stable.
      inversion HIc; eauto. 
      econstructor; eauto.
      {   
        clear - Ic_no_conflict_bi Hbf_upd_objm Henv_m Hvb_eq Hobj_mem Hin_obj_mem.
        rewrite <- Hbf_upd_objm; intros.
        unfolds tupdate.
        dis_if_else; subst.
        dis_if_else; subst.
        tryfalse.  
        eapply in_buffer_app_or in H2. 
        destruct H2; eauto.
        {
          inversion H2; subst.
          simpl in H5. 
          destruct H5; subst; tryfalse.
          inversion H6; subst.
          eapply Hin_obj_mem in H12.
          eapply Hobj_mem in H12; tryfalse.
        }
        { 
          dis_if_else; subst; eauto.
          eapply in_buffer_app_or in H1.
          destruct H1; eauto.
          inversion H1; subst.
          simpl in H5.
          destruct H5; subst; tryfalse.
          inversion H6; subst.
          eapply Hin_obj_mem in H12.
          eapply Hobj_mem in H12; tryfalse.
        }
      }
      {
        intros.
        lets Happly_buf : Hub_safe.
        eapply unbuffer_safe_apply_buffer' with (t := t0) in Happly_buf.
        destruct Happly_buf as [tgm Happly_buf].
        assert (~ obj_mem gm b0 ofs0).
        {
          intro.
          contradiction H0.
          eapply Hobj_mem; eauto.
        }
        lets HIc_mem_eq : Happly_buf.  
        eapply Ic_mem_eq in HIc_mem_eq; eauto; clear Ic_mem_eq.
        inversion HIc_mem_eq; subst.
        assert (Hgm_vb_eq : GMem.valid_block gm' b0 <-> GMem.valid_block tgm' b0).
        {
          unfolds GMem.valid_block.
          split; intros.
          {
            rewrite <- Hvb_eq in H3.
            eapply eq_loc_validity in H3.
            clear - Htm_vb_eq H Happly_buf Hbf_upd_objm H3.
            rewrite <- Hbf_upd_objm in H; clear Hbf_upd_objm.
            unfolds tupdate.
            dis_if_else; subst.
            {
              eapply apply_buf_prefix_in_apply_more_still ; eauto.
            }
            {
              eapply in_valid_block_eq_apply_same_buf_still in Htm_vb_eq; eauto.
              rewrite <- Htm_vb_eq; eauto.
            }
          }
          {
            rewrite <- Hvb_eq.
            eapply eq_loc_validity.
            rewrite <- Hbf_upd_objm in H.
            unfold tupdate in H.
            dis_if_else; subst.
            {
              clear - H Happly_buf Htm_vb_eq H3.
              eapply apply_buf_orign_vb_eq_add_store_item_vb_eq_still in Htm_vb_eq;
                eauto.
              rewrite Htm_vb_eq; eauto.
            }
            {
              eapply in_valid_block_eq_apply_same_buf_still in Htm_vb_eq; eauto.
              rewrite Htm_vb_eq; eauto.
            }
          }
        }

        rewrite <- Hbf_upd_objm in H.
        econstructor; eauto; intros.
        {
          specialize (eq_loc_perm k).
          unfold tupdate in H.
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks gm))).
          {
            lets Hloc_stable : H2.
            eapply Henv_m in Hloc_stable; eauto.
            unfold loc_stable in Hloc_stable.
            split_and Hloc_stable. 
            rewrite <- H7.
            dis_if_else; subst.
            {
              eapply apply_buf_orign_access_eq_add_store_item_access_eq_still
                in Hm_access; eauto.
              rewrite <- Hm_access; eauto.
            }
            {
              eapply apply_buf_maccess_eq_still in Hm_access; eauto.
              rewrite <- Hm_access; eauto.
            }
          }
          {
            rewrite Hvb_eq in H3. 
            assert ((GMem.mem_access gm') !! b0 ofs0 k = None).
            {
              eapply GMem.invalid_noaccess; eauto.
            }
            rewrite H4.
            assert (~ In b0 (GMem.validblocks tgm')).
            {
              clear - Hgm_vb_eq H3.
              intro.
              contradiction H3.
              unfolds GMem.valid_block.
              eapply Hgm_vb_eq; eauto.
            }
            eapply GMem.invalid_noaccess in H5; eauto.
          }
        }
        {
          unfold tupdate in H.
          assert (Hnot_objm : b0 <> b \/
                              (b0 = b /\ ((ofs0 < ofs)%Z \/
                                         (ofs0 >= ofs + size_chunk Mint32)%Z))).
          {
            clear - Hin_obj_mem H2.
            destruct (peq b0 b); subst; eauto.
            {
              right.
              split; eauto.
              lets Ht : inrange_or_not1 ofs0 ofs (size_chunk Mint32).
              destruct Ht; eauto.
              eapply Hin_obj_mem in H; tryfalse.
            }
          }
          destruct (Classical_Prop.classic (In b0 (GMem.validblocks gm))).
          {
            eapply Henv_m in H3; eauto.
            unfold loc_stable in H3.
            split_and H3.
            rewrite <- H3.
            dis_if_else; subst.
            {
              destruct Hnot_objm as [Hnot_objm | Hnot_objm].
              {
                clear - H Happly_buf Hnot_objm H4 eq_loc_content.
                eapply apply_bf_tail_store_not_same_block_cont_stable
                with (m1' := tgm) (m2' := tgm') in H4; eauto.
                rewrite <- H4; eauto.
              }
              {
                clear - H Happly_buf Hnot_objm H4 eq_loc_content.
                split_and Hnot_objm; subst.
                eapply apply_bf_tail_store_not_same_range_cont_stable
                with (m1' := tgm) (m2' := tgm') in H4; eauto.
                rewrite <- H4; eauto.
              }
            }
            {
              eapply gm_cont_eq_apply_same_buf_stable
              with (m1' := tgm) (m2' := tgm') in H4; eauto.
              rewrite <- H4; eauto.
            }
          }
          {
            rewrite Hvb_eq in H3.
            lets Ht1 : H3.
            eapply Hcont_sm in Ht1.
            rewrite <- Ht1; eauto.
            assert (~ In b0 (GMem.validblocks tgm')).
            {
              clear - H3 Hgm_vb_eq.
              intro.
              eapply H3; eauto.
              eapply Hgm_vb_eq; eauto.
            }
            eapply not_in_apply_bf_vb_not_in_orign in H4; eauto.
            eapply Hcont_tm with (ofs := ofs0) in H4; eauto.
            dis_if_else; subst.
            {
              destruct Hnot_objm as [Hnot_objm | Hnot_objm].
              {
                eapply apply_bf_tail_store_not_same_block_cont_stable with
                (m1' := tgm) (m2' := tgm') in H4; eauto.
                rewrite <- H4; eauto.
              }
              {
                destruct Hnot_objm; subst.
                eapply apply_bf_tail_store_not_same_range_cont_stable with
                (m1' := tgm) (m2' := tgm') in H4; eauto.
                rewrite <- H4; eauto.                
              }
            }
            {
              eapply gm_cont_eq_apply_same_buf_stable
              with (m1' := tgm) (m2' := tgm') in H4; eauto.
              rewrite <- H4; eauto.
            }
          }
        }

        rewrite <- Hbf_upd_objm in H1.
        clear - H1; intros. 
        eapply H1 in H; eauto.
        intro.
        contradiction H.
        unfold tupdate.
        ex_match2; eauto; subst.
        eapply in_buffer_app_or_rev; eauto.
      }
      { 
        unfold buf_alloc_invalid. rewrite <- Hbf_upd_objm. unfold tupdate.
        intros t0 b0 lo hi. destruct peq.
        { subst. intro. apply in_app in H. destruct H.
          unfold GMem.valid_block. rewrite <- Htm_vb_eq. eapply Ic_buf_alloc_invalid; eauto.
          simpl in H. destruct H as [H|H]; inv H. }
        { intro. unfold GMem.valid_block. rewrite <- Htm_vb_eq. eapply Ic_buf_alloc_invalid; eauto. }
      }
      { destruct tm' as [bufs' tgm']. simpl in *. subst bufs'.
        eapply alloc_norep_preserve; eauto.
      }
    }
    Unshelve. auto.
  Qed.

  (** [RepectPerm (Io, Ro, Go)] ======> [Gc] *)
  Lemma RP_Io_Sta_Gc:
    forall ge t, Sta (Io ge) (Gc t).
  Proof. 
    inversion HRP; subst.
    clear - Ip; intros.
    unfold Sta; intros.
    eapply Ip; eauto.
    clear - H0.
    unfolds Gc, env_not_touch_objm.
    split_and H0.
    repeat (split; eauto).
    exists t.
    right.
    split; eauto.
    split; eauto.
    inversion H0; eauto.
  Qed.

  (** [Go] ======> [Rc] *)
  Lemma RP_Go_Implies_Rc:
    forall ge t t', Implies' Ic (Go ge t) (Rc t').
  Proof.
    unfold Implies'.
    intros.
    unfold Rc.
    split; eauto.
    eapply RP_Ic_Sta_Go; eauto.
  Qed.

  (** [Gc] ======> [Ro] *)
  Lemma RP_Gc_Implies_Ro:
    forall t ge t', t <> t' -> Implies' (Io ge) (Gc t) (Ro ge t').
  Proof.
    intros.
    inversion HRP; subst.
    unfold Implies'; intros.
    eapply Rp; eauto; intros.
    {
      clear - H1 H2.
      unfolds Gc.
      split_and H1.
      eapply H3 in H2.
      inversion H2; subst.
      unfolds loc_stable.
      split; eauto.
      eapply FunctionalExtensionality.functional_extensionality; eauto.
    }
    { 
      exists t.
      split; eauto.
      clear - H1.
      split.
      unfolds Gc. 
      split_and H1; eauto.
      right.
      unfolds Gc.
      split_and H1.
      renames H4 to bis.
      unfold env_inbuffer_step.
      split; eauto.
      split; eauto.
      clear - H1.
      inversion H1; subst; eauto.
    }
  Qed.
  
End RP_RGI_Props.