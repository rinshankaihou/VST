From mathcomp.ssreflect Require Import fintype ssrnat.                
Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
 
Require Import Asm.  

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset. 
Require Import loadframe. 

Require CminorLang. 
Require SpecLang.
(** This file shows that the implementation of the spain-lock and its 
specification satisfies the definition of object correctness (corresponding 
to definition 26 in submission #115 supplemental text). The Coq code in this file 
can be viewed as the proof of [Lemma 43] (Lock impl. correctness) in submission 
#115 supplemental text. *)
Require Import ASM_local. 
Require Import AsmLang.
Require Import AsmTSO.

Require Import Coq.Lists.Streams.

Require Import RGRels.
Require Import LibTactics.

Require Import code.
Require Import ObjectSim.
Require Import TSOGlobSem.
Require Import InvRG. 

Require Import AuxTacLemmas.
Require Import TSOMemLemmas MemLemmas FMemLemmas.
Require Import ObjLemmas.
Require Import ObjRGIProp.

(** The definition of object correctness tells that there exists Ro, Go and Io, 
such that the following propositions hold : 
- the implementation and its corresponding specification satisfies 
  object simulation (proved by [Theorem LockProof] in this file).
- [RespectPerm (Io, Ro, Go)], and we call it [RespectPermission] in paper    
  (proved by [Theorem Lock_RGI_satisfy_RespectPerm] in this file).
- Io is stable under Ro   
  (proved by [Theorem H_sta_oo] in this file).
- Go can imply Ro   
  (proved by [Theorem H_rg_oo] in this file).
 *)

(** ** Auxiliary MemLemmas *)
Lemma obj_mem_eq_on_loc_obj_inv_stable :
  forall ge M M' tm,
    GMem.forward M M' ->
    obj_inv ge M tm ->
    (forall b ofs, obj_mem M b ofs -> eq_on_loc b ofs M M') ->
    obj_inv ge M' tm.
Proof.
  introv Hgm_forward.
  intros.
  unfolds obj_inv.
  destruct H as [L H].
  split_and H.
  exists L.
  repeat (split; eauto).
  clear - H H0 H5.
  destruct H.
  {
    left.
    unfolds lock_st.
    split_and H.
    split.
    eapply loc_stable_load_same; eauto.
    intros.
    eapply H5 in H2.
    eapply H0 in H2.
    inversion H2; subst.
    unfold loc_stable.
    split; eauto.
    eapply functional_extensionality; intros.
    rewrite eq_loc_perm; eauto.
    split; eauto.
  }
  {
    right.
    unfolds unlock_st.
    split_and H.
    split; eauto.
    clear - H1 H5 H0.
    eapply loc_stable_load_same; eauto.
    intros.
    eapply H5 in H.
    eapply H0 in H.
    inversion H; subst.
    unfold loc_stable.
    split; eauto.
    eapply functional_extensionality; intros.
    rewrite eq_loc_perm; eauto.
  }
  {
    intros.
    specialize (H2 n).
    destruct H2 as [M'' H2].
    eapply loc_stable_store_still; eauto.
    simpls; intros.
    eapply H5 in H7.
    eapply H0 in H7.
    inversion H7; subst.
    unfold loc_stable.
    split; eauto.
    eapply functional_extensionality; intros.
    rewrite eq_loc_perm; eauto.
  }
  {
    eapply H5 in H7.
    lets Heq_on_loc : H7.
    eapply H0 in Heq_on_loc.
    clear - H7 Heq_on_loc.
    unfolds obj_mem.
    split_and H7.
    inversion Heq_on_loc; subst.
    intro.
    contradiction H.
    rewrite eq_loc_perm; eauto.
  }
  {
    eapply H5 in H7.
    lets Heq_on_loc : H7.
    eapply H0 in Heq_on_loc.
    clear - H7 Heq_on_loc.
    unfolds obj_mem.
    split_and H7.
    inversion Heq_on_loc; subst.
    rewrite <- eq_loc_perm; eauto.
  } 
  { 
    assert (In L (GMem.validblocks M)).
    {
      specialize (H2 Int.zero).
      clear - H2.
      destruct H2 as [M' H2].
      eapply store_succ_invb; eauto.
    }
    eapply H8 with (k := k) (p := p) in H7.
    clear - H7 H9 Hgm_forward.
    intro.
    destruct H7.
    contradiction H0.
    inversion Hgm_forward; subst.
    unfolds GMem.perm; eauto.
  }
  {
    eapply H8 with (p := p) (k := k) in H7.
    destruct H7; eauto.
  }
Qed.
  
Lemma obj_inv_env_inbuffer_stable :
  forall ge M tm M' tm' t,
    obj_inv ge M tm -> GMem.forward M M' ->
    (forall (b : block) (ofs : Z), obj_mem M b ofs -> loc_stable M M' b ofs) ->
    env_inbuffer_step t M M' tm tm' ->
    obj_inv ge M' tm'.
Proof. 
  intros.
  unfolds obj_inv.
  destruct H as [L H].
  split_and H.
  exists L. split; eauto.
  unfolds env_inbuffer_step.
  split_and H2.
  
  renames H11 to bis.
  assert (HL_vb : In L (GMem.validblocks M)).
  {
    clear - H4.
    specialize (H4 Int.zero).
    destruct H4 as [M' H4].
    eapply store_succ_invb; eauto.
  }   
  destruct H.
  { 
    split.
    { 
      left; unfolds lock_st.
      split_and H.
      split.
      eapply loc_stable_load_same; eauto.
      split.
      renames H12 to Hunbuffer_safe.   
      clear - H H2 H7 H10 H0 H14 HL_vb Hunbuffer_safe H9.
      intros.
      lets Hnot_inbuffer : H.
      specialize (H t0).
      intro. 
      contradiction H; clear H.
      destruct H1 as [ofs H1].
      rewrite H2 in H1.
      unfold tupdate in H1.
      ex_match2; subst; eauto.
      { 
        (* have to change in the future *)
        eapply in_buffer_app_or in H1.
        destruct H1; eauto.
        assert (forall t,
                   ~ (exists lo hi, In (BufferedAlloc L lo hi)
                                       (tso_buffers tm' t))).
        {
          clear - H2 Hunbuffer_safe Hnot_inbuffer H14 H7.
          intros.
          try rewrite H2 in *.
          unfold tupdate.
          ex_match2; subst.
          intro.
          destruct H as (lo & hi & H).
          eapply in_or_app_rev in H.
          destruct H.
          specialize (Hnot_inbuffer t).
          contradiction Hnot_inbuffer.
          exists 0%Z.
          econstructor; eauto.
          econstructor; eauto.
          specialize (Hnot_inbuffer t).
          assert (in_buffer bis L 0%Z).
          econstructor; eauto.
          econstructor; eauto.
          eapply H14 in H0.
          contradiction H0.
          eapply H7; simpl; Lia.lia.
          intro.
          destruct H as (lo & hi & H).
          specialize (Hnot_inbuffer t0).
          contradiction Hnot_inbuffer.
          exists 0%Z.
          econstructor; eauto.
          econstructor; eauto.
        }  
        pose proof inrange_or_not1. 
        specialize (H3 ofs 0%Z (size_chunk Mint32)). 
        destruct H3.
        eapply H7 in H3; tryfalse.
        eapply H14 in H; tryfalse.
        eapply unbuffer_safe_noalloc_noperm_not_inbuffer
          with (t := t) in H1; eauto.
        contradiction H1.
        rewrite H2, tupdate_b_get.
        eapply in_buffer_app_or_rev; eauto.
        assert ((ofs >= 0 + size_chunk Mint32)%Z \/ (ofs < 0)%Z).
        destruct H3; eauto.
        intros.
        eapply H10 in H4.
        rewrite <- H9; destruct H4; eauto.
      }
      {
        clear - H15 H9.
        unfolds load_tsomem.
        destruct tm, tm'; simpls; subst; eauto.
      }
    }
    split.
    {
      clear - H4 H7 H1.
      intros.
      specialize (H4 n).
      destruct H4 as [M'' H4].
      eapply loc_stable_store_still; eauto.
    }
    split.
    {
      clear - H5 H9.
      intros.
      specialize (H5 n).
      destruct H5 as [bm' Hstore_tsom].
      unfolds store_tsomem.
      destruct tm, tm'; simpls; subst.
      destruct (store Mint32 memory0 L 0 (Vint n)) eqn:?; simpls; tryfalse.
      eauto.
    }
    split; eauto.
    split.
    {
      clear - H7 H1.
      intros.
      eapply H7 in H.
      lets Hloc_stable : H.
      eapply H1 in Hloc_stable.
      eapply obj_mem_loc_stable_still; eauto.
    }
    split.
    {
      intros.
      eapply H8 in H11.
      destruct H11 as [p [Hmem_access Hperm]].
      clear - H9 Hmem_access Hperm.
      exists p.
      unfolds get_gm.
      destruct tm, tm'; simpls; subst; eauto.
    }
    {
      intros.
      eapply H10 with (k := k) (p := p) in H11.
      clear - H0 H11 HL_vb H9.
      destruct H11.
      split; [intro | ].
      contradiction H.
      clear - H0 H2 HL_vb.
      inversion H0; subst.
      eapply alloc_forward; eauto.
      rewrite <- H9; eauto.
    }
  }
  {
    split.
    {
      right.
      unfolds unlock_st.
      split_and H.
      split.
      {
        eapply loc_stable_load_same; eauto.
      }
      destruct H13.
      { 
        destruct H as [t' [bf1 [bf2 H]]].
        split_and H.
        left. exists t'. 
        assert (forall t, ~ (exists lo hi, In (BufferedAlloc L lo hi) (tso_buffers tm' t))).
        {
          intros.
          rewrite H2.
          unfold tupdate. 
          ex_match2; subst.
          intro Halloc. 
          destruct Halloc as (lo & hi & Halloc). 
          eapply in_or_app_rev in Halloc.
          destruct Halloc.   
          destruct (peq t' t). subst.
          rewrite H13 in H16.
          eapply in_or_app_rev in H16.
          contradiction (H15 0%Z).
          destruct H16.
          econstructor; eauto.
          eapply in_or_app; eauto.
          econstructor; eauto.
          simpl in H16.
          destruct H16; tryfalse.
          econstructor; eauto.
          eapply in_or_app; eauto.
          econstructor; eauto.
          eapply H in n.
          contradiction n.
          econstructor; eauto.
          econstructor; eauto.
          assert (in_buffer bis L 0%Z).
          econstructor; eauto.
          econstructor; eauto.
          eapply H14 in H18.
          assert ((0 <= 0 < size_chunk Mint32)%Z); simpl.
          Lia.lia.
          eapply H7 in H19; tryfalse.
          destruct (peq t0 t'); subst.
          assert (t' <> t); eauto.
          intro.
          destruct H18 as (lo & hi & H18).
          rewrite H13 in H18.
          clear - H15 H18.
          eapply in_app_or in H18.
          destruct H18.
          contradiction (H15 0%Z).
          econstructor; eauto.
          eapply in_or_app; eauto.
          econstructor; eauto.
          simpls.
          destruct H; tryfalse.
          contradiction (H15 0%Z).
          econstructor; eauto.
          eapply in_or_app; eauto.
          econstructor; eauto.
          assert (t' <> t0); eauto.
          intro.
          destruct H18 as (lo & hi & H18).
          eapply H in H16.
          contradiction H16; econstructor; eauto.
          econstructor; eauto.
        }
        destruct (peq t' t); subst.
        { 
          exists bf1 (bf2 ++ bis).
          rewrite H2.
          rewrite tupdate_b_get; eauto.
          rewrite H13. rewrite <- app_assoc; simpl.
          split; eauto.
          split.
          intros.
          rewrite tupdate_not_eq_get; eauto.
          split. 
          clear - H15 H14 H0 HL_vb H7 H10 H12 H2 H H13 H9 H16.
          intros; intro H_in_buffer.
          rewrite app_assoc in H_in_buffer.
          eapply in_buffer_app_or in H_in_buffer; eauto.
          specialize (H15 ofs). 
          destruct H_in_buffer; tryfalse. 
          eapply unbuffer_safe_noalloc_noperm_not_inbuffer in H16; eauto.
          rewrite H2 in H16.
          contradiction H16.
          rewrite tupdate_b_get.
          eapply in_buffer_app_or_rev; eauto.
          intros.
          rewrite <- H9.
          pose proof inrange_or_not1.
          specialize (H3 ofs 0%Z (size_chunk Mint32)).
          destruct H3.
          eapply H7 in H3.
          eapply H14 in H1; tryfalse.
          assert ((ofs >= 0 + size_chunk Mint32)%Z \/ (ofs < 0)%Z).
          destruct H3; eauto.
          eapply H10 in H4; destruct H4; eauto.
          clear - H17 H9.
          unfolds load_tsomem.
          destruct tm, tm'; simpls; subst; eauto.
        }
        {  
          exists bf1 bf2.
          rewrite H2.
          rewrite tupdate_not_eq_get; eauto.
          split; eauto.
          split.
          intros.
          unfold tupdate.
          ex_match2; subst; eauto.
          eapply H with (ofs := ofs) in H18. 
          clear - H16 H14 H7 H0 HL_vb H10 H H18 H12 H2 H9.
          intro H_in_buffer.
          contradiction H18; clear H18.
          eapply in_buffer_app_or in H_in_buffer; destruct H_in_buffer; eauto. 
          eapply unbuffer_safe_noalloc_noperm_not_inbuffer in H16; eauto.
          rewrite H2 in H16.
          contradiction H16; rewrite tupdate_b_get; eauto.
          eapply in_buffer_app_or_rev; eauto.
          intros; rewrite <- H9; intro.
          pose proof inrange_or_not1.
          specialize (H4 ofs 0%Z (size_chunk Mint32)).
          destruct H4.
          eapply H7 in H4; eapply H14 in H1; tryfalse.
          assert ((ofs >= 0 + size_chunk Mint32)%Z \/ (ofs < 0)%Z).
          destruct H4; eauto.
          eapply H10 in H5; destruct H5; eauto.
          split; eauto.
          clear - H17 H9.
          unfolds load_tsomem.
          destruct tm, tm'; simpls; subst; eauto.
        }
      }
      {
        right.
        destruct H.
        split.
        {
          clear - H H9.
          destruct tm, tm'; simpls; subst; eauto.
        }
        {
          rewrite H2.
          intros.
          unfold tupdate.
          ex_match2; subst; eauto.
          lets Hnot_inbuffer : H13.
          specialize (H13 t ofs).
          clear - H13 H0 H14 HL_vb H10 H7 H12 Hnot_inbuffer H2 H9.
          intro.
          contradiction H13.
          eapply in_buffer_app_or in H; destruct H; eauto.
          assert (forall t,  ~ (exists lo hi, In (BufferedAlloc L lo hi) (tso_buffers tm' t))).
          {
            intros; intro.
            destruct H1 as (lo & hi & H1).
            rewrite H2 in H1.
            unfold tupdate in H1.
            ex_match2; subst.
            specialize (Hnot_inbuffer t ofs).
            eapply in_app_or in H1.
            destruct H1.
            contradiction Hnot_inbuffer; econstructor; eauto.
            econstructor; eauto.
            assert (in_buffer bis L 0%Z).
            econstructor; eauto.
            econstructor; eauto.
            eapply H14 in H3.
            assert ((0 <= 0 < size_chunk Mint32)%Z).
            simpl; Lia.lia.
            eapply H7 in H4; tryfalse.
            specialize (Hnot_inbuffer t0 0%Z).
            contradiction Hnot_inbuffer.
            econstructor; eauto.
            econstructor; eauto.
          }
          eapply unbuffer_safe_noalloc_noperm_not_inbuffer in H1; eauto.
          rewrite H2 in H1.
          rewrite tupdate_b_get in H1.
          contradiction H1.
          eapply in_buffer_app_or_rev; eauto.
          intros; intro.
          rewrite <- H9 in H3.
          eapply H14 in H.
          pose proof inrange_or_not1.
          specialize (H4 ofs 0%Z (size_chunk Mint32)).
          destruct H4.
          eapply H7 in H4; tryfalse.
          assert ((ofs >= 0 + size_chunk Mint32)%Z \/ (ofs < 0)%Z).
          destruct H4; eauto.
          eapply H10 in H5; destruct H5; eauto.
        }
      }
    }
    split.
    {
      clear - H4 H1 H7.
      intros.
      specialize (H4 n).
      destruct H4 as [M'' H4].
      eapply loc_stable_store_still; eauto.
    }
    split.
    {
      clear - H5 H9.
      intros.
      specialize (H5 n).
      destruct H5 as [bm' Hstore].
      destruct tm, tm'; simpls; subst.
      destruct (store Mint32 memory0 L 0 (Vint n)) eqn:?; simpls; tryfalse.
      eexists; eauto.
    }
    split; eauto.
    split.
    {
      clear - H7 H1.
      intros.
      eapply H7 in H.
      lets Hloc_stable : H.
      eapply H1 in Hloc_stable.
      eapply obj_mem_loc_stable_still; eauto.
    }
    split.
    {
      intros.
      eapply H8 in H11; clear - H11 H9.
      unfolds get_gm; destruct tm, tm'; simpls; subst; eauto.
    }
    {
      intros.
      eapply H10 with (k := k) (p := p) in H11; eauto.
      clear - H0 HL_vb H11 H9.
      split.
      intro.
      destruct H11.
      contradiction H1.
      clear - H0 HL_vb H.
      inversion H0; subst.
      unfolds GMem.perm.
      eapply alloc_forward; eauto.
      rewrite <- H9.
      destruct H11; eauto.
    }
  }
  Unshelve.
  exact 0%Z.
  exact 0%Z.
Qed.
  
(** * Theorem about lock proof *)
(** [Io] is stable under [Go] *)
Theorem H_sta_oo :
  forall ge t,
    Sta (obj_inv ge) (Gobj ge t).
Proof.
  unfold Sta.
  introv Hobj_inv Hg_obj.
  unfolds Gobj.
  destruct Hg_obj as [H_lock | Hg_obj].
  unfolds G_lock.
  split_and H_lock.
  eauto.
  destruct Hg_obj as [Hunlock | Hg_obj].
  unfolds G_unlock.
  split_and Hunlock.
  eauto.
  destruct Hg_obj as [Hid | Hg_obj].
  unfolds Id.
  split_and Hid.
  subst; eauto.
  unfolds G_alloc.
  split_and Hg_obj.
  eauto.
Qed.

(** [Go] can imply [Ro] *)
Theorem H_rg_oo :
  forall t t' ge,
    t <> t' -> Implies (Gobj ge t) (Robj ge t').
Proof.
  introv Ht_neq.
  unfold Implies.
  introv Hg_obj.
  unfold Robj.
  eexists.
  split; eauto.
Qed.

(** [Io] is stable under unbuffer step *)
Theorem H_sta_o_ub :
  forall ge,
    UBSta (obj_inv ge).
Proof. 
  intros.
  unfold UBSta.
  introv Hobj_inv Hg_ub.
  unfolds G_ub.
  destruct Hg_ub as [Hgm Hunbuffer].
  subst.
  destruct Hunbuffer as [t Hunbuffer].
  unfolds unbuffer.
  destruct (tso_buffers tm t) eqn:Hbf; tryfalse.
  unfolds obj_inv.
  destruct Hobj_inv as [L [Hfind_find [Hst Hobj_inv]]].
  split_and Hobj_inv.
  eexists.
  split; eauto.
  destruct Hst as [Hlock_st | Hunlock_st].
  { 
    unfolds lock_st.
    destruct Hlock_st as [Hload_specm [Hnot_in_bf Hload_tsom]].
    destruct (apply_buffer_item b (memory tm)) eqn:Happly_buffer; tryfalse.
    inversion Hunbuffer; subst.
    simpl.
    clear_trivial_eq. 
    assert (~ (exists ofs, in_buffer_item b L ofs)).
    {
      specialize (Hnot_in_bf t).
      clear - Hnot_in_bf Hbf.
      intro.
      contradiction Hnot_in_bf; clear Hnot_in_bf.
      destruct H as [ofs H].
      rewrite Hbf.
      exists ofs.
      inv H; econstructor; simpls; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
    }
    split.
    left.
    split; eauto.
    split.
    intros. 
    specialize (Hnot_in_bf t0).
    clear - Hnot_in_bf Hbf.
    intros H_in_buffer; destruct H_in_buffer as [ofs H_in_buffer].
    contradiction Hnot_in_bf; clear Hnot_in_bf.
    unfolds tupdate.
    ex_match2; subst; eauto.
    rewrite Hbf.
    inv H_in_buffer. 
    exists ofs. econstructor; simpl; eauto.
    clear - Hnot_in_bf Hbf Happly_buffer Hload_tsom H4.
    specialize (Hnot_in_bf t).
    rewrite Hbf in Hnot_in_bf.
    unfolds load_tsomem; destruct tm; simpls. 
    eapply not_in_buf_item_apply_load_stable; eauto.

    split; eauto.

    split; intros.
    clear - H1 H4 Happly_buffer.
    specialize (H1 n).
    unfolds store_tsomem.
    destruct tm; simpls.
    destruct H1 as [bm' H1].
    destruct (store Mint32 memory L 0 (Vint n)) eqn:?; simpls; tryfalse.
    inv H1.
    eapply not_in_buf_item_apply_store_stable in Heqo; eauto.
    destruct Heqo as [m2 Heqo].
    rewrite Heqo; eauto.

    split. 
    clear - Hbf H0 Happly_buffer.
    inv H0.
    eapply UNBS; eauto.
  
    split; eauto.
    split; eauto.
    intros. 
    eapply H3 in H6.
    destruct H6 as [p [Hmem_access Hperm]].
    exists p. split; eauto.  
    eapply not_in_buf_item_apply_perm_stable; eauto.
    intros.
    eapply H5 in H6.
    destruct H6; split; eauto.
    eapply not_in_buf_item_apply_perm_stable'; eauto.
  }
  {
    destruct (apply_buffer_item b (memory tm)) eqn:Happly_buffer; tryfalse.
    inversion Hunbuffer; subst; clear Hunbuffer.
    simpls.
    clear_trivial_eq.
    unfold unlock_st in Hunlock_st.
    split_and Hunlock_st. 
    match goal with 
    | H : _ \/ _ |- _ =>
      destruct H as [Hst | Hst]
    end.
    { 
      destruct Hst as [t' [bf1 [bf2 [Hin_bf
                                       [Hnot_in_other [Hcount_one Hload_tsomem]]]]]].
      destruct (peq t t'); subst; eauto.
      {
        rewrite Hin_bf in Hbf.
        destruct bf1; simpls.
        {
          inv Hbf.
          split.
          right.
          unfold unlock_st; simpl.
          split; eauto.
          right.
          split.
          clear - Happly_buffer.
          simpls.
          eapply gm_store_v_load_same; eauto.
          intros.
          unfold tupdate.
          ex_match2; subst; eauto.
          split; eauto.
          split.
          intros.
          clear - Happly_buffer.
          simpls.
          eapply gm_store_succ_store_again with (n' := n) in Happly_buffer.
          destruct Happly_buffer as [m Happly_buffer].
          rewrite Happly_buffer; eauto.
          split.
          clear - H0 Hin_bf Happly_buffer.
          inv H0.
          eapply UNBS; eauto.
          split; eauto.
          split; eauto.
          intros.
          eapply H3 in H6; eauto.
          destruct H6 as [p [Hmem_access Hperm]].
          exists p. split; eauto.
          clear - Happly_buffer Hmem_access.
          destruct tm; simpls.
          eapply store_perm_nochange; eauto.
          intros.
          eapply H5 in H6.
          destruct H6; split; eauto.
          clear - Happly_buffer H7.
          simpls.
          unfolds store, GMem.perm; ex_match2.
          inv Happly_buffer; simpls; eauto.
        }
        {
          inv Hbf; simpls.
          assert (~ (exists ofs, in_buffer_item b L ofs)).
          {
            clear - Hcount_one.
            intro.
            destruct H as [ofs H].
            specialize (Hcount_one ofs).
            contradiction Hcount_one; clear Hcount_one.
            inv H; econstructor; simpls; eauto.
            econstructor; eauto.
            econstructor; eauto.
            econstructor; eauto.
          }
          split.
          right.
          unfold unlock_st; simpls.
          split; eauto.
          left.
          exists t' bf1 bf2.
          split.
          rewrite tupdate_b_get; eauto.
          split.
          intros.
          rewrite tupdate_not_eq_get; eauto.
          split; eauto.
          clear - Hcount_one.
          intros; intro.
          specialize (Hcount_one ofs).
          contradiction Hcount_one; clear Hcount_one.
          inv H; econstructor; simpls; eauto. 
          eapply not_in_buf_item_apply_load_stable; eauto.
          clear - Hload_tsomem.
          destruct tm; simpls; eauto.
          split; eauto.
          split.
          intros.
          clear - H1 Happly_buffer H6.
          specialize (H1 n).
          destruct H1 as [bm' H1].
          destruct tm; simpls.
          destruct (store Mint32 memory L 0 (Vint n)) eqn:?; simpls; tryfalse.
          inv H1.
          eapply not_in_buf_item_apply_store_stable in Heqo; eauto.
          destruct Heqo as [m2 Heqo].
          rewrite Heqo; eauto.
          split.
          clear - Hin_bf Happly_buffer H0.
          inv H0.
          eapply UNBS; eauto.
          split; eauto.
          split; eauto.
          intros.
          eapply H3 in H7.
          destruct H7 as [p [Hmem_access Hperm]].
          exists p. split; eauto.
          destruct tm; simpls.
          eapply not_in_buf_item_apply_perm_stable; eauto.
          intros.
          eapply H5 in H7.
          destruct H7; split; eauto.
          eapply not_in_buf_item_apply_perm_stable'; eauto.
        }
      }
      {
        assert (~ (exists ofs, in_buffer_item b L ofs)).
        {  
          clear - n Hnot_in_other Hbf.
          assert (Htid_neq : t' <> t); eauto.
          intro.
          destruct H as [ofs H].
          eapply Hnot_in_other with (ofs := ofs) in Htid_neq; eauto.
          contradiction Htid_neq; clear - H Hbf.
          rewrite Hbf.
          econstructor; simpls; eauto; try solve [econstructor; eauto].
        }
        split.
        right.
        unfold unlock_st; simpls.
        split; eauto.
        left.
        exists t' bf1 bf2.
        split.
        rewrite tupdate_not_eq_get; eauto.
        split.
        intros.
        unfold tupdate.
        ex_match2; subst.
        eapply Hnot_in_other with (ofs := ofs) in H7.
        rewrite Hbf in H7.
        intro; contradiction H7; clear H7.
        clear - H8.
        inv H8; econstructor; simpls; eauto.
        eapply Hnot_in_other in H7; eauto.
        split; eauto.

        eapply not_in_buf_item_apply_load_stable; eauto.
        clear - Hload_tsomem.
        destruct tm; simpls; eauto.
        split; eauto.
        split; eauto.
        intros.
        specialize (H1 n0).
        destruct H1 as [bm' H1].
        clear - H1 Hbf Happly_buffer H6.
        destruct tm; simpls.
        destruct (store Mint32 memory L 0 (Vint n0)) eqn:?; simpls; tryfalse.
        inv H1.
        eapply not_in_buf_item_apply_store_stable in Heqo; eauto.
        destruct Heqo as [m2 Heqo]; rewrite Heqo; eauto.

        split.
        clear - H0 Hbf Happly_buffer.
        inv H0.
        eapply UNBS; eauto.

        split; eauto.
        split; eauto.
        intros.
        eapply H3 in H7.
        destruct H7 as [p [Hmem_access Hperm]].
        exists p. split; eauto.
        eapply not_in_buf_item_apply_perm_stable; eauto.
        intros.
        eapply H5 in H7.
        destruct H7; split; eauto.
        eapply not_in_buf_item_apply_perm_stable'; eauto.
      }
    }
    {
      destruct Hst as [Hst Hnot_in].
      unfolds load_tsomem.
      destruct tm; simpls.

      assert (Hnot_in_buf_item : ~ (exists ofs, in_buffer_item b L ofs)).
      {
        intro.
        destruct H6 as [ofs H6].
        specialize (Hnot_in t ofs). 
        clear - Hnot_in Hbf H6.
        rewrite Hbf in Hnot_in; clear Hbf.
        contradiction Hnot_in; clear Hnot_in.
        econstructor; simpl; eauto.
      }
      
      split.
      right.
      unfold unlock_st.
      simpls.
      split; eauto.
      right.
      split.
      eapply not_in_buf_item_apply_load_stable; eauto.
      intros.
      unfold tupdate.
      ex_match2; subst.
      {
        specialize (Hnot_in t ofs).
        rewrite Hbf in Hnot_in; clear - Hnot_in.
        intro.
        contradiction Hnot_in; clear Hnot_in.
        inv H; econstructor; simpls; eauto.
      }
      {
        specialize (Hnot_in t0 ofs); eauto.
      }
      split; eauto.
      split; eauto.
      clear - H1 Happly_buffer Hnot_in_buf_item.
      intros.
      specialize (H1 n).
      destruct H1 as [bm H1].
      destruct (store Mint32 memory L 0 (Vint n)) eqn:?; simpls; tryfalse.
      inv H1.
      eapply not_in_buf_item_apply_store_stable in Heqo; eauto.
      destruct Heqo as [m2 Heqo]; rewrite Heqo; eauto.

      split.
      clear - Hbf Happly_buffer H0.
      inv H0; eapply UNBS; eauto.

      split; eauto.
      split; eauto.
      intros.
      eapply H3 in H6.
      destruct H6 as [p [Hmem_access Hperm]].
      exists p.
      split; eauto.
      eapply not_in_buf_item_apply_perm_stable; eauto.
      intros.
      eapply H5 in H6.
      destruct H6; split; eauto.
      eapply not_in_buf_item_apply_perm_stable'; eauto.
    }
  }
Qed.

(** [Io] is stable under [Ro] *)
Theorem H_rg_ub_o :
  forall ge t,
    UBImplies (obj_inv ge) (Robj ge t).
Proof.
  intros.
  unfold UBImplies.
  introv Hobj_inv HG_ub.
  unfold Robj.
  lets Ht : H_sta_o_ub ___; eauto.
  exists (Pos.succ t).
  split.
  intro. 
  assert (Pos.to_nat t = Pos.to_nat (Pos.succ t)).
  rewrite <- H; eauto.
  rewrite Pos2Nat.inj_succ in H0.
  Lia.lia.
  left.
  unfold Gclt.
  lets Hobj_inv' : Hobj_inv.
  unfold obj_inv in Hobj_inv'.
  destruct Hobj_inv' as [L' [Hfind_symb Hobj_inv']].
  eexists.
  split; eauto.
  destruct Hobj_inv' as [Hst Hobj_inv'].
  assert (exists v, load Mint32 gm L' 0 = Some v).
  {
    destruct Hst as [Hst | Hst].
    {
      clear - Hst.
      unfolds lock_st.
      split_and Hst; eauto.
    }
    {
      clear - Hst.
      unfolds unlock_st.
      split_and Hst; eauto.
    }
  }

  destruct H as [v Hload].
  exists v.
  split; eauto.
  split.
  unfolds G_ub.
  split_and HG_ub.
  subst; eauto.
  split; eauto.

  split.
  clear - Hobj_inv HG_ub Ht.
  unfolds UBSta.
  eapply Ht in Hobj_inv; eauto.
  unfolds G_ub.
  split_and HG_ub.
  subst; eauto.

  clear - HG_ub.
  intros.
  unfolds G_ub.
  destruct HG_ub as [Hgm [t' Hunbuffer]].
  subst.
  destruct tm.
  simpls.
  intro.
  eapply H.
  unfolds unbuffer.
  simpls.
  destruct (tso_buffers t') eqn:Hbf; tryfalse.
  unfolds apply_buffer_item.
  destruct b; simpls.
  {
    inv Hunbuffer; simpls.
    destruct H0 as [ofs Hin_buffer].
    exists ofs.
    unfolds tupdate.
    ex_match2; subst; eauto.
    rewrite Hbf; clear - Hin_buffer.
    inv Hin_buffer; econstructor; simpls; eauto.
  }
  {
    destruct (free memory b z z0) eqn:Hfree; tryfalse.
    inv Hunbuffer; simpls.
    clear - Hbf H0.
    destruct H0 as [ofs H0].
    exists ofs.
    unfolds tupdate.
    ex_match2; subst; eauto.
    rewrite Hbf; eauto.
    inv H0; econstructor; simpls; eauto.
  }
  {
    destruct (store m memory b z v) eqn:Hstore; tryfalse.
    inv Hunbuffer; simpls.
    clear - Hbf H0.
    destruct H0 as [ofs H0].
    exists ofs.
    unfolds tupdate.
    ex_match2; subst; eauto.
    rewrite Hbf; eauto.
    inv H0; econstructor; simpls; eauto.
  }
Qed.

Lemma obj_inv_env_unbuffer_stable :
  forall tm tm' M M' t ge,
    env_unbuffer_step t tm tm' M M' ->
    obj_inv ge M tm ->
    obj_inv ge M' tm'.
Proof.
  intros.
  assert (M = M').
  {
    unfolds env_unbuffer_step.
    split_and H; eauto.
  }
  subst.
  eapply H_sta_o_ub; eauto.
  instantiate (1 := M').
  unfolds env_unbuffer_step, G_ub.
  split_and H.
  split; eauto.
Qed.

(** [RespectPerm (Io, Ro, Go)] holds *)
Theorem Lock_RGI_satisfy_RespectPerm :
  RespectPerm obj_inv Robj Gobj.
Proof.  
  econstructor; intros.
  (** R *)
  {
    unfold Robj.
    destruct H1 as [t' H1].
    split_and H1.
    exists t'. split; eauto.
    left; unfold Gclt.
    lets Hobj_inv : H.
    unfold obj_inv in H.
    destruct H as [L H].
    split_and H.
    exists L. split; eauto.
    lets Hcan_store : H5.
    specialize (Hcan_store Int.zero).
    destruct Hcan_store as [M1' Hcan_store].
    eapply store_succ_load_succ in Hcan_store; eauto.
    destruct Hcan_store as [v Hcan_store].
    exists v.
    split; eauto.
    split.
    clear - H8 H0 Hcan_store.
    eapply loc_stable_load_same; eauto.
    split; eauto.
    assert (Hvb_L : In L (GMem.validblocks M)).
    {
      clear - H5.
      specialize (H5 Int.zero).
      destruct H5.
      eapply store_succ_invb; eauto.
    } 
    destruct H4.
    {
      split.
      eapply obj_inv_env_unbuffer_stable; eauto.
      intros.
      unfolds env_unbuffer_step.
      split_and H4; subst.
      intro. 
      contradiction H10.
      destruct H4 as [ofs H4].
      exists ofs.
      eapply in_bf_after_unbuffer_in_orign_bf1; eauto.
    }
    {  
      split. 
      eapply obj_inv_env_inbuffer_stable; eauto.
      unfolds env_inbuffer_step.
      split_and H4.
      renames H12 to bis.
      intros.
      intro. 
      contradiction H12.
      renames H to Hlock_st.
      clear - H4 H15 H14 H8 H11 H1 Hvb_L H13 Hlock_st H10.
      rewrite H4 in H14.
      destruct H14 as [ofs H14].
      unfold tupdate in H14.
      ex_match2; eauto; subst.
      eapply in_buffer_app_or in H14; eauto.
      destruct H14; eauto.
      lets Hin_buffer : H.
      eapply H15 in H; simpls.
      pose proof inrange_or_not1.
      specialize (H0 ofs 0%Z 4%Z).
      destruct H0; simpls.
      eapply H8 in H0; tryfalse. 
      assert ((ofs >= 4)%Z \/ (ofs < 0)%Z). destruct H0; eauto.  
      destruct Hlock_st as [Hlock_st | Hunlock_st].
      {
        unfolds lock_st.
        split_and Hlock_st.
        assert (forall t, ~ (exists lo hi,
                                In (BufferedAlloc L lo hi) (tso_buffers tm' t))).
        {
          intros; intro.
          destruct H5 as (lo & hi & H5).
          rewrite H4 in H5.
          unfold tupdate in H5.
          ex_match2; subst.
          eapply in_app_or in H5.
          destruct H5.
          contradiction (H6 t').
          exists 0%Z.
          econstructor; eauto.
          econstructor; eauto.
          assert (in_buffer bis L 0%Z).
          econstructor; eauto.
          econstructor; eauto.
          eapply H15 in H9.
          contradiction H9.
          eapply H8; eauto; Lia.lia.
          contradiction (H6 t).
          exists 0%Z.
          econstructor; eauto.
          econstructor; eauto.
        }
        eapply unbuffer_safe_noalloc_noperm_not_inbuffer in H5; eauto.
        contradiction H5.
        rewrite H4, tupdate_b_get; eauto.
        eapply in_buffer_app_or_rev; eauto.
        intros.
        rewrite <- H10.
        eapply H11 in H2; destruct H2; eauto.
      }
      {
        unfolds unlock_st.
        split_and Hunlock_st.
        destruct H5.
        {
          destruct H5 as (t0 & bf1 & bf2 & Hbf & Hother_bf & Hbf' & load).
          assert (forall t, ~ (exists lo hi, In (BufferedAlloc L lo hi) (tso_buffers tm' t))).
          intros; intro.
          destruct H5 as (lo & hi & H5).
          rewrite H4 in H5.
          unfold tupdate in H5.
          ex_match2; subst.
          eapply in_app_or in H5.
          destruct H5.
          destruct (peq t0 t'); subst.
          {
            rewrite Hbf in H5.
            eapply in_app_or in H5.
            destruct H5.
            contradiction (Hbf' 0%Z).
            econstructor; simpl; eauto.
            eapply in_or_app; eauto.
            econstructor; eauto.
            simpl in H5.
            destruct H5; tryfalse.
            contradiction (Hbf' 0%Z).
            econstructor; eauto.
            eapply in_or_app; eauto.
            econstructor; eauto.
          }
          {
            eapply Hother_bf in n.
            contradiction n; instantiate (1 := 0%Z).
            econstructor; eauto.
            econstructor; eauto.
          }
          assert (in_buffer bis L 0%Z).
          econstructor; eauto.
          econstructor; eauto.
          eapply H15 in H6.
          contradiction H6.
          eapply H8; Lia.lia.
          destruct (peq t0 t); subst.
          {
            rewrite Hbf in H5.
            eapply in_app_or in H5.
            contradiction (Hbf' 0%Z).
            destruct H5; eapply in_buffer_app_or_rev; eauto.
            left; econstructor; eauto.
            econstructor; eauto.
            right.
            destruct H5; tryfalse.
            econstructor; eauto.
            econstructor; eauto.
          }
          {
            eapply Hother_bf in n0.
            contradiction n0; instantiate (1 := 0%Z).
            econstructor; eauto.
            econstructor; eauto.
          }
          eapply unbuffer_safe_noalloc_noperm_not_inbuffer in H5; eauto.
          contradiction H5; rewrite H4, tupdate_b_get; eauto.
          eapply in_buffer_app_or_rev; eauto.
          intros.
          eapply H11 in H2.
          rewrite <- H10; destruct H2; eauto.
        }
        {
          destruct H5.
          assert (forall t, ~ (exists lo hi, In (BufferedAlloc L lo hi) (tso_buffers tm' t))).
          {
            intros; intro.
            destruct H7 as (lo & hi & H7).
            rewrite H4 in H7.
            unfold tupdate in H7.
            ex_match2; subst.
            eapply in_app_or in H7.
            destruct H7.
            contradiction (H6 t' 0%Z).
            econstructor; eauto.
            econstructor; eauto.
            assert (in_buffer bis L 0%Z).
            econstructor; eauto.
            econstructor; eauto.
            eapply H15 in H9.
            contradiction H9; eapply H8; Lia.lia.
            contradiction (H6 t 0%Z).
            econstructor; eauto.
            econstructor; eauto.
          }
          eapply unbuffer_safe_noalloc_noperm_not_inbuffer in H7; eauto.
          contradiction H7; rewrite H4, tupdate_b_get.
          instantiate (1 := ofs).
          eapply in_buffer_app_or_rev; eauto.
          intros.
          eapply H11 in H2.
          rewrite <- H10; destruct H2; eauto.
        }
      }
    }
  }
  (** G *)
  {
    unfolds Gobj.
    destruct H.
    { 
      unfolds G_lock.
      destruct H as [L H].
      split_and H.
      destruct H3.
      {
        split.
        {
          unfold env_m_stable; intros.
          unfolds lock_succ.
          split_and H2.
          unfold obj_inv in H.
          destruct H as [L' H].
          split_and H.
          rewrite H0 in H6.
          inversion H6; subst L'.
          assert (Hnot_objm : b <> L \/
                              (b = L /\ ((ofs < 0)%Z \/
                                         (ofs >= 0 + size_chunk Mint32)%Z))).
          {
            eapply not_obj_mem_upd_obj_mem_loc_stable; eauto.
          }
          destruct Hnot_objm as [Hnot_objm | Hnot_objm].
          {
            split.
            eapply store_diff_block_loc_stable; eauto.
            clear - H5 Hnot_objm.
            destruct tm, tm'; simpls.
            destruct (store Mint32 memory L 0 (Vint Int.zero)) eqn:?;
                     simpls; tryfalse.
            inversion H5; subst; clear H5.
            eapply store_diff_block_loc_stable; eauto.
          }
          {
            destruct Hnot_objm as [Hb_eq Hnot_objm]; subst; eauto.
            split; eauto.
            eapply store_ofs_not_inrange_loc_stable; eauto.
            clear - H5 H3 Hnot_objm.
            unfolds store_tsomem.
            destruct tm, tm'; simpls.
            destruct (store Mint32 memory L 0 (Vint Int.zero)) eqn:?;
                     simpls; tryfalse.
            inversion H5; subst; clear H5.
            eapply store_ofs_not_inrange_loc_stable; eauto.
          }
        }
        split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
        split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
        split.
        {
          left; unfolds obj_tau, lock_succ.
          split_and H2.
          clear - H6 H3.
          unfolds store.
          dis_if_else.
          inversion H6; subst; clear H6; eauto; simpl.
          split; eauto.
          destruct tm, tm'; simpls; eauto.
          ex_match2.
        }
        split.
        {
          unfolds lock_succ; split_and H2.
          clear - H3.
          destruct tm, tm'; simpls; ex_match2.
          inversion H3; subst; clear H3.
          unfolds store.
          ex_match2; inversion Hx; subst; eauto.
        }
        split.
        {
          unfolds lock_succ; split_and H2.
          clear - H3.
          destruct tm, tm'; simpls; ex_match2.
          inversion H3; subst; clear H3.
          unfolds store.
          ex_match2; inversion Hx; subst; eauto.
        }
        split.
        { 
          intros.
          unfolds lock_succ; split_and H2.
          clear - H7 H3.
          unfolds obj_mem.
          unfolds store.
          dis_if_else; inversion H7; subst; eauto.
        }
        split.
        {
          intros.
          unfolds lock_succ; split_and H2.
          clear - H3 H7.
          assert (In L (GMem.validblocks M)). eapply store_succ_invb; eauto.
          unfolds store.
          dis_if_else.
          inversion H7; subst; clear H7; simpls.
          assert (b <> L). intro; subst; tryfalse.
          rewrite PMap.gso; eauto.
        }
        {
          intros.
          unfolds lock_succ; split_and H2.
          clear - H3 H4.
          destruct tm, tm'; simpls.
          destruct (store Mint32 memory L 0 (Vint Int.zero)) eqn:?; simpls; tryfalse.
          inversion H4; subst; clear H4.
          assert (In L (GMem.validblocks memory)). eapply store_succ_invb; eauto.
          unfolds store.
          dis_if_else.
          inversion Heqo; subst; clear Heqo; simpls.
          assert (b <> L). intro; subst; tryfalse.
          rewrite PMap.gso; eauto.
        }
      }
      {
        split.
        {
          unfolds env_m_stable; intros.
          unfolds lock_fail.
          split_and H2; subst.
          split; eauto.
          unfold loc_stable; eauto.
          destruct tm, tm'; simpls.
          ex_match2.
          inversion H7; subst; clear H7.
          unfold obj_inv in H.
          destruct H as [L' H].
          split_and H.
          rewrite H0 in H2; inversion H2; subst L'.
          clear - H9 H12 Hx H3.
          assert (Hnot_objm : b <> L \/
                              (b = L /\ ((ofs < 0)%Z \/
                                         (ofs >= 0 + size_chunk Mint32)%Z))).
          {
            eapply not_obj_mem_upd_obj_mem_loc_stable; eauto.
          }
          destruct Hnot_objm as [Hnot_objm | Hnot_objm].
          {
            split.
            eapply store_diff_block_loc_stable; eauto.
            clear - Hx Hnot_objm.
            eapply store_diff_block_loc_stable; eauto.
          }
          {
            destruct Hnot_objm as [Hb_eq Hnot_objm]; subst; eauto.
            split; eauto.
            eapply store_ofs_not_inrange_loc_stable; eauto.
            clear - Hx H3 Hnot_objm.
            eapply store_ofs_not_inrange_loc_stable; eauto.
          }
        }
        split; [eapply obj_inv_impl_unbuffer_safe in H; eauto | ].
        split; [eapply obj_inv_impl_unbuffer_safe in H1; eauto | ].
        split.
        {
          left.
          unfolds lock_fail, obj_tau.
          split_and H2; subst; split; eauto.
          destruct tm, tm'; simpls.
          ex_match2.
        }
        split.
        {
          unfolds lock_fail; split_and H2; subst.
          destruct tm, tm'; simpls.
          ex_match2.
          inversion H5; subst; clear H5.
          unfolds store.
          ex_match2.
          inversion Hx; subst; eauto.
        }
        split.
        {
          unfolds lock_fail; split_and H2; subst.
          destruct tm, tm'; simpls.
          ex_match2.
          inversion H5; subst; clear H5.
          unfolds store.
          ex_match2.
          inversion Hx; subst; eauto.
        }
        split.
        { 
          intros.
          unfolds lock_fail; split_and H2; subst; eauto.
        }
        split; intros.
        { 
          unfolds lock_fail.
          split_and H2; subst; eauto.
        }
        {
          unfolds lock_fail.
          split_and H2; subst; eauto.
          clear - H6 H3.
          destruct tm, tm'; simpls.
          ex_match2.
          inversion H6; subst; clear H6.
          lets Ht : Hx.
          eapply store_succ_invb in Ht; eauto.
          unfolds store; ex_match2.
          inversion Hx; subst; clear Hx; simpls.
          assert (b <> L). intro; subst; tryfalse.
          rewrite PMap.gso; eauto.
        }
      }
    }
    destruct H.
    { 
      unfolds G_unlock.
      destruct H as [L H].
      split_and H.
      unfolds unlock_succ.
      split_and H3.
      split.
      {
        unfold env_m_stable; intros.
        unfold obj_inv in H.
        destruct H as [L' H].
        split_and H.
        rewrite H0 in H8; inversion H8; subst L'.
        assert (Hnot_objm : b <> L \/
                              (b = L /\ ((ofs < 0)%Z \/
                                         (ofs >= 0 + size_chunk Mint32)%Z))).
        {
          eapply not_obj_mem_upd_obj_mem_loc_stable; eauto.
        }
        split.
        Focus 2.
        clear - H6.
        destruct tm, tm'; simpls.
        unfolds append_t_buffer; simpls.
        inversion H6; subst; eauto.
        unfold loc_stable; eauto.
        destruct Hnot_objm as [Hnot_objm | Hnot_objm].
        {  
          eapply store_diff_block_loc_stable; eauto.
        }
        {
          destruct Hnot_objm as [Hb_eq Hofs_not_inrange]; subst.
          eapply store_ofs_not_inrange_loc_stable; eauto.
        }
      }
      split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
      split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
      split.
      {
        right; right.
        unfold obj_upd_objm.
        exists L 0%Z Int.one.
        split.
        {
          intros; simpls.
          clear - H H4 H0.
          unfolds obj_inv.
          destruct H as [L' H].
          split_and H.
          rewrite H0 in H1; inversion H1; subst L'; eauto.
        }
        split.
        {
          clear - H6.
          destruct tm, tm'; simpls.
          unfolds append_t_buffer; simpls.
          inversion H6; subst; clear H6; eauto.
        }
        eapply store_vb_eq; eauto.
(*      split; [eapply store_vb_eq; eauto | ].
        {   
          intros. 
          clear - H0 H H6 H4 H3 H5. 
          unfolds obj_inv.
          destruct H as [L' H].
          split_and H.
          rewrite H0 in H1; inversion H1; subst L'.
          destruct tm, tm'; simpls.
          destruct H.
          { 
            unfolds lock_st; simpls.
            split_and H.
            specialize (H t'); eauto.
          }
          {
            unfolds unlock_st; simpls.
            split_and H.
            clear - H11 H3.
            rewrite H3 in H11.
            tryfalse.
          }
        }*)
      }
      split.
      {
        clear - H6.
        destruct tm, tm'; simpls.
        unfolds append_t_buffer; simpls; inversion H6; subst; eauto.
      }
      split.
      {
        clear - H6.
        destruct tm, tm'; simpls.
        unfolds append_t_buffer; simpls; inversion H6; subst; eauto.
      }
      split.
      { 
        intros.
        clear - H2 H4.
        unfolds obj_mem.
        unfolds store.
        dis_if_else; inversion H2; subst; eauto.
      }
      split; intros.
      {
        clear - H2 H4.
        assert (In L (GMem.validblocks M)). eapply store_succ_invb; eauto.
        unfolds store.
        dis_if_else.
        inversion H2; subst; clear H2; simpls.
        assert (b <> L). intro; subst; tryfalse.
        rewrite PMap.gso; eauto.
      }
      {
        clear - H6.
        destruct tm, tm'; simpls.
        unfolds append_t_buffer; simpls.
        inversion H6; subst; eauto.
      }
    }
    destruct H.
    {
      unfolds Id.
      split_and H; subst M'; subst tm'.
      split.
      {
        unfold env_m_stable; intros.
        unfold loc_stable; eauto.
      }
      split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
      split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
      split. left. unfold obj_tau; eauto.
      split; eauto.
    }
    {
      unfolds G_alloc.
      destruct H as [nb H].
      split_and H.
      split.
      {
        unfold env_m_stable; intros.
        rewrite <- H2.
        unfold loc_stable.
        unfolds alloc; inversion H1; subst; clear H1; simpls.
        assert (b <> nb). intro; subst; tryfalse.
        repeat (rewrite PMap.gso; eauto).
      }
      split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
      split; [eapply obj_inv_impl_unbuffer_safe; eauto | ].
      split.
      { 
        right; left.
        unfold obj_alloc_b.
        exists nb. split; eauto.
        split; eauto.
        exists 0%Z 0%Z.
        split; eauto.
        destruct tm, tm'; simpls.
        clear - H2.
        unfolds append_t_buffer.
        inv H2; simpls; eauto.
      }
      unfolds append_t_buffer; subst; simpls; eauto.
      split; eauto.
      split; eauto.
      split.
      { 
        clear - H1 H3 H3; intros.
        unfolds obj_mem, alloc.
        inversion H1; subst; clear H1; simpls; eauto.
        destruct H.
        assert (b <> nb).
        {
          intro; subst.
          eapply GMem.invalid_noaccess in H3.
          contradiction H.
          eauto.
        }
        rewrite PMap.gso; eauto.
      }
      split; intros; eauto.
      {
        clear - H1 H3 H2.
        unfolds alloc.
        inversion H1; subst; clear H1; simpls.
        assert (b <> nb).
        {
          intro.
          contradiction H2; eauto.
        }
        rewrite PMap.gso; eauto.
      }
    }
  }
  (** I *)
  {
    unfolds env_not_touch_objm.
    split_and H0.
    renames H2 to t.
    destruct H4.
    {
      eapply obj_mem_eq_on_loc_obj_inv_stable in H; eauto.
      eapply H_sta_o_ub; eauto.
      unfold G_ub; eauto.
    }
    {
      split_and H0. 
      eapply obj_inv_env_inbuffer_stable; eauto.
      introv Hobj_mem.
      eapply H1 in Hobj_mem.
      inversion Hobj_mem; subst.
      unfold loc_stable.
      split; eauto.
      eapply functional_extensionality; intros.
      rewrite eq_loc_perm; eauto.
    }
  }
Qed.

(** The implementation of spin-lock and its corresponding specification satify
object simulation *)
Theorem LockProof :
  objectsim Robj Gobj obj_inv SpecLang.speclang lock_comp_unit lock_comp_tso_unit.
Proof.
  intro.
  unfold objectsim.
  intros.
  match goal with
  | H0 : InteractionSemantics.init_genv _ _ _ _,
         H1 : init_genv _ _,
              H2 : genv_match _ _ _ _ |- _ =>
    rename H0 into Hspec_init; rename H1 into Himp_init;
      rename H2 into Hge_equiv
  end.
  
  exists (obj_match_state sge tge).
  econstructor.
 
  - (* init state satisfies obj_inv *)
    introv HSpecLang_init_mem.
    introv Htso_init_mem.
    introv Htso_init_gmem.
    eapply ObjInit_inv; eauto.
 
  - (* init state match *)
    introv Hinit_tso_core.
    eapply ObjInit_core_match; eauto.

  - (* init not *)
    intros.
    eapply tso_init_fail_spec_init_fail; eauto.

  - (* tau step state match *)
    intros.
    eapply obj_tau_step_match; eauto.
 
  - (* unbuffer safe *) 
    intros.
    eapply obj_unbuffer_safe; eauto.

  - (* footprint *)
    intros.
    eapply obj_footprint_case; eauto.
    
  - (* no external *)
    intros.
    eapply obj_no_external_call; eauto.

  - (* return value match *)
    intros.
    eapply obj_return_value_match; eauto.

  - (* tso halt; spec halt *)
    intros.
    eapply obj_tso_halt_spec_not_exec; eauto.
 
  - (* tso not halt; spec not halt *)
    intros.
    eapply obj_tso_not_halt_spec_not_halt; eauto.

  - (* Rely step match *)
    intros.
    eapply obj_rely_step_match; eauto.

  - (* not abort *)
    introv Hobj_match_state.
    introv Hbf_nil Hgm Hstep Hnot_halt.
    introv Hembed.
    eapply obj_not_abort; eauto.
Qed.


    