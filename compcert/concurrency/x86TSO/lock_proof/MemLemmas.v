(** This file contains a set of lemmas for lock correctness proof.  *)
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
Require Import AuxTacLemmas TSOMemLemmas TSOStepAuxLemmas TSOAuxDefs.

Require Import FMemLemmas.

Local Transparent Mem.load Mem.alloc Mem.store Mem.free.

(** ** Auxiliary Lemmas *)
Lemma genv_defs_fun_find_fun_eq :
  forall F V (ge : Genv.t F V) b (f f' : F)
    (Hfind_func : Genv.find_funct_ptr ge b = Some f)
    (Hgenv_defs : (Genv.genv_defs ge) ! b = Some (Gfun f')),
    f = f'.
Proof.
  intros.
  unfolds Genv.find_funct_ptr.
  unfolds Genv.find_def.
  rewrite Hgenv_defs in Hfind_func.
  inversion Hfind_func; eauto.
Qed.
 
Lemma ogenv_match_L_addr_eq :
  forall sge tge sG,
    InteractionSemantics.init_genv SpecLang.speclang
                                   lock_comp_unit sge sG ->
    init_genv lock_comp_tso_unit tge ->
    genv_match (InteractionSemantics.F SpecLang.speclang)
                (InteractionSemantics.V SpecLang.speclang) sge tge ->
    exists L, Genv.find_symbol tge lock_L_ident = Some L /\
         Genv.find_symbol sge lock_L_ident = Some L.
Proof.
  intros.
  simpl in H.
  inversion H; subst.
  inversion H3; subst.
  specialize (H6 lock_L_ident).
  inversion H6; subst; simpls.
  clear H3 H2 H4 H5 H6 H7 H8 H9 H10.
  inversion H0; subst; simpls.
  specialize (H5 lock_L_ident).
  inversion H5; subst; simpls.
  clear H2 H3 H4 H5 H6 H7 H8 H9.
  inversion H1; subst.
  unfold Genv.find_symbol in H13, H12.
  specialize (genv_symb_eq lock_L_ident).
  rewrite <- H13 in genv_symb_eq.
  rewrite <- H12 in genv_symb_eq.
  inversion genv_symb_eq; subst; eauto.
Qed.

Lemma get_lock_ident_from_ge :
  forall tge
    (Himp_init : init_genv lock_comp_tso_unit tge),
  exists L, Genv.find_symbol tge lock_L_ident = Some L.
Proof.
  intros.
  inversion Himp_init.
  specialize (H2 lock_L_ident).
  inversion H2; subst.
  eapply H5 in H10; eauto.
Qed.

Lemma R_impl_I_I :
  forall tge t sm tm sm' tm'
    (HRobj : Robj tge t sm tm sm' tm'),
    obj_inv tge sm tm /\ obj_inv tge sm' tm'.
Proof. 
  intros.
  unfolds Robj.
  split_and HRobj.
  destruct H2.
  {
    unfolds Gclt.
    split_and H0.
    eauto.
  }
  {
    unfolds Gobj.
    destruct H0.
    unfolds G_lock.
    split_and H0; eauto.
    destruct H0.
    unfolds G_unlock.
    split_and H0; eauto.
    destruct H0.
    unfolds Id.
    split_and H0; subst; eauto.
    unfolds G_alloc.
    split_and H0.
    eauto.
  }
Qed.

Lemma spec_init_not_none :
  forall sG id args,
    InteractionSemantics.init_core SpecLang.speclang sG id args <> None ->
    exists tc, InteractionSemantics.init_core SpecLang.speclang sG id args = Some tc.
Proof.
  intros.
  simpls.
  unfolds SpecLang.init_core.
  unfolds generic_init_core.
  destruct (Genv.find_symbol sG id) eqn:?; tryfalse.
  try rewrite Heqo in *.
  destruct (Genv.find_funct_ptr sG b) eqn:?; tryfalse.
  unfolds SpecLang.fundef_init.
  destruct f; tryfalse.
  destruct args; tryfalse.
  eauto.
Qed.
 
Lemma obj_inv_impl_unbuffer_safe :
  forall tge sm tm,
    obj_inv tge sm tm ->
    unbuffer_safe tm.
Proof.
  intros.
  unfolds obj_inv.
  split_and H.
  eauto.
Qed.

Lemma b_not_bf_item_not1 :
  forall bf L c ofs v,
    In (BufferedStore c L ofs v) bf ->
    In L (get_buffer_b bf).
Proof.
  intro bf.
  induction bf; intros.
  -
    simpls; tryfalse.
  -
    simpls.
    destruct H; subst.
    simpl; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma perm_w_store :
  forall fm b n,
    Mem.range_perm fm b 0 4 Memperm.Cur Memperm.Writable ->
    exists gm, store Mint32 (strip fm) b 0 (Vint n) = Some gm.
Proof.
  memunfolds;intros.
  ex_match2;eauto.
  clear Hx;contradict n0;split;auto.
  memunfolds;auto.
  apply range_perm_cur_max;auto.
  simpl. apply Z.mod_divide;auto;Lia.lia.
Qed.

Lemma item_in_bf_add_count_one_block_neq :
  forall bi' bf c L ofs v,
    In (BufferedStore c L ofs v) bf ->
    count_occ Pos.eq_dec (get_buffer_b (bi' :: bf)) L = 1 ->
    get_bi_block bi' <> L.
Proof.
  intros.
  destruct bi'; intro; simpls; subst; dis_if_else;
    try eapply nat_add_nochange_zero in H0; 
    try eapply count_occ_not_In in H0;
    try eapply b_not_bf_item_not1 in H;
    try contradiction H; eauto.
Qed.

Lemma in_buffer_count_one_load' :
  forall bf L n m m' v,
    In (BufferedStore Mint32 L 0 (Vint n)) bf ->
    count_occ Pos.eq_dec (get_buffer_b bf) L = 1 ->
    apply_buffer bf m = Some m' ->
    load Mint32 m' L 0 = Some v ->
    v = Vint n.
Proof.
  intro bf.
  induction bf; intros.
  -
    simpls; tryfalse.
  -   
    simpls.  
    destruct H.
    {
      subst.
      unfolds optbind.
      simpls.
      destruct (Pos.eq_dec L L) eqn:?; tryfalse.
      destruct (store Mint32 m L 0 (Vint n)) eqn:Hstore; tryfalse.
      assert (load Mint32 g L 0 = Some (Vint n)).
      eapply gm_store_v_load_same; eauto.
      eapply not_in_apply_buffer_load_eq_rev in H1; eauto.
      rewrite H2 in H1.
      inversion H1; subst; eauto.
      assert (count_occ Pos.eq_dec (get_buffer_b bf) L = 0).
      Lia.lia.
      eapply count_occ_not_In in H3; eauto.
    }
    {
      eauto.
      assert (Hblock_neq : get_bi_block a <> L).
      {
        eapply item_in_bf_add_count_one_block_neq; eauto.
      }
      
      destruct a; unfolds optbind; simpls.
      { 
        destruct (alloc m b z z0) eqn:Halloc; tryfalse.
        eapply IHbf with (m := g); eauto.
        destruct (Pos.eq_dec b L); tryfalse.
        eauto.
        unfold alloc in Halloc. inv Halloc. auto.
      }
      {
        destruct (free m b z z0) eqn:Hfree; tryfalse.
        eapply IHbf with (m := g); eauto.
        destruct (Pos.eq_dec b L); tryfalse.
        eauto.
      }
      {
        destruct (store m0 m b z v0) eqn:Hfree; tryfalse.
        eapply IHbf with (m := g); eauto.
        destruct (Pos.eq_dec b L); tryfalse.
        eauto.
      }
    }
Qed.
    
Lemma in_buffer_count_one_load :
  forall L n bf fm v,
    In (BufferedStore Mint32 L 0 (Vint n)) bf ->
    count_occ Pos.eq_dec (get_buffer_b bf) L = 1 ->
    tsoloadv Mint32 {| tbuffer := bf; fmemory := fm |}
             (Vptr L (Ptrofs.repr 0)) = Some v ->
    v = Vint n.
Proof.
  intros.
  unfolds tsoloadv.
  unfolds tsoload.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0%Z in H1.
  destruct (apply_buffer bf (strip fm)) eqn:Happly_buffer; tryfalse.
  eapply in_buffer_count_one_load'; eauto.
Qed.

Lemma in_buffer_count_one_load2' :
  forall bf1 bf2 bf b ofs v n m m',
    bf = bf1 ++ (BufferedStore Mint32 b ofs (Vint n) :: bf2) ->
    (forall ofs, ~ in_buffer (bf1 ++ bf2) b ofs) ->
    apply_buffer bf m = Some m' -> load Mint32 m' b ofs = Some v ->
    v = Vint n.
Proof.
  induction bf1; simpls; intros; subst; simpls.
  {
    destruct (store Mint32 m b ofs (Vint n)) eqn:?; simpls; tryfalse.
    eapply gm_store_v_load_same in Heqo.
    eapply load_orignal_loc_not_in_bf_apply_buf_same_val in Heqo; eauto.
    rewrite Heqo in H2.
    inv H2; eauto.
  }
  {
    destruct (apply_buffer_item a m); simpls; tryfalse.
    eapply IHbf1; eauto.
    intros; intro.
    specialize (H0 ofs0).
    contradiction H0.
    clear - H.
    inv H.
    econstructor; eauto.
    simpl; eauto.
  }
Qed.
  
Lemma in_buffer_count_one_load2 :
  forall bf1 bf2 bf L n fm v,
    bf = bf1 ++ (BufferedStore Mint32 L 0 (Vint n)) :: bf2 ->
    (forall ofs, ~ in_buffer (bf1 ++ bf2) L ofs) ->
    tsoloadv Mint32 {| tbuffer := bf; fmemory := fm |}
             (Vptr L (Ptrofs.repr 0)) = Some v ->
    v = Vint n.
Proof.
  intros.
  unfolds tsoloadv.
  unfolds tsoload.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0%Z in H1.
  destruct (apply_buffer bf (strip fm)) eqn:Happly_buffer; tryfalse.
  eapply in_buffer_count_one_load2'; eauto.
Qed.

Lemma not_in_apply_buffer_load_eq' :
  forall bf c gm gm' b ofs v,
    apply_buffer bf gm = Some gm' -> ~ (exists ofs, in_buffer bf b ofs) ->
    load c gm' b ofs = Some v ->
    load c gm b ofs = Some v.
Proof. 
  induction bf; intros.
  -
    simpls; eauto.
    inversion H; subst; eauto.
  -
    simpl in H.
    unfolds optbind.
    destruct (apply_buffer_item a gm) eqn:?; tryfalse.
    eapply IHbf in H; eauto.
    clear - H0 Heqo H.
    unfolds apply_buffer_item.
    destruct a.
    {
      assert (b <> b0).
      intro.
      subst.
      eapply H0.
      exists z. econstructor; eauto.
      instantiate (1 := BufferedAlloc b0 z z0).
      simpl; eauto.
      econstructor; eauto.
      eapply load_alloc_val_same_rev; eauto.
    }
    {
      unfolds free.
      ex_match2.
      inv Heqo.
      unfolds unchecked_free, load; simpls.
      ex_match2.
      clear - H0 v0 n.
      simpls.
      unfolds valid_access, range_perm; simpls.
      contradiction n; clear n.
      destruct v0.
      split; eauto.
      intros.
      eapply H in H2.
      destruct (peq b0 b); subst.
      {
        rewrite PMap.gss in H2.
        ex_match2.
        contradiction H0.
        exists ofs0.
        econstructor; eauto.
        instantiate (1 := BufferedFree b z z0); simpls; eauto.
        econstructor; eauto.
        clear - Hx.
        unfolds andb.
        destruct (zle z ofs0); destruct (zlt ofs0 z0); simpls; eauto; tryfalse.
      }
      {
        rewrite PMap.gso in H2; eauto.
      }
    }
    {
      unfolds store.
      ex_match2.
      inv Heqo.
      unfolds load; simpls.
      ex_match2.
      inv H.
      destruct (peq b0 b); subst.
      {
        rewrite PMap.gss; eauto.
        clear - v2 H0 v1 v3.
        unfolds valid_access, range_perm; simpls.
        assert (Mem.getN (size_chunk_nat c) ofs (GMem.mem_contents gm) !! b =
                Mem.getN (size_chunk_nat c) ofs
                         (Mem.setN (encode_val m v0) z (GMem.mem_contents gm) !! b)).
        {
          eapply get_eq_getN_eq; eauto.
          intros.
          rewrite Mem.setN_outside; eauto.
          pose proof inrange_or_not1.
          rewrite encode_val_length.
          rewrite <- size_chunk_conv.
          specialize (H1 ofs0 z (size_chunk m)).
          destruct H1.
          contradiction H0.
          exists ofs0.
          econstructor.
          instantiate (1 := BufferedStore m b z v0).
          simpl; eauto.
          econstructor; eauto.
          destruct H1; eauto.
        }
        rewrite <- H; eauto.
      }
      {
        rewrite PMap.gso; eauto.
      }
      clear - v2 n.
      contradiction n.
    }

    intro.
    eapply H0.
    destruct H2.
    exists x.
    inv H2; econstructor; eauto.
    simpl; eauto.
Qed.
 
Lemma tsoloadv_not_in_bf_load_gm_eq :
  forall b fm L v m fl,
    tsoloadv Mint32 {| tbuffer := b; fmemory := fm |} (Vptr L (Ptrofs.repr 0))
    = Some v ->
    embed m fl fm -> ~ (exists ofs, in_buffer b L ofs) ->
    load Mint32 m L 0 = Some v.
Proof.
  intros.
  unfolds tsoloadv.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0%Z in H.
  unfolds tsoload.
  destruct (apply_buffer b (strip fm)) eqn:Happly_buffer; tryfalse.
  inversion H0; subst.
  eapply not_in_apply_buffer_load_eq'; eauto.
Qed.

Lemma unbuffer_safe_store_preserve :
  forall c b bfs ofs m m' v,
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    store c m b ofs v = Some m' ->
    (forall t, In b (get_buffer_b (bfs t)) ->
               (exists v', In (BufferedStore c b ofs v') (bfs t)
    /\ count_occ Pos.eq_dec (get_buffer_b (bfs t)) b = 1)) ->
    unbuffer_safe {| tso_buffers := bfs; memory := m' |}.
Proof. 
  introv H.
  generalize dependent m'.
  generalize dependent c.
  generalize dependent b.
  generalize dependent ofs.
  generalize dependent v.
  remember {| tso_buffers := bfs; memory := m |} as tm.
  generalize dependent m.
  generalize dependent bfs.
  induction H; simpls; intros. 
  econstructor; intros; subst; simpls.
  {  
    lets Ht : H2.
    eapply ABIS in H2.
    destruct H2 as [m'' H2].
    eapply apply_buffer_item_store_still; eauto.
  }
  { 
    destruct bi.
    {
      assert (b1 <> b).
      {
        intro; subst.
        specialize (H1 t).
        assert (Ht : In b (get_buffer_b (bfs t))).
        rewrite H2; eauto.
        simpl; eauto.
        eapply H1 in Ht.
        destruct Ht as [v' [Hin_buf Hcount]].
        rewrite H2 in Hin_buf, Hcount.
        simpl in Hin_buf, Hcount.
        destruct (Pos.eq_dec b b) eqn:?; tryfalse.
        subst.
        destruct Hin_buf; tryfalse.
        assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
        Lia.lia.
        clear - H4 H5.
        eapply count_occ_not_In in H5.
        eapply b_not_bf_item_not1 in H4.
        eapply H5 in H4.
        tryfalse.
      }
 
      lets Halloc : H3.
      simpl in Halloc.
      eapply alloc_store_still_rev in Halloc; eauto.
      destruct Halloc as [m'' Halloc]. 
      lets Hstore : store_alloc_still ___; eauto.
      destruct Hstore as [m''' Hstore].
      assert (m'0 = m''').
      {
        eapply store_alloc_eq_alloc_store with (m := m); eauto.
      }
      subst.
      
      eapply H; eauto.
      intros.
      unfold tupdate in H5.
      destruct (peq t0 t) eqn:?; subst.

      assert (In b (get_buffer_b (bfs t))).
      rewrite H2.
      simpl; eauto.
      eapply H1 in H6.
      destruct H6 as [v' [Hin Hcount_occ]].
      eexists.
      unfold tupdate.
      destruct (peq t t); tryfalse.
      rewrite H2 in Hin.
      simpl in Hin. 
      destruct Hin; tryfalse.
      split; eauto.
      rewrite H2 in Hcount_occ.
      simpl in Hcount_occ.
      destruct (Pos.eq_dec b1 b); tryfalse.
      eauto.

      unfold tupdate.
      destruct (peq t0 t); tryfalse.
      eauto.
    }
    {
      assert (b1 <> b).
      {
        intro; subst.
        specialize (H1 t).
        assert (Ht : In b (get_buffer_b (bfs t))).
        rewrite H2; eauto.
        simpl; eauto.
        eapply H1 in Ht.
        destruct Ht as [v' [Hin_buf Hcount]].
        rewrite H2 in Hin_buf, Hcount.
        simpl in Hin_buf, Hcount.
        destruct (Pos.eq_dec b b) eqn:?; tryfalse.
        subst.
        destruct Hin_buf; tryfalse.
        assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
        Lia.lia.
        clear - H4 H5.
        eapply count_occ_not_In in H5.
        eapply b_not_bf_item_not1 in H4.
        eapply H5 in H4.
        tryfalse.
      }

      lets Hfree : H3.
      simpl in Hfree.
      eapply free_store_still_rev in Hfree; eauto.
      destruct Hfree as [m'' Hfree].
      lets Hstore : store_free_other_still ___; eauto.
      destruct Hstore as [m''' Hstore].

      assert (m'0 = m''').
      {
        eapply store_free_eq_free_store with (m := m); eauto.
      }
      subst.

      eapply H; eauto.
      intros.
      unfold tupdate in H5.
      destruct (peq t0 t) eqn:?; subst.

      assert (In b (get_buffer_b (bfs t))).
      rewrite H2.
      simpl; eauto.
      eapply H1 in H6.
      destruct H6 as [v' [Hin Hcount_occ]].
      eexists.
      unfold tupdate.
      destruct (peq t t); tryfalse.
      rewrite H2 in Hin.
      simpl in Hin.
      destruct Hin; tryfalse.
      split; eauto.
      rewrite H2 in Hcount_occ.
      simpl in Hcount_occ.
      destruct (Pos.eq_dec b1 b); tryfalse.
      eauto.

      unfold tupdate.
      destruct (peq t0 t); tryfalse.
      eauto.
    }
    {
      destruct (peq b1 b).
      {
        subst.
        assert (In b (get_buffer_b (bfs t))).
        rewrite H2.
        simpl; eauto.
        eapply H1 in H4.
        destruct H4 as [v' [Hin_bf Hcount]].
        rewrite H2 in Hin_bf.
        simpl in Hin_bf. 
        destruct Hin_bf.
        { 
          inversion H4; subst.
          clear_trivial_eq.

          lets Hstore1 : H3.
          simpl in Hstore1.

          assert (exists m'', apply_buffer_item (BufferedStore c b ofs v') m =
                              Some m'').
          {
            simpl.
            eapply store_store_other_val; eauto.
          }
          destruct H4 as [m'' H4].
          eapply H with (m' := m''); eauto.
          simpl in H4.
          assert (m'0 = m'').
          {
            eapply store_twice_eq_store_dir with (m := m) (m' := m') in H0;
              eauto.
            rewrite H4 in H0.
            inversion H0; subst; eauto.
          }
          subst.
          eapply store_again_mem_eq; eauto.

          intros.
          unfold tupdate.
          destruct (peq t0 t) eqn:?; subst; tryfalse.
          {
            unfold tupdate in H5.
            destruct (peq t t); tryfalse.
            rewrite H2 in Hcount.
            simpl in Hcount.
            destruct (Pos.eq_dec b b); tryfalse.
            assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
            Lia.lia.
            eapply count_occ_not_In in H6.
            eapply H6 in H5.
            tryfalse.
          }
          {
            unfold tupdate in H5.
            destruct (peq t0 t); tryfalse.
            eauto.
          }
        }
        {
          rewrite H2 in Hcount.
          simpl in Hcount.
          destruct (Pos.eq_dec b b); tryfalse.
          assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
          Lia.lia.
          eapply count_occ_not_In in H5.
          eapply b_not_bf_item_not1 in H4.
          eapply H5 in H4.
          tryfalse.
        }
      }
      { 
        lets Hstore : H3.
        simpl in Hstore.

        renames m0 to c0.
        eapply store_store_still_rev in Hstore; eauto.
        destruct Hstore as [m'' Hstore].
        eapply H with (m' := m''); eauto.
        simpl in H3.
        instantiate (1 := v).
        instantiate (1 := ofs).
        instantiate (1 := b).
        instantiate (1 := c).
        clear - H0 H3 Hstore n.
        lets Ht : Hstore.
        eapply store_store_still with (c := c) (m := m) in Ht; eauto.
        destruct Ht as [m''' Ht].
        assert (m'0 = m''').
        { 
          eapply store_store_eq_store_store.
          exact H0.
          exact H3.
          exact Hstore.
          eauto.
          eauto.
        }
        subst; eauto.

        intros.
        unfold tupdate in H4.
        destruct (peq t0 t) eqn:?; tryfalse.
        {
          subst.
          assert (In b (get_buffer_b (bfs t))).
          rewrite H2.
          simpl; eauto.
          eapply H1 in H5.
          destruct H5 as [v' [Hin_buf Hcount]].
          rewrite H2 in Hin_buf.
          simpl in Hin_buf.
          destruct Hin_buf.
          inversion H5; subst; tryfalse.
          unfold tupdate.
          destruct (peq t t); tryfalse.
          eexists.
          split; eauto.
          rewrite H2 in Hcount.
          simpl in Hcount.
          destruct (Pos.eq_dec b1 b); tryfalse.
          eauto.
        }
        {
          unfold tupdate.
          destruct (peq t0 t); tryfalse.
          eauto.
        }
      }
    }
  }
Qed.

Lemma unbuffer_safe_Mem_store_stable :
  forall tm fl fm b n fm',
    embed (memory tm) fl fm ->
    unbuffer_safe tm ->
    (forall t, In b (get_tsom_b t tm) ->
               (exists v', In (BufferedStore Mint32 b
                  (Ptrofs.unsigned (Ptrofs.repr 0))  v') (tso_buffers tm t)
    /\ count_occ Pos.eq_dec (get_tsom_b t tm) b = 1)) ->
    Mem.storev Mint32 fm (Vptr b (Ptrofs.repr 0)) (Vint n) = Some fm' ->
    unbuffer_safe {| tso_buffers := tso_buffers tm; memory := strip fm' |}.
Proof.
  intros.
  simpl in H1.
  destruct tm.
  simpls.
  inversion H; subst. 
  eapply store_fm_eq_store_gm in H2. 
  eapply unbuffer_safe_store_preserve in H2; eauto.
Qed.

(** Can remove to TSOMemlemmas *)
Lemma alloc_apply_buf_block_neq_reorder_succ1:
  forall m m1 m2 b lo hi bi,
     ~ (exists lo' hi', BufferedAlloc b lo' hi' = bi) ->
    alloc m b lo hi = Some m1 ->
    apply_buffer_item bi m = Some m2 ->
    ~ In b (GMem.validblocks m) ->
    exists m3, apply_buffer_item bi m1 = Some m3.
Proof.
  introv Hnot_alloc_b.
  intros.
  lets Hstep : H0.
  eapply buf_item_unbuf_locality_1 in Hstep.
  specialize (Hstep m1).
  assert (InteractionSemantics.MemPre m m1 (bi_footprint bi)).
  {
    eapply apply_buf_item_outside_stable with
    (bi := BufferedAlloc b lo hi); eauto.
    simpls. 
    unfold uncheck_alloc_fp.
    clear - H0 H1 Hnot_alloc_b.
    destruct bi; simpls.
    {
      unfold uncheck_alloc_fp.
      econstructor; simpl; eauto; unfold Locs.smile;
        repeat (rewrite Locs.locs_intersect_emp_sym);
        try solve [split; eapply Locs.eq_refl].
      unfold Locs.eq; intros; simpls.
      unfolds Locs.intersect, Locs.emp.
      ex_match2; subst; simpls; eauto.
      contradiction Hnot_alloc_b; eauto.
    }
    {
      unfold free_fp.
      econstructor; eauto; simpl; unfold Locs.smile;
        repeat (rewrite Locs.locs_intersect_emp_sym);
        try solve [split; eapply Locs.eq_refl].
      unfold range_locset, Locs.eq, Locs.intersect, Locs.emp; intros; simpls.
      ex_match2; subst; eauto.
      rewrite Zplus_minus.
      destruct (zle z ofs); destruct (zlt ofs z0); simpls; tryfalse; eauto.
      clear - H0 H1 l l0.
      unfolds free.
      ex_match2.
      clear - r H1 l l0.
      unfolds range_perm.
      assert ((z <= ofs < z0)%Z); eauto.
      eapply r in H.
      eapply GMem.invalid_noaccess in H1.
      unfolds Mem.perm_order'.
      rewrite H1 in H; simpl; tryfalse.
    }
    {
      unfold store_fp.
      econstructor; eauto; simpl; unfold Locs.smile;
        repeat (rewrite Locs.locs_intersect_emp_sym);
        try solve [split; eapply Locs.eq_refl].
      split.
      eapply Locs.eq_refl.
      unfold range_locset, Locs.eq, Locs.intersect, Locs.emp; intros; simpls.
      ex_match2; simpl; subst; simpl; eauto.
      destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m0));
        simpl; eauto.
      unfolds store.
      ex_match2.
      clear - v0 H1 l l0.
      unfolds valid_access, range_perm.
      destruct v0.
      assert ((z <= ofs < z + size_chunk m0)%Z); eauto.
      eapply H in H2.
      eapply GMem.invalid_noaccess in H1.
      unfolds Mem.perm_order'.
      rewrite H1 in H2; simpls; tryfalse.
      destruct (zle z ofs); destruct (zlt ofs (z + size_chunk m0));
        simpl; eauto.
      unfold range_locset, Locs.eq, Locs.intersect, Locs.emp; intros; simpls.
      ex_match2; eauto.
    }
  }
  eapply Hstep in H2.
  destruct H2 as (m'0 & Happly_buf & HMemPost).
  eauto.
Qed.

Lemma alloc_newblk_apply_buf_on_original_block_reorder :
    forall m m' m'0 m1 bi b lo hi,
      ~ (exists lo' hi', BufferedAlloc b lo' hi' = bi) ->
      ~ In b (GMem.validblocks m) ->
      alloc m b lo hi = Some m' ->
      apply_buffer_item bi m' = Some m'0 ->
      apply_buffer_item bi m = Some m1 ->
      exists m'1, alloc m1 b lo hi = Some m'1 /\
             GMem.mem_access m'0 = GMem.mem_access m'1.
Proof.
  intros.
  destruct bi; simpls.
  {
    unfolds alloc.
    inv H1; inv H2; inv H3; simpls.
    eexists.
    split; eauto.
    simpl.
    assert (b <> b0).
    intro; subst.
    contradiction H.
    eauto.
    rewrite PMap_set_twice_not_same_reorder_eq; eauto.
  }
  {
    unfolds alloc, free, unchecked_free; simpls.
    ex_match2.
    inv H1; inv H2; inv H3; simpls.
    eexists.
    split; eauto; simpl.
    destruct (peq b0 b) eqn:?; simpls; subst.
    {
      repeat rewrite PMap.gss; eauto.
      repeat rewrite PMap.set2.
      assert ((fun (ofs : Z) (_ : perm_kind) =>
                if zle z ofs && zlt ofs z0
                then None
                else if zle lo ofs && zlt ofs hi then
                       Some Freeable else None) = 
              (fun (ofs : Z) (_ : perm_kind) =>
                if zle lo ofs && zlt ofs hi then Some Freeable
                else None)).
      {
        eapply functional_extensionality; intro.
        eapply functional_extensionality; intro.
        clear - r H0.
        destruct (zle z x); destruct (zlt x z0); simpls; tryfalse;
          eauto.
        unfolds range_perm.
        assert ((z <= x < z0)%Z); eauto.
        eapply r in H.
        destruct m; simpls.
        eapply invalid_noaccess in H0.
        unfold Mem.perm_order' in H.
        rewrite H0 in H; tryfalse.
      }
      rewrite H1; eauto.
    }
    {
      repeat (rewrite PMap.gss; eauto).
      repeat (rewrite PMap.gso; eauto).
      rewrite PMap_set_twice_not_same_reorder_eq; eauto.
    }
  }
  {
    unfolds alloc, store.
    ex_match2.
    inv H1; inv H2; inv H3; simpl.
    eexists.
    split; eauto.
  }
Qed.
  
Lemma unbuffer_safe_alloc_preserve' :
  forall m m' bfs lo hi b,
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    alloc m b lo hi = Some m' ->
    ~ In b (GMem.validblocks m) ->
    (forall t lo' hi', ~ In (BufferedAlloc b lo' hi') (bfs t)) ->
    unbuffer_safe {| tso_buffers := bfs; memory := m' |}.
Proof.
  intros.
  remember {| tso_buffers := bfs; memory := m |} as tm.
  generalize dependent bfs.
  generalize dependent m.
  generalize dependent m'.
  induction H; simpls; intros; subst; simpls; eauto.
  econstructor; intros; simpls; eauto.
  {
    lets Hbf : H3.
    eapply ABIS in H3.
    destruct H3 as [m'' H3].
    clear - H0 H1 H2 H3 Hbf. 
    eapply alloc_apply_buf_block_neq_reorder_succ1; eauto.
    intro.
    destruct H as (lo' & hi' & Hub_alloc); subst.
    specialize (H2 t lo' hi').
    contradiction H2; rewrite Hbf; simpl; eauto.
  }
  { 
    lets Happly_buf : H3.
    eapply ABIS in Happly_buf.
    destruct Happly_buf as [m1 Happly_buf].
    lets Hcons : H3.
    lets Halloc : H0.
    eapply alloc_newblk_apply_buf_on_original_block_reorder in Halloc;
      eauto.
    destruct Halloc as (m'1 & Halloc & Hmem_access).
    eapply H in Hcons.
    2 : eauto.
    4 : eauto.
    2 : eauto.
    eapply unbuffer_safe_mem_access_same_stable; eauto.
    clear - H1 Happly_buf H2 H3.
    destruct bi; simpls.
    unfolds alloc; inv Happly_buf; simpl.
    intro.
    destruct H; subst; tryfalse.
    contradiction (H2 t z z0).
    rewrite H3; simpl; eauto.
    unfolds free, unchecked_free; ex_match2; inv Happly_buf; simpl; eauto.
    unfolds store; ex_match2; inv Happly_buf; simpl; eauto.
    intros.
    destruct (peq t t0); subst.
    {
      specialize (H2 t0 lo' hi').
      intro.
      contradiction H2.
      try rewrite H3 in *.
      rewrite tupdate_b_get in H5.
      simpl; eauto.
    }
    {
      rewrite tupdate_not_eq_get; eauto.
    }
    clear - H2 H3.
    intro.
    destruct H as (lo & hi & H).
    contradiction (H2 t lo hi).
    rewrite H3; subst; simpl; eauto.
  }
Qed.

Lemma unbuffer_safe_tsoalloc_0_stable' :
  forall tm gm fl gm' fm' lo hi t,
    unbuffer_safe tm ->
    (forall t' blk n lo hi,
        t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
        blk <> get_block fl n
    ) ->
    apply_buffer (tso_buffers tm t) gm = Some gm' ->
    embed gm' fl fm' ->
    gm = memory tm ->
    unbuffer_safe
      {| tso_buffers := tupdate t
                                (tso_buffers tm t ++
                                  BufferedAlloc (Mem.nextblock fm') lo hi :: nil)
                                (tso_buffers tm);
         memory := gm |}.
Proof.
  introv Hp.
  lets Ht : Hp.
  generalize dependent gm.
  generalize dependent gm'.
  generalize dependent fm'.
  generalize dependent lo.
  generalize dependent hi.
  generalize dependent t.
  induction Hp; intros; simpls.
  econstructor; intros; simpls.
  {
    unfold tupdate in H4.
    destruct (peq t0 t) eqn:?; tryfalse; subst.
    {
      destruct (tso_buffers tso t) eqn:?; tryfalse; subst; simpls.
      {
        inversion H4; subst; eauto.
        simpl.
        unfold alloc; eauto.
      }
      {
        inversion H4; subst; eauto.
      }
    }
    {
      eapply ABIS in H4; eauto.
    }
  }
  {
    unfold tupdate in H4.
    destruct (peq t0 t) eqn:?; tryfalse; subst.
    {
      rewrite tupdate_same_tid_eq; eauto.
      destruct (tso_buffers tso t) eqn:?; tryfalse; simpls.
      {
        inversion H4; subst; eauto.
        simpl in H5.
        inversion H1; subst.
        inversion H2; subst. 
        destruct tso; simpls.
        rewrite tupdate_same_eq; eauto.
        subst; simpls.
        assert (unbuffer_safe {| tso_buffers := tso_buffers;
                                 memory := (strip fm') |}).
        econstructor; eauto.
        pose proof next_block_not_in_validblock.
        specialize (H6 fm').
        rewrite mem_strip_gm_vb_eq in H6. 
        eapply unbuffer_safe_alloc_preserve'; eauto.
        {
          intros.
          destruct (peq t t0); subst.
          {
            rewrite Heqb0.
            intro; simpls; tryfalse.
          }
          {
            intro.
            eapply H0 in H7; eauto.
            contradiction H7.
            unfold Mem.nextblock; eauto.
          }
        }
      }
      {
        inversion H4; subst; simpl.
        clear H4 Heqs.
        specialize (H t bi b1 m').
        lets Hcons : Heqb0.
        eapply H in Hcons.  
        2 : eauto.
        2 : eapply UNBS; eauto.
        Focus 3.
        instantiate (1 := gm').
        instantiate (1 := m').
        instantiate (1 := t).
        rewrite tupdate_b_get.
        rewrite H5 in H1.
        simpl in H1; eauto.
        3 : eauto.
        3 : eauto.
        rewrite tupdate_b_get in Hcons.
        rewrite tupdate_same_tid_eq in Hcons; eauto.
        clear - H0 Hcons.
        intros.
        eapply H0 in H; eauto.
        unfold tupdate in H1.
        destruct (peq t' t) eqn:?; tryfalse; eauto.
      }
    }
    {  
      specialize (H t0 bi b m').
      lets Hcons : H4.
      lets Happly_buffer : H5. 
      eapply unbuffer_safe_apply_buffer_stable in Happly_buffer; eauto.
      2 : destruct tso; eauto.
      destruct Happly_buffer as [gm'' Happly_buffer].
      lets Hembed : Happly_buffer.
      eapply embed_appply_buffer_update_not_in_freelist_stable' in Hembed; eauto.
      Focus 2.
      clear - H0 Hcons n.
      intros; subst.
      eapply H0 in n; eauto.
      rewrite Hcons; simpls; eauto.
      destruct Hembed as [fm'' [Hembed Hnext_blk_eq]]. 
      eapply H in Hcons.
      2 : eauto.
      2 : eapply UNBS; eauto.   
      Focus 3.
      instantiate (3 := t).
      instantiate (2 := m').
      instantiate (1 := gm'').
      rewrite in_tbf_upd_oth_stillin; eauto.
      4 : eauto.
      Focus 2. 
      clear - H0 H4.
      intros.
      eapply H0 in H; eauto.
      unfold tupdate in H1.
      destruct (peq t' t0) eqn:?; subst; eauto.
      rewrite H4; simpl; eauto.
      2 : instantiate (1 := fm''); eauto.
      rewrite <- Hnext_blk_eq in Hcons.
      rewrite tupdate_not_eq_get in Hcons; eauto. 
      rewrite tupdate_tid_neq_twice_rev in Hcons; eauto.
    }
  }
Qed.
  
Lemma unbuffer_safe_tsoalloc_0_stable :
  forall tm fl fm tsofm' stk t,
    embed (memory tm) fl fm ->
    (forall t' blk n lo hi,
        t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
        blk <> get_block fl n) ->
    tsoalloc {| tbuffer := tso_buffers tm t; fmemory := fm |} 0 0 (tsofm', stk) ->
    unbuffer_safe tm ->
    unbuffer_safe
      {|
        tso_buffers := tupdate t (tbuffer tsofm') (tso_buffers tm);
        memory := strip (fmemory tsofm') |}.
Proof. 
  intros.
  inversion H1; subst; simpls.
  inversion H; subst; simpls.
  eapply unbuffer_safe_tsoalloc_0_stable';  eauto.
Qed.

Lemma unbuffer_safe_tsostore_stable' :
  forall m bfs ofs b n t,
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    (forall n' : int, exists m', store Mint32 m b (Ptrofs.unsigned (Ptrofs.repr ofs))
                                       (Vint n') = Some m') ->
    (
      forall t : tid,
        In b (get_buffer_b (bfs t)) ->
        exists v',
          In (BufferedStore Mint32 b (Ptrofs.unsigned (Ptrofs.repr ofs)) v')
             (bfs t) /\
          count_occ Pos.eq_dec (get_buffer_b (bfs t)) b = 1
    ) ->
    unbuffer_safe
      {|
        tso_buffers := tupdate t
               (bfs t ++ BufferedStore Mint32 b (Ptrofs.unsigned (Ptrofs.repr ofs))
                    (Vint n) :: nil) bfs; memory := m |}.
Proof.
  introv H. 
  remember {| tso_buffers := bfs; memory := m |} as tsofm.
  lets Ht : H.
  revert Ht.
  generalize dependent bfs.
  generalize dependent m.
  generalize dependent ofs.
  generalize dependent b.
  generalize dependent n.
  generalize dependent t.
  induction H; intros; subst; simpls. 
  econstructor; simpls; intros. 
  {
    unfold tupdate in H2.
    destruct (peq t0 t); tryfalse.
    {
      subst.
      destruct (bfs t) eqn : ?; tryfalse.
      {
        simpl in H2.
        inversion H2; subst.
        clear - H0.
        simpl.
        specialize (H0 n).
        eauto.
      }
      {
        simpl in H2.
        inversion H2; subst.
        eapply ABIS in Heqb1.
        eauto.
      }
    }
    {
      eapply ABIS in H2.
      eauto.
    }
  }
  { 
    unfold tupdate in H2.
    destruct (peq t0 t); tryfalse.
    {
      subst.
      destruct (bfs t) eqn:?; tryfalse.
      {
        simpls.
        inversion H2; subst; eauto.
        clear_trivial_eq.
        rewrite tupdate_same_tid_eq.
        rewrite tupdate_same_eq; eauto.
        simpl in H3.
        eapply unbuffer_safe_store_preserve; eauto.
      }
      {
        simpl in H2.
        inversion H2; subst.
        clear_trivial_eq.
        lets Ht1 : Heqb1.
        eapply H in Heqb1.
        rewrite tupdate_same_tid_eq.
        Focus 3.
        eauto.
        Focus 2. eauto.
        assert (tupdate t b2 bfs t = b2).
        eapply tupdate_b_get; eauto.
        rewrite H2 in Heqb1.
        rewrite tupdate_same_tid_eq in Heqb1.
        eauto.
        eauto.
        intros.
        specialize (H0 n').
        destruct H0 as [m'' Hstore].
        clear - Hstore H1 Heqb1 H3. 
        destruct bi.
        { 
          simpl in H3.
          assert (b0 <> b).
          {
            intro.
            subst. 
            assert (In b (get_buffer_b (bfs t))).
            rewrite Heqb1.
            simpl.
            eauto.
            eapply H1 in H.
            destruct H as [v' [Hin Hcount]].
            rewrite Heqb1 in Hin.
            rewrite Heqb1 in Hcount.
            simpl in Hin.
            destruct Hin.
            inversion H; subst.
            simpl in Hcount.
            destruct (Pos.eq_dec b b); tryfalse.
            assert (count_occ Pos.eq_dec (get_buffer_b b2) b = 0).
            Lia.lia.
            eapply count_occ_not_In in H0.
            eapply b_not_bf_item_not1 in H.
            eapply H0 in H.
            tryfalse.
          }
          eapply store_alloc_still; eauto.
        }
        {
          simpl in H3.
          assert (b0 <> b).
          {
            intro.
            subst. 
            assert (In b (get_buffer_b (bfs t))).
            rewrite Heqb1.
            simpl.
            eauto.
            eapply H1 in H.
            destruct H as [v' [Hin Hcount]].
            rewrite Heqb1 in Hin.
            rewrite Heqb1 in Hcount.
            simpl in Hin.
            destruct Hin.
            inversion H; subst.
            simpl in Hcount.
            destruct (Pos.eq_dec b b); tryfalse.
            assert (count_occ Pos.eq_dec (get_buffer_b b2) b = 0).
            Lia.lia.
            eapply count_occ_not_In in H0.
            eapply b_not_bf_item_not1 in H.
            eapply H0 in H.
            tryfalse.
          }

          eapply store_free_other_still; eauto.
        }
        {
          simpl in H3.
          eapply store_store_other_still; eauto.
        }

        intros.
        unfold tupdate in H2.
        destruct (peq t0 t) eqn:?; tryfalse.
        {
          subst.
          unfold tupdate.
          destruct (peq t t); tryfalse.
          assert (Ht2 : In b (get_buffer_b (bfs t))).
          rewrite Heqb1; simpl; eauto.
          destruct bi; simpl; eauto.
          eapply H1 in Ht2.

          destruct Ht2 as [v' [Hin' Hcount]].
          rewrite Heqb1 in Hin'.
          simpl in Hin'.
          destruct Hin'; subst.
          rewrite Heqb1 in Hcount.
          simpl in Hcount.
          destruct (Pos.eq_dec b b); tryfalse.
          assert (count_occ Pos.eq_dec (get_buffer_b b2) b = 0).
          eauto.
          eapply count_occ_not_In in H4.
          eapply H4 in H2. tryfalse.
          rewrite Ht1 in Hcount.
          simpl in Hcount.
          destruct bi.
          {
            simpl in Hcount.
            destruct (Pos.eq_dec b0 b) eqn:?; tryfalse.
            subst.
            assert (count_occ Pos.eq_dec (get_buffer_b b2) b = 0).
            eauto.
            eapply count_occ_not_In in H5.
            eapply H5 in H2; tryfalse.
            eexists.
            split; eauto.
          }
          {
            simpl in Hcount.
            destruct (Pos.eq_dec b0 b) eqn:?; tryfalse.
            subst.
            assert (count_occ Pos.eq_dec (get_buffer_b b2) b = 0).
            eauto.
            eapply count_occ_not_In in H5.
            eapply H5 in H2; tryfalse.
            eexists.
            split; eauto.
          }
          {
            simpl in Hcount.
            destruct (Pos.eq_dec b0 b) eqn:?; tryfalse.
            subst.
            assert (count_occ Pos.eq_dec (get_buffer_b b2) b = 0).
            eauto.
            eapply count_occ_not_In in H5.
            eapply H5 in H2; tryfalse.
            eexists.
            split; eauto.
          }
        }
        {
          eapply H1 in H2.
          split_and H2.
          eexists.
          unfold tupdate.
          destruct (peq t0 t); tryfalse.
          eauto.
        }
      }
    }
    {
      lets Ht1 : H2.
      eapply H in Ht1.
      Focus 2.
      eauto.
      Focus 2.
      eauto.
      assert (tupdate t0 b0 bfs t = bfs t).
      {
        eapply tupdate_not_eq_get; eauto.
      }
      rewrite H4 in Ht1.
      rewrite tupdate_tid_neq_twice_rev; eauto.
      eauto.

      intros.
      specialize (H0 n').
      destruct H0 as [m'' Hstore].
      clear - Hstore H1 Ht1 H3.
      destruct bi.
      { 
        simpl in H3.
        assert (b1 <> b).
        {
          intro; subst.
          assert (In b (get_buffer_b (bfs t0))).
          rewrite Ht1.
          simpl.
          eauto.
          eapply H1 in H.
          destruct H as [v' [Hin Hcount]].
          rewrite Ht1 in Hin.
          rewrite Ht1 in Hcount.
          simpl in Hin.
          destruct Hin.
          inversion H; subst.
          simpl in Hcount.
          destruct (Pos.eq_dec b b); tryfalse.
          assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
          Lia.lia.
          eapply count_occ_not_In in H0.
          eapply b_not_bf_item_not1 in H.
          eapply H0 in H.
          tryfalse.
        }
        
        eapply store_alloc_still; eauto.
      }
      { 
        simpl in H3.
        assert (b1 <> b).
        {
          intro.
          subst.
          assert (In b (get_buffer_b (bfs t0))).
          rewrite Ht1.
          simpl.
          eauto.
          eapply H1 in H.
          destruct H as [v' [Hin Hcount]].
          rewrite Ht1 in Hin.
          rewrite Ht1 in Hcount.
          simpl in Hin.
          destruct Hin.
          inversion H; subst.
          simpl in Hcount.
          destruct (Pos.eq_dec b b); tryfalse.
          assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
          Lia.lia.
          eapply count_occ_not_In in H0.
          eapply b_not_bf_item_not1 in H.
          eapply H0 in H.
          tryfalse.
        }

        eapply store_free_other_still; eauto.
      }
      {
        simpl in H3.
        eapply store_store_other_still; eauto.
      }
 
      intros.
      unfold tupdate in H4.
      destruct (peq t1 t0) eqn:?; tryfalse.
      { 
        subst.
        unfold tupdate.
        destruct (peq t0 t0); tryfalse.
        assert (Ht2 : In b (get_buffer_b (bfs t0))).
        rewrite Ht1; simpl; eauto.
        destruct bi; simpl; eauto.
        eapply H1 in Ht2.

        destruct Ht2 as [v' [Hin' Hcount]].
        rewrite Ht1 in Hin'.
        simpl in Hin'.
        destruct Hin'; subst.
        rewrite Ht1 in Hcount.
        simpl in Hcount.
        destruct (Pos.eq_dec b b); tryfalse.
        assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
        eauto.
        eapply count_occ_not_In in H5.
        eapply H5 in H4. tryfalse.
        rewrite Ht1 in Hcount.
        simpl in Hcount.
        destruct bi.
        {
          simpl in Hcount.
          destruct (Pos.eq_dec b1 b) eqn:?; tryfalse.
          subst.
          assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
          eauto.
          eapply count_occ_not_In in H6.
          tryfalse.
          eapply H6 in H4; tryfalse.
          eexists.
          split; eauto.
        }
        {
          simpl in Hcount.
          destruct (Pos.eq_dec b1 b) eqn:?; tryfalse.
          subst.
          assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
          eauto. 
          eapply count_occ_not_In in H6.
          eapply H6 in H4; tryfalse.
          eexists.
          split; eauto.
        }
        {
          simpl in Hcount.
          destruct (Pos.eq_dec b1 b) eqn:?; tryfalse.
          subst.
          assert (count_occ Pos.eq_dec (get_buffer_b b0) b = 0).
          eauto.
          eapply count_occ_not_In in H6.
          eapply H6 in H4; tryfalse.
          eexists.
          split; eauto.
        }
      }
      {
        eapply H1 in H4.
        split_and H4.
        eexists.
        unfold tupdate.
        destruct (peq t1 t0); tryfalse.
        eauto.
      }
    }
  }
Qed.
  
Lemma unbuffer_safe_tsostore_stable :
  forall tm fl fm b ofs n tsofm' t,
    embed (memory tm) fl fm ->
    (forall n', exists m', store Mint32 (memory tm) b
                  (Ptrofs.unsigned (Ptrofs.repr ofs)) (Vint n') = Some m') ->
    (forall t, In b (get_tsom_b t tm) ->
               (exists v', In (BufferedStore Mint32 b
                  (Ptrofs.unsigned (Ptrofs.repr ofs))  v') (tso_buffers tm t)
    /\ count_occ Pos.eq_dec (get_tsom_b t tm) b = 1)) ->
    tsostorev Mint32 {| tbuffer := tso_buffers tm t; fmemory := fm |}
              (Vptr b (Ptrofs.repr ofs)) (Vint n) = Some tsofm' ->
    unbuffer_safe tm ->
    unbuffer_safe
      {|
        tso_buffers := tupdate t (tbuffer tsofm') (tso_buffers tm);
        memory := strip (fmemory tsofm') |}.
Proof.
  intros.
  unfolds tsostorev.
  unfolds tsostore.
  inversion H2; subst; simpls.
  destruct tm.
  simpls.
  inversion H; subst; simpls.
  eapply unbuffer_safe_tsostore_stable'; eauto.
Qed.

Lemma spec_init_lock_one :
  forall sge sG sm L,
    InteractionSemantics.init_genv SpecLang.speclang
                                   lock_comp_unit sge sG ->
    InteractionSemantics.init_gmem SpecLang.speclang sge sm ->
    Genv.find_symbol sge lock_L_ident = Some L ->
    load Mint32 sm L 0 = Some (Vint Int.one) /\
    (forall n, exists M', store Mint32 sm L 0 (Vint n) = Some M').
Proof.
  intros; simpls.
  inversion H; subst.
  inversion H0; subst.
  renames x to fm.
  destruct H2 as [Hfm Hinit_fmem].
  inversion Hinit_fmem; subst.
  unfolds SpecLang.globals_initialized_fmem_speclang; subst.
  inversion H3; subst.
  specialize (H6 lock_L_ident).
  inversion H6; subst.
  rewrite H1 in H13.
  inversion H13; subst b'.
  clear H13.
  eapply H9 in H14.
  simpl in H14.
  clear - globdef_initialized_fm H14.
  lets Ht : H14.
  symmetry in Ht.
  unfolds Genv.find_def.
  eapply globdef_initialized_fm in Ht; simpl in Ht.
  split_and Ht.
  split.
  {
    assert (Hload : false = false); eauto.
    eapply H2 in Hload.
    split_and Hload; eauto.
  }
  {
    intros.
    unfold store.
    ex_match2; eauto.
    contradiction n0.
    clear - H.
    unfold valid_access; simpl; split; eauto.
    eapply Zmod_divide; eauto.
    Lia.lia.
  }
Qed.

Lemma spec_init_obj_mem :
  forall sge sG sm ofs L,
    InteractionSemantics.init_genv SpecLang.speclang
                                   lock_comp_unit sge sG ->
    InteractionSemantics.init_gmem SpecLang.speclang sge sm ->
    Genv.find_symbol sge lock_L_ident = Some L ->
    (0 <= ofs < 4)%Z ->
    obj_mem sm L ofs.
Proof.
  simpl; intros.
  inversion H; subst.
  inversion H4; subst.
  specialize (H7 lock_L_ident).
  inversion H7; subst.
  rewrite H1 in H14.
  inversion H14; subst b'.
  clear H14.
  lets Ht : H15.
  eapply H10 in Ht.
  simpl in Ht.
  clear - H0 H1 H2 Ht.
  inversion H0; subst.
  renames x to fm.
  destruct H as [Hfm Hinit_mem]; subst.
  inversion Hinit_mem; subst.
  unfolds SpecLang.globals_initialized_fmem_speclang.
  lets Hvar : Ht.
  unfold Genv.find_def in globdef_initialized_fm.
  symmetry in Hvar.
  eapply globdef_initialized_fm in Hvar.
  simpl in Hvar.
  split_and Hvar.
  lets Hcur_perm_none : H2.
  eapply H4 in Hcur_perm_none.
  unfold obj_mem.
  split; eauto.
  clear - H2 H.
  intro.
  unfolds Mem.range_perm.
  eapply H in H2; clear H.
  unfolds Mem.perm.
  unfolds Mem.perm_order'.
  rewrite <- Mem_GMem_access_eq in H0.
  rewrite H0 in H2; tryfalse.
Qed.

(** [Io] still holds after allocation *)
Lemma obj_inv_alloc_stable :
  forall fsm fsm' tm fm bm1 fl t tge stk' stk,
    (forall t' blk n lo hi,
        t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
        blk <> get_block fl n) ->
    obj_inv tge (strip fsm) tm ->
    embed (memory tm) fl fm ->
    embed (strip fsm) fl fsm ->
    tsoalloc {| tbuffer := tso_buffers tm t; fmemory := fm |} 0 0 (bm1, stk) ->
    Mem.alloc fsm 0 0 = (fsm', stk') ->
    obj_inv tge (strip fsm')
            {|
              tso_buffers := tupdate t (tbuffer bm1) (tso_buffers tm);
              memory := strip (fmemory bm1) |}.
Proof.
  introv Hno_conflict.
  intros.
  inversion H0; subst.
  inversion H1; subst.
  clear H6.
  unfold obj_inv in H.
  simpl get_gm. 
  destruct H as [L [H_L [Hlock_st [H_spec_store [Htso_store [Hunbuffer_safe H]]]]]].
  eexists; split; eauto. 
  split.
  {
    destruct Hlock_st as [H_lock | H_unlock].
    { 
      left.   
      clear - H_lock H2 H3 H4 H5.
      unfolds lock_st.
      simpls.
      split_and H_lock.
      lets Hload : load_Mem_alloc_still ___; eauto.
      split; eauto.

      inversion H2; subst; simpls; clear H2.
      split.
      {  
        intros; intro.
        unfolds tupdate.
        dis_if_else; subst.
        {
          destruct H0 as [ofs H0].
          specialize (H1 t).
          contradiction H1.
          eapply in_buffer_app_or in H0.
          destruct H0; eauto.
          inv H0.
          simpl in H7.
          destruct H7; tryfalse.
          subst. inv H8.
          simpls. 
          unfolds load_tsomem.
          destruct tm.
          simpls.
          rewrite H5 in H11.
          lets Ht : H6.
          eapply load_in_validblocks in Ht; eauto.
          lets Hin_valid_block : apply_buffer_in_validblocks_stable ___; eauto.
          inv H13.
          destruct fm'.
          unfolds strip, Mem.nextblock.
          simpls; subst.
          clear - valid_wd Hin_valid_block.
          assert (get_block (Mem.freelist fm) nextblockid =
                  get_block (Mem.freelist fm) nextblockid); eauto.
          eapply valid_wd in H.
          eapply H in Hin_valid_block.
          Lia.lia.
        }
        {
          eapply (H1 t0).
          eauto.
        }
      }
      {
        clear - H6 H5.
        unfolds load_tsomem.
        destruct tm; simpls; subst; eauto.
      }
    }
    {  
      right. 
      unfolds unlock_st; simpls.
      split_and H_unlock.
      split.
      {
        eapply load_Mem_alloc_still; eauto.
      }
 
      inversion H2; subst; simpls.
      destruct H7.
      {        
        left.
        destruct H7 as [t0 [bf1 [bf2 H7]]].
        split_and H7.
        exists t0.
        destruct (peq t0 t) eqn:?; subst; eauto.
        rewrite tupdate_b_get; eauto.
        do 2 eexists.
        split.
        rewrite H8.
        rewrite app_assoc_reverse; simpls; eauto.
        split.
        intros; intro.
        rewrite tupdate_not_eq_get in H12; eauto.
        eapply H7 with (ofs := ofs) in H10.
        tryfalse.

        split.
        intros; intro.
        rewrite <- app_assoc_reverse in H10; eauto.
        eapply in_buffer_app_or in H10.
        destruct H10.
        clear - H9 H10.
        specialize (H9 ofs); tryfalse.
        inv H10.
        simpl in H12; destruct H12; tryfalse; subst.
        inv H14.
        unfolds load_tsomem.
        destruct tm; simpls; subst.
        inv H15.
        lets Ht : load_in_validblocks ___; eauto.
        eapply apply_buffer_in_validblocks_stable in Ht; eauto.
        rewrite <- mem_strip_gm_vb_eq in Ht.
        eapply next_block_not_in_validblock in Ht; tryfalse.
        clear - H11 H5.
        destruct tm; simpls; subst; eauto.
 
        do 2 eexists.
        split.
        rewrite tupdate_not_eq_get; eauto.
        split.
        intros; intro.
        unfold tupdate in H12.
        destruct (peq t' t); subst.
        eapply H7 with (ofs := ofs) in H10.
        contradiction H10.
        eapply in_buffer_app_or in H12; destruct H12; eauto.
        inv H12.
        simpl in H14; destruct H14; tryfalse; subst.
        inv H16. inv H15.
        clear - H11 H13 H5.
        unfolds load_tsomem; destruct tm; simpls; subst.
        lets Ht : load_in_validblocks ___; eauto.
        eapply apply_buffer_in_validblocks_stable in Ht; eauto.
        rewrite <- mem_strip_gm_vb_eq in Ht.
        eapply next_block_not_in_validblock in Ht; tryfalse.
        eapply H7 with (ofs := ofs) in H10; tryfalse.

        split; eauto.
        clear - H5 H11.
        destruct tm; simpls; subst; eauto.
      }
      { 
        right.
        destruct H7. 
        clear - H7 H5 H8 H13 H15.
        split.
        unfolds load_tsomem.
        destruct tm; simpls; subst; eauto.
        do 3 intro. 
        unfolds tupdate.
        dis_if_else; subst; eauto.
        {
          eapply in_buffer_app_or in H.
          destruct H.
          specialize (H8 t ofs); tryfalse.
          inv H.
          simpl in H1; destruct H1; tryfalse; subst.
          inv H2. inv H15.
          destruct tm; simpls; subst.
          lets Ht : load_in_validblocks ___; eauto.
          eapply apply_buffer_in_validblocks_stable in Ht; eauto.
          rewrite <- mem_strip_gm_vb_eq in Ht.
          eapply next_block_not_in_validblock in Ht; tryfalse.
        }
        {
          eapply (H8 t0 ofs).
          unfold get_tsom_b.
          destruct tm; simpls; eauto.
        }
      }
    }
  }
  {
    split. 
    clear - H_spec_store H3.
    intros.
    specialize (H_spec_store n). 
    destruct H_spec_store as [M' H_spec_store].
    eapply GMem_store_alloc_store; eauto.
    split. 
    clear - Htso_store H2 H5.
    intros.
    specialize (Htso_store n).
    destruct Htso_store as [bm' Htso_store].
    inversion H2; subst; simpls.
    unfolds store_tsomem.
    destruct tm; simpls; subst; simpls.
    destruct (store Mint32 (strip fm) L 0 (Vint n)) eqn:?; tryfalse.
    eauto.

    split.  
    eapply unbuffer_safe_tsoalloc_0_stable; eauto.
  
    split.
    clear - H H3.
    destruct H.
    intros.
    eapply H in H1.
    eapply obj_mem_alloc_stable; eauto.

    destruct H.
    destruct H6.
    split.
    intros; simpls.
    eapply H6 in H8.
    clear - H0 H2 H8.
    inversion H0; subst; eauto.
    destruct tm; simpls; subst.
    unfolds buffer_insert.
    simpls.
    inversion H2; subst.
    clear H2.
    eauto.

    intros; simpl.
    renames H2 to Htso_alloc, H0 to Hembed. 
    clear - H7 H3 H8 H_spec_store Htso_alloc Hembed.
    eapply H7 in H8.
    destruct H8.
    split.
    intro.
    contradiction H.
    instantiate (2 := k).
    instantiate (1 := p). 
    clear - H_spec_store H1 H3.
    specialize (H_spec_store Int.zero).
    destruct H_spec_store as [M' H_spec_store].
    unfolds Mem.alloc.
    inv H3; subst.
    unfolds strip; simpls.
    unfolds GMem.perm; simpls.
    unfolds store; simpls.
    dis_if_else. 
    inversion H_spec_store; subst; clear H_spec_store.
    clear H.
    pose proof next_block_not_in_validblock.
    specialize (H fsm).
    assert (L <> Mem.nextblock fsm).
    {
      intro; subst.
      destruct fsm; simpls.
      unfolds Mem.nextblock; simpls.
      unfold valid_access, range_perm in v; simpls.
      lets Ht : v.
      destruct Ht.
      assert ((0 <= 0 < 4)%Z). Lia.lia.
      eapply H0 in H3.
      eapply invalid_noaccess in H.
      rewrite H in H3.
      clear - H3.
      unfolds Mem.perm_order'; tryfalse.
    }
    rewrite PMap.gso in H1; eauto.
    intro.
    contradiction H0.
    clear - Htso_alloc H1 Hembed.
    inv Hembed.
    inv Htso_alloc; simpls.
    rewrite <- H0; eauto.
  }
Qed.

Lemma obj_inv_impl_load_zero_or_one :
  forall sm tm tge b v,
    Genv.find_symbol tge lock_L_ident = Some b ->
    obj_inv tge sm tm ->
    load Mint32 (memory tm) b 0 = Some v ->
    v = Vone \/ v = Vzero.
Proof.
  intros.
  unfolds obj_inv.
  destruct H0 as (L & H0).
  split_and H0.
  rewrite H in H2; inv H2.
  destruct H0.
  unfolds lock_st.
  split_and H0.
  unfolds load_tsomem; simpl.
  destruct tm; simpls.
  rewrite H10 in H1.
  inv H1; eauto.
  unfolds unlock_st.
  split_and H0.
  destruct H8.
  split_and H0.
  unfolds load_tsomem.
  destruct tm; simpls.
  rewrite H15 in H1; inv H1; eauto.
  split_and H0.
  unfolds load_tsomem.
  destruct tm; simpls.
  rewrite H8 in H1; inv H1; eauto.
Qed.