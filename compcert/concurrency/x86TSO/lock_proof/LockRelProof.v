(** We prove that the implementation of function unlock and its corresponding 
specification satisfy the object simulation in this file. *)
From mathcomp.ssreflect Require Import fintype ssrnat.                
Require Import Coqlib Maps Axioms.  
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
 
Require Import Asm. 

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory TSOMem MemAux. 
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe. 
 
Require CminorLang. 
Require SpecLang. 
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

(** * Lemmas about lock release *)
Lemma tso_lock_release_init_state :
  forall tge tc
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hinit_core : Some tc = init_core tge lock_release_ident nil),
  exists fb, Genv.find_symbol tge lock_release_ident = Some fb /\
        Some tc = fundef_init fb (fn_sig lock_release_tso_fnbody) nil.
Proof.
  intros.
  inversion Himp_init.
  unfolds init_core.
  unfolds ASM_local.init_core.
  destruct (Genv.find_symbol tge lock_release_ident) eqn:Hfind_symb;
    try discriminate.
  specialize (H2 lock_release_ident).
  inversion H2; subst.
  rewrite Hfind_symb in H9.
  inversion H9; subst.
  eapply H5 in H10.
  simpl in H10.
  clear - Hinit_core H10.
  unfolds Genv.find_funct_ptr.
  unfolds Genv.find_def.
  rewrite <- H10 in Hinit_core.
  simpls.
  eauto.
Qed.

Lemma spec_lock_release_init_state :
  forall sge sG sc
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Hsc_init : Some sc = SpecLang.init_core sge lock_release_ident nil),
  exists fb, Genv.find_symbol sge lock_release_ident = Some fb /\
        Some sc = SpecLang.fundef_init (Internal lock_release_fnbody) nil.
Proof.
  intros.
  inversion Hspec_init; subst.
  inversion H0; subst.
  specialize (H3 lock_release_ident).
  inversion H3; subst.
  eapply H6 in H11; eauto.
  simpl in H11.
  clear H0 H H1 H2 H3 H4 H5 H6 H7.
  unfold SpecLang.init_core in Hsc_init.
  unfold generic_init_core in Hsc_init.
  unfold SpecLang.F, SpecLang.V in H10. 
  rewrite <- H10 in Hsc_init.
  unfold Genv.find_funct_ptr in Hsc_init.
  unfold Genv.find_def in Hsc_init.
  unfold SpecLang.F, SpecLang.V  in H11.
  rewrite <- H11 in Hsc_init.
  simpl in Hsc_init.
  eexists.
  split; eauto.
Qed.

Lemma lock_release_core_init_match :
  forall tge tc sge sG
    (Htso_init_genv : init_genv lock_comp_tso_unit tge)
    (Hspec_init_genv : InteractionSemantics.init_genv
                         SpecLang.speclang lock_comp_unit sge sG)
    (Hinit_core : init_core tge lock_release_ident nil = Some tc),
  exists sc,
    InteractionSemantics.init_core SpecLang.speclang sG lock_release_ident nil
    = Some sc.
Proof.
  intros.
  inversion Hspec_init_genv.
  subst.
  inversion H0; subst.
  simpl.
  unfold SpecLang.init_core.
  unfold generic_init_core.
  specialize (H3 lock_release_ident).
  inversion H3; subst.
  eapply H6 in H11; eauto.
  simpl in H11.
  eexists.
  unfolds SpecLang.F, SpecLang.V.
  rewrite <- H10.
  unfold Genv.find_funct_ptr.
  unfold Genv.find_def.
  rewrite <- H11.
  simpl.
  eauto.
Qed.

Lemma lock_release_core_init_match' :
  forall tge sc sge sG args
    (Htso_init_genv : init_genv lock_comp_tso_unit tge)
    (Hspec_init_genv : InteractionSemantics.init_genv
                         SpecLang.speclang lock_comp_unit sge sG)
    (Hspec_init_core : InteractionSemantics.init_core SpecLang.speclang
                                           sG lock_release_ident args = Some sc),
  exists tc,
    init_core tge lock_release_ident args = Some tc.
Proof. 
  intros.
  inversion Htso_init_genv.
  specialize (H2 lock_release_ident).
  inversion H2; subst.
  unfold init_core.
  unfold ASM_local.init_core.
  rewrite <- H9.
  eapply H5 in H10.
  simpl in H10.
  unfold Genv.find_funct_ptr.
  unfold Genv.find_def.
  rewrite <- H10.
  simpl.
  unfold fundef_init.
  simpl.

  clear H H0 H1 H2 H3 H4 H5 H6. 
  inversion Hspec_init_genv; subst.
  inversion H0; subst.
  specialize (H3 lock_release_ident).
  inversion H3; subst.
  eapply H6 in H13; eauto.
  simpl in H13.
  clear H H0 H1 H2 H3 H4 H5 H6 H7.
  simpl in Hspec_init_core.
  unfolds SpecLang.init_core.
  simpls.
  unfolds generic_init_core.
  clear - Hspec_init_core H12 H13.
  unfolds SpecLang.F, SpecLang.V.
  rewrite <- H12 in Hspec_init_core.
  unfolds Genv.find_funct_ptr, Genv.find_def.
  clear - Hspec_init_core H13.
  rewrite <- H13 in Hspec_init_core.
  simpls.
  destruct args; tryfalse.
  simpl.
  eauto.
Qed.

(** [match_no_extcall] holds in function unlock *)
Lemma lock_release_no_external :
  forall t sc sm tc tm sge tge sG
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hlock_rel_match_state : unlock_match_state sge tge t (sc, sm) (tc, tm)),
    at_external tge tc = None.
Proof.
  intros.
  inversion Hlock_rel_match_state; subst;
    try solve [simpl; eauto].
  { 
    (* init state *)
    eapply tso_lock_release_init_state in H4; eauto.
    destruct H4 as [fb [Hfb Hinit_state]].
    unfolds fundef_init.
    simpls.
    inversion Hinit_state; subst.
    simpl.
    eauto.
  }
Qed.

(** [match_halt] holds in function unlock *)
Lemma unlock_ret_val_eq :
  forall sge tge t sc sm tc tm rv
    (Hhalt : halt tc = Some rv)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hunlock_match_state : unlock_match_state sge tge t (sc, sm) (tc, tm)),
    SpecLang.halt sc = Some rv.
Proof.
  intros.
  inversion Hunlock_match_state; subst;
    try solve
        [
          simpl in Hhalt; 
          match goal with
          | H : ?rs _ = Vptr _ _ |- _ =>
            rewrite H in Hhalt; simpl in Hhalt; tryfalse
          end
        ].
  {
    eapply tso_lock_release_init_state in H4; eauto.
    destruct H4 as [fb [Hfind_symb Hfunc_init]].
    unfolds fundef_init.
    simpls.
    inversion Hfunc_init; subst.
    simpls; tryfalse.
  } 
  {
    simpl.
    simpl in Hhalt.
    rewrite H6 in Hhalt.
    simpls.
    unfold loc_result in Hhalt.
    destruct Archi.ptr64 eqn:?;try discriminate.
    simpl in Hhalt.
    rewrite H7 in Hhalt; eauto. 
  }
Qed.

(** The initial step of function unlock satisfies [Go] *)
Lemma unlock_init_step_satify_Gobj :
  forall sge sG tge t sc sm tc tc' tm tm' b' gm' fp fl
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                            (InteractionSemantics.V SpecLang.speclang) sge tge)
    (Hno_conflict : 
       forall t' blk n lo hi,
         t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
         blk <> get_block fl n
    )
    (Hrel_tm_gm_vb : rel_tm_gm_vb sm tm fl t)
    (Htsostep : tsostep tge fl tc (tso_buffers tm t, memory tm) fp tc'
                        (b', gm'))
    (Htm : tm' = (mktsomem (tupdate t b' (tso_buffers tm)) gm'))
    (Htc_init : Some tc = init_core tge lock_release_ident nil)
    (Hsc_init : Some sc = SpecLang.init_core sge lock_release_ident nil)
    (Hobj_inv : obj_inv tge sm tm),
    (exists FP sc' sm',
        InteractionSemantics.star
          (InteractionSemantics.step SpecLang.speclang sG fl)
          sc sm FP sc' sm' /\
        (
          (* match after star step *)
          ( Gobj tge t sm tm sm' tm' /\
            obj_match_state sge tge t (sc', sm') (tc', tm') /\
            tm_alloc_not_fl tm' fl t /\ rel_tm_gm_vb sm' tm' fl t /\
            obj_fp sm sm' fp)
          \/
          (* abort after star step *)
          ((forall FP' sc'' sm'', ~ InteractionSemantics.step SpecLang.speclang sG fl
                               sc' sm' FP' sc'' sm'')
           /\ InteractionSemantics.at_external SpecLang.speclang sG sc' = None
           /\ (forall ores, InteractionSemantics.after_external SpecLang.speclang sc' ores
                      = None)
           /\ InteractionSemantics.halt SpecLang.speclang sc' = None)
        )
    ).
Proof.
  intros.
  eapply tso_lock_release_init_state in Htc_init; eauto.
  destruct Htc_init as [fb [Hfind_symb Hf_init]].
  unfold fundef_init in Hf_init.
  simpl in Hf_init.
  inversion Hf_init; subst.
  eapply spec_lock_release_init_state in Hsc_init; eauto.
  destruct Hsc_init as [fb' [Hfind_symb' Hsc_init]].
  simpl in Hsc_init.
  inversion Hsc_init; subst.
  clear Hsc_init.

  inversion Htsostep; subst.
  clear Htsostep.

  match goal with
  | H : context [tsofstep] |- _ => inversion H; subst
  end.
  match goal with
  | H1 : context [args_len_rec],
         H2 : context [tsoalloc], H3 : context [store_args_fmem] |- _ =>
    renames H1 to Hargs_len, H2 to Htsoalloc, H3 to Hstore_args
  end.
  simpl in Hargs_len, Htsoalloc, Hstore_args.
  inversion Hargs_len; subst.
  simpl in Htsoalloc.
  unfolds store_args_fmem.
  simpl in Hstore_args.
  inversion Hstore_args; subst tsofm'.
  clear_trivial_eq.

  match goal with
  | H : embed _ _ _ |- _ => inversion H; subst;
                            match goal with
                            | H1 : strip _ = memory _ |- _ =>
                              renames H1 to Hm_eq
                            end
  end.
  inversion Htsoalloc; subst; simpl.
  lets Hembed_same_block : rel_tm_gm_vb_impl_alloc_same_block ___; eauto.
  rewrite <- Hm_eq; eauto.
  destruct Hembed_same_block as [fsm [Hspec_embed_ex Hnextblock_eq]].
  lets Hmem_alloc : embed_alloc_succ ___; eauto.
  destruct Hmem_alloc as [fsm' Hmem_alloc].
  inversion Hspec_embed_ex; subst.
  match goal with
  | H : Mem.freelist _ = Mem.freelist _ |- _ => renames H to Hmem_freels
  end.
  do 3 eexists.
  split.
  eapply InteractionSemantics.star_step; eauto.
  rewrite <- Hmem_freels.
  econstructor.
  rewrite Hmem_freels; eauto.
  instantiate (1 := fsm'); econstructor; eauto.
  eauto.
  econstructor; eauto.
  left.
  lets Hobj_inv' : obj_inv_alloc_stable ___; eauto; simpl in Hobj_inv'.

  assert (HGalloc :
            G_alloc tge t (strip fsm) tm (strip fsm')
                    {|
                      tso_buffers := tupdate t
                     (tso_buffers tm t ++
                      BufferedAlloc (Mem.nextblock fm') 0 0 :: nil)
                     (tso_buffers tm);
                      memory := strip fm |}).
  {
    unfold G_alloc.
    exists (Mem.nextblock fsm).
    split; eauto.
    split; eauto. 
    split.
    symmetry. 
    eapply Mem_alloc_gm_alloc; eauto.
    split. 
    unfold buffer_insert in Htsoalloc; simpl in Htsoalloc.
    lets Ht : tsoalloc_append ___; eauto.
    simpl in Ht.
    try rewrite Hnextblock_eq in *; eauto.
    simpl. 
    split.
    rewrite mem_strip_gm_vb_eq; eauto.
    eapply next_block_not_in_validblock; eauto.
    pose proof next_block_not_in_validblock.
    specialize (H fm').
    assert (~ In (Mem.nextblock fm') (GMem.validblocks gm')).
    {
      clear - H8 H.
      inv H8.
      rewrite mem_strip_gm_vb_eq in H; eauto.
    }
    lets Hnot_in_vb : H0.
    eapply not_in_apply_bf_vb_not_in_orign in H0; eauto.
    lets Hunbuffer_safe : Hobj_inv.
    eapply obj_inv_impl_unbuffer_safe in Hunbuffer_safe; eauto.
    rewrite Hm_eq in H0. 
    assert (forall t lo hi, ~ In (BufferedAlloc (Mem.nextblock fm') lo hi)
                         (tso_buffers tm t)).
    {
      clear - Hunbuffer_safe Hno_conflict H0 H5 H8 Hm_eq H.
      intros; intro.
      destruct (peq t t0); subst.
      {
        inv H8.
        eapply apply_buffer_not_in_vb_not_alloc_in_bf in H5; eauto.
      }
      { 
        inv H8.
        eapply Hno_conflict in H1; eauto.
        contradiction H1.
        unfold Mem.nextblock.
        rewrite H2; eauto.
      }
    } 
    clear - Hrel_tm_gm_vb Hnextblock_eq Hmem_freels Hunbuffer_safe H1 H0 H5 Hm_eq.
    split; eauto.
    intros.
    destruct (peq t t') eqn:?; subst.
    {
      introv Hin; destruct Hin as [ofs Hin].
      rewrite Hm_eq in H5.
      eapply unbuffer_safe_block_not_alloc_and_invb_not_in_buffer; eauto.
      rewrite Hnextblock_eq; eauto.
    }
    {
      introv Hin.
      rewrite <- Hnextblock_eq in Hin.
      destruct Hin as [ofs Hin]. 
      eapply unbuffer_safe_block_not_alloc_and_invb_not_in_buffer; eauto.
    }
    rewrite <- Hnextblock_eq; eauto.
  }

  split.
  (* G *)
  unfold Gobj.
  do 3 right; eauto.
 
  (* match state *)
  split.
  eapply obj_unlock_match; eauto.
  eapply unlock_label_match; eauto.
  subst rs0.
  Pregmap_elim.
  eauto.
  clear - Himp_init Hfind_symb.
  inversion Himp_init; subst.
  specialize (H2 lock_release_ident).
  inversion H2; subst.
  eapply H5 in H10.
  clear - H9 H10 Hfind_symb.
  simpls.
  rewrite Hfind_symb in H9.
  inversion H9; subst; eauto.
  unfold Genv.find_funct_ptr.
  unfold Genv.find_def.
  rewrite <- H10.
  eauto.

  split.
  clear - Hno_conflict H5 H8 Hmem_alloc Hm_eq HGalloc.
  unfolds tm_alloc_not_fl; simpls.
  intros.
  rewrite tupdate_not_eq_get in H0; eauto.
  clear - Hrel_tm_gm_vb Hm_eq Hmem_alloc Hnextblock_eq HGalloc.
  unfolds rel_tm_gm_vb; simpls.
  split.
  intros.
  rewrite tupdate_b_get in H0; eauto.
  eapply apply_buffer_split in H0.
  destruct H0 as [gm' [Happly_buf1 Happly_buf2]].
  rewrite Hm_eq in Happly_buf1.
  eapply Hrel_tm_gm_vb in H; eauto.
  eapply Mem.alloc_validblocks in Hmem_alloc; subst.
  rewrite Hmem_alloc.
  split; intros.
  {
    simpls.
    inv Happly_buf2; simpls.
    destruct H0; subst; eauto.
    right; eapply H; eauto.
  }
  {
    simpls.
    inv Happly_buf2; simpls.
    destruct H0; subst; eauto.
    right; eapply H; eauto.
  }
  
  eapply obj_alloc_fp.
  intros.
  unfolds tsoalloc_fp, uncheck_alloc_fp, store_args_fp, FP.locs, FP.union; simpls.
  unfolds G_alloc; simpls.
  destruct HGalloc as (b' & HGalloc).
  split_and HGalloc.
  assert (b' = Mem.nextblock fsm).
  {
    clear - H1 Hmem_alloc.
    Transparent Mem.alloc.
    unfolds Mem.alloc, alloc.
    inv H1; inv Hmem_alloc; simpls.
    inv H3; eauto.
  }
  subst.
  unfolds Locs.belongsto, Locs.union; simpls.
  ex_match2; subst; try rewrite Hnextblock_eq.
  split; eauto.
  split.
  clear - Hmem_alloc.
  unfolds Mem.alloc; inv Hmem_alloc; unfold strip; simpls.
  unfold GMem.valid_block; simpl; eauto.
  clear - H4 H1.
  intros.
  unfolds alloc; inv H1; subst.
  right.
  destruct fsm; simpls.
  unfolds unused_mem, Mem.nextblock; simpls.
  rewrite H2.
  rewrite PMap.gss; eauto.
  ex_match2.
  destruct (zle 0 ofs') eqn:?; destruct (zlt ofs' 0) eqn:?; tryfalse; simpls.
  omega.
Qed.

(** [match_tau] holds in function unlock *)
Lemma unlock_step_satisfy_Gobj :
  forall sge sG tge t sc sm tc tc' tm tm' b' gm' fp fl
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                             (InteractionSemantics.V SpecLang.speclang) sge tge)
    (Htsostep : tsostep tge fl tc (tso_buffers tm t, memory tm) fp tc'
                        (b', gm'))
    (Hno_conflict : 
      forall t' blk n lo hi,
         t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
         blk <> get_block fl n
    )
    (Hrel_tm_gm_vb : rel_tm_gm_vb sm tm fl t)
    (Hlock_rel_match_state : unlock_match_state sge tge t (sc, sm) (tc, tm))
    (Htm : tm' = (mktsomem (tupdate t b' (tso_buffers tm)) gm')),
    (exists FP sc' sm',
        InteractionSemantics.star
          (InteractionSemantics.step SpecLang.speclang sG fl) sc sm FP sc' sm' /\
        (
          (Gobj tge t sm tm sm' tm' /\
           obj_match_state sge tge t (sc', sm') (tc', tm') /\
           tm_alloc_not_fl tm' fl t /\ rel_tm_gm_vb sm' tm' fl t /\
           obj_fp sm sm' fp)
          \/
          (* abort after star step *)
          (* abort after star step *)
          ((forall FP' sc'' sm'', ~ InteractionSemantics.step SpecLang.speclang sG fl
                               sc' sm' FP' sc'' sm'')
           /\ InteractionSemantics.at_external SpecLang.speclang sG sc' = None
           /\ (forall ores, InteractionSemantics.after_external SpecLang.speclang sc' ores
                      = None)
           /\ InteractionSemantics.halt SpecLang.speclang sc' = None)
        )
    )
    \/
    (* atomic block *)
    (exists FP1 sc_ent sm1 sc_ent' FP2 sc_ext sm' sc',
        (* star step *)
        InteractionSemantics.star
          (InteractionSemantics.step SpecLang.speclang sG fl) sc sm FP1 sc_ent sm1 /\
        (* ent atom *)
        InteractionSemantics.at_external SpecLang.speclang sG sc_ent =
        Some (ent_atom, ent_atom_sg, nil) /\
        InteractionSemantics.after_external SpecLang.speclang sc_ent None =
        Some sc_ent' /\
        (* star step *)
        InteractionSemantics.star
          (InteractionSemantics.step SpecLang.speclang sG fl)
          sc_ent' sm1 FP2 sc_ext sm' /\
        
        (
          ( (* ext atom and match *)
            InteractionSemantics.at_external SpecLang.speclang sG sc_ext =
            Some (ext_atom, ext_atom_sg, nil) /\
            InteractionSemantics.after_external SpecLang.speclang sc_ext None =
            Some sc' /\
            Gobj tge t sm tm sm' tm' /\
            obj_match_state sge tge t (sc', sm') (tc', tm') /\
            tm_alloc_not_fl tm' fl t /\ rel_tm_gm_vb sm' tm' fl t /\
            obj_fp sm sm' fp
          )
          \/
          ( (* abort inside atomic block *)
            (forall FP' sc' sm'',
                ~ InteractionSemantics.step SpecLang.speclang
                  sG fl sc_ext sm' FP' sc' sm'')
            /\ InteractionSemantics.at_external SpecLang.speclang sG sc_ext
              = None
                  /\ (forall ores, InteractionSemantics.after_external
                               SpecLang.speclang sc_ext ores = None)
                  /\ InteractionSemantics.halt SpecLang.speclang sc_ext = None
          )
        )
    ).
Proof.
  Ltac interaction_sem_exec :=
    eapply InteractionSemantics.star_step;
    [try econstructor; eauto; try econstructor; eauto;
     try econstructor; eauto | idtac].
  Ltac solve_mem_strip :=
    try rewrite tupdate_same_eq; eauto;
    match goal with
    | H : embed (memory ?tm) _ _ |- _ => inv H
    end;
    match goal with
    | H : strip _ = memory _ |- _ => rewrite H; eauto
    end. 
  
  intros. 
  inversion Hlock_rel_match_state; subst.
  {
    (** init step match  *)
    left.
    eapply unlock_init_step_satify_Gobj; eauto.
  }
  {
    (** lock release : unlock label *)
    left.
    do 3 eexists.
    split. 
    eapply InteractionSemantics.star_refl; eauto.
    left.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst; clear H
    end.
 
    ptr_elim.
    exec_instr_tso.
    simpl.
    
    split. 

    (* G *)
    unfold Gobj.
    right. right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.

    (* match_state *)
    split.
    erewrite tm_unchange; eauto.
    eapply obj_unlock_match.
    eapply get_lock_addr_match; eauto.
    elim_next_intr'.
    
    split; solve_mem_strip. split; eauto.
    econstructor; eauto.
    external_call_elim.
  }
  {
    (** lock release : mov $L R8 *)
    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl; eauto.
    left.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst; clear H
    end.
    ptr_elim.
    clear_trivial_eq.
    exec_instr_tso.
    simpl.

    split.

    (* G *)
    unfold Gobj.
    right; right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.
 
    (* match state *)
    split.
    lets H_lock_addr : get_lock_ident_from_ge ___; eauto.
    destruct H_lock_addr as [L H_lock_addr].
    erewrite tm_unchange; eauto.
    eapply obj_unlock_match.
    eapply mov_one_match; eauto. 
    elim_next_intr.
    unfold nextinstr_nf, nextinstr.
    simpl.
    Pregmap_elim.
    clear - H_lock_addr.
    unfold Genv.symbol_address.
    rewrite H_lock_addr.
    eauto.
    split; solve_mem_strip. split; eauto.
    econstructor; eauto.
    external_call_elim.
  }
  {
    (** lock release : mov 1 R9 *)
    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl; eauto.
    left.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst; clear H
    end.
    ptr_elim.
    clear_trivial_eq.
    exec_instr_tso.
    simpl.

    split.

    (* G *)
    unfold Gobj.
    right; right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.

    (* match state *)
    split.
    eapply obj_unlock_match.
    eapply unlock_step_match; eauto.
    elim_next_intr. 
    solve_m_unchange_objinv1 tm.
    split; solve_mem_strip. split; eauto.
    econstructor; eauto.
    external_call_elim.
  }
  {
    (** lock release : mov R9 [R8] *)
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst; clear H
    end; try solve [external_call_elim].
    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H1 : embed _ _ _,
           H2 : exec_instr_TSO _ _ _ _ _ = _,
                H3 : rs (IR RCX) = _ |- _ =>
      renames H1 to Hembed, H2 to Hexec_instr_tso, H3 to HR8
    end.

    (** lets Hunbuffer_safe : lock_rel_unbuffer_safe ___; eauto.*) 
    lets Hspec_embed : (Classical_Prop.classic (exists fsm, embed sm fl fsm)).
    destruct Hspec_embed as [Hspec_embed_ex | Hspec_embed_nex].
    {
      destruct Hspec_embed_ex as [fsm Hspec_embed_ex].
      unfolds exec_instr_TSO, exec_store_TSO.
      unfolds eval_addrmode.
      destruct Archi.ptr64 eqn:?; tryfalse.
      simpl in Hexec_instr_tso.
      rewrite HR8 in Hexec_instr_tso.
      simpl in Hexec_instr_tso.
      rewrite Heqb in Hexec_instr_tso.
      assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                              (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                   = Ptrofs.repr 0).
      eauto.
      rewrite Ht in Hexec_instr_tso.
      match goal with
      | H : obj_inv _ _ _ |- _ => rename H into Hobj_inv
      end.
      match goal with
      | H : obj_inv _ _ _ |- _ => rename H into Hobj_inv
      end.
      lets Hobj_inv' : Hobj_inv.
      unfold obj_inv in Hobj_inv.
      destruct Hobj_inv as [L' [Hfind_symb' [Hst [Hstore Hstore_tsom]]]].
      destruct Hst as [Hst | Hst].
      { 
        unfolds lock_st.
        destruct Hst as [Hload_specm [Hnot_in Hload_tsomem]].
        right.
        inversion Hspec_embed_ex; subst.
        assert (sG = sge).
        {
          inversion Hspec_init; subst; eauto.
        }
        subst sG.
        lets H_L_addr : ogenv_match_L_addr_eq ___; eauto.
        destruct H_L_addr as [L'' [H_L_tsoaddr H_L_spec]].
        match goal with
        | H : _ = Genv.find_symbol _ lock_L_ident |- _ =>
          rewrite H_L_tsoaddr in H; inversion H; subst L''
        end.
        rewrite Hfind_symb' in H_L_tsoaddr.
        inversion H_L_tsoaddr; subst L'.
        clear_trivial_eq.
        specialize (Hstore Int.one).
        destruct Hstore as [M' Hstore].
        lets Hstore_spec_m : store_gm_store_spec_m ___; eauto.
        destruct Hstore_spec_m as [fsm' [Hstore_spec_m Hembed1]].
        do 8 eexists.
        unfold unlock_spec_fn.
 
        (* spec program execute *)
        split.
        spec_p_exec.
        
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto.
        eapply SpecLang.EntAtomstep; eauto.
        econstructor; eauto.

        split.
        (* At EntAtom *)
        eauto.

        split.
        (* After EntAtom *)
        simpl; eauto.

        split.  
        (* seq *)
        interaction_sem_exec.

        (* load *)
        interaction_sem_exec.
        eapply load_gm_load_spec_m; eauto.
        instantiate (1 := (fun r' : positive =>
                             if peq r' r then Vint Int.zero else te r')).
        eauto.

        (* skip *)
        interaction_sem_exec.

        (* seq *)
        interaction_sem_exec.

        (* assgin *)
        interaction_sem_exec.
        instantiate (1 := (fun r' : positive =>
                             if peq r' x then Vint Int.one
                             else if peq r' r then Vint Int.zero else te r')).
        eauto.

        (* skip *)
        interaction_sem_exec.

        (* seq *)
        interaction_sem_exec.

        (* assert (r == 0) *)
        interaction_sem_exec.
        econstructor; eauto.

        (* skip *)
        interaction_sem_exec.

        (* store x L *)
        interaction_sem_exec.
        destruct (peq x x) eqn:?; tryfalse.

        eapply InteractionSemantics.star_step.
        econstructor; eauto.
        inversion Hembed1; subst; eauto. 
        eapply SpecLang.ExtAtomstep; eauto.
        econstructor; eauto.

        left.
        (* At ExtAtom *)
        split.
        simpl; eauto.

        (* After ExtAtom *)
        split.
        simpl; eauto.

        match goal with
        | H : rs (IR RDX) = _ |- _ => rename H into HR9
        end.

        rewrite HR9 in Hexec_instr_tso.
        destruct
          (tsostorev Mint32
                        {| tbuffer := tso_buffers tm t; fmemory := fm |}
                        (Vptr L (Ptrofs.repr 0)) (Vint Int.one)) eqn:Hstore_tso;
          tryfalse.
        inversion Hexec_instr_tso; subst. 
        clear_trivial_eq.

        assert (Hobj_inv'' : obj_inv tge (strip fsm')
                             {|
                               tso_buffers := tupdate t (tbuffer tsofm')
                                                      (tso_buffers tm);
                               memory := strip (fmemory tsofm') |}).
        { 
          unfold obj_inv.
          exists L.
          split; eauto.
          split.
          right.
          unfold unlock_st.
          simpl.
          split.
          eapply store_v_load_eq_spec_m in Hstore_spec_m; eauto.
          inversion Hembed1; subst.
          eapply load_spec_m_load_gm; eauto.
          left.
          eexists t, (tso_buffers tm t), nil.          
          split. 
          clear - Hstore_tso Hnot_in Hembed.
          inv Hembed.
          unfolds tsostorev, tsostore, buffer_insert; simpls.
          inv Hstore_tso; simpls.
          rewrite tupdate_b_get; eauto.
          split.
          clear - Hnot_in Hstore_tso.
          introv Htid_neq.
          unfolds tsostorev, tsostore, buffer_insert; simpls.
          inv Hstore_tso; simpls.
          rewrite tupdate_not_eq_get; eauto.
          specialize (Hnot_in t').
          intros H_in_buffer.
          contradiction Hnot_in.
          eauto.
          split.
          rewrite app_nil_r.
          clear - Hnot_in.
          intros; intro H_in_buffer.
          specialize (Hnot_in t).
          contradiction Hnot_in.
          eauto.
          unfolds load_tsomem.
          destruct tm.
          simpls TSOMem.tso_buffers.
          eapply tso_store_not_imm ; eauto.
          clear - Hload_tsomem Hembed.
          simpls.
          inversion Hembed; subst; eauto.
          split.  
          clear - Hstore Hembed1 Hstore_tsom.
          inversion Hembed1; subst.
          intros. 
          eapply gm_store_succ_store_again; eauto. 
          split. 
          clear - Hstore_tso Hembed1 Hstore_tsom Hembed.
          intros.
          destruct Hstore_tsom as [Hstore_tsom [Hunbuffer Hobj_mem]].
          specialize (Hstore_tsom n).
          destruct Hstore_tsom as [tm' Hstore_tsom].
          unfolds tsostorev.
          unfolds tsostore.
          inversion Hstore_tso; subst; eauto.
          simpls.
          destruct tm.
          simpls. 
          inversion Hembed; subst; eauto.
          destruct (store Mint32 (strip fm) L 0 (Vint n)) eqn:Hstore; tryfalse.
          eauto.
          split.
          destruct Hstore_tsom as [Hstore_tsom Hother].
          specialize (Hstore_tsom Int.zero).
          eapply unbuffer_safe_storev_still with (v' := Vint Int.zero); eauto.
          clear - Hstore_tsom.
          destruct Hstore_tsom as [bm' Hstore_tsom].
          unfolds store_tsomem.
          destruct tm; simpls.
          ex_match2; eauto.
          split_and Hother; eauto.
          split.
          intros.   
          destruct Hstore_tsom as [Hstore_tsom [Hunbuffer_safe' [Hobj_mem Hperm]]].
          eapply speclang_store_impl_obj_mem with (n := Int.one); eauto.
          simpl.  
          clear - Hstore_tsom Hstore_tso Hfind_symb' Hembed Hstore_spec_m.
          split_and Hstore_tsom.
          renames H2 to Hperm.
          split.
          introv Hrange.
          eapply Hperm in Hrange.
          unfolds tsostorev.
          unfolds tsostore.
          simpls.
          inversion Hstore_tso; subst.
          simpl.
          destruct tm.
          simpls.
          inversion Hembed; subst; eauto.
          introv Hrange.
          eapply H4 with (ofs := ofs) (k := k) (p := p) in Hrange.
          destruct Hrange as [Hrange Hrange1].
          split.
          intro.
          eapply Hrange.
          clear - Hstore_spec_m H2.
          unfolds GMem.perm, Memperm.perm_order'.
          try rewrite <- Mem_GMem_access_eq in *.
          destruct ((Mem.mem_access fsm') !! L ofs k) eqn:?; simpls; tryfalse.
          eapply speclang_not_change_perm in Hstore_spec_m.
          rewrite Hstore_spec_m.
          rewrite Heqo; eauto.
          intro.
          contradiction Hrange1.
          unfolds tsostorev, tsostore.
          inv Hstore_tso; simpls.
          inv Hembed.
          rewrite <- H5; eauto.
        }

        split.
        unfold Gobj.
        right; left.
        unfold G_unlock. 
        
        exists L.
        split; eauto.
        split; eauto.
        split.
        eauto.

        (* unlock succ *)
        unfold unlock_succ.
        split.
        eauto.
        split.
        eapply SpecLang_store_store_gm; eauto.
        clear - Hembed Hstore_tso.
        destruct tm.
        simpls.
        eapply tsostorev_append_bf; eauto.
 
        (* match state *)
        split. eapply obj_unlock_match.
        eapply unlock_set_ret_val_match; eauto.
        elim_next_intr.

        inv Hembed; inv Hembed1.
        clear - Hrel_tm_gm_vb Hno_conflict Hstore_tso Hstore_spec_m H0 HR8 Hobj_inv' Hfind_symb' H_L_spec.
        unfolds tsostorev, tsostore; inv Hstore_tso; simpls.
        split.
        unfolds tm_alloc_not_fl; eauto; simpls.
        introv Htid_neq Hin_buf.
        rewrite tupdate_not_eq_get in Hin_buf; eauto.
        unfolds rel_tm_gm_vb; simpls.
        rewrite tupdate_b_get; eauto.
        split.
        introv Hget_block Happly_buffer.
        eapply apply_buffer_split in Happly_buffer.
        destruct Happly_buffer as [gm'' [Happly_buf1 Happly_buf2]].
        rewrite H0 in Happly_buf1; eapply Hrel_tm_gm_vb in Happly_buf1; eauto.
        simpls.
        destruct (store Mint32 gm'' L (Ptrofs.unsigned (Ptrofs.repr 0))) eqn:Hstore;
          simpls; tryfalse.
        inv Happly_buf2.
        eapply store_vb_eq in Hstore.
        rewrite Hstore in Happly_buf1.
        eapply speclang_store_vb_eq in Hstore_spec_m.
        rewrite <- Hstore_spec_m.
        split; intro Hin_vb; eauto; eapply Happly_buf1; eauto.

        unfold exec_store_fp, storev_fp, eval_addrmode.
        destruct Archi.ptr64 eqn:?; tryfalse.
        unfold eval_addrmode32, store_fp.
        change (Val.add (Vint Int.zero) (Vint (Int.repr 0))) with Vzero.
        rewrite HR8; simpl.
        rewrite Heqb.
        change (Ptrofs.unsigned
                      (Ptrofs.add (Ptrofs.repr 0)
                                  (Ptrofs.of_int Int.zero))) with 0%Z.
        unfold range_locset; simpl.
        eapply obj_valid_block_fp; eauto.
        unfold Locs.belongsto, FP.locs, Locs.union; simpl.
        intros; left.
        ex_match2; subst.
        destruct (zle 0 ofs); destruct (zlt ofs 4); simpls; tryfalse.
        unfolds obj_inv.
        destruct Hobj_inv' as (L' & HL' & Hobj_inv').
        split_and Hobj_inv'.
        rewrite Hfind_symb' in HL'; inv HL'; subst.
        eapply H5; eauto.
      }
      {
        unfolds unlock_st. 
        destruct Hst as [Hload_spec_m Hst].
        lets H_L_addr_eq : ogenv_match_L_addr_eq ___; eauto.
        destruct H_L_addr_eq as [L'' [H_L_addr_tso H_L_addr_spec]].
        rewrite Hfind_symb' in H_L_addr_tso.
        inversion H_L_addr_tso; subst L''.
        right. 
        assert (sge = sG).
        {
          inversion Hspec_init; subst; eauto.
        }
        subst sG.
        do 8 eexists.
        split.
        spec_p_exec. 
        eapply InteractionSemantics.star_step.
        econstructor; eauto.
        inversion Hspec_embed_ex; subst; eauto.
        unfold unlock_spec_fn.
        eapply SpecLang.EntAtomstep; eauto.
        econstructor; eauto.
        split.

        (* At EntAtom *)
        eauto.

        (* After EntAtom *)
        split.
        simpl.
        eauto.

        (* Seq *)
        split.
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto.
        inversion Hspec_embed_ex; subst; eauto.
        eapply SpecLang.Atomstep; eauto.
        econstructor; eauto.

        (* load *)
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto.
        inversion Hspec_embed_ex; subst; eauto.
        eapply SpecLang.Atomstep; eauto.
        econstructor; eauto.
        instantiate (1 := Vint Int.one).
        eapply load_gm_load_spec_m; eauto.
        instantiate (1 :=
                       (fun r' : positive => if peq r' r then Vint Int.one else te r')).
        eauto.

        (* skip *)
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto.
        inversion Hspec_embed_ex; subst; eauto.
        econstructor; eauto.
        econstructor; eauto.

        (* assgin *)
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto. 
        inversion Hspec_embed_ex; subst; eauto.
        econstructor; eauto.
        econstructor; eauto.

        (* seq *)
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto.
        inversion Hspec_embed_ex; subst; eauto.
        econstructor; eauto.
        econstructor; eauto.
        instantiate (1 := (fun r' : positive =>
                             if peq r' x then Vint Int.one
                             else if peq r' r then Vint Int.one else te r')).
        eauto.

        (* skip *)
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto.
        inversion Hspec_embed_ex; subst; eauto.
        econstructor; eauto.
        econstructor; eauto.

        (* seq *) 
        eapply InteractionSemantics.star_step; eauto.
        econstructor; eauto.
        inversion Hspec_embed_ex; subst; eauto.
        econstructor; eauto.
        econstructor; eauto.

        econstructor; eauto.

        right.

        (* abort step *)
        split.
        introv Hstep_abort.
        inversion Hstep_abort; subst.
        match goal with
        | H : SpecLang.fstep _ _ _ _ _ _ |- _ =>
          inversion H; subst
        end.
        match goal with
        | H : SpecLang.normalstep _ _ _ _ _ _ _ _ _ _ |- _ =>
          inversion H; subst
        end.
        match goal with
        | H : SpecLang.eval_bexpr _ _ _ |- _ =>
          clear - H; inversion H; subst
        end.
        destruct (peq r x) eqn:?; tryfalse.

        (* not at external *)
        split.
        eauto.

        (* not after external *)
        split.
        intro.
        eauto.

        (* not halt *)
        eauto.
      }
    }
    {
      left.
      do 3 eexists.
      split.
      eapply InteractionSemantics.star_refl.
      right.  
      clear - Hspec_embed_nex Hspec_init.
      split. 
      introv Hstep.  
      inversion Hspec_init; subst.
      inversion Hstep; subst. 
      match goal with
      | H : SpecLang.fstep _ _ _ _ _ _ |- _ =>
        inversion H; subst
      end. 
      eapply Hspec_embed_nex; eauto.
      split; simpl; eauto.
    }
  }
  {
    (** lock release : movl $0 RAX *)
    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl; eauto.
    left.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst; clear H
    end.
    ptr_elim.
    clear_trivial_eq.
    exec_instr_tso.
    simpl.
 
    split.

    (* G *)
    unfold Gobj.
    right; right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.

    (* match state *)
    split.
    eapply obj_unlock_match.
    eapply unlock_retl_match; eauto.
    elim_next_intr.
    solve_m_unchange_objinv1 tm.
    split; solve_mem_strip. split; eauto.
    econstructor; eauto.
    external_call_elim.
  }
  {
    (** lock release : retl *)
    lets Hspec_embed : (Classical_Prop.classic (exists fsm, embed sm fl fsm)).
    destruct Hspec_embed as [Hspec_embed | Hspec_embed].
    {
      destruct Hspec_embed as [fsm Hspec_embed].
      left.
      do 3 eexists.
      split. 
      spec_p_exec. 
      eapply InteractionSemantics.star_refl; eauto.
      left.
      inversion Htsostep; subst.
      match goal with
      | H : tsofstep _ _ _ _ _ _ |- _ =>
        inversion H; try solve [ptr_elim]; subst; clear H
      end.
      ptr_elim.
      clear_trivial_eq.
      exec_instr_tso.
      simpl.
 
      split.

      (* G *)
      unfold Gobj.
      right; right.
      erewrite tm_unchange; eauto.
      unfold Id; eauto.
      inversion Hspec_embed; subst; eauto.

      (* match state *)
      split.
      eapply obj_unlock_match.
      eapply unlock_halt_match; eauto.
      Pregmap_elim.
      inversion Hspec_embed.
      solve_m_unchange_objinv1 tm. 
      split; solve_mem_strip.
      split; inv Hspec_embed; eauto.
      econstructor; eauto.
      external_call_elim.
    }
    {
      left.
      do 3 eexists.
      split.
      eapply InteractionSemantics.star_refl; eauto.
      right.
      split.
      introv Hstep. 
      inversion Hstep; subst.
      eapply Hspec_embed; eauto.
      split; eauto.
    }
  }
  {
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst; clear H
    end; ret_zero_ptr_false.
  }

  Unshelve.
  simpl.
  exact (SpecLang.CallStateIn SpecLang.Sskip).
Qed.

(** [match_tau_obj_mem_fp] holds in function unlock. *)
Lemma unlock_footprint_case :
  forall sge sG tge sc tm gm t b fp tc tc' b' gm' sm ofs fl b0
         (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                      lock_comp_unit sge sG)
         (Himp_init : init_genv lock_comp_tso_unit tge)
         (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                                  (InteractionSemantics.V SpecLang.speclang)
                                  sge tge)
         (Hunlock_match_state : unlock_match_state sge tge t (sc, sm) (tc, tm))
         (Hbf : tso_buffers tm t = b)
         (Hmem : memory tm = gm)
         (Hstep : tsostep tge fl tc (b, gm) fp tc' (b', gm'))
         (Hlocs_belongsto : Locs.belongsto (FP.locs fp) b0 ofs),
    obj_mem sm b0 ofs \/ (exists n, get_block fl n = b0).
Proof.
  intros.
  unfolds Locs.belongsto.
  inversion Hunlock_match_state; subst;
    try solve
        [
          inversion Hstep; subst;
          match goal with
          | H : context [tsofstep] |- _ =>
            inversion H; try solve [ptr_elim]; subst
          end; try external_call_elim;
          ptr_elim; simpl in Hlocs_belongsto;
          inversion Hlocs_belongsto; eauto
        ].
  {
    lets Htso_core : tso_lock_release_init_state ___; eauto.
    destruct Htso_core as [fb [Hfind_symb Htso_core]].
    simpl in Htso_core.
    unfolds fundef_init.
    simpl in Htso_core.
    inversion Htso_core; subst; eauto.
    inversion Hstep; subst; eauto.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.
    match goal with
    | H1 : args_len_rec _ _ = _,
           H2 : obj_inv _ _ _, H3 : embed _ _ _, H4 : tsoalloc _ _ _ _ |- _ =>
      renames H1 to Hargs_len_rec, H2 to Hobj_inv, H3 to Hembed, H4 to Htsoalloc
    end.  
    clear - Hlocs_belongsto Hargs_len_rec Hobj_inv Hembed Htsoalloc.
    inversion Htsoalloc; subst; clear Htsoalloc.
    simpls.  
    inversion Hargs_len_rec; subst; eauto.
    unfolds store_args_fp.
    simpls.
    rewrite FP.fp_union_emp in Hlocs_belongsto.
    unfolds uncheck_alloc_fp.
    unfolds FP.locs.
    simpls.
    unfolds Locs.union.
    simpls.
    inversion Hembed; subst.
    right.
    dis_if_else; subst.
    unfold Mem.nextblock.
    eauto.
    inv H6.
    rewrite H1; eauto.
  }
  {
    inversion Hstep; subst; eauto.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.
    renames H6 to H_L_addr, H8 to H_L_addr_get, H9 to H_rel, H14 to Hobj_inv.
    clear - H_L_addr H_L_addr_get H_rel Hlocs_belongsto Hobj_inv.
    unfolds exec_instr_TSO_fp.
    unfolds exec_store_fp.
    unfolds eval_addrmode.
    destruct Archi.ptr64 eqn:?; tryfalse.
    simpls.
    assert (Ht : Int.add Int.zero (Int.repr 0) = Int.repr 0).
    eauto.
    rewrite Ht in Hlocs_belongsto.
    rewrite H_L_addr in Hlocs_belongsto.
    simpls.
    rewrite Heqb in Hlocs_belongsto.
    simpls.
    assert (Ht1 : Ptrofs.add (Ptrofs.repr 0)
                               (Ptrofs.of_int (Int.repr 0))
                  = Ptrofs.repr 0); eauto.
    rewrite Ht1 in Hlocs_belongsto.
    assert (Ht2 : Ptrofs.unsigned (Ptrofs.repr 0) = 0%Z).
    eauto.
    rewrite Ht2 in Hlocs_belongsto.
    unfolds store_fp, FP.locs.
    simpls.
    unfolds Locs.union, range_locset.
    simpls.
    destruct (eq_block L b0) eqn:?; tryfalse.
    subst.
    destruct (zle 0 ofs) eqn:?;
             destruct (zlt ofs 4) eqn:?; tryfalse.
    unfolds obj_inv.
    destruct Hobj_inv as [L' [Hfind_symb' Hobj_inv]].
    rewrite Hfind_symb' in H_L_addr_get.
    inversion H_L_addr_get; subst.
    split_and Hobj_inv.
    eauto.
  }
  { 
    inversion Hstep; subst; eauto.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim; ret_zero_ptr_false.
  }
Qed.

(** [match_rely] holds in function unlock. *)
Lemma lock_release_rely :
  forall t sc sm sm' tc tm tm' sge sG tge
    (Hspec_init : InteractionSemantics.init_genv
                    SpecLang.speclang lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hunlock_match : unlock_match_state sge tge t (sc, sm) (tc, tm))
    (Hrely_step : Robj tge t sm tm sm' tm'),
    unlock_match_state sge tge t (sc, sm') (tc, tm').
Proof.
  intros.
  eapply R_impl_I_I in Hrely_step; eauto.
  destruct Hrely_step.
  inversion Hunlock_match; subst.

  eapply unlock_init_match; eauto.
  eapply unlock_label_match; eauto.
  eapply get_lock_addr_match; eauto.
  eapply mov_one_match; eauto.
  eapply unlock_step_match; eauto.
  eapply unlock_set_ret_val_match; eauto.
  eapply unlock_retl_match; eauto.
  eapply unlock_halt_match; eauto.
Qed.

(** [match_halt_noscstep] holds in function unlock. *)
Lemma lock_rel_not_abort :
  forall sge sG tge t sc sm tc tm fl fm gm
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hlock_rel_match_state : unlock_match_state sge tge t (sc, sm) (tc, tm))
    (Hbf_nil : tso_buffers tm t = nil)
    (Hgm : memory tm = gm)
    (Hstep : forall (fp : FP.t) (tc' : core) (b' : buffer) (gm' : gmem),
        ~ tsostep tge fl tc (nil, gm) fp tc' (b', gm'))
    (Hnot_halt : halt tc = None)
    (Hembed : embed gm fl fm),
    False.
Proof.
  intros. 
  inversion Hlock_rel_match_state; subst.
  {
    (** lock acquire : init *)
    lets Htc : tso_lock_release_init_state ___; eauto.
    destruct Htc as [fb [Hfind_symb Hfun_init]].
    simpl in Hfun_init.
    unfolds fundef_init.
    simpls.
    inversion Hfun_init; subst.
    clear_trivial_eq.
    lets Halloc : tsoalloc_bf_nil_succ_sz0 ___; eauto.
    destruct Halloc as [tm1 [stk Halloc]].
    eapply Hstep; eauto.
    trivial_not_abort.
    simpl.
    unfold store_args_fmem.
    simpl.
    eauto.
  }
  {
    (** lock acquire : unlock label *)
    eapply Hstep; trivial_not_abort.
  }
  {
    (** lock acquire : movl $L R8 *)
    eapply Hstep; trivial_not_abort.
  }
  {
    (** lock acquire : movl $1 R9 *)
    eapply Hstep; trivial_not_abort.
  }
  {
    (** lock acquire : movl R9 [R8] *)
    match goal with
    | H1 : obj_inv _ _ _, H2 : _ = Genv.find_symbol _ lock_L_ident,
      H3 : rs (IR RDX) = _, H4 : rs (IR RCX) = _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hfind_symb, H3 to HR9, H4 to HR8
    end.
    unfolds obj_inv.
    destruct Hobj_inv as
        [L' [Hfind_symb' [Hst [Hstore [Htso_store Hunbuffer_safe]]]]].
    destruct Hst as [Hst | Hst].
    {  
      unfolds lock_st.
      split_and Hst.
      destruct tm.
      inversion Hembed; subst.
      rewrite Hfind_symb' in Hfind_symb.
      inversion Hfind_symb; subst L'.
      specialize (Htso_store Int.one).
      destruct Htso_store as [bm' Htso_store].
      unfolds store_tsomem.
      destruct (store Mint32 memory L 0 (Vint Int.one)) eqn:Hstore_gm; tryfalse.
      lets Hstore_tso : store_gm_embed_store_tsofmem ___; eauto.
      destruct Hstore_tso as [tm' Hstore_tso].
      eapply Hstep.
      simpl.
      econstructor; eauto.
      econstructor; eauto.
      simpl; eauto.
      simpl.
      unfold exec_store_TSO.
      rewrite HR9. 
      unfold eval_addrmode. 
      destruct Archi.ptr64 eqn:?; tryfalse.
      simpl.
      rewrite HR8.
      simpl.
      rewrite Heqb0.
      assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                              (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                   = Ptrofs.repr 0); eauto.
      rewrite Ht. 
      simpl in Hembed.
      inversion Htso_store; subst.
      rewrite Hstore_tso.
      eauto.
    }
    {
      unfolds unlock_st.
      split_and Hst.
      match goal with
      | H : _ \/ _ |- _ => destruct H as [Hst | Hst]
      end.
      {
        destruct tm.
        inversion Hembed; subst.
        rewrite Hfind_symb' in Hfind_symb.
        inversion Hfind_symb; subst L'.
        simpl in Hst. 
        destruct Hst as [t' [bf1 [bf2 [Hin_bf [Hnot_in_obfs [Hcont_one Hload]]]]]].
        simpls; subst; simpls.
        destruct (Pos.eq_dec t t') eqn:Htid; try subst t'.
        {
          rewrite Hbf_nil in Hin_bf.
          destruct bf1; simpls; tryfalse.
        }
        {
          specialize (Htso_store Int.one).
          destruct Htso_store as [bm' Htso_store].
          unfolds store_tsomem.
          destruct (store Mint32 (strip fm) L 0 (Vint Int.one))
                   eqn:Hstore_gm; tryfalse.
          lets Hstore_tso : store_gm_embed_store_tsofmem ___; eauto.
          destruct Hstore_tso as [tm' Hstore_tso].
          eapply Hstep.
          simpl.
          econstructor; eauto.
          econstructor; eauto.
          simpl; eauto.
          simpl.
          unfold exec_store_TSO.
          rewrite HR9. 
          unfold eval_addrmode. 
          destruct Archi.ptr64 eqn:?; tryfalse.
          simpl.
          rewrite HR8.
          simpl.
          rewrite Heqb0.
          assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                                  (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                       = Ptrofs.repr 0); eauto.
          rewrite Ht. 
          simpl in Hembed.
          inversion Htso_store; subst.
          rewrite Hstore_tso.
          eauto.
        }
      }
      {
        destruct tm.
        inversion Hembed; subst.
        rewrite Hfind_symb' in Hfind_symb.
        inversion Hfind_symb; subst L'.
        specialize (Htso_store Int.one).
        destruct Htso_store as [bm' Htso_store].
        unfolds store_tsomem.
        destruct (store Mint32 memory L 0 (Vint Int.one)) eqn:Hstore_gm; tryfalse.
        lets Hstore_tso : store_gm_embed_store_tsofmem ___; eauto.
        destruct Hstore_tso as [tm' Hstore_tso].
        eapply Hstep.
        simpl.
        econstructor; eauto.
        econstructor; eauto.
        simpl; eauto.
        simpl.
        unfold exec_store_TSO.
        rewrite HR9. 
        unfold eval_addrmode. 
        destruct Archi.ptr64 eqn:?; tryfalse.
        simpl.
        rewrite HR8.
        simpl.
        rewrite Heqb0.
        assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                                (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                     = Ptrofs.repr 0); eauto.
        rewrite Ht. 
        simpl in Hembed.
        inversion Htso_store; subst.
        rewrite Hstore_tso.
        eauto.
      }
    }
  }
  {
    (** lock acquire : mov $0 RAX *)
    eapply Hstep; trivial_not_abort.
  }
  {
    (** lock acquire : retl *)
    eapply Hstep; trivial_not_abort.
  }
  {
    simpl in Hnot_halt.
    match goal with
    | H : rs PC = Vzero |- _ =>
      rewrite H in Hnot_halt; clear - Hnot_halt; simpls; tryfalse
    end.
  }
Qed.