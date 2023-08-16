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
Require Import InvRG.
Require Import TSOGlobSem.
Require Import AuxTacLemmas.
Require Import TSOMemLemmas MemLemmas.
Require Import LockAcqProof.
Require Import LockRelProof.
  
(** * Lemmas about object : [spin-lock] *)
Lemma ObjInit_inv : 
  forall sge sG tge sm tm gm
    (HSpecLang_init_genv : InteractionSemantics.init_genv SpecLang.speclang
                                                          lock_comp_unit sge sG)
    (Htso_init_genv : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                (InteractionSemantics.V SpecLang.speclang) sge tge)
    (HSpecLang_init_mem : InteractionSemantics.init_gmem SpecLang.speclang sge sm)
    (Htso_init_mem : init_mem tge gm)
    (Htso_init_gmem : tm = tsomem_init gm),
    obj_inv tge sm tm.
Proof.      
  intros. 
  unfold obj_inv. 
  inversion Htso_init_genv; subst.
  specialize (H2 lock_L_ident).
  inversion H2; subst.
  eapply H5 in H10; eauto.
  simpl in H10.
  clear H0 H1 H2 H3 H4 H5 H6 H.
  eexists. 
  split; eauto. 
  lets Haddr_eq : ogenv_match_L_addr_eq ___; eauto.
  destruct Haddr_eq as [L' [H_t_addr_L H_s_addr_L]].
  rewrite H_t_addr_L in H9.
  inversion H9; subst; eauto.
  lets Hspec_init_gm : spec_init_lock_one ___; eauto. 
  split. 
  right.
  unfold tsomem_init.
  unfold unlock_st.
  destruct Hspec_init_gm.
  split; eauto.
  right.
  simpl. 
  split; eauto.   
  
  clear - Htso_init_mem H_t_addr_L H10.
  unfolds init_mem.
  unfolds init_gmem_generic. 
  destruct Htso_init_mem as [fm [Hstrip Hinit_gm]]; subst.
  inversion Hinit_gm.
  unfolds globals_initialized_fmem. 
  unfolds Genv.find_def.
  symmetry in H10.
  eapply globdef_initialized_fm in H10; eauto.
  simpl in H10.
  split_and H10.
  destruct H0.
  eauto.
  eapply load_fm_eq_load_gm in H0; eauto.
  intros.
  intros H_in_buffer.
  inv H_in_buffer.
  simpls; tryfalse.
         
  destruct Hspec_init_gm.
  split; eauto.
  split.

  clear - Htso_init_mem H_t_addr_L H10.
  unfolds init_mem.
  unfolds init_gmem_generic. 
  destruct Htso_init_mem as [fm [Hstrip Hinit_gm]]; subst.
  inversion Hinit_gm.
  unfolds globals_initialized_fmem.
  unfolds Genv.find_def.
  symmetry in H10.
  eapply globdef_initialized_fm in H10; eauto.
  simpl in H10.
  split_and H10.
  intros.
  unfold store_tsomem.
  unfolds tsomem_init.
  lets Ht : perm_w_store ___; eauto.
  destruct Ht as [gm Ht].
  rewrite Ht.
  eauto.

  split.
  unfolds tsomem_init.
  econstructor; simpls.
  intros; tryfalse.
  intros; tryfalse.

  split.
  simpl.
  intros. 
  eapply spec_init_obj_mem; eauto.
  
  split; intros.  
  unfolds init_mem.
  unfolds init_gmem_generic.
  destruct Htso_init_mem as [fm [Hstrip Hinit_fm]].
  inversion Hinit_fm.
  unfolds globals_initialized_fmem.
  unfolds Genv.find_def.
  unfolds Genv.find_symbol.
  symmetry in H10.
  eapply globdef_initialized_fm in H10.
  simpl in H10. 
  split_and H10.
  simpl.
  rewrite <- Hstrip.
  unfold strip.
  simpl.
  clear - H2 H1.
  lets Hrange : H1.
  eapply H2 in H1. 
  unfold Mem.perm in H1.
  lets Ht : Mem_range_perm_cur_max ___; eauto.
  clear - H2 Ht Hrange.
  unfolds Mem.range_perm.
  lets Ht1 : H2 Hrange.
  lets Ht2 : Ht Hrange.
  clear - Ht1 Ht2.
  unfolds Mem.perm.
  unfolds Mem.perm_order'.  
  destruct ((Mem.mem_access fm) !! L' ofs Memperm.Cur) eqn:?; tryfalse.
  destruct ((Mem.mem_access fm) !! L' ofs Memperm.Max) eqn:?; tryfalse.
  eexists; eauto.

  lets Ht : H1.
  simpl in HSpecLang_init_mem.
  unfolds SpecLang.init_gmem.
  destruct HSpecLang_init_mem as [fm [Hstrip Hinit_sm]]; subst.
  inversion Hinit_sm; subst.
  unfolds SpecLang.globals_initialized_fmem_speclang.
  assert (Some lock_L = (Genv.genv_defs sge) ! L').
  {
    clear - H_s_addr_L HSpecLang_init_genv.
    inversion HSpecLang_init_genv; subst.
    inversion H0; subst; simpls.
    specialize (H3 lock_L_ident).
    inversion H3; subst.
    rewrite H_s_addr_L in H10.
    inversion H10; subst b'.
    eapply H6 in H11.
    simpl in H11; eauto.
  } 
  symmetry in H2.
  unfold Genv.find_def in globdef_initialized_fm.
  eapply globdef_initialized_fm in H2; eauto; simpl in H2.
  split_and H2.
  split.
  intro.
  rewrite gmem_perm_strip_mem_perm_eq in H6.
  eapply H4 in H6.
  split_and H6. 
  clear - H1 H6 H12.
  simpls.
  Lia.lia.

  clear - Htso_init_mem H_t_addr_L H10 Ht. 
  unfolds init_mem.
  unfolds init_gmem_generic. 
  destruct Htso_init_mem as [fm [Hstrip Hinit_gm]]; subst.
  inversion Hinit_gm.
  unfolds globals_initialized_fmem. 
  unfolds Genv.find_def.
  symmetry in H10.
  eapply globdef_initialized_fm in H10; eauto.
  simpl in H10.
  split_and H10.
  intro.
  unfolds tsomem_init.
  simpls.
  eapply H1 in H2.
  destruct H2; clear - H2 Ht.
  Lia.lia.
Qed.
  
Lemma id_eq_lock_unit :
    forall tge id args tc
      (Hinit_genv : init_genv lock_comp_tso_unit tge)
      (Hinit_core : init_core tge id args = Some tc),
      (id = lock_acquire_ident \/ id = lock_release_ident) /\ args = nil.
Proof. 
  intros.
  unfolds init_core.
  unfolds ASM_local.init_core.
  destruct (Genv.find_symbol tge id) eqn:Hfind_symbol; try discriminate.
  destruct (Genv.find_funct_ptr tge b) eqn:Hfptr; try discriminate.
  destruct f; try discriminate.
  inversion Hinit_genv.   
  revert H2 H3 H4 H5 Hfind_symbol Hfptr Hinit_core H1.
  clear. 
  intros.
  specialize (H2 id).
  inversion H2; subst; try discriminate.
  unfold Genv.find_symbol in H.
  unfold Genv.globalenv in H.
  simpl in H.
  destruct id; try simpl in H; 
  try destruct id; try simpl in H; try discriminate.
  destruct id; try simpl in H; try discriminate.
  destruct id; try simpl in H; try discriminate. 
  eapply H5 in H7. 
  inversion H; subst.
  rewrite Hfind_symbol in H6.
  inversion H6; subst.
  simpl in H7.
  eapply genv_defs_fun_find_fun_eq in Hfptr; eauto.
  inversion Hfptr; subst.
  clear - Hinit_core.
  unfolds fundef_init.
  simpls.
  unfolds wd_args.
  destruct (val_has_type_list_func args nil && vals_defined args &&
                   zlt (4 * (2 * Zlength args)) Int.max_unsigned) eqn : Hargs.
  symmetry in Hargs.
  eapply andb_true_eq in Hargs.
  destruct Hargs as [Hargs1 Hargs2].
  eapply andb_true_eq in Hargs1.
  destruct Hargs1 as [Hargs Hargs1].
  destruct args.
  eauto.
  simpl in Hargs.
  discriminate.
  discriminate.
  rewrite PTree.gleaf in H.
  discriminate.
  rewrite PTree.gleaf in H.
  discriminate.
  eapply H5 in H7.
  inversion H; subst.
  simpl in H7.
  rewrite Hfind_symbol in H6.
  inversion H6; subst.
  eapply genv_defs_fun_find_fun_eq in Hfptr; eauto.
  inversion Hfptr; subst.
  clear - Hinit_core.
  unfolds fundef_init.
  simpls.
  unfolds wd_args.
  destruct (val_has_type_list_func args nil && vals_defined args &&
                   zlt (4 * (2 * Zlength args)) Int.max_unsigned) eqn : Hargs.
  symmetry in Hargs.
  eapply andb_true_eq in Hargs.
  destruct Hargs as [Hargs1 Hargs2].
  eapply andb_true_eq in Hargs1.
  destruct Hargs1 as [Hargs Hargs1].
  destruct args.
  eauto. 
  simpl in Hargs.
  discriminate.
  discriminate.
  eapply H5 in H7.
  inversion H; subst.
  simpl in H7.
  rewrite Hfind_symbol in H6.
  inversion H6; subst.
  clear - Hfptr H7.
  unfolds Genv.find_funct_ptr.
  unfolds Genv.find_def.
  rewrite <- H7 in Hfptr.
  simpls.
  discriminate.
  rewrite Hfind_symbol in H7.
  discriminate.
Qed.

Lemma id_eq_lock_unit' :
    forall sge id sG args sc
      (Hinit_genv : InteractionSemantics.init_genv SpecLang.speclang
                                                          lock_comp_unit sge sG)
      (Hinit_core : InteractionSemantics.init_core
                         SpecLang.speclang sG id args = Some sc),
      (id = lock_acquire_ident \/ id = lock_release_ident) /\ args = nil.
Proof. 
  intros.
  simpls.
  unfolds SpecLang.init_core.
  unfolds generic_init_core.
  assert (sge = sG). 
  inversion Hinit_genv; subst; eauto. subst sG.
  destruct (Genv.find_symbol sge id) eqn:Hfind_symbol; try discriminate.
  destruct (Genv.find_funct_ptr sge b) eqn:Hfptr; try discriminate.
  destruct f; try discriminate.
  inversion Hinit_genv.
  inversion H0. 
  revert H3 H4 H5 H6 H7 Hfind_symbol Hfptr Hinit_core H2.
  clear. 
  intros.
  specialize (H4 id).
  inversion H4; subst; try discriminate.
  unfold Genv.find_symbol in H. 
  unfold Genv.globalenv in H.
  simpl in H.
  destruct id; try simpl in H; 
  try destruct id; try simpl in H; try discriminate.
  destruct id; try simpl in H; try discriminate.
  destruct id; try simpl in H; try discriminate.
  split; eauto.
  eapply H7 in H8.  
  inversion H; subst.
  rewrite Hfind_symbol in H1.
  inversion H1; subst.
  simpl in H8.
  unfolds SpecLang.F, SpecLang.V.
  rewrite Hfind_symbol in Hinit_core.
  unfolds Genv.find_funct_ptr.
  unfolds Genv.find_def.
  rewrite <- H8 in Hinit_core.
  simpls.
  destruct args; tryfalse.
  eauto.
  destruct id; simpls; tryfalse.
  destruct id; simpls; tryfalse.
  inversion H; subst.
  unfolds SpecLang.F, SpecLang.V.
  rewrite <- H1 in Hinit_core.
  unfolds Genv.find_funct_ptr.
  unfolds Genv.find_def.
  eapply H7 in H8.
  simpls.
  rewrite <- H8 in Hinit_core.
  simpls.
  destruct args; tryfalse; eauto.
  unfolds SpecLang.F, SpecLang.V.
  rewrite <- H1 in Hinit_core.
  unfolds Genv.find_funct_ptr.
  inversion H; subst.
  eapply H7 in H8.
  simpls.
  unfolds Genv.find_def.
  rewrite <- H8 in Hinit_core.
  simpls; tryfalse.
  rewrite Hfind_symbol in H8.
  tryfalse.
  unfolds SpecLang.F, SpecLang.V.
  rewrite Hfind_symbol in Hinit_core.
  rewrite Hfptr in Hinit_core.
  simpls.
  tryfalse.
  unfolds SpecLang.F, SpecLang.V.
  rewrite Hfind_symbol in Hinit_core.
  rewrite Hfptr in Hinit_core.
  tryfalse.
  unfolds SpecLang.F, SpecLang.V.
  rewrite Hfind_symbol in Hinit_core.
  tryfalse.
Qed. 
  
Lemma ObjInit_core_match :
      forall sge tge sG id args tc
        (HSpecLang_init_genv : InteractionSemantics.init_genv SpecLang.speclang
                                                              lock_comp_unit sge sG)
        (Htso_init_genv : init_genv lock_comp_tso_unit tge)
        (Htso_init_core : init_core tge id args = Some tc),
      exists sc,
        InteractionSemantics.init_core SpecLang.speclang sG id args = Some sc /\
        (forall (t0 : tid) (sm : gmem) (tm : tsomem),
            obj_inv tge sm tm -> obj_match_state sge tge t0 (sc, sm) (tc, tm)).
Proof.
  intros.
  assert (Hfid : (id = lock_acquire_ident \/ id = lock_release_ident) /\ args = nil).
  eapply id_eq_lock_unit; eauto.
  destruct Hfid as [Hfid Hargs].
  subst args.
  destruct Hfid; subst.
  {
    (** init_lock_acquire *)  
    assert (HSpecLang_init_core :
              exists sc,
                InteractionSemantics.init_core SpecLang.speclang
                                               sG lock_acquire_ident nil = Some sc).
    eapply lock_acquire_core_init_match; eauto.
    destruct HSpecLang_init_core as [sc HSpecLang_init_core].
    eexists.
    split; eauto.
    introv Hobj_inv.
    econstructor.
    eapply lock_init_match; eauto.
    inversion HSpecLang_init_genv.
    subst; eauto.
  }
  {
    (** init_lock_release *)
    assert (HSpecLang_init_core :
              exists sc,
                InteractionSemantics.init_core SpecLang.speclang
                                               sG lock_release_ident nil = Some sc).
    eapply lock_release_core_init_match; eauto.
    destruct HSpecLang_init_core as [sc HSpecLang_init_core].
    eexists.
    split; eauto.
    introv Hobj_inv.
    eapply obj_unlock_match.
    eapply unlock_init_match; eauto.
    inversion HSpecLang_init_genv.
    subst; eauto.
  }
Qed.

Lemma ObjInit_core_match' :
  forall sge tge sG id args sc
    (HSpecLang_init_genv : InteractionSemantics.init_genv SpecLang.speclang
                                                          lock_comp_unit sge sG)
    (Htso_init_genv : init_genv lock_comp_tso_unit tge)
    (Hspec_init_core : InteractionSemantics.init_core
                         SpecLang.speclang sG id args = Some sc),
  exists tc,
    init_core tge id args = Some tc.
Proof.
  intros.
  assert (Hfid : (id = lock_acquire_ident \/ id = lock_release_ident) /\ args = nil).
  eapply id_eq_lock_unit'; eauto.
  destruct Hfid as [Hfid Hargs].
  subst args.
  destruct Hfid; subst.
  {
    eapply lock_acquire_core_init_match'; eauto.
  }
  {
    eapply lock_release_core_init_match'; eauto.
  }
Qed.

Lemma obj_tau_step_match :
  forall t sc sm tc tm b gm fl fp tc' b' gm' tm' sge tge sG
    (Hspec_init : InteractionSemantics.init_genv
                    SpecLang.speclang lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                             (InteractionSemantics.V SpecLang.speclang) sge tge)  
    (Hmatch : obj_match_state sge tge t (sc, sm) (tc, tm))
    (Hbuffer : tso_buffers tm t = b)
    (Hmem : memory tm = gm)
    (Hno_conflict : 
      forall t' blk n lo hi,
         t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
         blk <> get_block fl n
    )
    (Hrel_tm_gm_vb : rel_tm_gm_vb sm tm fl t)
    (Htsostep : tsostep tge fl tc (b, gm) fp tc' (b', gm'))
    (Htm' : tm' = (mktsomem (tupdate t b' (tso_buffers tm)) gm')),
    (* normal star step *)
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
                  /\ InteractionSemantics.at_external SpecLang.speclang sG sc_ext = None
                  /\ (forall ores, InteractionSemantics.after_external
                               SpecLang.speclang sc_ext ores = None)
                  /\ InteractionSemantics.halt SpecLang.speclang sc_ext = None
          )
        )
    ).
Proof.
  intros.
  inversion Hmatch; subst.
  { 
    (** lock step satisfies Guarantee *)
    lets Ht : lock_step_satisfy_Gobj ___; eauto.
  }
  {
    (** unlock step satisfies Guarantee *)
    eapply unlock_step_satisfy_Gobj; eauto.
  }
Qed.
  
Lemma obj_no_external_call :
  forall t sc sm tc tm sge tge sG
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hobj_match_state : obj_match_state sge tge t (sc, sm) (tc, tm)),
    at_external tge tc = None.
Proof.
  intros.
  inversion Hobj_match_state; subst.
  - (* lock acquire no external *)
    eapply lock_acquire_no_external; eauto.
  - (* lock release no external *)
    eapply lock_release_no_external; eauto.
Qed.

Lemma obj_return_value_match :
  forall t sc sm tc tm rv tge sge sG
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hobj_state_match: obj_match_state sge tge t (sc, sm) (tc, tm))
    (Htc_halt : halt tc = Some rv),
    InteractionSemantics.halt SpecLang.speclang sc = Some rv.
Proof.
  intros.
  inversion Hobj_state_match; subst.
  - (* lock acquire halt *)
    eapply lock_ret_val_eq; eauto.
  - (* lock release halt *)
    eapply unlock_ret_val_eq; eauto.
Qed.

Lemma obj_rely_step_match :
  forall t sc sm tc tm sm' tm' tge sge sG
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                             (InteractionSemantics.V SpecLang.speclang) sge tge)
    (Hobj_match : obj_match_state sge tge t (sc, sm) (tc, tm))
    (Hrely_step : Robj tge t sm tm sm' tm'),
    obj_match_state sge tge t (sc, sm') (tc, tm').
Proof.
  intros.
  inversion Hobj_match; subst.
  - (* lock acquire rely *)
    eapply obj_lock_match; eauto.
    eapply lock_acquire_rely; eauto.

  - (* lock release rely *)
    eapply obj_unlock_match; eauto.
    eapply lock_release_rely; eauto.
Qed.

Lemma obj_not_abort :
  forall sge sG tge t sc sm tc tm fl fm gm
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hobj_match_state : obj_match_state sge tge t (sc, sm) (tc, tm))
    (Hbf_nil : tso_buffers tm t = nil)
    (Hgm : memory tm = gm)
    (Hstep : forall (fp : FP.t) (tc' : core) (b' : buffer) (gm' : gmem),
        ~ tsostep tge fl tc (nil, gm) fp tc' (b', gm'))
    (Hnot_halt : halt tc = None)
    (Hembed : embed gm fl fm),
    False.
Proof.
  intros.
  inversion Hobj_match_state; subst.
  - (* lock acquire not abort *)
    eapply lock_acq_not_abort; eauto.
  - (* lock release not abort *)
    eapply lock_rel_not_abort; eauto.
Qed.

Lemma tso_init_fail_spec_init_fail :
  forall tge sge sG id args
    (Hspec_init : InteractionSemantics.init_genv
                    SpecLang.speclang lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Himp_init_core_fail : init_core tge id args = None),
    InteractionSemantics.init_core SpecLang.speclang sG id args = None.
Proof.
  intros. 
  destruct (Classical_Prop.classic
              (InteractionSemantics.init_core SpecLang.speclang sG id args = None))
           eqn : Heqe; eauto.
  assert (InteractionSemantics.init_core SpecLang.speclang sG id args <> None);
    eauto.
  eapply spec_init_not_none in H; eauto.
  destruct H.
  eapply ObjInit_core_match' in H; eauto.
  destruct H.
  rewrite Himp_init_core_fail in H.
  tryfalse.
Qed.

Lemma obj_tso_halt_spec_not_exec :
  forall sge tge t sc sm tc tm rv sG
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang lock_comp_unit sge
                 sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                (InteractionSemantics.V SpecLang.speclang) sge tge)
    (Hobj_match : obj_match_state sge tge t (sc, sm) (tc, tm))
    (Hhalt : halt tc = Some rv),
    (
      forall fl fp sc' sm',
        ~ InteractionSemantics.step SpecLang.speclang sG fl sc sm fp sc' sm'
    ) /\ InteractionSemantics.at_external SpecLang.speclang sG sc = None.
Proof.
  intros.

  Ltac solve_not_halt_cases Hhalt :=
    match goal with
    | H : _ PC = Vptr _ _ |- _ =>
      simpl in Hhalt; rewrite H in Hhalt; simpl in Hhalt; tryfalse
    end.
  
  inversion Hobj_match; subst.
  {
    (** lock acquire *)
    match goal with
    | H : lock_match_state _ _ _ _ _ |- _ => inversion H; subst
    end; try (solve_not_halt_cases Hhalt).

    lets Hspec_core : spec_lock_acquire_init_state ___; eauto.
    lets Htso_core : tso_lock_acquire_init_state ___; eauto.
    destruct Hspec_core as [fb1 [Hspec_findsymb Hspec_core]].
    destruct Htso_core as [fb2 [Htso_findsymb Htso_core]].
    simpl in Hspec_core, Htso_core.
    inversion Hspec_core; subst.
    unfolds fundef_init.
    simpls.
    inversion Htso_core; subst.
    clear - Hhalt.
    simpls.
    tryfalse.

    split.
    introv Hstep.
    inversion Hstep; subst.
    match goal with
    | H : context [SpecLang.fstep] |- _ => inversion H; subst
    end.
    match goal with
    | H : context [SpecLang.normalstep] |- _ => inversion H; subst
    end.
    eauto.
  }
  {
    (** lock release *)
    match goal with
    | H : unlock_match_state _ _ _ _ _ |- _ => inversion H; subst
    end; try (solve_not_halt_cases Hhalt).
 
    lets Hspec_core : spec_lock_release_init_state ___; eauto.
    lets Htso_core : tso_lock_release_init_state ___; eauto.
    destruct Hspec_core as [fb1 [Hspec_findsymb Hspec_core]].
    destruct Htso_core as [fb2 [Htso_findsymb Htso_core]].
    simpl in Hspec_core, Htso_core.
    inversion Hspec_core; subst.
    unfolds fundef_init.
    simpls.
    inversion Htso_core; subst.
    clear - Hhalt.
    simpls.
    tryfalse.

    split.
    introv Hstep.
    inversion Hstep; subst.
    match goal with
    | H : context [SpecLang.fstep] |- _ => inversion H; subst
    end.
    match goal with
    | H : context [SpecLang.normalstep] |- _ => inversion H; subst
    end.
    eauto.
  }
Qed.

Lemma obj_tso_not_halt_spec_not_halt :
  forall sge tge t sc sm tc tm sG
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang lock_comp_unit sge
                 sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                (InteractionSemantics.V SpecLang.speclang) sge tge)
    (Hobj_match : obj_match_state sge tge t (sc, sm) (tc, tm))
    (Hhalt : halt tc = None),
    InteractionSemantics.halt SpecLang.speclang sc = None.
Proof.
  intros.
  inversion Hobj_match; subst.
  {
    (** lock acquire *)
    match goal with
    | H : context [lock_match_state] |- _ =>
      inversion H; subst
    end; try solve [simpl; eauto].

    lets Hspec_core : spec_lock_acquire_init_state ___; eauto.
    lets Htso_core : tso_lock_acquire_init_state ___; eauto.
    destruct Hspec_core as [fb1 [Hspec_findsymb Hspec_core]].
    destruct Htso_core as [fb2 [Htso_findsymb Htso_core]].
    simpl in Hspec_core, Htso_core.
    inversion Hspec_core; subst.
    unfolds fundef_init.
    simpls.
    inversion Htso_core; subst.
    clear - Hhalt.
    simpls.
    eauto.

    simpl in Hhalt.
    match goal with
    | H : rs PC = _ |- _ => rewrite H in Hhalt; simpls
    end.
    unfolds loc_result.
    destruct Archi.ptr64 eqn:?; tryfalse.
  }
  {
    (** lock release *)
    match goal with
    | H : context [unlock_match_state] |- _ =>
      inversion H; subst
    end; try solve [simpl; eauto].
 
    lets Hspec_core : spec_lock_release_init_state ___; eauto.
    lets Htso_core : tso_lock_release_init_state ___; eauto.
    destruct Hspec_core as [fb1 [Hspec_findsymb Hspec_core]].
    destruct Htso_core as [fb2 [Htso_findsymb Htso_core]].
    simpl in Hspec_core, Htso_core.
    inversion Hspec_core; subst.
    unfolds fundef_init.
    simpls.
    inversion Htso_core; subst.
    clear - Hhalt.
    simpls.
    eauto.

    simpl in Hhalt.
    match goal with
    | H : rs PC = _ |- _ => rewrite H in Hhalt
    end.
    simpl in Hhalt.
    unfolds loc_result.
    destruct Archi.ptr64 eqn:?; tryfalse.
  }
Qed.

Lemma obj_unbuffer_safe :
  forall sge tge t sc sm tc tm
    (Hobj_match : obj_match_state sge tge t (sc, sm) (tc, tm)),
    unbuffer_safe tm.
Proof.
  intros.
  inversion Hobj_match; subst.
  {
    inversion H1; subst;
      eapply obj_inv_impl_unbuffer_safe; eauto.
  }
  {
    inversion H1; subst;
      eapply obj_inv_impl_unbuffer_safe; eauto.
  }
Qed.
  
Lemma obj_footprint_case :
  forall sge sG tge sc tm gm t b fp tc tc' b' gm' sm ofs fl b0
         (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                      lock_comp_unit sge sG)
         (Himp_init : init_genv lock_comp_tso_unit tge)
         (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                                  (InteractionSemantics.V SpecLang.speclang)
                                  sge tge)
         (Hobj_match_state : obj_match_state sge tge t (sc, sm) (tc, tm))
         (Hbf : tso_buffers tm t = b)
         (Hmem : memory tm = gm)
         (Hstep : tsostep tge fl tc (b, gm) fp tc' (b', gm'))
         (Hlocs_belongsto : Locs.belongsto (FP.locs fp) b0 ofs),
    obj_mem sm b0 ofs \/ (exists n, get_block fl n = b0).
Proof.
  intros.
  inversion Hobj_match_state; subst; eauto.
  {
    eapply lock_footprint_case; eauto.
  }
  {
    eapply unlock_footprint_case; eauto.
  }
Qed.
  
    
    