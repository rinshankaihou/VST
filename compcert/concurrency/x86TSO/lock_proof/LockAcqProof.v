(** We prove that the implementation function lock and its corresponding 
specification satisfy the object simulation in this file. *)
From mathcomp.ssreflect Require Import fintype ssrnat.                       
Require Import Coqlib Maps Axioms.  
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
 
Require Import Asm. 

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory FMemLemmas TSOMem MemAux. 
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
Require Import TSOMemLemmas MemLemmas.

(** * Lemmas about lock acquire *)
Lemma tso_lock_acquire_init_state :
  forall tge tc
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hinit_core : Some tc = init_core tge lock_acquire_ident nil),
  exists fb, Genv.find_symbol tge lock_acquire_ident = Some fb /\
        Some tc = fundef_init fb (fn_sig lock_acquire_tso_fnbody) nil.
Proof.
  intros.
  inversion Himp_init.
  unfolds init_core.
  unfolds ASM_local.init_core.
  destruct (Genv.find_symbol tge lock_acquire_ident) eqn:Hfind_symb; try discriminate.
  specialize (H2 lock_acquire_ident).
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

Lemma find_lock_acquire_from_ge :
  forall tge fb
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hfb : Genv.find_symbol tge lock_acquire_ident = Some fb),
    Genv.find_funct_ptr tge fb = Some (Internal lock_acquire_tso_fnbody).
Proof.
  intros.
  inversion Himp_init; subst.
  specialize (H2 lock_acquire_ident).
  inversion H2; subst.
  eapply H5 in H10; eauto.
  simpl in H10.
  clear - Hfb H10 H9.
  rewrite Hfb in H9.
  inversion H9; subst.
  unfold Genv.find_funct_ptr.
  unfold Genv.find_def.
  rewrite <- H10.
  simpl; eauto.
Qed.
  
Lemma spec_lock_acquire_init_state :
  forall sge sG sc
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Hsc_init : Some sc = SpecLang.init_core sge lock_acquire_ident nil),
  exists fb, Genv.find_symbol sge lock_acquire_ident = Some fb /\
        Some sc = SpecLang.fundef_init (Internal lock_acquire_fnbody) nil.
Proof.
  intros.
  inversion Hspec_init; subst.
  inversion H0; subst.
  specialize (H3 lock_acquire_ident).
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
  
Lemma lock_acquire_core_init_match :
  forall tge tc sge sG
    (Htso_init_genv : init_genv lock_comp_tso_unit tge)
    (Hspec_init_genv : InteractionSemantics.init_genv
                         SpecLang.speclang lock_comp_unit sge sG)
    (Hinit_core : init_core tge lock_acquire_ident nil = Some tc),
  exists sc,
    InteractionSemantics.init_core SpecLang.speclang sG lock_acquire_ident nil
    = Some sc.
Proof. 
  intros.
  inversion Hspec_init_genv.
  subst.
  inversion H0; subst.
  simpl.
  unfold SpecLang.init_core.
  unfold generic_init_core.
  specialize (H3 lock_acquire_ident).
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

Lemma lock_acquire_core_init_match' :
  forall tge sc sge sG args
    (Htso_init_genv : init_genv lock_comp_tso_unit tge)
    (Hspec_init_genv : InteractionSemantics.init_genv
                         SpecLang.speclang lock_comp_unit sge sG)
    (Hspec_init_core : InteractionSemantics.init_core SpecLang.speclang
                                           sG lock_acquire_ident args = Some sc),
  exists tc,
    init_core tge lock_acquire_ident args = Some tc.
Proof. 
  intros.
  inversion Htso_init_genv.
  specialize (H2 lock_acquire_ident).
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
  specialize (H3 lock_acquire_ident).
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

(** [match_no_extcall] holds in function lock *)
Lemma lock_acquire_no_external :
  forall t sc sm tc tm sge tge sG
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hlock_acq_match : lock_match_state sge tge t (sc, sm) (tc, tm)),
    at_external tge tc = None.
Proof.
  intros.
  inversion Hlock_acq_match; subst;
    try solve [simpl; eauto].
  {
    (* init state *)
    eapply tso_lock_acquire_init_state in H4; eauto.
    destruct H4 as [fb [Hfb Hinit_state]].
    unfolds fundef_init.
    simpls.
    inversion Hinit_state; subst.
    simpl.
    eauto.
  }
Qed.

(** [match_halt] holds in function lock *)
Lemma lock_ret_val_eq :
  forall sge tge t sc sm tc tm rv
    (Hhalt : halt tc = Some rv)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hlock_match_state : lock_match_state sge tge t (sc, sm) (tc, tm)),
    SpecLang.halt sc = Some rv.
Proof.
  intros.
  inversion Hlock_match_state; subst;
    try solve
        [
          simpl in Hhalt; 
          match goal with
          | H : ?rs _ = Vptr _ _ |- _ =>
            rewrite H in Hhalt; simpl in Hhalt; tryfalse
          end
        ].
  {
    eapply tso_lock_acquire_init_state in H4; eauto.
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

(** [match_abort] holds in function lock *)
Lemma lock_acq_not_abort :
  forall sge sG tge t sc sm tc tm fl fm gm
    (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                 lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hlock_acq_match_state : lock_match_state sge tge t (sc, sm) (tc, tm))
    (Hbf_nil : tso_buffers tm t = nil)
    (Hgm : memory tm = gm)
    (Hstep : forall (fp : FP.t) (tc' : core) (b' : buffer) (gm' : gmem),
        ~ tsostep tge fl tc (nil, gm) fp tc' (b', gm'))
    (Hnot_halt : halt tc = None)
    (Hembed : embed gm fl fm),
    False.
Proof.
  intros.
  inversion Hlock_acq_match_state; subst.
  {
    (** lock acquire : init *)
    lets Hinit_core : tso_lock_acquire_init_state ___; eauto.
    destruct Hinit_core as [fb [Hfind_symb Hinit_core]].
    simpl in Hinit_core.
    unfolds fundef_init.
    simpls.
    inversion Hinit_core; subst.
    clear_trivial_eq.

    lets Halloc : tsoalloc_bf_nil_succ_sz0 ___; eauto.
    destruct Halloc as [tm1 [stk Halloc]].
    
    eapply Hstep.
    econstructor; eauto.
    econstructor; eauto.
    simpl; eauto.
    
    (* alloc case remaining to prove *)
    simpl.
    eauto.

    unfolds store_args_fmem.
    simpl.
    eauto.
  }
  { 
    (** lock acquire : lock label *)
    eapply Hstep. trivial_not_abort.
  }
  {
    (** lock acquire : movl $L RCX *)
    eapply Hstep. trivial_not_abort.
  }
  {
    (** lock acquire : movl $0 RDX *)
    eapply Hstep. trivial_not_abort.
  }
  {
    (** lock acquire : lock_acquire label *)
    eapply Hstep. trivial_not_abort.
  }
  {
    (** lock acquire : movl $1 RAX *)
    eapply Hstep. trivial_not_abort.
  }
  { 
    (** lock acquire : lock cmpxchg [RCX] RDX *)
    match goal with
    | H1 : obj_inv _ _ _, H2 : rs (IR RCX) = _, H3 : rs (IR RAX) = _ |- _ =>
      renames H1 to Hobj_inv, H2 to HR8, H3 to Hrax
    end.
    unfolds obj_inv.
    destruct Hobj_inv as
        [L' [Hfind_symb [Hst [H_spec_store [H_tso_store Hunbuffer_safe]]]]].
    match goal with
    | H : _ = Genv.find_symbol _ _ |- _ =>
      rewrite Hfind_symb in H; inversion H; subst L'
    end.
    destruct Hst as [H_lock_st | H_unlock_st].
    {   
      eapply Hstep.
      trivial_not_abort.
      instantiate (2 := (nextinstr (rs # ZF <- Vfalse) # RAX <- Vzero)).
      instantiate (1 := {| tbuffer := nil; fmemory := fm |}).
      unfold eval_addrmode.
      destruct Archi.ptr64 eqn:?; tryfalse.
      simpl.
      rewrite HR8.
      simpl.
      rewrite Heqb0.
      rewrite Int.add_zero. 
      assert (Ht : Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero) =
                   Ptrofs.repr 0).
      eauto.
      rewrite Ht.
      unfolds lock_st.
      destruct H_lock_st as [Hload_sm [Hnot_in_buf Hload_tsom]].
      simpl.
      lets Ht1 : Ptrofs.unsigned_zero ___; eauto. 
      unfold Ptrofs.zero in Ht1; rewrite Ht1. 
      clear - Hload_tsom Hembed Hrax Hunbuffer_safe. 
      unfolds load_tsomem.
      destruct tm.
      simpls. 
      eapply load_gm_embed_load_fm in Hload_tsom; eauto.
      rewrite Hload_tsom.
      rewrite Hrax.
      simpl.
      assert (Ht2 : Int.eq Int.zero Int.one = false); eauto.
      inversion Hembed; subst; eauto.
      split_and Hunbuffer_safe; eauto.
    }
    {
      unfolds unlock_st.
      destruct H_unlock_st as [Hload_sm H_unlock_st].
      destruct H_unlock_st as [H_unlock_st | H_unlock_st].
      {
        split_and H_unlock_st.
        match goal with
        | H : load_tsomem _ _ _ _ = _ |- _ =>
          rename H into Hload_tsom
        end.
        unfolds load_tsomem.
        destruct tm.
        simpl in Hstep, Hembed.
        inversion Hembed; subst.
        eapply Hstep.
        trivial_not_abort.
        unfold eval_addrmode.
        destruct Archi.ptr64 eqn:?; tryfalse.
        simpl.
        rewrite HR8.
        rewrite Int.add_zero.
        simpl.
        rewrite Heqb0.
        assert (Ht : Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero) =
                     Ptrofs.repr 0); eauto.
        rewrite Ht.
        simpl.
        lets Ht1 : Ptrofs.unsigned_zero ___; eauto.
        unfold Ptrofs.zero in Ht1; rewrite Ht1.
        eapply load_gm_embed_load_fm in Hload_tsom; eauto.
        rewrite Hload_tsom.
        rewrite Hrax.
        simpl.
        assert (Ht2 : Int.eq Int.zero Int.one = false); eauto.
        rewrite Ht2; eauto.
        clear - Hunbuffer_safe.
        simpls.
        split_and Hunbuffer_safe; eauto.
      }
      {   
        split_and H_unlock_st.
        clear_trivial_eq.
        specialize (H_tso_store Int.zero).
        destruct H_tso_store as [tm' H_tso_store].
        unfolds store_tsomem.
        destruct tm.
        destruct (store Mint32 memory L 0 (Vint Int.zero)) eqn:Hstore; tryfalse.
        rename g into m'.
        inversion H_tso_store; subst.
        clear_trivial_eq.
        simpl in Hembed.
        eapply store_gm_embed_store_fm in Hstore; eauto.
        destruct Hstore as [fm' [Hstore Hembed1]].
        eapply Hstep.
        trivial_not_abort.
        unfold eval_addrmode.
        destruct Archi.ptr64 eqn:?; tryfalse.
        simpl.
        rewrite HR8.
        rewrite Int.add_zero. 
        simpl.
        rewrite Heqb0.
        assert (Ht : Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero) =
                     Ptrofs.repr 0); eauto.
        rewrite Ht.
        simpl.
        lets Ht1 : Ptrofs.unsigned_zero ___; eauto.
        unfold Ptrofs.zero in Ht1; rewrite Ht1.
        rewrite Hrax.
        simpl.
        match goal with
        | H : load_tsomem _ _ _ _ = _ |- _ => rename H into Hload_tm
        end.
        simpl in Hload_tm. 
        eapply load_gm_embed_load_fm in Hload_tm; eauto.
        rewrite Hload_tm.
        simpl.
        rewrite Int.eq_true.
        match goal with
        | H : rs (IR RDX) = _ |- _ => rewrite H
        end.
        unfold Vzero.
        rewrite Hstore.
        eauto.
        clear - Hunbuffer_safe Hembed.
        inversion Hembed; subst.
        simpls.
        split_and Hunbuffer_safe; eauto.
        clear - Hembed Hunbuffer_safe.
        simpls.
        inversion Hembed; subst.
        split_and Hunbuffer_safe; eauto.
      }
    }
  }
  {
    (** lock acquire : je enter [ZF = 1] *)
    eapply Hstep.
    trivial_not_abort.
    match goal with
    | H : rs (CR ZF) = _ |- _ => rewrite H; simpl
    end.
    rewrite Int.eq_true.
    unfold tso_goto_label, lock_acquire_tso_fnbody.
    simpl.
    destruct (peq enter_lbl lock_lbl) eqn:?; tryfalse.
    destruct (peq enter_lbl lock_acquire_lbl) eqn:?; tryfalse.
    destruct (peq enter_lbl spin_lbl) eqn:?; tryfalse.
    destruct (peq enter_lbl enter_lbl) eqn:?; tryfalse.
    match goal with
    | H : rs PC = _ |- _ => rewrite H; eauto
    end.
  }
  {
    (** lock acquire : je enter [ZF = 0] *)
    eapply Hstep.
    trivial_not_abort.
    match goal with
    | H : rs (CR ZF) = _ |- _ => rewrite H; simpl
    end.
    assert (Ht : Int.eq Int.zero Int.one = false); eauto.
    rewrite Ht; eauto.
  }
  {
    (** lock acquire : spin label *)
    eapply Hstep. trivial_not_abort.
  }
  {
    (** lock acquire : movl [RCX] RBX *)
    match goal with
    | H : obj_inv _ _ _, H2 : rs (IR RCX) = _  |- _ =>
      renames H to Hobj_inv, H2 to HR8
    end.
    unfolds obj_inv.
    destruct Hobj_inv as [L' [Hfind_symb [Hlock_st [Hstore_sm Hstore_tm]]]].
    destruct Hlock_st as [Hlock_st | Hlock_st].
    { 
      unfolds lock_st.
      split_and Hlock_st.
      inversion Hembed; subst.
      match goal with
      | H : load_tsomem _ _ _ _ = _ |- _ =>
        unfold load_tsomem in H; destruct tm; simpl in H;
          rename H into Hload_tsomem
      end.
      match goal with
      | H : strip _ = _ |- _ => simpl in H; subst
      end.  
      eapply load_gm_embed_load_fm in Hload_tsomem; eauto.
      eapply Hstep; simpl.
      trivial_not_abort.      
      unfold exec_load_TSO.
      lets Htso_loadv : Mem_load_fm_load_tm_eq ___; eauto.
      eapply load_fm_eq_load_gm;eauto.
      unfold eval_addrmode.
      destruct Archi.ptr64 eqn:?; tryfalse.
      simpl.
      rewrite HR8.
      rewrite Int.add_zero.
      simpl.
      rewrite Heqb0.
      assert (Ht : Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero)
                   = Ptrofs.repr 0); eauto.
      rewrite Ht.
      match goal with
      | H : _ = Genv.find_symbol _ lock_L_ident |- _ =>
        rewrite Hfind_symb in H; inversion H; subst L'
      end.
      rewrite Htso_loadv.
      eauto.
      clear - Hstore_tm.
      simpls.
      split_and Hstore_tm; eauto.
    }
    {
      unfolds unlock_st.
      split_and Hlock_st.
      inversion Hembed; subst.
      match goal with
      | H : _ \/ _ |- _ => destruct H as [Hlock | Hunlock]
      end.
      {
        split_and Hlock.
        match goal with
        | H : load_tsomem _ _ _ _ = _ |- _ =>
          unfold load_tsomem in H; destruct tm; simpl in H;
            rename H into Hload_tsomem
        end.
        match goal with
        | H : strip _ = _ |- _ => simpl in H; subst
        end.
        
        eapply load_gm_embed_load_fm in Hload_tsomem; eauto.
        eapply Hstep.
        trivial_not_abort.
        unfold exec_load_TSO.
        lets Htso_loadv : Mem_load_fm_load_tm_eq ___; eauto.
        eapply load_fm_eq_load_gm;eauto.

        unfold eval_addrmode.
        destruct Archi.ptr64 eqn:?; tryfalse.
        simpl.
        rewrite HR8.
        rewrite Int.add_zero.
        simpl.
        rewrite Heqb0.
        assert (Ht : Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero)
                     = Ptrofs.repr 0); eauto.
        rewrite Ht.
        match goal with
        | H : _ = Genv.find_symbol _ lock_L_ident |- _ =>
          rewrite Hfind_symb in H; inversion H; subst L'
        end.
        rewrite Htso_loadv.
        eauto.
        clear -Hstore_tm.
        split_and Hstore_tm; eauto.
      }
      {
        split_and Hunlock.
        match goal with
        | H : load_tsomem _ _ _ _ = _ |- _ =>
          unfold load_tsomem in H; destruct tm; simpl in H;
            rename H into Hload_tsomem
        end.
        match goal with
        | H : strip _ = _ |- _ => simpl in H; subst
        end.
        eapply load_gm_embed_load_fm in Hload_tsomem; eauto.
        eapply Hstep.
        trivial_not_abort.
        unfold exec_load_TSO.
        lets Htso_loadv : Mem_load_fm_load_tm_eq ___; eauto.
        eapply load_fm_eq_load_gm;eauto.
        unfold eval_addrmode.
        destruct Archi.ptr64 eqn:?; tryfalse.
        simpl.
        rewrite HR8.
        rewrite Int.add_zero.
        simpl.
        rewrite Heqb0.
        assert (Ht : Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero)
                     = Ptrofs.repr 0); eauto.
        rewrite Ht.
        match goal with
        | H : _ = Genv.find_symbol _ lock_L_ident |- _ =>
          rewrite Hfind_symb in H; inversion H; subst L'
        end.
        rewrite Htso_loadv.
        eauto.
        clear -Hstore_tm.
        split_and Hstore_tm; eauto.
      }
    }
  }
  {
    (** lock acquire : cmp R9 $0 *) 
    match goal with
    | H : rs (IR RBX) = _ \/ rs (IR RBX) = _ |- _ =>
      destruct H as [HR9 | HR9];
        eapply Hstep;
        trivial_not_abort; try solve [rewrite HR9; simpl; eauto]
    end.
  }
  { 
    (** lock acquire : je spin *)
    match goal with
    | H : rs (CR ZF) = _ \/ rs (CR ZF) = _ |- _ =>
      destruct H as [Hzf | Hzf];
        eapply Hstep; trivial_not_abort; try (rewrite Hzf; simpl; eauto)
    end.
    rewrite Int.eq_true; eauto.
    unfold tso_goto_label.
    simpl.
    destruct (peq spin_lbl lock_lbl) eqn:?; tryfalse.
    destruct (peq spin_lbl lock_acquire_lbl) eqn:?; tryfalse.
    destruct (peq spin_lbl spin_lbl) eqn:?; tryfalse.
    match goal with
    | H : rs PC = _ |- _ => rewrite H; eauto
    end.
    assert (Ht : Int.eq Int.zero Int.one = false).
    eauto.
    rewrite Ht; eauto.
  }
  {
    (** lock acquire : jmp lock *)
    eapply Hstep; trivial_not_abort.
    unfold tso_goto_label.
    simpl.
    destruct (peq lock_acquire_lbl lock_lbl) eqn:?; tryfalse.
    destruct (peq lock_acquire_lbl lock_acquire_lbl) eqn:?; tryfalse.
    match goal with
    | H : rs PC = _ |- _ => rewrite H; eauto
    end.
  }
  {
    (** lock acquire : enter *) 
    eapply Hstep; trivial_not_abort.
  }
  { 
    (** lock acquire : movl $0 RAX *)
    eapply Hstep; trivial_not_abort.
  }
  {
    (** lock acquire : retl *)
    eapply Hstep; trivial_not_abort.
  }
  {
    (** lock acquire : halt *)
    simpl in Hnot_halt.
    match goal with
    | H : rs PC = _ |- _ =>
      rewrite H in Hnot_halt; simpl in Hnot_halt
    end.
    unfolds loc_result.
    destruct Archi.ptr64 eqn:?; tryfalse.
  }
Qed.

(** [match_tau_obj_mem_fp] holds in function lock *)
Lemma lock_footprint_case :
  forall sge sG tge sc tm gm t b fp tc tc' b' gm' sm ofs fl b0
         (Hspec_init : InteractionSemantics.init_genv SpecLang.speclang
                                                      lock_comp_unit sge sG)
         (Himp_init : init_genv lock_comp_tso_unit tge)
         (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                                  (InteractionSemantics.V SpecLang.speclang)
                                  sge tge)
         (Hlock_match_state : lock_match_state sge tge t (sc, sm) (tc, tm))
         (Hbf : tso_buffers tm t = b)
         (Hmem : memory tm = gm)
         (Hstep : tsostep tge fl tc (b, gm) fp tc' (b', gm'))
         (Hlocs_belongsto : Locs.belongsto (FP.locs fp) b0 ofs),
    obj_mem sm b0 ofs \/ exists n, get_block fl n = b0.
Proof.
  intros.
  unfolds Locs.belongsto.
  inversion Hlock_match_state; subst;
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
    lets Htso_core : tso_lock_acquire_init_state ___; eauto.
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
           H2 : obj_inv _ _ _,
                H3 : embed _ _ _,
                     H4 : tsoalloc _ _ _ _ |- _ =>
      renames H1 to Hargs_len_rec, H2 to Hobj_inv, H3 to Hembed, H4 to Htsoalloc
    end.       
    clear - Htsoalloc Hlocs_belongsto Hargs_len_rec Hembed.
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
    dis_if_else; tryfalse; subst.
    right.
    unfold Mem.nextblock.
    inversion Hembed; subst.
    eexists; eauto.
    inv H6; eauto.
    rewrite H0; eauto.
  }
  {
    inversion Hstep; subst; eauto.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.
    match goal with
    | H : context [exec_instr_TSO], H1 : rs (IR RCX) = _ |- _ =>
      renames H to Hexec_instr_tso, H1 to Hecx
    end. 
    simpl in Hlocs_belongsto.
    destruct (tso_buffers tm t) eqn:?; tryfalse.
    unfold eval_addrmode in Hlocs_belongsto.
    destruct Archi.ptr64 eqn:?; tryfalse.
    simpl in Hlocs_belongsto.
    rewrite Hecx in Hlocs_belongsto.
    simpl in Hlocs_belongsto.
    rewrite Heqb0 in Hlocs_belongsto.
    assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                            (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                 = Ptrofs.repr 0).
    eauto.
    rewrite Ht in Hlocs_belongsto.
    destruct (Mem.loadv Mint32 fm (Vptr L (Ptrofs.repr 0))) eqn:Hmem_load; tryfalse.
    {
      match goal with
      | H : rs (IR RAX) = _, H2 : obj_inv _ _ _,
        H3 : _ = Genv.find_symbol _ lock_L_ident |- _ =>
        renames H to Heax, H2 to Hobj_inv, H3 to Hfind_symbol
      end.
      clear - Hlocs_belongsto Heax Hobj_inv Hfind_symbol
                              Heqb0 Hexec_instr_tso Hmem_load Hecx.
      rewrite Heax in Hlocs_belongsto. 
      destruct (Val.cmpu_bool (Mem.valid_pointer fm) Ceq v Vone) eqn:?; tryfalse.
      destruct b.
      simpls.
      assert (Ht1 : Ptrofs.unsigned (Ptrofs.repr 0) = 0%Z).
      eauto.
      rewrite Ht1 in Hlocs_belongsto.
      unfolds Cop_fp.cmpu_bool_fp.
      destruct v; simpls; tryfalse.
      unfolds FP.locs, load_fp, store_fp.
      simpls.
      unfolds Locs.union.
      simpls.
      destruct (Locs.emp b0 ofs) eqn:?; simpls; tryfalse.
      unfolds range_locset.
      destruct (eq_block L b0) eqn:?; tryfalse; subst.
      destruct (zle 0 ofs) eqn:?; tryfalse; subst.
      simpls.
      destruct (zlt ofs 4) eqn:?; tryfalse; subst.
      unfolds obj_inv.
      destruct Hobj_inv as [L [Hfind_symb' Hobj_inv]].
      split_and Hobj_inv.
      rewrite <- Hfind_symbol in Hfind_symb'.
      inversion Hfind_symb'; subst.
      eauto. 

      unfolds loadv_fp, Cop_fp.cmpu_bool_fp.
      rewrite Heqb0 in Hlocs_belongsto.
      destruct v; tryfalse.
      simpls.
      unfolds FP.locs, load_fp, FP.union.
      simpls.
      assert (Ht1 : Ptrofs.unsigned (Ptrofs.repr 0) = 0%Z).
      eauto.
      rewrite Ht1 in Hlocs_belongsto.
      unfolds Locs.union.
      destruct (Locs.emp b0 ofs) eqn:?; tryfalse.
      simpls.
      unfolds range_locset.
      destruct (eq_block L b0) eqn:?; tryfalse; subst.
      unfolds obj_inv.
      destruct Hobj_inv as [L [Hfind_symb' Hobj_inv]].
      split_and Hobj_inv.
      rewrite <- Hfind_symbol in Hfind_symb'.
      inversion Hfind_symb'; subst.
      simpls.
      destruct (zle 0 ofs) eqn:?;
               destruct (zlt ofs 4) eqn:?; tryfalse.
      eauto.
 
      unfolds FP.union, loadv_fp, Cop_fp.cmpu_bool_fp.
      rewrite Heqb0 in Hlocs_belongsto.
      simpls.
       
      unfolds eval_addrmode.
      rewrite Heqb0 in Hexec_instr_tso.
      simpls.
      rewrite Hecx in Hexec_instr_tso.
      simpls.
      rewrite Heqb0 in Hexec_instr_tso.
      assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                              (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                   = Ptrofs.repr 0); eauto.
      rewrite Ht in Hexec_instr_tso.
      simpls.
      assert (Ht1 : Ptrofs.unsigned (Ptrofs.repr 0) = 0%Z).
      eauto.
      rewrite Ht1 in Hexec_instr_tso, Hmem_load.
      rewrite Hmem_load in Hexec_instr_tso.
      rewrite Heax in Hexec_instr_tso.
      rewrite Heqo in Hexec_instr_tso.
      tryfalse.
    }
    {
      simpl in Hexec_instr_tso.
      unfold eval_addrmode in Hexec_instr_tso.
      rewrite Heqb0 in Hexec_instr_tso.
      simpl eval_addrmode32 in *.
      rewrite Hecx in Hexec_instr_tso.
      simpl in Hexec_instr_tso.
      rewrite Heqb0 in Hexec_instr_tso.
      rewrite Ht in Hexec_instr_tso.
      rewrite Hmem_load in Hexec_instr_tso.
      tryfalse.
    }
  }
  {
    inversion Hstep; subst; eauto.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.
    match goal with
    | H : context [exec_instr_TSO], H1 : rs (IR RCX) = _ |- _ =>
      renames H to Hexec_instr_tso, H1 to Hecx
    end. 
    simpl in Hlocs_belongsto.
    clear - Hstep Hexec_instr_tso Hecx H9 Hlocs_belongsto H14.
    simpls.
    unfolds exec_load_TSO.
    unfolds eval_addrmode.
    destruct Archi.ptr64 eqn:?; tryfalse.
    simpls.
    rewrite Hecx in Hexec_instr_tso.
    simpls.
    rewrite Heqb in Hexec_instr_tso.
    assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                              (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                 = Ptrofs.repr 0); eauto.
    rewrite Ht in Hexec_instr_tso.
    unfolds exec_load_fp.
    unfolds eval_addrmode.
    rewrite Heqb in Hlocs_belongsto.
    clear Hstep.
    simpls.
    rewrite Hecx in Hlocs_belongsto.
    simpls.
    rewrite Heqb in Hlocs_belongsto.
    simpls.
    rewrite Ht in Hlocs_belongsto.
    assert (Ht1 : Ptrofs.unsigned (Ptrofs.repr 0) = 0%Z).
    eauto.
    rewrite Ht1 in Hlocs_belongsto.
    unfolds FP.locs, load_fp.
    simpls.
    unfolds Locs.union, range_locset.
    simpls.
    destruct (Locs.emp b0 ofs) eqn:?; tryfalse.
    destruct (eq_block L b0) eqn:?; tryfalse; subst.
    destruct (zle 0 ofs) eqn:?;
             destruct (zlt ofs 4) eqn:?; tryfalse.
    renames H14 to Hobj_inv.
    unfolds obj_inv.
    destruct Hobj_inv as [L' [Hfind_symb' Hobj_inv]].
    rewrite Hfind_symb' in H9.
    inversion H9; subst.
    split_and Hobj_inv.
    eauto.
  }
  {
    inversion Hstep; subst; eauto.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.
    match goal with
    | H : rs _ = _ \/ rs _ = _ |- _ => rename H into Hlock_var
    end.
    clear - Hlocs_belongsto Hlock_var.
    unfolds exec_instr_TSO_fp.
    unfolds compare_ints_TSO_fp.
    unfolds tso_cmpu_bool_fp_total.
    destruct Hlock_var as [Hlock_var | Hlock_var];
      rewrite Hlock_var in Hlocs_belongsto; simpls.
    rewrite FP.fp_union_emp in Hlocs_belongsto.
    unfolds FP.locs.
    unfolds Locs.union.
    simpls.
    unfolds Locs.emp.
    tryfalse.
    rewrite FP.fp_union_emp in Hlocs_belongsto.
    unfolds FP.locs.
    unfolds Locs.union.
    simpls.
    unfolds Locs.emp.
    tryfalse.
  }
  {
    match goal with
    | H : rs PC = _ |- _ => rename H into Hpc
    end.

    Ltac halt_elim rs :=
      match goal with
      | H : rs PC = Vptr _ _,
            H2 : rs PC = Vzero |- _ =>
        rewrite H in H2; tryfalse
      end.
     
    inversion Hstep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim; halt_elim rs.
  }
Qed.

Lemma lock_acq_unbuffer_safe :
  forall sge sG tge b gm b' gm' fp tc tc' tm sc sm t fl
    (Hspec_init : InteractionSemantics.init_genv
                    SpecLang.speclang lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hge_equiv : genv_match (InteractionSemantics.F SpecLang.speclang)
                             (InteractionSemantics.V SpecLang.speclang) sge tge)
    (Hlock_acq_match : lock_match_state sge tge t (sc, sm) (tc, tm))
    (Hbf : tso_buffers tm t = b)
    (Hno_conflict : 
      forall t' blk n lo hi,
        t' <> t -> In (BufferedAlloc blk lo hi) (tso_buffers tm t') ->
        blk <> get_block fl n
    )
    (Hgm : memory tm = gm)
    (Htsostep : tsostep tge fl tc (b, gm) fp tc' (b', gm')),
    unbuffer_safe {| tso_buffers := tupdate t b' (tso_buffers tm);
                     memory := gm' |}.
Proof.
  intros.
  inversion Hlock_acq_match; subst.
  {
    (** lock acquire : init *)
    lets Htso_init_core : tso_lock_acquire_init_state ___; eauto.
    destruct Htso_init_core as [fb [Hfind_symb Htso_init_core]].
    simpl in Htso_init_core.
    unfold fundef_init in Htso_init_core.
    simpl in Htso_init_core.
    inversion Htso_init_core; subst.
    lets Hspec_init_core : spec_lock_acquire_init_state ___; eauto.
    destruct Hspec_init_core as [fb2 [Hfind_symb' Hspec_init_core]].
    simpl in Hspec_init_core.
    inversion Hspec_init_core; subst.
    clear_trivial_eq.

    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    match goal with
    | H1 : args_len_rec _ _ = _,
           H2 : context [tsoalloc],
                H3 : store_args_fmem _ _ _ _ = _ |- _ =>
      renames H1 to Hargs, H2 to Htsoalloc, H3 to Hstore_args
    end.
    simpl in Hargs.
    inversion Hargs; subst.
    simpl in Htsoalloc.
    unfolds store_args_fmem.
    simpl in Hstore_args.
    inversion Hstore_args; subst.
    clear_trivial_eq.
    match goal with
    | H : obj_inv _ _ _ |- _ =>
      rename H into Hobj_inv
    end.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    eapply unbuffer_safe_tsoalloc_0_stable; eauto.
  }
  {
    (** lock acquire : lock label *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  { 
    (** lock acquire : movl $L %ecx *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : movl $0 %edx *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : lock acquire label *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : movl $0 RAX *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : lock cmpxchg [%ecx] %edx *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim. 
    clear_trivial_eq.
 
    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end. 
    simpl in Hexec_instr_tso.
    destruct (tso_buffers tm t) eqn:Hbf; tryfalse.
    unfolds eval_addrmode. 
    destruct Archi.ptr64 eqn:?; tryfalse.
    simpl in Hexec_instr_tso.
    match goal with
    | H : rs (IR RCX) = _ |- _ =>
      rewrite H in Hexec_instr_tso; simpl in Hexec_instr_tso
    end.
    rewrite Heqb0 in Hexec_instr_tso.
    assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                            (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
                 = Ptrofs.repr 0).
    eauto.
    rewrite Ht in Hexec_instr_tso.
    destruct (Mem.loadv Mint32 fm (Vptr L (Ptrofs.repr 0))) eqn:Hload; tryfalse.
    match goal with
    | H : rs (IR RAX) = _ |- _ => rewrite H in Hexec_instr_tso
    end.
    destruct (Val.cmpu_bool (Mem.valid_pointer fm) Ceq v Vone) eqn:Hcmp; tryfalse.
    destruct b0; eauto.
    { 
      match goal with
      | H : rs (IR RDX) = _ |- _ => rewrite H in Hexec_instr_tso
      end.
      destruct (Mem.storev Mint32 fm (Vptr L (Ptrofs.repr 0)) Vzero) eqn:Hstore;
        tryfalse.
      inversion Hexec_instr_tso; subst.
      clear_trivial_eq.
      simpl.
      rewrite buffer_unchange1; eauto.
      lets Hunbuffer_safe : obj_inv_impl_unbuffer_safe ___; eauto.
      eapply unbuffer_safe_mem_access_same_stable
      with (bfs := tso_buffers tm) (m1 := memory tm); eauto.
      clear - Hunbuffer_safe.
      destruct tm; simpls; eauto.
      clear - Hembed Hstore.
      inv Hembed.
      unfolds Mem.storev; simpls.
      eapply Mem_store_mem_access_stable in Hstore.
      rewrite Mem_GMem_access_eq in Hstore.
      rewrite H0 in Hstore; eauto.
    }
    {
      inversion Hexec_instr_tso; subst; eauto.
      clear_trivial_eq.
      simpl.
      rewrite buffer_unchange1; eauto.
      clear - Hobj_inv Hembed.
      eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
      destruct tm.
      simpls.
      inversion Hembed; subst; eauto.
    }
  }
  {
    (** lock acquire : je enter [ZF = 0] *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    match goal with
    | H : rs (CR ZF) = _ |- _ => rewrite H in Hexec_instr_tso
    end.
    rewrite Int.eq_true in Hexec_instr_tso.
    unfold tso_goto_label in Hexec_instr_tso.
    simpl in Hexec_instr_tso.
    find_label.
    destruct (peq enter_lbl lock_lbl) eqn:?; tryfalse.
    destruct (peq enter_lbl lock_acquire_lbl) eqn:?; tryfalse.
    destruct (peq enter_lbl spin_lbl) eqn:?; tryfalse.
    match goal with
    | H : rs PC = _ |- _ => rewrite H in Hexec_instr_tso
    end.
    inversion Hexec_instr_tso; subst.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : je enter [ZF = 1] *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    match goal with
    | H : rs (CR ZF) = _ |- _ => rewrite H in Hexec_instr_tso
    end.
    assert (Hnot_eq : Int.eq Int.zero Int.one = false); eauto.
    rewrite Hnot_eq in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : spain label *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : movl %ebx [%ecx] *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    unfolds exec_load_TSO.
    unfolds eval_addrmode.
    destruct Archi.ptr64 eqn:?; tryfalse.
    simpl in Hexec_instr_tso.
    match goal with
    | H : rs (IR RCX) = _ |- _ => rewrite H in Hexec_instr_tso
    end.
    simpl in Hexec_instr_tso.
    rewrite Heqb0 in Hexec_instr_tso.
    assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                       (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))
            = Ptrofs.repr 0).
    eauto.
    rewrite Ht in Hexec_instr_tso.
    destruct (tsoloadv Mint32
                       {| tbuffer := tso_buffers tm t; fmemory := fm |}
                       (Vptr L (Ptrofs.repr 0))) eqn:Hload; tryfalse.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : cmp %ebx $0 *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    destruct (check_vundef (rs RBX) (Vint Int.zero)) eqn:Heq; tryfalse.
    unfolds compare_ints_TSO.
    match goal with
    | H : rs (IR RBX) = _ \/ rs (IR RBX) = _ |- _ =>
      destruct H as [H | H]; rewrite H in Hexec_instr_tso;
        simpl in Hexec_instr_tso; inversion Hexec_instr_tso; subst
    end;
    clear_trivial_eq.

    simpl.
    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.

    simpl.
    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : je spin *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.

    match goal with
    | H : rs (CR ZF) = _ \/ rs (CR ZF) = _ |- _ =>
      destruct H as [H | H]; rewrite H in Hexec_instr_tso;
        simpl in Hexec_instr_tso
    end.
    rewrite Int.eq_true in Hexec_instr_tso.
    unfolds tso_goto_label.
    simpl in Hexec_instr_tso.
    find_label.
    destruct (peq spin_lbl lock_lbl);
      destruct (peq spin_lbl lock_acquire_lbl); tryfalse.
    match goal with
    | H : rs PC = _ |- _ => rewrite H in Hexec_instr_tso
    end.
    inversion Hexec_instr_tso; subst.
    clear_trivial_eq.

    simpl.
    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.

    change (Int.eq Int.zero Int.one) with false in Hexec_instr_tso.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    rewrite buffer_unchange; eauto.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : jmp lock_acquire *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    unfolds tso_goto_label.
    simpl in Hexec_instr_tso.
    find_label.
    destruct (peq lock_acquire_lbl lock_lbl) eqn:?; tryfalse.
    match goal with
    | H : rs PC = _ |- _ =>
      rewrite H in Hexec_instr_tso
    end.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.

    rewrite buffer_unchange.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : enter label *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.
    rewrite buffer_unchange; eauto.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : movl $0 %eax *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.
    rewrite buffer_unchange; eauto.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : retl *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.

    ptr_elim.
    clear_trivial_eq.

    match goal with
    | H : context [exec_instr_TSO],
          H2 : context [obj_inv], H3 : embed _ _ _ |- _ =>
      renames H to Hexec_instr_tso, H2 to Hobj_inv, H3 to Hembed
    end.
    simpl in Hexec_instr_tso.
    inversion Hexec_instr_tso; subst; eauto.
    simpl.
    clear_trivial_eq.
    rewrite buffer_unchange; eauto.
    eapply obj_inv_impl_unbuffer_safe in Hobj_inv; eauto.
    clear - Hembed Hobj_inv.
    destruct tm.
    simpls.
    inversion Hembed; subst; eauto.
  }
  {
    (** lock acquire : halt *)
    inversion Htsostep; subst.
    match goal with
    | H : context [tsofstep] |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; try external_call_elim.
 
    ret_zero_ptr_false.
    ret_zero_ptr_false.
    ret_zero_ptr_false.
    ret_zero_ptr_false.
  }
Qed.

(** The function initial step of function lock satisfies [Go] *)
Lemma lock_init_step_satify_Gobj :
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
    (Htc_init : Some tc = init_core tge lock_acquire_ident nil)
    (Hsc_init : Some sc = SpecLang.init_core sge lock_acquire_ident nil)
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
  eapply tso_lock_acquire_init_state in Htc_init; eauto.
  destruct Htc_init as [fb [Hfind_symb Hf_init]].
  unfold fundef_init in Hf_init.
  simpl in Hf_init.
  inversion Hf_init; subst.
  eapply spec_lock_acquire_init_state in Hsc_init; eauto.
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
    split; eauto.
    clear - Hrel_tm_gm_vb Hnextblock_eq Hmem_freels Hunbuffer_safe H1 H0 H5 Hm_eq.
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
  do 3 right. eauto.
  
  (* match state *)
  split.
  eapply obj_lock_match; eauto.
  eapply lock_label_match; eauto.
  subst rs0.
  Pregmap_elim.
  eauto.
  clear - Himp_init Hfind_symb.
  inversion Himp_init; subst.
  specialize (H2 lock_acquire_ident).
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

(** [match_tau] holds in function lock *)
Lemma lock_step_satisfy_Gobj :
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
    (Hlock_acq_match_state : lock_match_state sge tge t (sc, sm) (tc, tm))
    (Htm : tm' = (mktsomem (tupdate t b' (tso_buffers tm)) gm')),
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
    ) \/
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
  intros.

  Ltac solve_mem_strip :=
    try rewrite tupdate_same_eq; eauto;
    match goal with
    | H : embed (memory ?tm) _ _ |- _ => inv H
    end;
    match goal with
    | H : strip _ = memory _ |- _ => rewrite H; eauto
    end. 

  inversion Hlock_acq_match_state; subst.
  {
    (** lock acquire : init step *)
    left.
    eapply lock_init_step_satify_Gobj; eauto.
  }
  {
    (** lock acquire : lock label *)
    left.
    do 3 eexists.
    split. 
    eapply InteractionSemantics.star_refl; eauto.
    left.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst
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
    eapply obj_lock_match.
    eapply mov_Laddr_match; eauto.
    unfold nextinstr.
    match goal with
    | H : rs _ = Vptr _ _ |- _ =>
      rewrite H; eauto
    end.

    split; solve_mem_strip.
    split; eauto.
    eapply obj_emp_fp; eauto.
    external_call_elim.
  }
  { 
    (** lock acquire : movl $L RCX *)
    left.
    do 3 eexists.
    split. 
    eapply InteractionSemantics.star_refl; eauto.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end.

    ptr_elim.
    exec_instr_tso.
    simpl. 
    lets HL : get_lock_ident_from_ge ___; eauto.
    destruct HL as [L HL].

    left; split.

    (* G *)
    unfold Gobj.
    right. right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.

    (* match state *)
    split.
    eapply obj_lock_match.
    eapply set_lock_val; eauto.

    unfold Genv.symbol_address.
    rewrite HL.
    elim_next_intr.
    unfold Genv.symbol_address.
    rewrite HL.    
    unfold nextinstr_nf.
    simpl.
    unfold nextinstr.
    do 6 (rewrite Pregmap.gso; try (intro; tryfalse)).
    eapply Pregmap.gss; eauto.
    
    clear_trivial_eq.
    match goal with
    | H : embed _ _ _ |- _ => rename H into Hembed
    end. 
    solve_m_unchange_objinv tm Hobj_inv.
    match goal with
    | H : strip _ = _, H2 : obj_inv _ _ _ |- _ =>
      clear - H H2; simpls; subst; eauto
    end.

    split;
      try rewrite tupdate_same_eq; eauto.
    split.
    match goal with
    | H : embed (memory ?tm) _ _ |- _ => inv H
    end.
    match goal with
    | H : strip _ = memory _ |- _ => rewrite H; eauto
    end. 
    eapply obj_emp_fp; eauto.
    external_call_elim.
  }
  {
    (** lock acquire : movl $0, RDX *)
    left.
    do 3 eexists.
    split. 
    eapply InteractionSemantics.star_refl; eauto.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end.
 
    ptr_elim.
    exec_instr_tso.
    simpl. 
    
    left; split.

    (* G *)
    unfold Gobj.
    right. right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.

    (* match state *)
    split.
    eapply obj_lock_match.
    eapply lock_acquire_label; eauto.
 
    elim_next_intr.
    clear Htsostep.
    clear_trivial_eq.
    simpl.
    match goal with
    | H : embed _ _ _ |- _ => rename H into Hembed
    end.
    solve_m_unchange_objinv tm Hobj_inv.
    match goal with
    | H : strip _ = _, H2 : obj_inv _ _ _ |- _ =>
      clear - H H2; simpls; subst; eauto
    end.

    split; solve_mem_strip.
    split; eauto.
    eapply obj_emp_fp; eauto.
    external_call_elim.
  }
  {
    (** lock acquire : lock acquire label *)
    left.
    do 3 eexists.
    split. 
    eapply InteractionSemantics.star_refl; eauto.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end.
 
    ptr_elim.
    exec_instr_tso.
    simpl. 
    
    left; split.

    (* G *)
    unfold Gobj.
    right. right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.

    (* match state *)
    split.
    eapply obj_lock_match.
    eapply get_cmp_val; eauto.
 
    elim_next_intr'.
    clear Htsostep.
    clear_trivial_eq.
    simpl.
    match goal with
    | H : embed _ _ _ |- _ => rename H into Hembed
    end.
    solve_m_unchange_objinv tm Hobj_inv.
    match goal with
    | H : strip _ = _, H2 : obj_inv _ _ _ |- _ =>
      clear - H H2; simpls; subst; eauto
    end.

    split; solve_mem_strip.
    split; eauto.
    eapply obj_emp_fp; eauto.
    external_call_elim.
  }
  {
    (** lock acquire : movl $1, %eax *)
    left.
    do 3 eexists.
    split. 
    eapply InteractionSemantics.star_refl; eauto.
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end.
 
    ptr_elim.
    exec_instr_tso.
    simpl. 
    
    left; split.

    (* G *)
    unfold Gobj.
    right. right.
    erewrite tm_unchange; eauto.
    unfold Id; eauto.

    (* match state *)
    split.
    eapply obj_lock_match.
    eapply lock_cmpxchg_match; eauto.

    elim_next_intr.
    clear Htsostep.
    clear_trivial_eq.
    match goal with
    | H : embed _ _ _ |- _ => rename H into Hembed
    end.
    solve_m_unchange_objinv tm Hobj_inv.
    match goal with
    | H : strip _ = _, H2 : obj_inv _ _ _ |- _ =>
      clear - H H2; simpls; subst; eauto
    end.

    split; solve_mem_strip.
    split; eauto.
    eapply obj_emp_fp; eauto.
    external_call_elim.
  }
  { 
    (** lock acquire : lock cmpxchg [RCX] RDX *)
    lets Hunbuffer_safe : lock_acq_unbuffer_safe ___; eauto.
    
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end.
    2 : external_call_elim.
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexe_instr
    end. 
    simpl in Hexe_instr.
    clear_trivial_eq.

    destruct (tso_buffers tm t) eqn:Hbf; tryfalse.
    destruct (Mem.loadv Mint32 fm
                        (eval_addrmode tge (Addrmode (Some RCX) None (inl 0%Z)) rs))
             eqn:Hload_L_val; tryfalse.
    match goal with
    | H1 : @eq val (rs (IR RAX)) Vone,
           H2 : context [rs (IR RAX)] |- _ =>
      rewrite H1 in H2; renames H1 to Hvrax 
    end.
    destruct (Val.cmpu_bool (Mem.valid_pointer fm) Ceq v Vone) eqn:Hcmp;
      tryfalse.
    destruct b; tryfalse.
    {
      lets Ht : ogenv_match_L_addr_eq ___; eauto.
      destruct Ht as [L' [Htge_L Hsge_L]].
      match goal with
      | H1 : Some L = Genv.find_symbol _ lock_L_ident,
             H2 : Genv.find_symbol _ lock_L_ident = Some _ |- _ =>
        rewrite H2 in H1; symmetry in H1; inversion H1; subst
      end.
      clear_trivial_eq.

      assert (Hsge_eq : sge = sG).
      {
        clear - Hspec_init.
        inversion Hspec_init; subst.
        eauto.
      }
      subst.
      
      (** lock succ *)
      match goal with
      | H : rs (IR RDX) = Vzero |- _ =>
        rewrite H in Hexe_instr
      end.
      destruct (Mem.storev Mint32 fm
                           (eval_addrmode tge (Addrmode (Some RCX)
                                                        None (inl 0%Z)) rs) Vzero)
               eqn : Hlock_succ; tryfalse. 
      inversion Hexe_instr; subst.
      clear_trivial_eq.
      clear Htsostep.

      match goal with
      | H : rs (IR RCX) = Vptr _ _ |- _ =>
        rename H into H_L_addr
      end.
      
      assert (H_L_var : v = Vone /\ load Mint32 sm L 0 = Some (Vint Int.one) /\
             exists sm', store Mint32 sm L 0 (Vint Int.zero) = Some sm').
      {    
        clear - Hload_L_val Hcmp H_L_addr Hobj_inv Htge_L Hbf Hembed.
        unfolds Val.cmpu_bool.
        destruct v; tryfalse.
        simpls.
        inversion Hcmp; subst.
        lets Ht : Int.eq_spec ___; eauto.
        match goal with
        | H : Int.eq i Int.one = true |- _ =>
          rewrite H in Ht
        end.
        subst.
        unfold eval_addrmode in Hload_L_val.
        destruct Archi.ptr64 eqn:?; tryfalse.
        simpls eval_addrmode32.
        rewrite Int.add_zero in Hload_L_val.
        rewrite H_L_addr in Hload_L_val.
        simpls.
        rewrite Heqb in Hload_L_val.
        simpls.
        rewrite Ptrofs.add_zero in Hload_L_val.
        assert (Ht : Ptrofs.unsigned (Ptrofs.repr 0) = 0%Z).
        eauto.
        rewrite Ht in Hload_L_val.
        unfolds obj_inv.
        destruct Hobj_inv as [L' [H_L_ge H_L_state]].
        rewrite Htge_L in H_L_ge.
        symmetry in H_L_ge.
        inversion H_L_ge; subst.
        clear_trivial_eq.
        destruct H_L_state as [H_L_state H_store_ok].
        split_and H_store_ok.
        destruct H_L_state as [H_L_state | H_L_state].
        {
          unfolds lock_st.
          split_and H_L_state.
          inversion Hembed; subst.
          eapply load_fm_eq_load_gm in Hload_L_val; eauto.
          match goal with
          | H : load_tsomem _ _ _ _ = Some _ |- _ =>
            rename H into Hload_tsom
          end.
          unfolds load_tsomem.
          destruct tm; simpls.
          subst.
          rewrite Hload_tsom in Hload_L_val.
          tryfalse.
        }
        {
          unfolds unlock_st.
          split_and H_L_state.
          eauto.
        }
      }
      destruct H_L_var as [H_L_var [Hload_L_sm Hstore_L'_sm]].
      subst v.
      destruct Hstore_L'_sm as [sm' Hstore_L'_sm].

      lets Hspec_embed : (Classical_Prop.classic (exists fsm, embed sm fl fsm)).
      destruct Hspec_embed as [Hspec_embed_ex | Hspec_embed_nex].
      {
        destruct Hspec_embed_ex as [fsm Hspec_embed_ex].

        assert (Hspec_m_store : exists fsm',
                   SpecLang.storemax fsm L (Vint Int.zero) = Some fsm' /\
                        embed sm' fl fsm').
        {
          eapply store_gm_store_spec_m; eauto.
        }
        destruct Hspec_m_store as [fsm' [Hspec_m_store Hembed1]].
        
        right.
        do 8 eexists.
        split. 

        {
          (* spec program executes *)
          unfold lock_spec_fn.
          spec_p_exec.
 
          (* seq *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.

          (* assign *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.
          instantiate
            (1 := (fun r' : positive => if peq r' r then Vint Int.zero else te r')).
          eauto.
 
          (* skip *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.

          (* seq *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.

          (* assign *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.
          instantiate
            (1 := (fun r' : positive =>
                     if peq r' x then Vint Int.zero
                     else if peq r' r then Vint Int.zero else te r')).
          eauto.

          (* skip *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.

          (* sseq *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.

          (* while *)
          spec_p_exec.
          inversion Hspec_embed_ex; subst; eauto.
          eapply SpecLang.Eval_btrue; eauto.
          destruct (peq r x) eqn:?; tryfalse; subst; eauto.
          destruct (peq r r) eqn:?; tryfalse; subst; eauto.

          (* atom *) 
          eapply InteractionSemantics.star_step.
          simpl.
          econstructor; eauto.
          inversion Hspec_embed_ex; subst; eauto.
          eapply SpecLang.EntAtomstep; eauto.
          eapply InteractionSemantics.star_refl; eauto.
        }

        (* AtEntAtom *)
        split.
        eauto.

        (* AfterEntAtom *)
        split.
        simpl.
        eauto.
 
        (* exec atom *)
        split.
        (* seq *)
        spec_p_exec.
        inversion Hspec_embed_ex; subst; eauto.
        (* load *)
        spec_p_exec.
        inversion Hspec_embed_ex; subst; eauto.
        {
          instantiate (1 := Vone).
          eapply load_gm_load_spec_m; eauto.
        }
        instantiate
        (
          1 :=
            (fun r' : positive =>
               if peq r' r
               then Vone
               else
                 if peq r' x then Vint Int.zero else
                   if peq r' r then Vint Int.zero else te r')
        ).
        eauto. 
        (* skip *)
        spec_p_exec.
        inversion Hspec_embed_ex; subst; eauto.
        (* store *)  
        spec_p_exec.
        inversion Hspec_embed_ex; subst; eauto.
        eapply InteractionSemantics.star_step; eauto.
        simpl.
        econstructor; eauto.
        instantiate (1 := fsm').
        inversion Hembed1; subst; eauto.
        eapply SpecLang.ExtAtomstep; eauto.
        econstructor; eauto.

        (* AtExtatom *)
        left.
        split.
        simpl; eauto.
        split.
        simpl.
        eauto.
        simpl.
  
        unfolds eval_addrmode.
        destruct Archi.ptr64 eqn:?; tryfalse.
        simpl in Hload_L_val, Hlock_succ.  
        rewrite Int.add_zero in Hload_L_val, Hlock_succ.
        rewrite H_L_addr in Hload_L_val, Hlock_succ.
        simpl in Hload_L_val, Hlock_succ.
        rewrite Heqb in Hload_L_val, Hlock_succ. 
        eapply load_fm_eq_load_gm in Hload_L_val; eauto.
        eapply store_fm_eq_store_gm in Hlock_succ; eauto.
        assert (Ht : Ptrofs.unsigned
                       (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero))
                     = 0%Z).
        eauto.
        rewrite Ht in Hload_L_val, Hlock_succ. 
        assert (Hobj_inv' : obj_inv tge (strip fsm')
                                    {| tso_buffers := tupdate t nil (tso_buffers tm);
                                       memory := strip m |}).
        {
          clear - Hbf Hobj_inv Hstore_L'_sm  Hspec_embed_ex Hsge_L
                      Hspec_m_store Hembed1 Htge_L
                      Hload_L_val H_L_addr Hembed Hlock_succ Hunbuffer_safe.
          inversion Hembed1; subst.
          rewrite buffer_unchange1; eauto.
          unfold obj_inv.
          eexists. 
          split; eauto.
          split.
          left.
          unfold lock_st.
          split.
          eapply gm_store_v_load_same in Hstore_L'_sm.
          eauto.
          split.
          unfolds obj_inv.
          split_and Hobj_inv.
          introv H_buf_clear.
          simpls.  
          match goal with
          | H1 : Genv.find_symbol tge lock_L_ident = Some H |- _ =>
            rewrite Htge_L in H1; inversion H1; subst H
          end. 
          match goal with
          | H : lock_st _ _ _ \/ unlock_st _ _ _ |- _ =>
            rename H into Hst
          end.
          eauto. 
          destruct Hst as [Hlock_st | Hunlock_st].
          { 
            unfolds lock_st.
            split_and Hlock_st.
            match goal with
            | H : load_tsomem _ _ _ _ = Some _ |- _ =>
              rename H into Hload_tsomem
            end.
            unfold load_tsomem in Hload_tsomem.
            destruct tm; simpls.
            inversion Hembed; subst.
            rewrite Hload_tsomem in Hload_L_val.
            tryfalse.
          }
          {
            unfolds unlock_st.
            split_and Hunlock_st.
            match goal with
            | H : _ \/ _ |- _ => rename H into Hunlock_st
            end.
            destruct Hunlock_st as [Hunlock_st1 | Hunlock_st2].
            {
              split_and Hunlock_st1.
              match goal with
              | H : load_tsomem _ _ _ _ = _ |- _ =>
                unfold load_tsomem in H; destruct tm; simpls;
                  rename H into Hload_tsomem
              end.
              inversion Hembed; subst.
              rewrite Hload_tsomem in Hload_L_val.
              tryfalse.
            }
            {
              destruct Hunlock_st2 as [Hload_tsomem HL_not_bf].
              destruct H_buf_clear as [ofs H_buf_clear].
              specialize (HL_not_bf t0 ofs); tryfalse.
            }
          }
    
          clear - Hembed Hlock_succ.
          destruct tm.
          simpls.
          eapply gm_store_v_load_same; eauto.
          split.
          clear - Hstore_L'_sm Hembed1 Hlock_succ.
          intros. 
          inversion Hembed1; subst. 
          eapply gm_store_succ_store_again in Hstore_L'_sm; eauto.
          split.
          intros.
          clear - Hlock_succ.
          simpl.
          eapply gm_store_succ_store_again in Hlock_succ; eauto.
          destruct Hlock_succ as [sm'' Hlock_succ].
          rewrite Hlock_succ.
          eauto.
          simpls.   
          split.  
          rewrite buffer_unchange1 in Hunbuffer_safe; eauto.   
          clear - Hspec_m_store Hobj_inv Hspec_embed_ex Htge_L Hlock_succ Hembed.
          split. 
          intros. 
          eapply speclang_store_impl_obj_mem; eauto.
          inversion Hspec_embed_ex; subst; eauto.
          unfolds obj_inv.
          split_and Hobj_inv; eauto.
          match goal with
          | H1 : Genv.find_symbol _ _ = _,
                 H2 : Genv.find_symbol _ _ = _ |- _ =>
            rewrite H1 in H2; inversion H2; subst; eauto
          end. 
          clear - Hobj_inv Hlock_succ Htge_L Hembed Hspec_m_store Hspec_embed_ex.
          unfolds obj_inv.
          split_and Hobj_inv.
          rewrite Htge_L in H1.
          inversion H1; subst H.
          split.
          introv Hrange.
          eapply H6 in Hrange.
          destruct tm.
          simpls. 
          inversion Hembed; subst.
          rewrite Mem_GMem_access_eq. 
          clear - Hrange Hlock_succ.
          destruct Hrange as [p [Hperm Hperm_order]].
          exists p; split; eauto. 
          eapply store_perm_nochange; eauto.
          introv Hrange.
          eapply H8 with (k := k) (p := p) in Hrange.
          clear - Hspec_embed_ex Hspec_m_store Hrange Hlock_succ
                                 Hembed.
          inversion Hspec_embed_ex; subst.
          destruct Hrange as [Hrange Hrange1].
          split.
          intro.
          contradiction Hrange.
          unfolds GMem.perm.
          unfolds Memperm.perm_order'.
          clear - Hspec_m_store H0. 
          try rewrite <- Mem_GMem_access_eq in *.
          destruct ((Mem.mem_access fsm') !! L ofs k) eqn:?; simpls; tryfalse.
          eapply speclang_not_change_perm in Hspec_m_store.
          rewrite <- Hspec_m_store in Heqo.
          rewrite Heqo; eauto.
          intro.
          contradiction Hrange1.
          unfolds GMem.perm.
          inv Hembed.
          unfolds store.
Require Import FMemLemmas.
ex_match2.
destruct m; unfolds strip; simpls.
          inversion Hlock_succ; subst; simpls.
          rewrite <- H2; simpls; eauto.
        }
        
        split.
        (* G *)
        unfold Gobj.
        left.
        unfold G_lock.
        eexists.
        split; eauto.
        split; eauto.
        split.
        eapply Hobj_inv'; eauto.
        left.
        unfold lock_succ.
        split; eauto.
        split; eauto.
        clear - Hembed Hload_L_val.
        inversion Hembed; subst.
        destruct tm.
        simpls.
        subst.
        eauto.
        rewrite buffer_unchange1; eauto. 
        clear - Hlock_succ Hembed Hbf Hspec_m_store Hspec_embed_ex.
        destruct tm.
        simpls.
        inversion Hembed; subst.
        unfold Vzero in Hlock_succ.
        rewrite Hlock_succ.
        split; eauto.
        inversion Hspec_embed_ex; subst.
        eapply SpecLang_store_store_gm; eauto.

        (* match state *)
        split. eapply obj_lock_match.
        eapply jne_enter_ZF_1_match; eauto.
        elim_next_intr'.
        simpl.
        destruct (peq r r) eqn:?; tryfalse.
        eauto.

        inv Hembed1. inv Hspec_embed_ex. inv Hembed.
        rewrite tupdate_same_eq; eauto.  
        clear - Hno_conflict Hrel_tm_gm_vb Hstore_L'_sm Hlock_succ Hbf H1 Hcmp Hload_L_val H_L_addr Hvrax Hobj_inv Hsge_L Htge_L.
        split; eauto. split.
        unfolds rel_tm_gm_vb.
        introv Hget_block Happly_buffer; simpls.
        try rewrite Hbf in *.
        eapply Hrel_tm_gm_vb in Hget_block.
        2 : instantiate (1 := memory tm); simpls; eauto.
        simpl in Happly_buffer; inv Happly_buffer.
        eapply store_vb_eq in Hlock_succ.
        eapply store_vb_eq in Hstore_L'_sm.
        repeat rewrite mem_strip_gm_vb_eq in *.
        split; intros Hvb.
        rewrite <- Hlock_succ in Hvb; rewrite H1 in Hvb.
        eapply Hget_block in Hvb.
        rewrite <- Hstore_L'_sm; eauto.
        rewrite <- Hlock_succ; rewrite H1.
        eapply Hget_block; rewrite Hstore_L'_sm; eauto.
        eapply obj_valid_block_fp; eauto.
        unfolds Mem.loadv; simpls.
        rewrite H_L_addr; simpl.
        destruct (Archi.ptr64) eqn:?; tryfalse.
        change (Ptrofs.unsigned
                  (Ptrofs.add (Ptrofs.repr 0)
                              (Ptrofs.of_int (Int.add Int.zero (Int.repr 0))))) with 0%Z.
        unfolds obj_inv.
        destruct Hobj_inv as (L' & Htge_L' & Hobj_inv).
        rewrite Htge_L in Htge_L'; inv Htge_L'.
        split_and Hobj_inv.
        eapply load_gm_embed_load_fm in Hload_L_val; eauto.
        rewrite Hload_L_val.
        rewrite Hvrax; simpl.
        ex_match2.
        change (Ptrofs.unsigned
                (Ptrofs.add (Ptrofs.repr 0)
                            (Ptrofs.of_int (Int.add Int.zero (Int.repr 0))))) with 0%Z.
        unfold load_fp, store_fp, FP.locs, FP.union; simpl.
        unfold Locs.belongsto, Locs.union, range_locset; simpl.
        intros.
        ex_match2; tryfalse; subst.
        destruct (zle 0 ofs) eqn:?; destruct (zlt ofs 4) eqn:?;
                 simpls; tryfalse.
        left. 
        eapply H4; eauto.
        rewrite H1; clear - H5.
        destruct tm; simpls; eauto.
        econstructor; eauto.
      }
      {
        left.
        do 3 eexists.
        split.
        eapply InteractionSemantics.star_refl; eauto.
        right.
        clear - Hspec_embed_nex.
        split.
        introv Hsem.
        inversion Hsem; subst.
        eapply Hspec_embed_nex; eauto.
        simpl; eauto.
      }
    }
    { 
      (** lock fail *)
      inversion Hexe_instr; subst.
      clear_trivial_eq.
      left.
      do 3 eexists.
      split.
      eapply InteractionSemantics.star_refl; eauto.
      simpl.
      rewrite buffer_unchange1; eauto.
      left; split.

      (* G *)
      unfold Gobj.
      right; right; left.
      clear - Hembed Hobj_inv.
      inversion Hembed; subst.
      destruct tm. 
      simpls; subst; eauto.
      unfold Id; eauto.

      (* match state *)
      split.
      eapply obj_lock_match; eauto.
      eapply jne_enter_ZF_0_match; eauto.
      unfold nextinstr.
      rewrite Pregmap.gss; try solve [intro; tryfalse].
      do 2 (rewrite Pregmap.gso; try solve [intro; tryfalse]).
      match goal with
      | H : rs PC = Vptr _ _ |- _ =>
        rewrite H; unfold Val.offset_ptr
      end.
      eauto. 
      solve_m_unchange_objinv tm Hobj_inv.
      inv Hembed.
      match goal with
      | H : strip _ = memory _ |- _ => rewrite H
      end.
      split; eauto.
      split; eauto.

      rewrite Hload_L_val, Hvrax, Hcmp; simpl.
      unfold loadv_fp, eval_addrmode.
      destruct (Archi.ptr64) eqn:?; tryfalse.
      simpl.
      change (Int.add Int.zero (Int.repr 0)) with Int.zero.
      rewrite H7; simpl.
      destruct (Archi.ptr64); tryfalse.
      change (Ptrofs.unsigned
                (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero)))
        with 0%Z.
      unfold Mem.loadv, eval_addrmode in Hload_L_val.
      ex_match2; tryfalse.
      eapply obj_valid_block_fp; eauto. 
      eapply load_fm_eq_load_gm in Hload_L_val.
      rewrite H0 in Hload_L_val.
      unfold eval_addrmode32 in Hx.
      rewrite H7 in Hx; simpl in Hx.
      ex_match2.
      change (Ptrofs.add (Ptrofs.repr 0)
                         (Ptrofs.of_int (Int.add Int.zero (Int.repr 0)))) with Ptrofs.zero in Hx.
      inv Hx. 
      change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in Hload_L_val.
      eapply obj_inv_impl_load_zero_or_one in Hload_L_val; eauto.
      destruct Hload_L_val as [Hv_one | Hv_zero]; subst. 
      simpl in Hcmp; inv Hcmp.
      intros.
      unfolds Locs.belongsto, FP.locs, FP.union, load_fp; simpl in H.
      unfolds Locs.union, range_locset; simpl in H.
      ex_match2; subst.
      destruct (zle 0 ofs) eqn:?; destruct (zlt ofs 4) eqn:?; tryfalse.
      left.
      clear - Hobj_inv H10 l l0.
      unfolds obj_inv.
      destruct Hobj_inv as [L Hobj_inv].
      split_and Hobj_inv.
      rewrite <- H10 in H; inv H; eauto.
    }
  }
  {
    (** lock acquire : je enter [ZF = 1] *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end.
    2 : external_call_elim.
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexe_instr
    end.
    simpl in Hexe_instr. 
   
    match goal with
    | H1 : rs (CR ZF) = _,
      H2 : rs PC = _ |- _ => renames H1 to Hzf, H2 to Hpc
    end.
    rewrite Hzf in Hexe_instr.
    rewrite Int.eq_true in Hexe_instr.
    unfold tso_goto_label in Hexe_instr.
    simpl in Hexe_instr. 
    find_label.
    destruct (peq enter_lbl lock_lbl) eqn:?; tryfalse.
    destruct (peq enter_lbl lock_acquire_lbl) eqn:?; tryfalse.
    destruct (peq enter_lbl spin_lbl) eqn:?; tryfalse.
    rewrite Hpc in Hexe_instr.
    inversion Hexe_instr; subst.
    clear_trivial_eq.
    simpl. 
 
    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl.
    rewrite buffer_unchange.

    left; split.
    (* G *)
    unfold Gobj.
    right; right.
    clear - Hembed Hobj_inv.
    inversion Hembed; subst.
    destruct tm.
    simpls. 
    unfold Id; subst; eauto.

    (* match state *)
    split.
    eapply obj_lock_match; eauto.
    eapply set_ret_val; eauto.
    Pregmap_elim. eauto.
    solve_m_unchange_objinv tm Hobj_inv.
    split; solve_mem_strip.
    split; eauto.
    eapply obj_emp_fp; eauto.
  }
  {
    (** lock acquire : je enter [ZF = 0] *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end.
    2 : external_call_elim.
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexe_instr
    end.
    simpl in Hexe_instr.

    match goal with
    | H1 : rs (CR ZF) = _,
      H2 : rs PC = _ |- _ => renames H1 to Hzf, H2 to Hpc
    end.
    rewrite Hzf in Hexe_instr.
    assert (Ht : Int.eq Int.zero Int.one = false).
    eauto.
    rewrite Ht in Hexe_instr.
    inversion Hexe_instr; subst.
    simpl. 
    clear_trivial_eq.
    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl.
    rewrite buffer_unchange.

    left; split.
    (* G *)
    unfold Gobj.
    right; right.
    clear - Hembed Hobj_inv.
    inversion Hembed; subst.
    destruct tm.
    simpls.
    unfold Id; subst; eauto.

    (* match state *)
    split.
    eapply obj_lock_match; eauto.
    eapply spin_label_match; eauto.
    elim_next_intr'.
    solve_m_unchange_objinv tm Hobj_inv.
    split; solve_mem_strip. split; eauto.
    eapply obj_emp_fp; eauto.
  }
  {
    (** lock_acquire : spain label *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end.
    2 : external_call_elim.
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexe_instr
    end.
    simpl in Hexe_instr.
    inversion Hexe_instr; subst.
    clear_trivial_eq.

    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl; eauto.

    match goal with
    | H1 : Genv.find_funct_ptr _ _ = _,
           H2 : ?rs PC = Vptr _ _,
                H3 : find_instr _ _ = _ |- _ =>
      renames H1 to Hfind_b, H2 to Hpc, H3 to Hfind_instr
    end.
    clear Htsostep.
    
    left; split.
    (* G *)
    unfold Gobj.
    right. right.
    simpl.
    rewrite buffer_unchange; eauto.
    inversion Hembed; subst.
    destruct tm.
    simpl.
    match goal with
    | H : strip _ = _ |- _ =>
      simpl in H; subst
    end.
    unfold Id. eauto.

    (* match_state *)
    split. eapply obj_lock_match.
    simpl.
    rewrite buffer_unchange; eauto.
    eapply get_lock_var; eauto.
    unfold nextinstr.
    rewrite Pregmap.gss.
    rewrite Hpc.
    simpl.
    eauto.
    destruct tm.
    simpl.
    simpl in Hembed.
    inversion Hembed; subst.
    eauto.
    simpl.
    split; solve_mem_strip.
    split; eauto.
    eapply obj_emp_fp; eauto.
  }
  { 
    (** lock acquire : movl [RCX] RBX  *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end. 
    2 : external_call_elim.
    clear_trivial_eq. 
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexe_instr
    end.
    simpl in Hexe_instr.
    inversion Hexe_instr; subst.
    clear_trivial_eq.

    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl; eauto.
    rename H0 into Hexec_load_tso.
    unfold exec_load_TSO in Hexec_load_tso.
    unfold eval_addrmode in Hexec_load_tso.
    destruct Archi.ptr64 eqn:?; tryfalse.
    unfold eval_addrmode32 in Hexec_load_tso. 
    destruct
      (
        tsoloadv Mint32
                 {| tbuffer := tso_buffers tm t; fmemory := fm |}
                 (Val.add (rs RCX)
                          (Val.add (Vint Int.zero) (Vint (Int.repr 0))))
      ) eqn:Htso_load; tryfalse.
    inversion Hexec_load_tso; tryfalse; subst.
    simpl.
    inversion Hembed; subst.
    clear Htsostep.
    
    left; split.
    (* G *)
    unfold Gobj.
    right. right. left.
    destruct tm.
    match goal with
    | H : strip _ = _ |- _ =>
      simpl in H; subst
    end. 
    simpl.
    unfold Id.
    rewrite buffer_unchange'.
    split; eauto.

    (* match state *) 
    split. eapply obj_lock_match. 
    eapply cmp_Lvar_match; eauto.
    elim_next_intr.

    match goal with
    | H : rs (IR RCX) = Vptr _ _, H2 : _ = Genv.find_symbol _ lock_L_ident |- _ =>
      renames H to HR8, H2 to H_L_addr
    end.  
    clear - Hobj_inv Hembed HR8 H_L_addr Htso_load.
    rewrite HR8 in Htso_load.
    simpls.
    unfolds obj_inv.
    destruct Archi.ptr64 eqn:?; tryfalse.
    assert (Ht : Ptrofs.add (Ptrofs.repr 0)
                            (Ptrofs.of_int (Int.add Int.zero (Int.repr 0))) =
                 Ptrofs.repr 0); eauto.
    rewrite Ht in Htso_load.
    clear Ht.
    split_and Hobj_inv.
    match goal with
    | H : lock_st _ _ _ \/ unlock_st _ _ _ |- _ =>
      destruct H as [Hst | Hst]
    end.
    {
      unfolds lock_st.
      split_and Hst.
      match goal with
      | H1 : Genv.find_symbol _ lock_L_ident = Some _,
        H2 : load_tsomem _ _ _ _ = _ |- _ =>
        rewrite <- H_L_addr in H1; inversion H1; subst H;
          renames H2 to Hload_tsomem
      end.
      unfolds load_tsomem.
      destruct tm.
      inversion Hembed.
      simpls.
      clear_trivial_eq.
      eapply tsoloadv_not_in_bf_load_gm_eq in Htso_load; eauto.
      rewrite Hload_tsomem in Htso_load.
      inversion Htso_load; subst.
      right.
      unfold nextinstr_nf, nextinstr.
      simpl.
      Pregmap_elim.
      eauto.
    }
    {
      unfolds unlock_st.
      split_and Hst.
      match goal with
      | H : _ \/ _ |- _ =>
        destruct H as [Hst | Hst]
      end.
      {
        split_and Hst.
        match goal with
        | H1 : Genv.find_symbol _ lock_L_ident = Some _,
               H2 : load_tsomem _ _ _ _ = _ |- _ =>
          rewrite <- H_L_addr in H1; inversion H1; subst H;
            renames H2 to Hload_tsomem
        end. 
        unfolds load_tsomem.
        destruct tm.
        inversion Hembed.
        simpls.   
        clear_trivial_eq. 
        renames H7 to t''.  
        destruct (Pos.eq_dec t t'') eqn:?; try subst t''; eauto.
        eapply in_buffer_count_one_load2 with (n := Int.one) in Htso_load; eauto.
        eapply tsoloadv_not_in_bf_load_gm_eq in Htso_load; eauto.
        rewrite Hload_tsomem in Htso_load.
        inversion Htso_load; subst.
        unfold nextinstr_nf, nextinstr.
        simpl.
        Pregmap_elim.
        eauto.
        assert (Hneq : t'' <> t); eauto.
        intro H_in_buffer.
        destruct H_in_buffer as [ofs H_in_buffer].
        eapply H12 with (ofs := ofs) in Hneq; tryfalse.
      }
      {
        destruct Hst as [Hload_tsomem Hnot_bf].
        match goal with
        | H1 : Genv.find_symbol _ lock_L_ident = Some _,
               H2 : load_tsomem _ _ _ _ = _ |- _ =>
          rewrite <- H_L_addr in H1; inversion H1; subst H;
            renames H2 to Hload_tsomem
        end.
        unfolds load_tsomem.
        destruct tm.
        inversion Hembed.
        simpls.
        clear_trivial_eq.
        eapply tsoloadv_not_in_bf_load_gm_eq in Htso_load; eauto.
        rewrite Hload_tsomem in Htso_load.
        inversion Htso_load; subst.
        left.
        unfold nextinstr_nf, nextinstr.
        simpl.
        Pregmap_elim.
        eauto.
        clear - Hnot_bf.
        intro H_in_bf; destruct H_in_bf as [ofs H_in_bf].
        specialize (Hnot_bf t ofs); tryfalse.
      }
    }
    
    solve_m_unchange_objinv tm Hobj_inv.
    split; solve_mem_strip.
    split; eauto.
    unfold exec_load_fp, loadv_fp, eval_addrmode.
    destruct (Archi.ptr64); tryfalse; simpl.
    change (Int.add Int.zero (Int.repr 0)) with Int.zero.
    rewrite H7; simpl.
    ex_match2.
    change (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.of_int Int.zero))
           with Ptrofs.zero in Hx.
    inv Hx.
    unfold load_fp, range_locset.
    eapply obj_valid_block_fp; eauto.
    unfold FP.locs, Locs.belongsto, Locs.union; simpl.
    change (Ptrofs.unsigned Ptrofs.zero) with 0%Z; simpl.
    intros.
    ex_match2; subst.
    destruct (zle 0 ofs); destruct (zlt ofs 4); tryfalse.
    left.
    clear - H9 Hobj_inv l l0.
    unfolds obj_inv.
    destruct Hobj_inv as (L & Hobj_inv).
    split_and Hobj_inv.
    rewrite <- H9 in H; inv H.
    eapply H4; eauto.
  }
  {
    (* lock acqurie : cmp RBX $0 *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end. 
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end. 
    2 : external_call_elim.
    clear_trivial_eq. 
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexe_instr
    end.  
    simpl in Hexe_instr.
    ex_match2.
    match goal with
    | H : Next _ _ = Next _ _ |- _ => inv H
    end.
    clear_trivial_eq.
    simpl.
    clear Htsostep.

    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl; eauto.
    left; split.

    (* G *) 
    unfold Gobj.
    right. right.
    rewrite buffer_unchange; eauto.
    destruct tm.
    simpl in Hembed.
    simpl.
    unfold Id.
    inversion Hembed; subst.
    eauto.

    (* match_state *)
    split. simpl.
    eapply obj_lock_match.
    eapply je_spin_match; eauto.
    unfold compare_ints_TSO.
    elim_next_intr'.
    match goal with
    | H : rs (IR RBX) = _ \/ rs (IR RBX) = _ |- _ =>
      destruct H as [H | H]; rewrite H; simpl; eauto
    end.
    solve_m_unchange_objinv tm Hobj_inv.
    split; solve_mem_strip. split; eauto.
    unfold compare_ints_TSO_fp; simpl.
    destruct H9 as [H9 | H9]; rewrite H9; simpl; rewrite GDefLemmas.fp_union_emp_l; econstructor; eauto.
  }
  {
    (** lock acquire : je spin *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end. 
    2 : external_call_elim.
    clear_trivial_eq. 
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexe_instr
    end.
    simpl in Hexe_instr.
    inversion Hexe_instr; subst.
    clear_trivial_eq.
    clear Htsostep.
    
    destruct (rs ZF) eqn:Hzf; tryfalse.
    
    destruct (Int.eq i Int.one) eqn:Heq1; tryfalse.
    {
      (* jmp *)  
      match goal with
      | H: _ = Next _ _ |- _ =>
        clear H
      end.
      simpl in Hexe_instr.
      unfold tso_goto_label in Hexe_instr.
      simpl in Hexe_instr.
      find_label.
      destruct (peq spin_lbl lock_lbl); tryfalse.
      destruct (peq spin_lbl lock_acquire_lbl); tryfalse.
      destruct (rs PC) eqn:Hpc; tryfalse.
      inversion Hexe_instr; subst.
      simpl.
      clear_trivial_eq.

      left.
      do 3 eexists.
      split.
      eapply InteractionSemantics.star_refl; eauto.
 
      left; split.
      (* G *) 
      unfold Gobj.
      right. right. left.
      rewrite buffer_unchange.
      inversion Hembed; subst.
      destruct tm.
      match goal with
      | H : strip _ = _ |- _ =>
        clear - H Hobj_inv; simpls; subst; unfold Id; eauto
      end. 

      (* match state *)
      split.
      rewrite buffer_unchange.
      match goal with
      | H : Vptr _ _ = Vptr _ _ |- _ =>
        inversion H; subst
      end. 
      eapply obj_lock_match.
      eapply get_lock_var; eauto.
      rewrite Pregmap.gss; eauto.
      solve_m_unchange_objinv tm Hobj_inv.
      split; solve_mem_strip. split; eauto.
      econstructor; eauto.
    }
    {
      clear H0.
      simpl in Hexe_instr.
      inversion Hexe_instr; subst.
      simpl.
      clear_trivial_eq.
      left.
      do 3 eexists.
      split.
      eapply InteractionSemantics.star_refl.

      (* G *)
      left; split.
      unfold Gobj.
      right; right.
      inversion Hembed; subst; eauto.
      unfold Id.
      rewrite buffer_unchange.
      destruct tm.
      match goal with
      | H : strip _ = _ |- _ =>
        simpl in H; subst; eauto
      end.

      (* match state *)
      split.
      eapply obj_lock_match; eauto.
      eapply jmp_lock_match; eauto.
      elim_next_intr'.
      solve_m_unchange_objinv tm Hobj_inv.
      split; solve_mem_strip. split; eauto.
      econstructor; eauto.
    }
  }
  {
    (** lock acquire : jmp lock_acquire *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end. 
    2 : external_call_elim. 
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = Next _ _ |- _ =>
      rename H into Hexec_instr_TSO
    end.
    simpl in Hexec_instr_TSO.
    unfold tso_goto_label in Hexec_instr_TSO.
    simpl in Hexec_instr_TSO.
    find_label.
    destruct (peq lock_acquire_lbl lock_lbl) eqn:?; tryfalse.
    match goal with
    | H : _ PC = Vptr _ _ |- _ =>
      rewrite H in Hexec_instr_TSO; simpl in H
    end.
    inversion Hexec_instr_TSO; subst.
    simpl.
    clear_trivial_eq.

    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl.

    left; split.
    (* G *) 
    unfold Gobj.
    right; right.
    inversion Hembed; subst.
    unfold Id.
    destruct tm.
    match goal with
    | H : strip _ = _ |- _ => rewrite H; rewrite buffer_unchange; eauto
    end.
     
    (* match state *)
    split.
    rewrite buffer_unchange.
    eapply obj_lock_match; eauto.
    eapply get_cmp_val; eauto.
    rewrite Pregmap.gss; eauto.
    solve_m_unchange_objinv tm Hobj_inv.
    split; solve_mem_strip. split; eauto.
    econstructor; eauto.
  }
  {
    (** lock acquire : enter label *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end. 
    2 : external_call_elim.
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexec_instr_TSO
    end.
    simpl in Hexec_instr_TSO.
    inversion Hexec_instr_TSO; subst.
    clear_trivial_eq.
    simpl.
    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl.

    left; split.
    (* G *)
    unfold Gobj.
    right; right; left.
    rewrite buffer_unchange.
    inversion Hembed; subst.
    unfold Id.
    destruct tm. 
    match goal with
    | H : strip _ = _ |- _ =>
      clear - H Hobj_inv; simpls; subst; eauto
    end.

    (* match state *)
    split.
    eapply obj_lock_match; eauto.
    eapply set_ret_val; eauto.
    elim_next_intr'.
    solve_m_unchange_objinv tm Hobj_inv.
    split; solve_mem_strip. split; eauto.
    econstructor; eauto.
  }
  {
    (** lock acquire : mov $0 RAX *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end. 
    2 : external_call_elim.
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexec_instr_TSO
    end.
    simpl in Hexec_instr_TSO.
    inversion Hexec_instr_TSO; subst.
    simpl.
    clear_trivial_eq.
    clear Htsostep.
    left.
    do 3 eexists.
    split.
    eapply InteractionSemantics.star_refl; eauto.

    left; split.
    (* G *)
    unfold Gobj.
    right; right; left.
    inversion Hembed; subst.
    unfold Id.
    rewrite buffer_unchange.
    destruct tm.
    match goal with
    | H : strip _ = _ |- _ =>
      clear - H Hobj_inv; simpls; subst; eauto
    end.

    (* match state *)
    split.
    eapply obj_lock_match; eauto.
    eapply lock_retl_match; eauto.
    elim_next_intr.
    solve_m_unchange_objinv tm Hobj_inv.
    split; solve_mem_strip. split; eauto.
    econstructor; eauto.
  }
  {
    (** lock acquire : retl *)
    inversion Htsostep; subst.
    match goal with
    | H1 : obj_inv _ _ _,
           H2 : embed _ _ _ |- _ =>
      renames H1 to Hobj_inv, H2 to Hembed
    end.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; subst; try ptr_elim; clear H
    end. 
    2 : external_call_elim.
    clear_trivial_eq.
    match goal with
    | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
      rename H into Hexec_instr_TSO
    end.
    simpl in Hexec_instr_TSO.
    inversion Hexec_instr_TSO; subst.
    simpl.
    clear_trivial_eq.
    clear Htsostep.
    left. 
    lets Hspec_embed : (Classical_Prop.classic (exists fsm, embed sm fl fsm)).
    destruct Hspec_embed as [Hspec_embed_ex | Hspec_embed_nex].
    {
      destruct Hspec_embed_ex as [fsm Hspec_embed_ex].
      do 3 eexists.
      split.

      (* skip *)
      spec_p_exec.

      (* while *) 
      eapply InteractionSemantics.star_step; eauto.
      econstructor; eauto. 
      inversion Hspec_embed_ex; subst; eauto.
      econstructor; eauto.
      eapply SpecLang.Swhile_false; eauto.
      eapply SpecLang.Eval_bfalse.
      match goal with
      | H : te _ = Vone |- _ =>
        clear - H; introv Hcontr; rewrite H in Hcontr; tryfalse
      end.
 
      (* skip *)
      spec_p_exec.
      inversion Hspec_embed_ex; subst; eauto.

      (* skip *)
      spec_p_exec.
      inversion Hspec_embed_ex; subst; eauto.
      econstructor; eauto.       
 
      left.
      split.
      (* G *)  
      unfold Gobj.
      right; right.
      clear - Hembed Hspec_embed_ex Hobj_inv.
      inversion Hembed; subst.
      rewrite buffer_unchange; eauto.
      destruct tm.
      simpls.
      subst.
      unfold Id; eauto.
      inversion Hspec_embed_ex; subst; eauto.
   
      (* match state *)
      split.
      inversion Hspec_embed_ex; subst.
      eapply obj_lock_match; eauto.
      eapply lock_halt_match; eauto.
      solve_m_unchange_objinv tm Hobj_inv.
      solve_mem_strip.
      split; inv Hspec_embed_ex; eauto.
      split; eauto.
      econstructor; eauto.
    }
    {
      do 3 eexists.
      split.
      eapply InteractionSemantics.star_refl; eauto.
      right.
      split.
      introv Hcontr.
      inversion Hcontr; subst.
      eapply Hspec_embed_nex; eauto.
      simpl; eauto.
    }
  }
  {
    (** module halt *)
    inversion Htsostep; subst.
    match goal with
    | H : tsofstep _ _ _ _ _ _ |- _ =>
      inversion H; try solve [ptr_elim]; subst
    end; ret_zero_ptr_false.
  }
Qed.

Hint Resolve lock_init_match lock_label_match mov_Laddr_match set_lock_val
     lock_acquire_label get_cmp_val lock_cmpxchg_match jne_enter_ZF_1_match
     jne_enter_ZF_0_match spin_label_match get_lock_var cmp_Lvar_match
     je_spin_match jmp_lock_match enter_label_match set_ret_val
     lock_retl_match lock_halt_match
  : lock_match.

(** [match_rely] holds in function lock *)
Lemma lock_acquire_rely :
  forall t sc sm sm' tc tm tm' sge sG tge
    (Hspec_init : InteractionSemantics.init_genv
                    SpecLang.speclang lock_comp_unit sge sG)
    (Himp_init : init_genv lock_comp_tso_unit tge)
    (Hlock_match : lock_match_state sge tge t (sc, sm) (tc, tm))
    (Hrely_step : Robj tge t sm tm sm' tm'),
    lock_match_state sge tge t (sc, sm') (tc, tm').
Proof.
  intros.
  eapply R_impl_I_I in Hrely_step; eauto.
  destruct Hrely_step.
  inversion Hlock_match; subst; eauto with lock_match.
Qed.