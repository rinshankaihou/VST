Require Import mathcomp.ssreflect.fintype List.
Require Import Coqlib Maps Globalenvs
        Blockset Footprint InteractionSemantics GAST 
        ReachClose LDSim AuxLDSim Invs GlobDefs GSimDefs GlobDSim.

Lemma list_forall2_nth_rel:
  forall A B (P: A -> B -> Prop) l1 l2,
    list_forall2 P l1 l2 ->
    forall n, option_rel P (nth_error l1 n) (nth_error l2 n).
Proof.
  clear. induction 1; intros; destruct n; simpl; try constructor; auto.
Qed.

Definition existTeq := ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2.

(** * Compositionality of local simulations *)

(** This file defines and proves compositionality of local simulations.
    It says when modules of source and target programs are locally simulated, 
    then we could deduce a global downward simulation on whole programs.
 *)

Definition reach_close' {NL} {L} (c : @cunit NL L): Prop :=
  reach_close (c.(cu L)).


Definition rc_cunits {NL: nat} {L: @langs NL} (cus: cunits L) : Prop :=
  Forall reach_close' cus.

Definition ldsims {NL: nat} {L: @langs NL} scus tcus : Prop :=
  list_forall2 (fun scu tcu => ldsim scu.(cu L) tcu.(cu L)) scus tcus.

Definition ldsims_aux {NL: nat} {L: @langs NL} scus tcus : Prop :=
  list_forall2 (fun scu tcu => ldsim_aux scu.(cu L) tcu.(cu L)) scus tcus.

Lemma ldsim_rc_ldsim_aux_list:
  forall (NL: nat) (L: @langs NL) (scu tcu: cunits L),
    wd_langs scu ->
    ldsims scu tcu ->
    rc_cunits scu ->
    ldsims_aux scu tcu.
Proof.
  intros NL L. 
  induction scu; intros.
  { destruct tcu. constructor. inversion H0. }
  { inversion H0. inversion H1. subst. clear H1 H0.
    constructor; auto. apply ldsim_rc_ldsim_aux; auto. apply H. simpl. auto.
    apply IHscu; auto. intros cu IN. apply H. simpl. auto.
  }
Qed.


Definition fn_preserved {NL: nat} {L:@langs NL} (scus tcus: cunits L) : Prop :=
  list_forall2 (fun scu tcu: cunit L => internal_fn (L (lid L scu)) ((cu L scu))
                                     = internal_fn (L (lid L tcu)) ((cu L tcu)))
               scus tcus.

Lemma fn_preserved_get_mod_eq:
  forall NL (L: @langs NL) (scus tcus: cunits L) SGE TGE,
    fn_preserved scus tcus ->
    GlobEnv.init scus SGE ->
    GlobEnv.init tcus TGE ->
    forall fnid,
      option_rel (fun ord1 ord2 => Nat.eq (nat_of_ord ord1) (nat_of_ord ord2))
                 (GlobEnv.get_mod SGE fnid) (GlobEnv.get_mod TGE fnid).
Proof.
  intros.
  remember (fun (ir: nat * option nat) (cui: cunit L)
                => let (i, res) := ir in
                  if res then (S i, res)
                  else
                    if in_dec peq fnid (internal_fn (L (lid L cui)) (cu L cui))
                    then (S i, Some i)
                    else (S i, res)) as FUN.
  assert (fold_left FUN scus (0%nat, None)
                = fold_left FUN tcus (0%nat, None)).
  { generalize HeqFUN H (0%nat, @None nat). clear. intros HFUN Hfn.
    induction Hfn; simpl; auto.
    intros. replace (FUN p a1) with (FUN p b1). auto.
    subst FUN. destruct p. destruct o; auto.
    rewrite H. auto. }
  destruct (GlobEnv.get_mod SGE fnid) as [[m LTM]|] eqn:GETS;
    destruct (GlobEnv.get_mod TGE fnid) as [[m' LTM']|] eqn:GETT;
    try erewrite GlobEnv.get_mod_init in GETS;
    try erewrite GlobEnv.get_mod_init in GETT; eauto;
      try constructor; rewrite <- HeqFUN in *; simpl in *.
  rewrite H2 in GETS. congruence.
  exfalso. rewrite H2 in GETS.
  erewrite GlobEnv.mod_num, list_forall2_length, <- GlobEnv.mod_num in LTM; eauto.
  replace m with (nat_of_ord (Ordinal LTM)) in GETS by auto.
  subst. erewrite <- GlobEnv.get_mod_init in GETS; eauto. congruence.
  exfalso. rewrite <- H2 in GETT.
  erewrite GlobEnv.mod_num in LTM'; eauto.
  erewrite <- list_forall2_length in LTM'; eauto.
  erewrite <- GlobEnv.mod_num in LTM'; eauto.
  replace m' with (nat_of_ord (Ordinal LTM')) in GETT by auto.
  subst. erewrite <- GlobEnv.get_mod_init in GETT; eauto. congruence.
Qed.
  

(** TODO: move to ? *)
Lemma init_tp_next:
  forall GE e thdp,
    @ThreadPool.init GE e thdp ->
    (Pos.to_nat (ThreadPool.next_tid thdp) - 1)%nat = length e.
Proof.
  induction e; intros thdp INIT; inv INIT; simpl; auto.
  apply IHe in H2. rewrite <- H2. generalize (ThreadPool.next_tid thdp0). clear.
  intro. rewrite minus_Sn_m, Pos2Nat.inj_succ; auto.
  apply Pos2Nat.is_pos.
Qed.

Lemma init_get_valid_spec:
  forall GE e tp t,
    @ThreadPool.init GE e tp ->
    ThreadPool.valid_tid tp t ->
    exists funid mid cc fid,
      nth_error (rev e) (Pos.to_nat t - 1)%nat = Some funid
      /\ GlobEnv.get_mod GE funid = Some mid
      (* /\ FLists.thread_flmap (GlobEnv.freelists GE) t 0 = fid *)
      /\ init_core (ModSem.lang (GlobEnv.modules GE mid))
                  (ModSem.Ge (GlobEnv.modules GE mid)) funid nil
        = Some cc
      /\ ThreadPool.get_cs tp t = Some (Core.Build_t mid cc AST.signature_main fid :: nil).
Proof.
  clear. induction e; intros.
  inversion H. subst. exfalso. eapply Pos.nlt_1_r; eauto.
  inversion H. subst. 
  unfold ThreadPool.spawn, ThreadPool.valid_tid in H0. simpl in H0.
  apply Plt_succ_inv in H0. destruct H0 as [VALID|NEW].
  specialize (IHe thdp t H4 VALID). destruct IHe as (funid & mid & cc' & fid & NTH & GETMOD (*& GETFID*) & INIT & GETCS).
  exists funid, mid, cc', fid. split. simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
  split; auto. split; auto. unfold ThreadPool.spawn, ThreadPool.get_cs in *; simpl in *.
  rewrite PMap.gso. auto. intro; subst. eapply Plt_ne; eauto.
  (** NEW *)
  exploit init_tp_next; eauto. intro.
  subst. eexists a, m_id, cc, _. split. simpl. rewrite nth_error_app2.
  rewrite H0. rewrite rev_length, Nat.sub_diag. auto.
  rewrite rev_length, <- H0. auto.
  split; auto. split; auto. (*split; auto.*) unfold ThreadPool.spawn, ThreadPool.get_cs in *; simpl in *.
  rewrite PMap.gss. unfold FLists.get_tfid. eauto.
Qed.


Section Compositionality.
  (* NL languages, M modules, N threads *)
  Context {NL: nat}.
  (* Languages *)
  Variable (L: @langs NL).
  (* Compilation units of source/target program*)
  Variable (scunits tcunits: @cunits NL L).
  
  (* Thread entries *)
  Variable (e: entries).

  (** The compositionality lemma (Lem. 4) *)
  Theorem compositionality:
    forall
      (** languages are well-defined *)
      (Hwd_src: wd_langs scunits)
      (Hwd_tgt: wd_langs tcunits)
      (** all compilation units are reach-closed *)
      (Hrc: rc_cunits (scunits))
      (** all cunits are ldsimed *)
      (Hldsim: ldsims scunits tcunits)
      (** functions exposed to other modules are preserved *)
      (Hfn: fn_preserved scunits tcunits)
    ,
      GlobDSim (scunits, e) (tcunits, e).
  Proof.
    intros.
    intros mu sgm SGE spc tgm TGE tpc t MEMREL SINITCONFIG TINITCONFIG.
    assert (Hldsim_aux: ldsims_aux scunits tcunits).
    { apply ldsim_rc_ldsim_aux_list; auto. }
    clear Hrc Hldsim.
    exists glob_index, glob_order, (Invs.match_state SGE TGE sgm tgm mu).
    destruct spc as [stp t1 sgm' b1], tpc as [ttp t2 tgm' b2].
    destruct SINITCONFIG as [INITSGE INITSM INITSTP SFLWD SFLFREE SMRC STID STPTID SAB SM].
    simpl in *. subst.
    destruct TINITCONFIG as [INITTGE INITTM INITTTP TFLWD TFLFREE TMRC TTID TTPTID TAB TM].
    simpl in *. subst.
    assert (GEMODSIM: GE_mod_sim SGE TGE mu).
    { intros fnid Is sfid tfid SGETMOD.
      exploit fn_preserved_get_mod_eq; eauto.
      rewrite SGETMOD. intro. inv H. symmetry in H1.
      rename H1 into TGETMOD, y into It, H2 into MIDEQ.
      exists It. split; auto.
      pose proof (GlobEnv.ge_init scunits SGE INITSGE Is) as [scu [NTH MODSEM]].
      pose proof (GlobEnv.ge_init tcunits TGE INITTGE It) as [tcu [NTH' MODSEM']].
      assert (MODSIM: ldsim_aux (cu L scu) (cu L tcu)).
      { destruct Is as [Is HIs], It as [It HIt]. 
        generalize Hldsim_aux NTH NTH' MIDEQ; unfold Nat.eq; simpl; clear.
        intros. subst. exploit list_forall2_nth_rel; eauto. 
        rewrite NTH, NTH'. intros. inv H. auto. }
      destruct (GlobEnv.modules SGE Is) as [sl sge sG] eqn:SMODSEM; simpl in *.
      destruct (GlobEnv.modules TGE It) as [tl tge tG] eqn:TMODSEM; simpl in *.
      inv MODSEM. apply existTeq in H2. apply existTeq in H1. subst.
      inv MODSEM'. apply existTeq in H2. apply existTeq in H3. subst.
      rename H0 into INITSG, H1 into INITTG.      
      simpl in *. exploit MODSIM; eauto.      
      exploit GlobEnv.ge_bound_consist. eapply GlobEnv.ge_wd. exact INITSGE.
      instantiate (2:= Is). eauto. 
      exploit GlobEnv.ge_bound_consist. eapply GlobEnv.ge_wd. exact INITTGE.
      instantiate (2:= It). eauto.
      simpl. intros. rewrite H, H0.      
      (** Done: constraints on GE bounds ? *)
      inv MEMREL; auto.
      intros (I & I_order & R & MATCH). exists I, I_order, R. simpl.
      intros fnid' argS argT score GARGS ARGREL INITS.
      pose proof MATCH as SIM.
      eapply match_init in MATCH; eauto.
      destruct MATCH as (tcore & INITT & MATCH).
      eexists. simpl. split; eauto. 
      intros. exploit MATCH; eauto. clear MATCH. intros [i MATCH].
      eexists. eauto.
      (** Done: strengthen InitRel: including SGE TGE and ge_init_inj... *)
      { constructor; try (inv MEMREL; auto; fail).
        inv MEMREL. rewrite ir_shared_src.
        exploit GlobEnv.ge_bound_consist. eapply GlobEnv.ge_wd. exact INITSGE.
        instantiate (2:= Is). eauto. simpl. intro. rewrite H. auto.
        inv MEMREL. rewrite ir_shared_tgt.
        exploit GlobEnv.ge_bound_consist. eapply GlobEnv.ge_wd. exact INITTGE.
        instantiate (2:= It). eauto. simpl. intro. rewrite H. auto.
        intro. inv MEMREL. specialize (ir_senv_init_inj Is It).
        exploit fn_preserved_get_mod_eq; eauto.
        rewrite SGETMOD, TGETMOD. intro. inv H. specialize (ir_senv_init_inj H2 id).
        rewrite SMODSEM, TMODSEM in ir_senv_init_inj. simpl in ir_senv_init_inj.
        unfold Senv.find_symbol. simpl. inv ir_senv_init_inj; constructor; auto.
      }
    }
    assert (exists score tcore,
               ThreadPool.get_cs stp t = Some (score :: nil) /\
               ThreadPool.get_cs ttp t = Some (tcore :: nil) /\
               exists index index_order i',
                 CallStack_sim_cur SGE TGE index index_order i' mu FP.emp FP.emp (score::nil) sgm (tcore::nil) tgm)
      as (score & tcore & HSCS & HTCS & index & index_order & i' & CSSIMCUR).
    { exploit init_get_valid_spec; try eexact INITSTP; eauto.
      intros (funid & mid & cc & fid & NTH & GETMOD & INIT & GETCS).
      exploit init_get_valid_spec; try eexact INITTTP; eauto.
      intros (funid' & mid' & cc' & fid' & NTH' & GETMOD' & INIT' & GETCS').
      rewrite NTH in NTH'. inv NTH'.
      assert (GlobEnv.M SGE = GlobEnv.M TGE).
      { rewrite (GlobEnv.mod_num scunits), (GlobEnv.mod_num tcunits); auto. eapply list_forall2_length; eauto. }
      assert (nat_of_ord mid = nat_of_ord mid').
      { (* by preservation of internal_fn *)
        erewrite GlobEnv.get_mod_init in GETMOD; eauto.
        erewrite GlobEnv.get_mod_init in GETMOD'; eauto.
        remember (fun (ir: nat * option nat) (cui: cunit L)
                  => let (i, res) := ir in
                    if res then (S i, res)
                    else
                      if in_dec peq funid' (internal_fn (L (lid L cui)) (cu L cui))
                      then (S i, Some i)
                      else (S i, res)) as FUN.
        assert (fold_left FUN scunits (0%nat, None)
                = fold_left FUN tcunits (0%nat, None)).
        { generalize HeqFUN Hfn (0%nat, @None nat). clear. intros HFUN Hfn.
          induction Hfn; simpl; auto.
          intros. replace (FUN p a1) with (FUN p b1). auto.
          subst FUN. destruct p. destruct o; auto.
          rewrite H. auto. }
        rewrite H0 in GETMOD. rewrite GETMOD in GETMOD'. inv GETMOD'; auto. }
      eexists _, _. repeat (split; eauto).
      (** sim *)
      exploit (GEMODSIM funid' mid fid fid'). eauto. intros [mid'' [GETMOD'' MODSIM]].
      rewrite GETMOD' in GETMOD''. inv GETMOD''.
      destruct MODSIM as (I & I_order & R & MODSIM).
      exploit MODSIM; eauto. constructor. econstructor.
      intros [tcore [INIT'' SIM]].
      rewrite INIT' in INIT''. inv INIT''.
      exploit SIM; eauto. inv INITSM. eauto. inv INITTM. eauto.
      { (* local_init_rel *)
        inv MEMREL; inv INITSM; inv INITTM; constructor; eauto.
        split. eapply Bset.inj_weak; eauto. split; eauto.
        eapply MemAux.bset_eq_no_overlap; auto. intro. rewrite ir_shared_src_valid. tauto.
        eapply MemAux.bset_eq_no_overlap; auto. intro. rewrite ir_shared_tgt_valid. tauto.
        eapply FLists.flist_norep. eauto.
        eapply FLists.flist_norep. eauto.
        eapply MemClosures.bset_eq_reach_closed; eauto. intro. rewrite ir_shared_src_valid. tauto.
        eapply MemClosures.bset_eq_reach_closed; eauto. intro. rewrite ir_shared_tgt_valid. tauto. }
      { (* HLRely refl *)
        inv MEMREL. constructor; try eapply ir_inject; eauto;
                      constructor; unfold MemAux.unchg_freelist; 
                        eauto using GMemory.GMem.forward_refl, GMemory.GMem.unchanged_on_refl.
        eapply MemClosures.bset_eq_reach_closed; eauto. intro. rewrite ir_shared_src_valid. tauto.
        eapply MemClosures.bset_eq_reach_closed; eauto. intro. rewrite ir_shared_tgt_valid. tauto. }
      clear SIM. intros (i & SIM & MATCH).
      exists I, I_order, i.
      eapply top_sim. constructor; simpl; eauto. constructor.
    }
    inversion CSSIMCUR; subst. clear H8. destruct H7 as [[Rcur [RcurSim RcurMatch]]].
    pose proof (AuxLDSim.index_wf _ _ _ _ _ _ _ _ _ RcurSim) as WF.
    exists (i_wrap index index_order WF i'). split.
    { (** init mem, init fl properties *)
      (** TODO: strengthen InitRel, validblock <-> Shared mu *)
      assert (forall b, GMemory.GMem.valid_block sgm b <-> Injections.SharedSrc mu b).
      { eapply ir_shared_src_valid. eauto. }
      assert (forall b, GMemory.GMem.valid_block tgm b <-> Injections.SharedTgt mu b).
      { eapply ir_shared_tgt_valid. eauto. }
      eapply Config_sim_GConfigDSim; auto.
      (** TODO: strengthen InitRel, inject_weak mu ? *)
      eapply Bset.inj_weak, ir_mu_wd; eauto.
      inversion MEMREL; auto.
      eapply (MemClosures.bset_eq_reach_closed _ _ _ H). eauto. 
      eapply (MemClosures.bset_eq_reach_closed _ _ _ H0). eauto.
      intro. eapply MemAux.bset_eq_no_overlap; eauto. intro. rewrite H. tauto.
      intro. eapply MemAux.bset_eq_no_overlap; eauto. intro. rewrite H0. tauto.
      (** wd_lang *)
      { intro. inversion INITSGE. destruct (ge_init i). 
        destruct H1. inversion H2. simpl. apply Hwd_src. eapply nth_error_In; eauto. }
      { intro. inversion INITTGE. destruct (ge_init i).
        destruct H1. inversion H2. simpl. apply Hwd_tgt. eapply nth_error_In; eauto. }
      (** env wd *)
      inversion INITSGE. auto.
      inversion INITTGE. auto.
    }
    unfold match_state. split. split; auto.
    (** TODO: strengthen InitRel *)
    intros b1 b2 b'. eapply Bset.inj_injective, Bset.inj_weak, ir_mu_wd; eauto.
    exists FP.emp, FP.emp.
    (** match state *)
    constructor; simpl.
    { apply GMemory.GMem.forward_refl. }
    { apply GMemory.GMem.forward_refl. }
    { constructor; eauto. }
    { constructor; eauto. }
    { split.
      { econstructor; eauto. revert INITSTP INITTTP. simpl. clear. revert stp ttp.
        induction e; intros stp ttp SINIT TINIT; inversion SINIT; inversion TINIT; subst; clear SINIT TINIT.
        intros. unfold ThreadPool.get_cs, ThreadPool.emp; simpl. do 2 rewrite PMap.gi. constructor.
        intro t'. unfold ThreadPool.spawn, ThreadPool.get_cs; simpl.
        exploit init_tp_next; try exact H2.
        exploit init_tp_next; try exact H8.
        specialize (IHe0 _ _ H2 H8). apply ThreadPool.init_inv in H2. apply ThreadPool.init_inv in H8.
        intros. rewrite <- H in H0. clear H. rename H0 into NEXTEQ.
        destruct (peq (ThreadPool.next_tid thdp) (ThreadPool.next_tid thdp0)). rewrite e1.
        destruct (plt t' (ThreadPool.next_tid thdp)) as [PLT|PGE].
        repeat rewrite PMap.gso; try (intro; subst; apply Plt_ne in PLT; eauto). eauto.
        apply Pos.le_nlt, Pos.lt_eq_cases in PGE. destruct PGE as [PGT|EQ].
        repeat rewrite PMap.gso; try (intro; subst; apply Plt_ne in PGT; eauto). eauto.
        subst. repeat rewrite e1. repeat rewrite PMap.gss. constructor. apply match_cs_cons. constructor; cbv; auto.
        exfalso. apply n.
        generalize (ThreadPool.next_tid thdp) (ThreadPool.next_tid thdp0) NEXTEQ. clear.
        intros. pose proof (Pos2Nat.is_pos t). pose proof (Pos2Nat.is_pos t0).
        apply Pos2Nat.inj_iff. omega.
      }
      split. constructor. auto. constructor. auto.
    }
    { split. apply GSimDefs.LFPG_emp.
      split; apply Footprint.FP.subset_emp. }
    { eapply ThreadPool.init_inv; eauto. }
    { eapply ThreadPool.init_inv; eauto. }
    { intros. rewrite HSCS in H. inv H. exists (tcore::nil). split; auto. }
    { intros until 1. intros GETCS GETCS'.
      clear STPTID score tcore HSCS HTCS index index_order i' Rcur CSSIMCUR RcurSim RcurMatch sg_eq_current WF. 
      assert (STPTID': Plt t0 (ThreadPool.next_tid stp)).
      { exploit (ThreadPool.init_inv e stp); eauto. intro.
        destruct (plt t0 (ThreadPool.next_tid stp)); auto.
        exfalso. unfold ThreadPool.get_cs in *. erewrite ThreadPool.tp_finite in GETCS. discriminate. eauto.
        eauto with coqlib. }
      assert (TTPTID': Plt t0 (ThreadPool.next_tid ttp)).
      { exploit (ThreadPool.init_inv e ttp); eauto. intro.
        destruct (plt t0 (ThreadPool.next_tid ttp)); auto.
        exfalso. unfold ThreadPool.get_cs in *. erewrite ThreadPool.tp_finite in GETCS'. discriminate. eauto.
        eauto with coqlib. }
      exploit init_get_valid_spec; try eexact STPTID'; eauto. 
      intros (funid & mid & cc & fid & NTH & GETMOD & INIT & SGETCS).
      exploit init_get_valid_spec; try eexact TTPTID'; eauto.
      intros (funid' & mid' & cc' & fid' & NTH' & GETMOD' & INIT' & TGETCS).
      rewrite NTH in NTH'. inv NTH'.
      rewrite SGETCS in GETCS. inv GETCS. rewrite TGETCS in GETCS'. inv GETCS'.
      assert (GlobEnv.M SGE = GlobEnv.M TGE).
      { rewrite (GlobEnv.mod_num scunits), (GlobEnv.mod_num tcunits); auto. eapply list_forall2_length; eauto. }
      assert (nat_of_ord mid = nat_of_ord mid').
      { (* by preservation of internal_fn *)
        erewrite GlobEnv.get_mod_init in GETMOD; eauto.
        erewrite GlobEnv.get_mod_init in GETMOD'; eauto.
        remember (fun (ir: nat * option nat) (cui: cunit L)
                  => let (i, res) := ir in
                    if res then (S i, res)
                    else
                      if in_dec peq funid' (internal_fn (L (lid L cui)) (cu L cui))
                      then (S i, Some i)
                      else (S i, res)) as FUN.
        assert (fold_left FUN scunits (0%nat, None)
                = fold_left FUN tcunits (0%nat, None)).
        { generalize HeqFUN Hfn (0%nat, @None nat). clear. intros HFUN Hfn.
          induction Hfn; simpl; auto.
          intros. replace (FUN p a1) with (FUN p b1). auto.
          subst FUN. destruct p. destruct o; auto.
          rewrite H. auto. }
        rewrite H1 in GETMOD. rewrite GETMOD in GETMOD'. inv GETMOD'; auto. }
      (** sim *)
      exploit (GEMODSIM funid' mid fid fid'). eauto. intros [mid'' [GETMOD'' MODSIM]].
      rewrite GETMOD' in GETMOD''. inv GETMOD''.
      destruct MODSIM as (I & I_order & R & MODSIM).
      exploit MODSIM; eauto. constructor. econstructor.
      intros [tcore [INIT'' SIM]].
      rewrite INIT' in INIT''. inv INIT''.
      econstructor. econstructor; simpl; eauto. intros. exists R.
      exploit SIM; eauto. inv INITSM. eauto. inv INITTM. eauto.
      { (* local_init_rel *)
        inv MEMREL; inv INITSM; inv INITTM; constructor; eauto.
        split. eapply Bset.inj_weak; eauto. split; eauto.
        eapply MemAux.bset_eq_no_overlap; auto. intro. rewrite ir_shared_src_valid. tauto.
        eapply MemAux.bset_eq_no_overlap; auto. intro. rewrite ir_shared_tgt_valid. tauto.
        eapply FLists.flist_norep. eauto.
        eapply FLists.flist_norep. eauto.
        eapply MemClosures.bset_eq_reach_closed; eauto. intro. rewrite ir_shared_src_valid. tauto.
        eapply MemClosures.bset_eq_reach_closed; eauto. intro. rewrite ir_shared_tgt_valid. tauto. }
      clear SIM. intros ( i & SIM & MATCH). eauto.

      unfold MemAux.unchg_freelist. split; eauto using GMemory.GMem.forward_refl, GMemory.GMem.unchanged_on_refl.
      unfold MemAux.unchg_freelist. split; eauto using GMemory.GMem.forward_refl, GMemory.GMem.unchanged_on_refl.
      constructor.
    }      
  Qed.
    
  
End Compositionality.
  
