From mathcomp.ssreflect Require Import fintype ssrnat.
Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import CUAST.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset DRF.

Require Import Languages.
Require Import TSOGlobSem GlobSemantics TSOGlobUSim
        RGRels ClientSim AsmClientSim ObjectSim.

Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.
Require Import InteractionSemantics.

Require Import TSOCompInvs ObjRGIProp.


Section Compositionality.
  (* Compilation units of source/target client code *)
  Variable (scunits: @cunits NL L).
  Variable (tcunits: list AsmTSO.comp_unit).

  Hypothesis (H_client_code: client_id scunits tcunits).

  (* object unit *)
  Variable (oscu: @cunit NL L).
  Variable (otcu: AsmTSO.comp_unit).
  
  Variable (Ro Go: ASM_local.genv -> tid -> stRel).
  Variable (Io: ASM_local.genv -> stInv).
  
  Hypothesis (H_object_sim: objcu_sim Ro Go Io oscu otcu).
  
  (* Thread entries *)
  Variable (e: entries).

  (* constraints on rely/guarantees *)

  Hypothesis (HRP: RespectPerm Io Ro Go).
  Hypothesis (H_sta_oo: forall ge t, Sta (Io ge) (Go ge t)).
  Hypothesis (H_rg_oo: forall ge t t', t <> t' -> Implies (Go ge t) (Ro ge t')).
  Hypothesis (H_sta_o_ub: forall ge, UBSta (Io ge)).
  Hypothesis (H_rg_ub_o: forall ge t, UBImplies (Io ge) (Ro ge t)).
  
  Lemma H_sta_co: forall ge t, Sta Ic (Go ge t).
  Proof. eapply RP_Ic_Sta_Go; eauto. Qed.
  Lemma H_sta_cc: forall t, Sta Ic (Gc t).
  Proof. exact Ic_sta. Qed.
  Lemma H_sta_oc: forall ge t, Sta (Io ge) (Gc t).
  Proof. eapply RP_Io_Sta_Gc; eauto. Qed.

  Local Hint Resolve H_sta_co H_sta_cc H_sta_oc.
  
  Lemma H_rg_cc: forall t t', Implies (Gc t) (Rc t').
  Proof. exact Gc_implies_Rc. Qed.
  Lemma H_rg_oc: forall ge t t', Implies' Ic (Go ge t) (Rc t').
  Proof. eapply RP_Go_Implies_Rc; eauto. Qed.
  Lemma H_rg_co: forall t ge t', t <> t' -> Implies' (Io ge) (Gc t) (Ro ge t').
  Proof. eapply RP_Gc_Implies_Ro; eauto. Qed.

  Local Hint Resolve H_rg_cc H_rg_oc H_rg_co.

  Lemma H_sta_c_ub: UBSta Ic.
  Proof. exact UBSta_Ic. Qed.
  Lemma H_rg_ub_c: forall t, UBImplies Ic (Rc t).
  Proof. exact UBImplies_Rc. Qed.

  Local Hint Resolve H_sta_c_ub H_rg_ub_c.

  Definition MATCH (SGE: GlobEnv.t) (TGE: TSOGlobEnv.t) iobj
             (spc: @ProgConfig SGE) (tpc: @TSOProgConfig TGE): Prop :=
    MS Ro Go Io SGE TGE iobj spc tpc /\ BufWD Ro Go Io SGE TGE iobj tpc.

  Lemma match_fls_eq:
    forall SGE TGE iobj spc tpc,
      MATCH SGE TGE iobj spc tpc ->
      GlobEnv.freelists SGE = TSOGlobEnv.freelists TGE.
  Proof. intros. destruct H. inv H. inv GE_eq. simpl in *. rewrite <- H4. auto. Qed.
  
  Definition progSrc : prog L := (oscu :: scunits, e).
  Definition progTgt : tsoprog := (otcu :: tcunits, e).
  
  Theorem compositionality:
    TSOGlobUSim progSrc progTgt.
  Proof.
    unfold TSOGlobUSim.
    intros sgm SGE spc t tgm TGE tpc INITREL INITCONFIG Hdrf Hsafe TSOINITCONFIG.
    exploit init_genvs_sim; eauto.
    intros [i_obj H_gemodsim].
    (** construct match_state *)
    exists (MATCH SGE TGE i_obj). split.
    (** match_state is a simulation invariant *)
    clear sgm spc tgm tpc t INITCONFIG Hdrf Hsafe TSOINITCONFIG INITREL H_gemodsim.
    constructor.
    (** tau-step sim *)
    intros spc tpc [MATCH BufWD] tpc' fpT' Hstep.
    exploit MS_preserved_after_tau_step_if_not_conflicting_client_fp; eauto.
    intro C. eapply BufWD_client_core_not_conflictc; eauto.
    intros (spc' & fpS' & Hsstep & MATCH').
    exploit BufWD_preserved_if_post_states_MS; try exact BufWD; eauto. intro BufWD'.
    eexists _, _. split. eauto. left. split; auto.
    (** sw-step sim *)
    intros spc tpc [MATCH BufWD] tpc' Hstep.
    exploit MS_preserved_after_sw; eauto. intros (spc' & Hsstep & MATCH').
    exploit BufWD_preserved_if_post_states_MS; try exact BufWD; eauto. intro BufWD'.
    eexists. split. eauto. split; auto.
    (** unbuffer sim *)
    intros spc tpc [MATCH BufWD] t' tpc' Hstep.
    exploit MS_preserved_after_unbuffer; eauto. intros MATCH'.
    exploit BufWD_preserved_if_post_states_MS; try exact BufWD; eauto. intro BufWD'.
    split; auto.
    (** evt-step sim *)
    intros spc tpc [MATCH BufWD] v tpc' Hstep.
    exploit MS_preserved_after_evt_step; eauto.
    intros (spc' & Hsstep & MATCH').
    exploit BufWD_preserved_if_post_states_MS; try exact BufWD; eauto. intro BufWD'.
    eexists. split. eauto. split; auto.
    (** final-state sim *)
    { intros spc tpc Hmatch Hfinal.
      inv Hfinal.
      inv Hmatch.
      inv H.
      destruct spc. simpl in *. subst.
      econstructor; eauto. simpl. inv thdp_sims.
      intros. pose proof H as Hvalid.
      eapply ThreadPool.tp_valid in H; eauto. destruct H as [csi Hgetcs].
      specialize (thread_simulation i).
      unfold ThreadPool.get_cs in *. rewrite Hgetcs in thread_simulation.
      inv thread_simulation.
      unfold ThreadPool.valid_tid in *. rewrite valid_tid_eq in Hvalid.
      specialize (H0 i Hvalid). destruct H0 as [Hthrdhalt Hbufnil].
      econstructor. eauto. inv Hthrdhalt. rewrite H in H2. inv H2. inv H3. inv H0. constructor.
    }
    (** abort case *)
    { intros.
      inv H0.
      { (* thread abort *)
        destruct H1 as (Hnthalt & Hbufnil & Habort).
        destruct tpc as [thdp cid tm] .
        destruct spc as [stp cid' sm atombit].
        destruct H as [HMS HBufWD].
        exploit tid_eq. eauto. simpl. intro. subst cid'.
        exploit atom_bit_0. eauto. simpl. intro. subst atombit.
        simpl in *.
        assert ((exists tC tcs, (TSOThrdPool.content thdp) !! cid = Some (tC :: tcs))
                \/ (TSOThrdPool.content thdp) !! cid = None) as [(tC & tcs & H_tp_core)|H_tp_core].
        { destruct ((TSOThrdPool.content thdp) !! cid) eqn:X; auto.
          destruct l; auto.
          contradict Hnthalt. simpl. constructor. auto. eauto. }
        { exploit thdp_sims; eauto. intro A. exploit thread_simulation; eauto; clear A.
          simpl. rewrite H_tp_core. intro. inv H. destruct x as [|sC scs]. inv H2. inv H.
          symmetry in H0. rename H0 into H_stp_core. rename H2 into Hthdsim. simpl in *.
          eexists _, FP.emp. split. econstructor.
          constructor. intro.
          (* not halted *)
          inv H. inv H1.
          exploit thdp_sims; eauto. intro A.
          exploit thread_simulation; eauto. intro B.
          exploit tid_eq; eauto. intro C.
          simpl in *. subst. rewrite H_tp_core in B. inv B. inv H2.
          inv H1. congruence. congruence.
          (* not non-sw step *)
          inv Hthdsim.
          (* case: client abort *)
          { inv H. inv H3.
            (* sc program no core step *)
            assert (exists fn, FLists.get_tfid (TSOGlobEnv.freelists TGE) cid fn = flid)
              as [fn Hfn].
            { erewrite <- TSOCompInvs.match_fls_eq; eauto.
              eapply thdp_sims in HMS.
              eapply tp_inv_src in HMS.
              eapply ThreadPool.cs_inv in HMS; eauto.
              eapply ThreadPool.fid_belongsto in HMS; [|left; eauto]. eauto. }
            exploit ClientSim.match_abort. eauto. eauto.
            { instantiate (1:= FLists.get_fl (TSOGlobEnv.freelists TGE) flid).
              rewrite <- Hfn.
              eapply buffered_alloc_local_tm_alloc_not_fl.
              erewrite <-TSOCompInvs.match_fls_eq; eauto.
              eapply GlobEnv.wd_fl. eapply GE_wd; eauto.
              eapply buffered_alloc_local in HMS; eauto. }
            { eapply fl_valid_eq_rel_tm_gm_vb. rewrite <- Hfn.
              eapply fl_valid_match in HMS; eauto. }
            eauto. eauto.
            intros tfp tc' b' m'.
            intros [Hcorestep [m'' Happly']].
            destruct (Classical_Prop.classic (conflictc cid tfp (tso_buffers tm)))
              as [Hconflict|Hnoconflict].
            (* not conflict by buf nil... *)
            revert Hbufnil Hconflict; clear. intros.
            inv Hconflict. rewrite Hbufnil in H0. inv H0.
            rewrite <- (Hbufnil cid) in Hcorestep.
            eapply TSOSemLemmas.non_conflict_access_unbuffer_safe' in Hnoconflict; eauto.
            exploit (@TSOGlobSem.Corestep TGE); eauto.
            econstructor; eauto. econstructor; eauto. simpl. intro C.
            apply Habort in C. discriminate.
            eapply Ic_unbuffer_safe. inv HMS; eauto.
            assert (TSOGlobEnv.freelists TGE = GlobEnv.freelists SGE) as Heqfls.
            { apply GE_eq in HMS. inv HMS. simpl. rewrite <- H7. auto. }
            simpl. intros Hsc_no_corestep.
            (* sc program no call step *)
            assert (forall funid sg args new_ix cc',
                       at_external (ModSem.lang (GlobEnv.modules SGE ix))
                                   (ModSem.Ge (GlobEnv.modules SGE ix))
                                   sc = Some (funid, sg, args) ->
                       not_primitive funid ->
                       GlobEnv.get_mod SGE funid = Some new_ix ->
                       init_core (ModSem.lang (GlobEnv.modules SGE new_ix))
                                 (ModSem.Ge (GlobEnv.modules SGE new_ix))
                                 funid args = Some cc' ->
                       False) as Hsc_no_callstep.
            { intros funid sg0 args new_ix cc' Hsatext Hextfun Hsgetmod Hsinit.
              destruct (AsmTSO.at_external (TSOGlobEnv.modules TGE ix') tc) as [[[funid' sg0']  args']|] eqn:Htatext.
              destruct SGE, TGE. exploit GE_eq. eauto. intro. inv H2. simpl in *.
              apply Eqdep.EqdepTheory.inj_pair2 in H8.
              apply Eqdep.EqdepTheory.inj_pair2 in H4.
              apply Eqdep.EqdepTheory.inj_pair2 in H11.
              apply Eqdep.EqdepTheory.inj_pair2 in H12.
              subst. rewrite <- H7 in Hsgetmod.
              exploit ClientSim.match_at_external; eauto. intro. rewrite Hsatext, Htatext in H2. inv H2.
              destruct (AsmTSO.init_core (modules0 new_ix) funid args) as [tcc'|] eqn:Htinit.
              exploit (@TSOGlobSem.Call {|
                           TSOGlobEnv.M := M;
                           TSOGlobEnv.modules := modules0;
                           TSOGlobEnv.get_mod := get_mod0;
                           TSOGlobEnv.ge_bound := ge_bound0;
                           TSOGlobEnv.freelists := freelists0 |}).
              eauto. simpl. eauto. auto. eauto. eauto.
              unfold TSOThrdPool.push. simpl. rewrite H_tp_core. eauto.
              intro C. apply Habort in C. discriminate.
              (* tso cannot init: *)
              specialize (H15 new_ix).
              destruct H15 as [[Hmodsim Hix]|[Hmodsim Hix]].
              inv Hmodsim. exploit ClientSim.match_init_none. exact H3. eauto. intro.
              destruct (modules new_ix). inv H2. apply Eqdep.EqdepTheory.inj_pair2 in H9. subst Ge.
              simpl in *. congruence.
              inv Hmodsim. exploit ObjectSim.match_init_none. exact H3. eauto. intro.
              assert (init_core (ModSem.lang (modules i_obj)) (ModSem.Ge (modules i_obj)) funid args <> None) as Hsinit'.
              { rewrite Hsinit. intro; discriminate. }
              clear Hsinit cc'.
              rewrite <- H2 in Hsinit'. simpl in *. contradiction.
              (* tso no at ext *)
              erewrite ClientSim.match_at_external in Htatext; eauto. congruence.
            }
            (* sc program no return step *)
            assert (forall sC' scs' res sc'',
                       scs = sC' :: scs' ->
                       halt (ModSem.lang (GlobEnv.modules SGE ix))
                            sc = Some res ->
                       after_external (ModSem.lang (GlobEnv.modules SGE (Core.i sC')))
                                      (Core.c sC')
                                      (res_sg sg res) = Some sc'' ->
                       False) as Hsc_no_return.
            { intros. subst scs.
              destruct tcs as [|tC' tcs'] eqn:X; subst tcs. inv H5. inv H5.
              erewrite <- ClientSim.match_halted in H3; eauto.
              destruct (AsmTSO.after_external (TSOCore.c tC') (res_sg sg res)) as [tc''|] eqn:Htaftext.
              exploit (@TSOGlobSem.Return TGE). eauto. eauto.
              unfold TSOThrdPool.pop. rewrite H_tp_core. eauto. eauto.
              econstructor; eauto. econstructor; eauto. simpl. rewrite PMap.gss. eauto.
              intro C. apply Habort in C. discriminate.
              inv H8. exploit ClientSim.match_after_external_none; eauto. intro.
              simpl in *. congruence.
            }
            (* sc program no thread halt *)
            assert (forall res,
                       scs = nil ->
                       halt (ModSem.lang (GlobEnv.modules SGE ix)) sc = Some res -> False) as Hsc_no_halt.
            { intros. erewrite <- ClientSim.match_halted in H3; eauto.
              subst scs. inv H5.
              exploit (@TSOGlobSem.Halt TGE). eauto. eauto.
              unfold TSOThrdPool.pop. rewrite H_tp_core. eauto. eauto.
              intro C. apply Habort in C. discriminate.
            }
            (* sc program no print *)
            assert (forall v sc',
                       at_external (ModSem.lang (GlobEnv.modules SGE ix))
                                   (ModSem.Ge (GlobEnv.modules SGE ix))
                                   sc = Some (print, print_sg, v :: nil) ->
                       not_pointer v ->
                       after_external (ModSem.lang (GlobEnv.modules SGE ix)) sc None = Some sc' ->
                       False) as Hsc_no_print.
            { intros. erewrite <- ClientSim.match_at_external in H2; eauto.
              destruct (AsmTSO.after_external tc None) as [tc'|] eqn:Htaftext.
              exploit (@TSOGlobSem.EF_Print TGE); eauto.
              econstructor; eauto. econstructor; eauto. intro C; apply Habort in C. discriminate.
              exploit ClientSim.match_after_external_none; eauto; intro.
              simpl in *. congruence. }
            destruct Hsc_no_corestep as [Hsc_no_corestep|C].
            intros. inv H2; auto; exfalso.
            { unfold ThreadPool.get_top, ThreadPool.get_cs in *.
              rewrite H_stp_core in H_tp_core0. simpl in *. inv H_tp_core0; simpl in *.
              eapply Hsc_no_corestep; eauto.
              rewrite Heqfls in *. eauto. }
            { unfold ThreadPool.get_top, ThreadPool.get_cs in *.
              rewrite H_stp_core in H_tp_core0. simpl in *. inv H_tp_core0; simpl in *.
              eapply Hsc_no_callstep; eauto. }
            { unfold ThreadPool.pop, ThreadPool.get_top, ThreadPool.get_cs in *.
              rewrite H_stp_core in H_tp_core0. rewrite H_stp_core in H_tp_pop. simpl in *. inv H_tp_pop.
              simpl in *. rewrite PMap.gss in H_tp_caller.
              destruct scs as [|sC' scs']; simpl in H_tp_caller; inv H_tp_caller.
              inv H_tp_core0. simpl in *.
              eapply Hsc_no_return; eauto.  }
            { unfold ThreadPool.pop, ThreadPool.get_top, ThreadPool.get_cs in *.
              rewrite H_stp_core in H_tp_core0. rewrite H_stp_core in H_tp_pop. simpl in *. inv H_tp_pop.
              destruct scs as [|sC' scs']. 
              inv H_tp_core0. simpl in *. eapply Hsc_no_halt; eauto.
              inv H_thread_halt. unfold ThreadPool.get_cs in H2. simpl in H2.
              rewrite PMap.gss in H2. inv H2. inv H3.  }
            { unfold ThreadPool.pop, ThreadPool.get_top, ThreadPool.get_cs in *.
              rewrite H_stp_core in H_tp_core0. inv H_tp_core0. simpl in *.
              eapply ClientSim.match_no_entatom in H_core_atext; eauto. destruct H_core_atext; contradiction. }
            {  unfold ThreadPool.pop, ThreadPool.get_top, ThreadPool.get_cs in *.
               rewrite H_stp_core in H_tp_core0. inv H_tp_core0. simpl in *.
               eapply Hsc_no_print; eauto. }
            { (* fl ill formed - impossible case *)
              revert C HMS. clear. intros. exfalso.
              eapply fls_embed in HMS. inv HMS. edestruct Embed. unfold FLists.get_fl in C.
              eapply C; eauto. }
          }
          { (* object abort *)
            inv H2. 
            (* tso program no core step *)
            assert (forall fp tc' b' gm', ~ tsostep (TSOGlobEnv.modules TGE i_obj)
                                       (FLists.get_fl (TSOGlobEnv.freelists TGE) flid)
                                       tc (nil, memory tm) fp tc' (b', gm')) as Hno_corestep.
            { intros. intro C.
              exploit (@TSOGlobSem.Corestep TGE). eauto.
              simpl. rewrite Hbufnil. eauto.
              econstructor; eauto. econstructor; eauto. eauto.
              { eapply match_tau in C; eauto; simpl in *.
                destruct C as [Hstep|Hatom].
                destruct Hstep as (FP & sc' & sm' & Hstar & [[HGo _]|Habort']).
                { unfold tsoupd. eapply Ic_unbuffer_safe. eapply H_sta_co. eapply mem_inv_client. exact HMS. eauto. }
                { exfalso. erewrite <- TSOCompInvs.match_fls_eq in Habort';[|eauto]. 
                  exploit SCSemLemmas.core_star_globstep_star.
                  erewrite <- TSOCompInvs.match_fls_eq in Hstar. eauto. eauto. eauto.
                  intros (stp' & Hsstar & [Htp' | Hrefl]).
                  eapply SCSemLemmas.taustar_etrace_star in Hsstar. destruct Hsstar.
                  eapply source_safe. eauto. eauto. eapply abort_condition_abort.
                  instantiate (1:=scs). instantiate (1:=flid). instantiate (1:=sg). instantiate (1:=sc').
                  simpl. GDefLemmas.solv_thread.
                  simpl. tauto. tauto. tauto. tauto.
                  destruct Hrefl as (A & B & C & D); subst sm' sc' stp' FP.
                  eapply source_safe. eauto. eauto. eapply ETrace.star_refl. eapply abort_condition_abort. eauto.
                  simpl. tauto. tauto. tauto. tauto. }
                destruct Hatom as (FP1 & sc_ent & sm1 & sc_ent' & FP2 & sc_ext & sm' & sc' &
                                   Hstar1 & Hent1 & Hent2 & Hstar2 & [Hext | Habort']).
                { destruct Hext as (_ & _ & HGo & _).
                  unfold tsoupd. eapply Ic_unbuffer_safe. eapply H_sta_co. eapply mem_inv_client. exact HMS. eauto. }
                { exfalso. erewrite <- TSOCompInvs.match_fls_eq in Habort'; [|eauto].
                  exploit SCSemLemmas.core_star_globstep_star.
                  erewrite <- TSOCompInvs.match_fls_eq in Hstar1. eauto. eauto. eauto.
                  intros (stp' & Hsstar1 & Hstp').
                  exploit (@Ent_Atom SGE).
                  instantiate (1:= {| Core.i := ix; Core.c := sc_ent; Core.sg := sg; Core.F := flid |}).
                  instantiate (1:= cid). instantiate (1:= stp').
                  destruct Hstp' as [Hstp'|(A & B & C & D)].
                  GDefLemmas.solv_thread. subst stp' sc. GDefLemmas.solv_thread. rewrite H_stp_core. simpl. auto.
                  simpl. auto. simpl. eauto. econstructor. eauto. econstructor.
                  instantiate (1:= {| Core.i := ix; Core.c := sc_ent; Core.sg := sg; Core.F := flid |} :: scs).
                  destruct Hstp' as [Hstp'|(A & B & C & D)].
                  GDefLemmas.solv_thread. subst stp' sc. GDefLemmas.solv_thread.
                  simpl. econstructor. econstructor. eauto. eauto. 
                  instantiate (1:= sm1). intro Hent.
                  exploit SCSemLemmas.core_star_globstep_star.
                  erewrite <- TSOCompInvs.match_fls_eq in Hstar2. exact Hstar2. eauto.
                  instantiate (1:= scs). instantiate (1:= sg).
                  GDefLemmas.solv_thread. 
                  instantiate (1:= {|
                                    ThreadPool.content := PMap.set cid
                                                                   (Some
                                                                      ({| Core.i := ix; Core.c := sc_ent'; Core.sg := sg; Core.F := flid |} :: scs))
                                                                   (ThreadPool.content stp');
                                    ThreadPool.next_tid := ThreadPool.next_tid stp';
                                    ThreadPool.next_fmap := ThreadPool.next_fmap stp' |}).
                  simpl. rewrite PMap.gss. auto.
                  intros (stp'' & Hsstar2 & Hstp''). 
                  eapply SCSemLemmas.taustar_etrace_star in Hsstar1. destruct Hsstar1 as [ls1 Hsstar1].
                  eapply SCSemLemmas.taustar_etrace_star in Hsstar2. destruct Hsstar2 as [ls2 Hsstar2].
                  eapply source_safe. eauto.
                  eapply SCSemLemmas.etrace_star_star. exact Hsstar1.
                  eapply SCSemLemmas.etrace_star_star. eapply ETrace.star_step. exact Hent. eapply ETrace.star_refl.
                  exact Hsstar2.
                  eapply abort_condition_abort.
                  instantiate (1:= scs). instantiate (1:= flid). instantiate (1:= sg). instantiate (1:= sc_ext).
                  simpl. destruct Hstp'' as [Hstp'' | (A & B & C & D)]; [| subst sc_ext stp''].
                  GDefLemmas.solv_thread. unfold ThreadPool.get_cs. simpl. rewrite PMap.gss. auto.
                  tauto. tauto. tauto. tauto.
                }
                { exploit thdp_sims. eauto. simpl. intro.
                  apply tp_inv_src in H1. eapply ThreadPool.cs_inv in H1; eauto.
                  eapply ThreadPool.fid_valid in H1;[|simpl;left;eauto]. destruct H1 as [fn [_ Hfn]].
                  simpl in Hfn. subst flid. erewrite <- TSOCompInvs.match_fls_eq; eauto.
                  eapply buffered_alloc_local_tm_alloc_not_fl. eapply GlobEnv.wd_fl. eapply GE_wd. eauto.
                  erewrite TSOCompInvs.match_fls_eq; eauto.
                  eapply buffered_alloc_local in HMS. eauto. }
                { exploit thdp_sims. eauto. simpl. intro.
                  apply tp_inv_src in H1. eapply ThreadPool.cs_inv in H1; eauto.
                  eapply ThreadPool.fid_valid in H1;[|simpl;left;eauto]. destruct H1 as [fn [_ Hfn]].
                  simpl in Hfn. subst flid. erewrite TSOCompInvs.match_fls_eq; eauto.
                  eapply fl_valid_match in HMS. simpl in HMS. revert HMS.
                  unfold fl_valid_eq, rel_tm_gm_vb. unfold FLists.get_block, MemAux.get_block. intros.
                  eapply HMS in H2; eauto. revert H2. clear. tauto. }
              }
              simpl. intro C'. apply Habort in C'. discriminate. 
            }
            (* tso program object not returning *)
            assert (AsmTSO.halt tc = None) as Hnot_returning.
            { destruct (AsmTSO.halt tc) as [res|] eqn:Hhalt; auto.
              exfalso.
              destruct tcs as [|tc' tcs'].
              exploit (@TSOGlobSem.Halt TGE); eauto.
              unfold TSOThrdPool.pop. rewrite H_tp_core. eauto. intro C. apply Habort in C. discriminate.
              destruct (AsmTSO.after_external (TSOCore.c tc') (res_sg sg res)) as [tc''|] eqn:Haftext.
              exploit (@TSOGlobSem.Return TGE); eauto.
              unfold TSOThrdPool.pop. rewrite H_tp_core. eauto. econstructor; eauto.
              econstructor; eauto. simpl. rewrite PMap.gss. eauto.
              intro C. apply Habort in C. discriminate.
              destruct scs as [|sc' scs']; inv H4.
              exploit ObjectSim.match_halt_noscstep; eauto. intros [Hno_sccorestep Hnot_atext].
              eapply ObjectSim.match_halt in Hhalt; eauto.
              inv H5.
              eapply ClientSim.match_after_external_none in Haftext; eauto.
              revert HMS Hhalt Haftext H_stp_core Hnot_atext Hno_sccorestep. clear. intros.
              apply source_safe in HMS. eapply HMS. eapply ETrace.star_refl.
              econstructor; simpl. intro. inv H. GDefLemmas.solv_thread. inv H1.
              intros. inv H; GDefLemmas.solv_thread; simpl in *; exfalso.
              inv H_tp_core. simpl in *. eapply Hno_sccorestep; eauto.
              inv H_tp_core. simpl in *. congruence.
              inv H_tp_core. inv H_tp_caller. inv H_tp_pop. simpl in *. rewrite PMap.gss in H. inv H. simpl in *. congruence.
              inv H_tp_core. inv H_thread_halt. inv H_tp_pop. GDefLemmas.solv_thread. inv H0.
              GDefLemmas.solv_thread. simpl in *. congruence.
              GDefLemmas.solv_thread. simpl in *. congruence.
            }
            exploit fls_embed. eauto. intros. inv H1. edestruct Embed.
            exploit ObjectSim.match_abort; eauto.
            contradiction.
          }
        }
        { exploit thdp_sims; eauto. intro A. exploit thread_simulation; eauto; clear A.
          simpl. rewrite H_tp_core. intro. inv H.
          eexists _, FP.emp. 
          split. econstructor. constructor.
          intro. inv H. simpl in *. congruence.
          intros. inv H; simpl in *; auto; unfold ThreadPool.get_top, ThreadPool.get_cs in *.
          rewrite <- H1 in H_tp_core0. discriminate.
          rewrite <- H1 in H_tp_core0. discriminate.
          rewrite <- H1 in H_tp_core0. discriminate.
          rewrite <- H1 in H_tp_core0. discriminate.
          rewrite <- H1 in H_tp_core0. discriminate.
          rewrite <- H1 in H_tp_core0. discriminate.
        }
      }
      { (* unbuffer abort *)
        destruct H. exploit mem_inv_client; eauto. intro A.
        eapply Ic_unbuffer_safe in A.
        destruct H1 as (t' & Htbuf & Hunbuf).
        eapply unbuffer_safe_unbuffer in A; eauto. contradiction.
      }
    }
    (** init states are matched *)
    { split. constructor.
      inv INITCONFIG. auto. eapply GlobEnv.ge_wd; eauto.
      auto.
      inv INITCONFIG. inv TSOINITCONFIG. simpl in *. auto.
      inv INITCONFIG. auto.
      
      inv INITCONFIG. inv TSOINITCONFIG. rewrite H15. eapply tso_sc_initRel_Ic; eauto.
      destruct SGE. destruct TGE. simpl in *. inv H_gemodsim. clear i_obj1. simpl in *.
      apply Eqdep.EqdepTheory.inj_pair2 in H0.
      apply Eqdep.EqdepTheory.inj_pair2 in H3.
      apply Eqdep.EqdepTheory.inj_pair2 in H6.
      apply Eqdep.EqdepTheory.inj_pair2 in H7.
      subst.
      destruct (H10 i_obj).
      destruct H; contradiction.
      destruct H. inv H. simpl in *. eapply match_initmem; eauto. 
      inv INITCONFIG. inv H4. simpl in *. specialize (H9 i_obj).
      rewrite <- H1 in H9. simpl in *. eauto.
      inv TSOINITCONFIG. simpl in *. inv H4. eauto.
      inv TSOINITCONFIG. auto.
      auto. auto.
      (* thread sims ... *)
      inv TSOINITCONFIG.
      inv INITCONFIG.
      simpl in *. rewrite H7.
      eapply ge_mod_sim_thdp_init_thrdsims; eauto.
      (* flists *)
      econstructor. intros. simpl.
      destruct (tm tpc) eqn:?. simpl. destruct memory eqn:?.
      eexists (Mem.mkmem mem_contents mem_access validblocks _ 0%nat _ _ access_max invalid_noaccess contents_default).
      econstructor; simpl; eauto.
      intros. inv TSOINITCONFIG. rewrite H9 in H. inv H.
      (* inv thdp *)
      inv INITCONFIG. inv TSOINITCONFIG. eapply TSOSemLemmas.init_inv;eauto. 
      (* buffered alloc *)
      intros t' b lo hi H. inv TSOINITCONFIG. rewrite H8 in H. inv H.
      (* valid_block eq *)
      { exploit init_rel_ge_bound. eauto. intro HBOUND.
        exploit init_rel_freelists. eauto. intro HFLS.
        simpl. intros t0 fn. unfold FLists.get_tfl.
        generalize (FLists.get_tfid (TSOGlobEnv.freelists TGE) t0 fn).
        clear fn. intro flid. unfold fl_valid_eq.
        inv INITCONFIG. inv TSOINITCONFIG. rewrite H15. simpl. intros tgm' A. inv A.
        revert H0 H8 HFLS. clear. intros.
        inv H0. inv H8. specialize (H2 flid). specialize (H0 flid). revert H0 H2.
        rewrite HFLS. clear.
        generalize (FLists.get_fl (TSOGlobEnv.freelists TGE) flid) (gm spc). clear.
        intros fl gm. unfold MemAux.no_overlap, MemAux.valid_block_bset. intros.
        specialize (H0 (FLists.get_block fl n) n eq_refl).
        specialize (H2 (FLists.get_block fl n) n eq_refl).
        split; intro C; [contradict H2|contradict H0]; auto.
      }
      (* sep *)
      { inv INITCONFIG. eapply init_rel_sgm_sep. eauto. }
      (* BufWD *)
      apply buf_emp_BufWD.
      inv TSOINITCONFIG. rewrite H7. simpl. auto.
      Unshelve.
      intros. inv TSOINITCONFIG. inv H3. eapply flist_norep; eauto.
      intros. inv TSOINITCONFIG. inv H1.
      split. intro. exfalso. eapply H6. eauto. unfold Bset.belongsto.
      unfold tsomem_init in H8. rewrite Heqt0 in H8. inv H8. eauto.
      intro. inversion H1.
    }
  Qed.

End Compositionality.

Check compositionality.
