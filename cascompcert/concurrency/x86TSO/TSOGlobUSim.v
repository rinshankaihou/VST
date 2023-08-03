From mathcomp.ssreflect Require Import fintype.
Require Import Coqlib Maps.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import Asm.

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe.

Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.

Require Import Coq.Lists.Streams.

Require Import TSOGlobSem GlobSemantics.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

Record TSOGConfigUSim
       {sge: GlobEnv.t}
       {tge: TSOGlobEnv.t}
       (match_state: @ProgConfig sge -> @TSOProgConfig tge -> Prop) : Prop :=
  {
    match_taustep:
      forall spc tpc,
        match_state spc tpc ->
        forall tpc' fpT',
          tso_globstep tpc tau fpT' tpc' ->
          exists spc' fpS',
            tau_star glob_step spc fpS' spc'
            /\
            (match_state spc' tpc'
             \/
             GlobSemantics.abort spc')
    ;

    match_swstep:
      forall spc tpc,
        match_state spc tpc ->
        forall tpc',
          tso_globstep tpc sw empfp tpc' ->
          exists spc',
            glob_step spc ETrace.sw empfp spc'
            /\ match_state spc' tpc'
    ;

    match_unbufferstep:
      forall spc tpc,
        match_state spc tpc ->
        forall t' tpc',
          tso_globstep tpc (ub t') empfp tpc' ->
          match_state spc tpc'
    ;

    match_eventstep:
      forall spc tpc,
        match_state spc tpc ->
        forall v tpc',
          tso_globstep tpc (evt v) empfp tpc' ->
          exists spc',
            glob_step spc (ETrace.evt v) empfp spc'
            /\ match_state spc' tpc'
    ;

    match_final:
      forall spc tpc,
        match_state spc tpc ->
        final_state tpc ->
        GlobDefs.final_state spc
    ;

    match_abort:
      forall spc tpc,
        match_state spc tpc ->
        TSOGlobSem.abort tpc ->
        exists spc' fpS,
          tau_star glob_step spc fpS spc' /\
          GlobSemantics.abort spc'
    ;
    
  }.


Definition TSOGlobUSim {NL: nat} {L: @langs NL}
           (pSC: prog L)
           (pTSO: tsoprog) : Prop :=
  forall sgm sge spc t tgm tge tpc,
    tso_sc_initRel sge tge sgm tgm ->
    init_config pSC sgm sge spc t ->
    ~ DRF.star_race_config spc ->
    safe_state glob_step abort spc ->
    tso_initconfig pTSO tgm tge tpc t ->
    exists match_state,
      TSOGConfigUSim match_state /\
      match_state spc tpc.



Lemma tau_star_non_evt_star_app:
  forall state step (pc: state) fp pc' fp' pc'',
    tau_star step pc fp pc' ->
    non_evt_star step pc' fp' pc'' ->
    non_evt_star step pc (FP.union fp fp') pc''.
Proof.
  induction 1. rewrite FP.emp_union_fp. auto.
  intros. apply IHtau_star in H1. rewrite <- FP.fp_union_assoc. econstructor; eauto.
Qed.

Lemma tau_star_star_step:
  forall state step (pc: state) fp pc',
    tau_star step pc fp pc' ->
    exists ll, star step pc ll fp pc'.
Proof.
  induction 1. eexists. constructor.
  destruct IHtau_star. eexists. econstructor; eauto.
Qed.

Lemma non_evt_star_star_step:
  forall state step (pc: state) fp pc',
    non_evt_star step pc fp pc' ->
    exists ll, star step pc ll fp pc'.
Proof.
  induction 1. eexists. constructor.
  destruct H.
  destruct IHnon_evt_star. eexists. econstructor; eauto.
  destruct IHnon_evt_star. eexists. econstructor; eauto.
Qed.

Lemma star_star_app:
  forall state step (pc: state) l1 fp pc' l2 fp' pc'',
    star step pc l1 fp pc' ->
    star step pc' l2 fp' pc'' ->
    star step pc (l1 ++ l2) (FP.union fp fp') pc''.
Proof.
  induction 1. simpl. rewrite FP.emp_union_fp. auto.
  intros. eapply IHstar in H1. simpl. rewrite <- FP.fp_union_assoc. econstructor; eauto.
Qed.

Lemma non_evt_star_sim:
  forall SGE TGE (spc: @ProgConfig SGE) (tpc: @TSOProgConfig TGE) match_state fp tpc',
    non_evt_star tso_etrstep tpc fp tpc' ->
    TSOGConfigUSim match_state ->
    match_state spc tpc ->
    ~ DRF.star_race_config spc ->    
    safe_state glob_step abort spc ->
    exists fpS spc', non_evt_star glob_step spc fpS spc' /\ match_state spc' tpc'.
Proof.
  intros until 1. revert spc. induction H.
  { econstructor. econstructor. split; eauto. econstructor. }
  { intros. destruct H; inv H; destruct l; try discriminate.
    { eapply match_taustep in H2; eauto. destruct H2 as (spc' & fpS & Hstar & [MS|Habort]); [|exfalso].
      eapply IHnon_evt_star in MS; eauto. destruct MS as (fpS' & spc'' & Hstar' & MS).
      exploit tau_star_non_evt_star_app. eauto. eauto. intros.
      do 2 eexists. split; eauto.
      
      intro. apply H3. unfold DRF.star_race_config in *. eapply tau_star_star_step in Hstar. destruct Hstar.
      destruct H as [l [fp [pc' [Hstar Hrace]]]].
      do 3 eexists. split. eapply star_star_app. eauto. eauto. eauto.
      
      unfold safe_state. intros. eapply tau_star_star_step in Hstar. destruct Hstar.
      eapply H4. eapply star_star_app. eauto. eauto.
      eapply tau_star_star_step in Hstar. destruct Hstar. eapply H4; eauto. }
    { assert (fp1 = FP.emp) by (inv H7; auto).
      subst fp1. eapply match_unbufferstep in H2; eauto. }
    { assert (fp1 = FP.emp) by (inv H7; auto).
      subst fp1. eapply match_swstep in H2; eauto. destruct H2 as (spc' & Hsw & MS').
      eapply IHnon_evt_star in MS'; eauto. destruct MS' as (fpS' & spc'' & Hstar' & MS').
      do 2 eexists. split; eauto. econstructor; eauto.
      unfold DRF.star_race_config in *. intro. apply H3. destruct H as [l [fp [pc' [Hstar Hrace]]]].
      do 3 eexists. split; eauto. eapply star_step; eauto. auto.
      unfold safe_state. intros. eapply H4. econstructor; eauto. }
  }
Qed.
         
Theorem tso_globusim_refinement:
  forall NL L (pSC: @prog NL L) pTSO,
    TSOGlobUSim pSC pTSO ->
    tso_refine_sc pSC pTSO.
Proof.
  intros NL L pSC pTSO HSim.
  constructor.
  intros sgm sge spc t tgm tge tpc
         Hinitrel Hinitsc Hdrf Hsafe Hinittso.
  specialize (HSim _ _ _ _ _ _ _ Hinitrel Hinitsc Hdrf Hsafe Hinittso).
  destruct HSim as [match_state [HSim MS]].
  clear Hinitrel Hinitsc Hinittso sgm tgm t. 
  revert tpc spc Hdrf Hsafe MS . cofix.
  destruct B; intros; try (inv H0; fail).
  { clear tso_globusim_refinement. inv H. inv H1.
    exploit non_evt_star_sim; eauto. intros (fpS & spc' & Hstar & MS').
    eapply match_final in MS'; eauto. econstructor; eauto.
  }
  { clear tso_globusim_refinement. inv H. inv H1.
    exploit non_evt_star_sim; eauto. intros (fpS & spc' & Hstar & MS').
    eapply match_abort in MS'; eauto. destruct MS' as (spc'' & fpS' & Hstar' & Habort).
    eapply non_evt_star_star_step in Hstar. eapply tau_star_star_step in Hstar'.
    destruct Hstar, Hstar'. exploit star_star_app. exact H1. exact H3. intro Hstar.
    exfalso. eapply Hsafe; eauto. }
  {
    assert (Etr tso_etrstep TSOGlobSem.abort final_state tpc (Behav_cons v B)) by (inv H; auto).
    clear H.
    assert (exists fp state' state'',
               non_evt_star tso_etrstep tpc fp state' /\
               tso_etrstep state' (ETrace.evt v) empfp state'' /\
               Etr tso_etrstep TSOGlobSem.abort final_state state'' B)
      as (fp & state' & state'' & ? & ? & ?).
    { inversion H1. subst. do 3 eexists. split; eauto. }
    assert (exists fpS spc', non_evt_star glob_step spc fpS spc' /\ match_state spc' state') as (fpS & spc' & Hstar & MS').
    { exploit non_evt_star_sim; eauto. }
    assert (tso_globstep state' (evt v) empfp state'') as Hevt.
    { inv H2. destruct l; inv H4. auto. }
    eapply match_eventstep in MS'; eauto.
    destruct MS' as (spc'' & Hevt' & MS'').
    apply (Etr_cons glob_step _ _ _ fpS spc' _ spc''). auto. auto.
    eapply tso_globusim_refinement; eauto.
    unfold DRF.star_race_config in *. intros (l & fp' & pc' & Hstar' & Hrace).
    apply Hdrf. apply non_evt_star_star_step in Hstar. destruct Hstar as [l' Hstar].
    do 3 eexists. split. eapply star_star_app. eauto. eapply star_step. eauto. eauto. eauto.
    unfold safe_state. intros. eapply non_evt_star_star_step in Hstar. destruct Hstar.
    eapply Hsafe. eapply star_star_app. exact H5. econstructor; eauto.
    econstructor; eauto.
    inv H0. auto. }
Qed.
