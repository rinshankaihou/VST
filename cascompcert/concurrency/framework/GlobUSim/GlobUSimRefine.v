Require Import InteractionSemantics GlobDefs Footprint Injections GAST ETrace GlobUSim NPSemantics SimEtr GlobSim GSimDefs GDefLemmas USimDRF.

(** * Simulation implies Refinement *)

(** This file defines the lemma [USim_Refine], which says when 
    source program simulates target program ( [S > T] ),
    target program refines the source program. *)
(** - [S > T] => [T NP_refine S]
    - [S > T] /\ [Safe(S)] => [Safe(T)]
 *)

Local Notation "{-| PC , T }" := 
  ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |})  (at level 70,right associativity).

Section usim_diverge.
  Variable SGE TGE:GlobEnv.t.
  Variable I:Type.
  Variable ord:I->I->Prop.
  Variable R:I->Mu->FP.t->FP.t->@ProgConfig SGE->@ProgConfig TGE->Prop.
  Hypothesis usim: GConfigUSim I ord R.
  
  (** In this section, Sdiverge and SEtr are auxiliary definition for proof and is defined in SimEtr.v *)
  
  Lemma tau_plus_star_step:
    forall ge pc fp pc',
      tau_plus np_step pc fp pc'->
      exists fp1 fp2 pc1,
        tau_star np_step pc fp1 pc1 /\
        @np_step ge pc1 tau fp2 pc' /\
        FP.union fp1 fp2 = fp.
  Proof.
    induction 1;intros. Esimpl;eauto. constructor. rewrite FP.emp_union_fp;auto.
    Hsimpl. Esimpl;eauto. econstructor;eauto. rewrite<- FP.fp_union_assoc. congruence.
  Qed.
  Lemma usim_Sdiverge_inva:
    forall i mu fpS fpT spc tpc,
      R i mu fpS fpT spc tpc->
      Sdiverge TGE tpc->
      exists tpc1 fpT1 tpc2 fpT2 o,
          (o = tau \/ o = sw) /\
          tau_star np_step tpc fpT1 tpc1 /\
          np_step tpc1 o fpT2 tpc2 /\ Sdiverge TGE tpc2 /\
          exists spc1 fpS1 spc2 fpS2,
            tau_star np_step spc fpS1 spc1 /\
            np_step spc1 o fpS2 spc2 /\
            exists i' fpS' fpT',
              R i' mu fpS' fpT' spc2 tpc2.

  Proof.
    apply index_wf in usim as ord_wf.
    induction i using (well_founded_ind ord_wf);intros.

    inversion H1;clear H1;subst;destruct H2;subst.
    {
      assert(atom_bit tpc = atom_bit pc' \/ atom_bit tpc <> atom_bit pc').
      apply Classical_Prop.classic.
      destruct H1.
      {
        eapply match_tau_step in H3 as ?;eauto.
        destruct H2;Hsimpl.
        {
          apply tau_plus_star_step in H2;Hsimpl.
          Esimpl;try eassumption;eauto. constructor.
        }
        {
          eapply H in H5;eauto.
          Hsimpl.
          eapply tau_star_cons in H3;eauto.
          Esimpl;eauto.
        }
      }
      {
        eapply match_ent_atom in H1 as ?;eauto.
        Hsimpl.
        Esimpl;try eassumption;eauto. constructor.
      }
    }
    {
      eapply match_npsw_step in H3 as ?;eauto.
      Hsimpl.
      assert(GSimDefs.pc_valid_tid x2 pc'.(cur_tid)).
      specialize (H7 x3).
      Hsimpl.
      assert(GSimDefs.pc_valid_tid pc' pc'.(cur_tid)).
      inversion H3;subst;split;auto.

      eapply match_tp in H9;eauto.
      Hsimpl.
      apply thrddom_eq'_comm in H12.
      eapply GlobSim.thrddom_eq'_valid_tid_preservation in H12;eauto.

      specialize (H7 (cur_tid pc')).
      Hsimpl.
      assert(({-|pc',cur_tid pc'})=pc'). destruct pc';simpl in *;subst;auto.
      rewrite H11 in H10.
      Esimpl;eauto. constructor.
      intro contra;inversion contra.
    }
  Qed.

  Lemma tau_star_cons_Sdiverge:
    forall ge pc fp pc',
      tau_star np_step pc fp pc'->
      Sdiverge ge pc'->
      Sdiverge ge pc.
  Proof.
    induction 1;intros. auto.
    econstructor;try left;eauto. 
  Qed.

  Lemma tau_star_cons_step_non_evt_plus:
    forall ge pc fp pc' fp' pc'' o,
      o = tau \/ o = sw ->
      tau_star (@np_step ge) pc fp pc'->
      np_step pc' o fp' pc''->
      non_evt_plus np_step pc (FP.union fp fp') pc''.
  Proof.
    induction 2;intros.
    rewrite FP.emp_union_fp. econstructor;eauto.
    Hsimpl.
    rewrite <- FP.fp_union_assoc.
    econstructor 2. left;eauto. eauto. eauto.
  Qed.
  Lemma usim_Sdiverge_preserve:
    forall i mu fpS fpT spc tpc,
      R i mu fpS fpT spc tpc->
      Sdiverge TGE tpc->
      Sdiverge SGE spc.
  Proof.
    intros. apply Pdiverge_sound. revert i mu fpS fpT spc tpc H H0;cofix;intros.
    eapply usim_Sdiverge_inva in H0 as ?;try apply H.
    Hsimpl.
    eapply tau_star_cons_step_non_evt_plus in H5;try apply H6;auto.

    econstructor. eauto. eauto.
  Qed.

  Lemma tau_star_non_evt_star{ge}:
    forall (step:@ProgConfig ge->glabel->FP.t->@ProgConfig ge->Prop) pc fp pc',
      tau_star step pc fp pc'->
      non_evt_star step pc fp pc'.
  Proof.
    induction 1;intros.
    constructor.
    econstructor;eauto.
  Qed.

  
  Lemma non_evt_star_cons{ge}:
    forall (step:@ProgConfig ge->glabel->FP.t->@ProgConfig ge->Prop) s s' s'' fp fp',
      non_evt_star step s fp s' ->
      non_evt_star step s' fp' s'' ->
      non_evt_star step s (FP.union fp fp')s''.
  Proof.
    induction 1;intros.
    rewrite FP.emp_union_fp;auto.
    rewrite <- FP.fp_union_assoc.
    apply IHnon_evt_star in H1.
    econstructor;eauto.
  Qed.
  Inductive non_evt_starN {State:Type}:(State->glabel->FP.t->State->Prop)->nat->State->FP.t->State->Prop:=
  | ne_star_refl: forall step s,
      @non_evt_starN State step 0  s FP.emp s
  | ne_star_step: forall step n s1 fp1 s2 fp2 s3,
      step s1 tau fp1 s2 \/ step s1 sw fp1 s2 ->
      @non_evt_starN State step n s2 fp2 s3 ->
      non_evt_starN step (S n)s1 (FP.union fp1 fp2) s3.
  Lemma non_evt_star_N_equiv{State:Type}:
    forall step s fp s',
      @non_evt_star State step s fp s' <-> exists n,non_evt_starN step n s fp s'.
  Proof.
    split;intros.
    induction H.
    exists 0;constructor.
    destruct IHnon_evt_star.
    exists (S x). econstructor;eauto.
    destruct H.
    induction H;econstructor;eauto.
  Qed.
  Ltac ccut H :=
    match type of H with
    | ?A -> ?B => enough(B);[clear H|apply H]
    end.

  Lemma usim_refine_done:
    forall j i mu fpS fpT spc tpc,
        R i mu fpS fpT spc tpc->
        forall fpT1 tpc1,
          non_evt_starN np_step j tpc fpT1 tpc1->
          final_state tpc1->
          SEtr SGE spc Behav_done.
  Proof.
    induction j.
    {
      intros.
      inversion H0;subst.
      eapply match_final in H1;eauto.
      Hsimpl. eapply tau_star_non_evt_star in H1.
      econstructor;eauto.
    }
    {
      induction i using(well_founded_induction (index_wf I ord R usim)).
      intros.
      inversion H1;subst.
      destruct H4 as [H4|H4].
      {
        assert(atom_bit tpc = atom_bit s2 \/ atom_bit tpc <> atom_bit s2).
        apply Classical_Prop.classic.
        destruct H3.
        {
          eapply match_tau_step in H4 as ?;eauto.
          destruct H5;Hsimpl;eauto.
          eapply IHj in H6 as ?;try apply H8;auto.
          inversion H9;subst.
          apply tau_plus2star in H5.
          apply tau_star_non_evt_star in H5.
          eapply non_evt_star_cons in H10;eauto.
          econstructor;eauto.
        }
        {
          eapply match_ent_atom in H3 as ?;eauto.
          Hsimpl. apply tau_star_non_evt_star in H5.
          eapply IHj in H6 as ?;try apply H10;auto.
          inversion H11;subst.
          pose proof @ETrace.ne_star_step _ (@np_step SGE) x0 x1 x2 fp pc'.
          ccut H14;auto.
          ccut H15;auto.
          eapply non_evt_star_cons in H14;eauto.
          econstructor;eauto.
        }
      }
      {
        eapply match_npsw_step in H4 as ?;eauto.
        Hsimpl.
        assert(GSimDefs.pc_valid_tid x2 (cur_tid s2)).
        specialize (H9 x3). Hsimpl.
        eapply match_tp in H11;eauto.
        Hsimpl.
        apply thrddom_eq'_comm in H13;auto.
        assert(GSimDefs.pc_valid_tid s2 (cur_tid s2)).
        inversion H4;subst;split;auto.
        eapply GlobSim.thrddom_eq'_valid_tid_preservation in H13;eauto.

        specialize (H9 (cur_tid s2)).
        Hsimpl.
        assert(({-|s2,cur_tid s2}) = s2). destruct s2;auto.
        rewrite H13 in H12;clear H13.

        eapply IHj in H6 as ?;try apply H12;auto.
        apply tau_star_non_evt_star in H3.
        assert(non_evt_star np_step x0 (FP.union x1 FP.emp) ({-|x2,cur_tid s2})).
        econstructor 2;eauto. constructor.
        inversion H13;subst.
        eapply non_evt_star_cons in H14;eauto.
        eapply non_evt_star_cons in H15;eauto.
        econstructor;eauto.

        intro swnottau;inversion swnottau.
      }
    }
  Qed.

  Lemma usim_refine_abort:
    forall j i mu fpS fpT spc tpc,
        R i mu fpS fpT spc tpc->
        forall fpT1 tpc1,
          non_evt_starN np_step j tpc fpT1 tpc1->
          np_abort tpc1->
          SEtr SGE spc Behav_abort.
  Proof.
    induction j.
    {
      intros.
      inversion H0;subst.
      eapply match_abort in H;eauto.
      Hsimpl. contradiction. 
    }
    {
      induction i using(well_founded_induction (index_wf I ord R usim)).
      intros.
      inversion H1;subst.
      destruct H4 as [H4|H4].
      {
        assert(atom_bit tpc = atom_bit s2 \/ atom_bit tpc <> atom_bit s2).
        apply Classical_Prop.classic.
        destruct H3.
        {
          eapply match_tau_step in H4 as ?;eauto.
          destruct H5;Hsimpl;eauto.
          eapply IHj in H6 as ?;try apply H8;auto.
          inversion H9;subst.
          apply tau_plus2star in H5.
          apply tau_star_non_evt_star in H5.
          eapply non_evt_star_cons in H10;eauto.
          econstructor;eauto.
        }
        {
          eapply match_ent_atom in H3 as ?;eauto.
          Hsimpl. apply tau_star_non_evt_star in H5.
          eapply IHj in H6 as ?;try apply H10;auto.
          inversion H11;subst.
          pose proof @ETrace.ne_star_step _ (@np_step SGE) x0 x1 x2 fp pc'.
          ccut H14;auto.
          ccut H15;auto.
          eapply non_evt_star_cons in H14;eauto.
          econstructor;eauto.
        }
      }
      {
        eapply match_npsw_step in H4 as ?;eauto.
        Hsimpl.
        assert(GSimDefs.pc_valid_tid x2 (cur_tid s2)).
        specialize (H9 x3). Hsimpl.
        eapply match_tp in H11;eauto.
        Hsimpl.
        apply thrddom_eq'_comm in H13;auto.
        assert(GSimDefs.pc_valid_tid s2 (cur_tid s2)).
        inversion H4;subst;split;auto.
        eapply GlobSim.thrddom_eq'_valid_tid_preservation in H13;eauto.

        specialize (H9 (cur_tid s2)).
        Hsimpl.
        assert(({-|s2,cur_tid s2}) = s2). destruct s2;auto.
        rewrite H13 in H12;clear H13.

        eapply IHj in H6 as ?;try apply H12;auto.
        apply tau_star_non_evt_star in H3.
        assert(non_evt_star np_step x0 (FP.union x1 FP.emp) ({-|x2,cur_tid s2})).
        econstructor 2;eauto. constructor.
        inversion H13;subst.
        eapply non_evt_star_cons in H14;eauto.
        eapply non_evt_star_cons in H15;eauto.
        econstructor;eauto.

        intro swnottau;inversion swnottau.
      }
    }
  Qed.


  Lemma usim_refine_cons:
    forall j i mu fpS fpT spc tpc,
      R i mu fpS fpT spc tpc->
      forall fpT1 tpc1 v tpc2,
        non_evt_starN np_step j tpc fpT1 tpc1->
        np_step tpc1 (evt v) FP.emp tpc2->
        exists k fpS1 spc1 spc2,
          non_evt_star np_step spc fpS1 spc1 /\
          np_step spc1 (evt v) FP.emp spc2 /\
          R k mu FP.emp FP.emp spc2 tpc2.
  Proof.
    induction j.
    {
      intros.
      inversion H0;subst.
      pose proof H1 as T1.
      eapply match_npsw_step in H1 ;eauto.
      Hsimpl.
      assert(GSimDefs.pc_valid_tid x2 (cur_tid tpc2)).
      specialize (H5 x3);Hsimpl.
      eapply match_tp in H7;eauto.
      Hsimpl.
      apply thrddom_eq'_comm in H9.
      assert(GSimDefs.pc_valid_tid tpc2 (cur_tid tpc2)).
      inversion T1;split;auto.
      eapply GlobSim.thrddom_eq'_valid_tid_preservation in H9;eauto.

      specialize (H5 (cur_tid tpc2));Hsimpl.
      assert(({-|tpc2,cur_tid tpc2}) = tpc2). destruct tpc2;auto.
      rewrite H9 in H8;clear H9.
      Esimpl;eauto. eapply tau_star_non_evt_star;eauto.
      assert(x1 =FP.emp). inversion H5;subst;auto. subst.
      auto.

      intro evtnottau;inversion evtnottau.
    }
    {
      induction i using(well_founded_induction (index_wf I ord R usim)).
      intros.
      inversion H1;subst.
      destruct H4 as [H4|H4].
      {
        assert(atom_bit tpc = atom_bit s2 \/ atom_bit tpc <> atom_bit s2).
        apply Classical_Prop.classic.
        destruct H3.
        {
          eapply match_tau_step in H4 as ?;eauto.
          destruct H5;Hsimpl;eauto.
          eapply IHj in H6 as ?;try apply H2;try apply H8.
          Hsimpl.
          apply tau_plus2star in H5.
          apply tau_star_non_evt_star in H5.
          eapply non_evt_star_cons in H9;eauto.
          Esimpl;eauto.
        }
        {
          eapply match_ent_atom in H3 as ?;eauto.
          Hsimpl. apply tau_star_non_evt_star in H5.
          eapply IHj in H6 as ?;try apply H10;eauto.
          Hsimpl.
          pose proof @ETrace.ne_star_step _ (@np_step SGE) x0 x1 x2 x5 x6.
          ccut H14;auto.
          ccut H15;auto.
          eapply non_evt_star_cons in H14;eauto.
          Esimpl;eauto.
        }
      }
      {
        eapply match_npsw_step in H4 as ?;eauto.
        Hsimpl.
        assert(GSimDefs.pc_valid_tid x2 (cur_tid s2)).
        specialize (H9 x3). Hsimpl.
        eapply match_tp in H11;eauto.
        Hsimpl.
        apply thrddom_eq'_comm in H13;auto.
        assert(GSimDefs.pc_valid_tid s2 (cur_tid s2)).
        inversion H4;subst;split;auto.
        eapply GlobSim.thrddom_eq'_valid_tid_preservation in H13;eauto.

        specialize (H9 (cur_tid s2)).
        Hsimpl.
        assert(({-|s2,cur_tid s2}) = s2). destruct s2;auto.
        rewrite H13 in H12;clear H13.

        eapply IHj in H6 as ?;try apply H12;eauto.
        Hsimpl.
        apply tau_star_non_evt_star in H3.
        assert(non_evt_star np_step x0 (FP.union x1 FP.emp) ({-|x2,cur_tid s2})).
        econstructor 2;eauto. constructor.
        eapply non_evt_star_cons in H13;eauto.
        eapply non_evt_star_cons in H13;eauto.
        Esimpl;eauto.

        intro swnottau;inversion swnottau.
      }
    }
  Qed.
  Lemma usim_refine:
      forall i mu fpS fpT spc tpc,
        R i mu fpS fpT spc tpc->
        forall b,
          SEtr TGE tpc b->
          SEtr SGE spc b.
  Proof.
    cofix.
    intros.
    inversion H0;subst.
    {
      apply  non_evt_star_N_equiv in H1 as [].
      eapply usim_refine_done;eauto.
    }
    {
      apply  non_evt_star_N_equiv in H1 as [].
      eapply usim_refine_abort;eauto.
    }
    {
      econstructor. eapply usim_Sdiverge_preserve ;eauto.
    }
    {
      apply non_evt_star_N_equiv in H1 as [].
      eapply usim_refine_cons in H1;try eassumption.
      Hsimpl.
      econstructor;eauto.
    }
  Qed.
End usim_diverge.

(** ** Main result: upward simulation implies NP-refinement *)
Theorem USim_Refine:
  forall NL (L: @langs NL) (sprog tprog: prog L),
    GlobUSim sprog tprog ->
    np_prog_refine sprog tprog.
Proof.
  intros.
  econstructor.
  intros.
  unfold GlobUSim in H.
  specialize (H mu sgm sge spc tgm tge tpc t H0 H1 H2).
  destruct H as (I&ord&R&i&HSim&Hmatch).
  unfold np_config_refine.
  intros.
  apply SEtr_exists in H.
  apply SEtr_sound.
  inversion H1;subst;auto. inversion H3;auto.
  inversion H1;subst. eapply ThreadPool.init_inv;eauto.
  eapply usim_refine;eauto.
Qed.

Lemma np_safe_config_cons:
  forall ge pc l fp pc',
    star np_step pc l fp pc'->
    @np_safe_config ge pc->
    np_safe_config pc'.
Proof.
  induction 1;auto.
  inversion 1. apply H3 in H;eauto.
Qed.
Lemma np_safe_config_safe_state:
  forall ge pc,
    @np_safe_config ge pc <->
    safe_state np_step np_abort pc.
Proof.
  split;intros.
  unfold safe_state;intros.
  apply np_safe_config_cons in H0 as [];eauto.
  revert ge pc H.
  cofix. intros.
  unfold safe_state in H.
  
  econstructor. eapply H. constructor.
  intros. assert(safe_state np_step np_abort s').
  unfold safe_state. intros. eapply star_step in H0;eauto.
  eauto.
Qed.
Inductive starN {ge}: nat -> @ProgConfig ge->list glabel ->FP.t->@ProgConfig ge ->Prop:=
  | star0:forall s,starN 0 s nil FP.emp s
  | star_step':forall i s1 e fp1 s2 l fp2 s3,
      np_step s1 e fp1 s2->
      starN i s2 l fp2 s3->
      starN (S i) s1 (cons e l) (FP.union fp1 fp2) s3.
Lemma star_starN_equiv:
    forall ge pc pc' l fp,
      star (@np_step ge) pc l fp pc' <-> exists i,starN i pc l fp pc'.
Proof.
  split;intro.
  induction H.
  eexists;constructor.
  destruct IHstar. eexists;econstructor;eauto.
  destruct H.
  revert pc pc' l fp H.
  induction x;intros. inversion H;subst. constructor.
  inversion H;subst.
  econstructor;eauto.
Qed.
Lemma USim_Safe_config':
  forall sge tge I ord match_state,
    @GConfigUSim sge tge I ord match_state->
    forall i mu fpS fpT spc tpc,
    match_state i mu fpS fpT spc tpc->
    safe_state np_step np_abort tpc.
Proof.
  unfold safe_state;intros.
  apply star_starN_equiv in H1 as [].
  revert sge tge I ord match_state H i mu fpS fpT spc tpc l fp s' H0 H1.
  induction x.
  {
    intros.
    inversion H1;subst;clear H1.
    eapply match_abort in H0 as [];eauto.
  }
  {
    intros.
    inversion H1;subst.
    eapply GUSim_progress in H3 as ?;eauto.
    Hsimpl;eauto.
  }
Qed.
Lemma USim_Safe_Config:
  forall NL L sprog tprog,
    @GlobUSim NL L sprog tprog->
    forall mu sgm sge spc tgm tge tpc,
      InitRel mu sge tge sgm tgm->
      init_config sprog sgm sge spc spc.(cur_tid)->
      init_config tprog tgm tge tpc tpc.(cur_tid)->
      spc.(cur_tid) = tpc.(cur_tid)->
      np_safe_config tpc.
Proof.
  intros.
  rewrite<- H3 in H2.
  edestruct H;eauto.
  Hsimpl.
  eapply  np_safe_config_safe_state;eauto.
  eapply USim_Safe_config';eauto.
Qed.