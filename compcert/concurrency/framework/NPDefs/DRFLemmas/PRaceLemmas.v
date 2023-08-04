Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics GlobSemantics_Lemmas NPSemantics TypedSemantics .

Require Import DRF USimDRF NPDRF FPLemmas.

Require Import Classical Wf Arith.
(** This file contains auxiliary definitions used in the proof of equivalence of NPDRF and DRF*) 
Local Notation "'<<' i ',' c ',' sg ',' F '>>'" := {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|} (at level 60, right associativity).
Local Definition pc_valid_tid {ge}:= @GSimDefs.pc_valid_tid ge.
Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:= D|}(at level 70,right associativity).  Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).
Section PRace.
  Lemma tau_star_np_step_star_glob_step:
    forall ge pc pc' fp',
       tau_star (@np_step ge) pc fp' pc' ->
      tau_star glob_step pc fp' pc'.
  Proof.
    intros.
    induction H.
    constructor.
    apply type_step_exists in H as [].
    destruct x;try (inversion H;reflexivity).
    apply core_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    apply call_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    apply ret_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    apply entat_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    assert(L:fp=FP.emp). inversion H;auto. subst.
    apply allhalt_step_equiv in H as [];apply type_glob_step_elim in H;econstructor 2;eauto.
  Qed.

  Inductive glob_predict{GE:GlobEnv.t}:@ProgConfig GE -> tid -> Bit -> FP.t -> Prop :=
  |predict0:
     forall pc pc' fp t,
       @type_glob_step GE core ({-|pc,t}) tau fp pc' ->
       atom_bit pc = O ->
       glob_predict pc t O fp
  |predictI:
     forall pc pc' pc'' fp t,
       @type_glob_step GE entat ({-|pc,t}) tau FP.emp pc' ->
       tau_star (type_glob_step core) pc' fp pc'' ->
       glob_predict pc t I fp.
  Lemma predict_equiv:
    forall ge pc t b fp,
      @predict ge pc t b fp <-> glob_predict pc t b fp.
  Proof.
    split;intro.
    {
      inversion H;subst.
      pose proof H_core_step as Tmp1.
      eapply local_core_step in Tmp1 as (c'&?&thdp'&?) ;eauto.      
      econstructor; econstructor;eauto.
      
      assert(exists c',Core.update c cc' c').
      eexists;econstructor;eauto.
      destruct H0 as (c'&H_core_upd).
      pose proof H_tp_core as backup1.
      unfold ThreadPool.get_top in H_tp_core.
      destruct (ThreadPool.get_cs thdp t) eqn:eq;[|inversion H_tp_core].
      unfold CallStack.top in H_tp_core.
      destruct t1 eqn:eq2;inversion H_tp_core;subst;clear H_tp_core.
      rename backup1 into H_tp_core.
      assert(exists thdp',ThreadPool.update thdp t c' thdp').
      eexists. econstructor;eauto. econstructor;eauto.
      destruct H0 as (t'&H_tp_upd).
      assert(entat_step:type_glob_step entat ({thdp, t, gm, O}) tau FP.emp ({t',t,gm,I})).
      econstructor;eauto.
      unfold ThreadPool.get_top in H_tp_core.
      destruct (ThreadPool.get_cs thdp t) eqn:eq2;[|inversion H_tp_core].
      assert(ThreadPool.get_cs t' t = Some(c'::t3)%list).
      unfold ThreadPool.get_cs.
      inversion H_tp_upd;subst.
      simpl. rewrite Maps.PMap.gsspec.
      destruct Coqlib.peq;[|contradiction].
      inversion H1;subst.
      rewrite H0 in eq2.
      inversion eq2;inversion eq;subst.
      inversion H5;subst.
      auto.
      assert(ThreadPool.get_top t' t = Some c').
      unfold ThreadPool.get_top. rewrite H0;auto.
      inversion H_core_upd;subst.
      eapply star_local_core_step with(d:=I) in H_core_step as [];eauto.
      econstructor 2;eauto.
    }
    {
      inversion H;subst.
      inversion H0;subst.
      destruct pc as (thdp,t',gm,b).
      compute in H1;subst.
      simpl in *.
      econstructor ;eauto.

      inversion H0;subst.
      destruct pc as (thdp,t',gm,b).
      compute in H6;subst.
      simpl in *.
      destruct pc''.

      pose proof H1 as Tmp1.
      apply star_core_step_equiv in Tmp1.
      apply tau_star_type_step in Tmp1.
      assert(cur_tid = t).
      apply GlobSim.GlobSim.tau_star_tid_preservation in Tmp1;auto.
      subst.
      assert(atom_bit = I).
      apply tau_star_tau_N_equiv in Tmp1 as [].
      apply GlobSim.GlobSim.tau_N_bit_I_preservation in H2;auto.
      subst.
      clear Tmp1.

      destruct c.
      destruct c'.
      inversion H_core_update;subst.
      simpl in H2.
      assert(ThreadPool.get_top thdp' t = Some (<< i,cc',sg,F>>)).
      unfold ThreadPool.get_top.
      inversion H_tp_upd;subst.
      unfold ThreadPool.get_cs.
      simpl.
      rewrite Maps.PMap.gsspec.
      destruct Coqlib.peq;[|contradiction].
      inversion H4;subst;auto.
      compute [CallStack.top].
      rewrite H2;auto.

      pose proof H3 as Tmp1.
      eapply corestar_localstar in Tmp1 as [cc''[]];eauto.
      econstructor 2;eauto.
    }
  Qed.

  Definition glob_npnsw_step {GE}(pc:@ProgConfig GE)(l:glabel)(fp:FP.t)(pc':@ProgConfig GE):Prop:=
    @type_glob_step GE core pc l fp pc' \/
    type_glob_step call pc l fp pc' \/
    type_glob_step ret pc l fp pc'.    

  Lemma glob_npnsw_step_bitO_preserve{GE}:
    forall pc l fp pc',
      atom_bit pc = O ->
      @glob_npnsw_step GE pc l fp pc'->
      atom_bit pc' = O.
  Proof.  inversion 2 as [T|[T|T]];inversion T;subst;auto. Qed.
  Lemma glob_npnsw_star_bitO_preserve{GE}:
    forall pc fp pc',
      atom_bit pc = O ->
      tau_star (@glob_npnsw_step GE) pc fp pc'->
      atom_bit pc' = O.
  Proof.
    induction 2;auto.
    apply IHtau_star.
    eapply glob_npnsw_step_bitO_preserve;eauto.
  Qed.
  Lemma glob_npnsw_step_to_np_step{GE}:
    forall pc l fp pc',
      @glob_npnsw_step GE pc l fp pc' ->
      np_step pc l fp pc'.
  Proof.
    intros.
    inversion H as [|[]];subst;inversion H0;subst.
    econstructor;eauto.
    eapply NPSemantics.Call;eauto.
    eapply NPSemantics.Return;eauto.
  Qed.
  Lemma glob_npnsw_star_to_np_taustar{GE}:
    forall pc fp pc',
      tau_star (@glob_npnsw_step GE) pc fp pc'->
      tau_star np_step pc fp pc'.
  Proof.
    induction 1. constructor.
    econstructor 2;eauto.
    eapply glob_npnsw_step_to_np_step;eauto.
  Qed.
  Inductive glob_predict_star{GE}:@ProgConfig GE -> tid -> Bit -> FP.t -> Prop :=
  | star_predict0:
      forall pc pc' fp t,
        tau_star glob_npnsw_step ({-|pc,t}) fp pc' ->
        atom_bit pc = O ->
        glob_predict_star pc t O fp
  | star_predictI:
      forall pc pc' pc'' fp t,
        @type_glob_step GE entat ({-|pc,t}) tau FP.emp pc' ->
        tau_star (type_glob_step core) pc' fp pc'' ->
        glob_predict_star pc t I fp.

  Inductive np_predict_star{GE}:@ProgConfig GE->tid->Bit->FP.t->Prop:=
  | np_predict0_star:
      forall pc pc' fp t,
        tau_star np_step ({-|pc,t}) fp pc' ->
        atom_bit pc = O -> atom_bit pc' = O ->
        @np_predict_star GE pc t O fp
  | np_predictI_star:
      forall pc pc1 pc2 pc3 fp1 fp2 t,
        tau_star np_step ({-|pc,t}) fp1 pc1 -> atom_bit pc = O -> 
        type_np_step entat pc1 tau FP.emp pc2 ->
        tau_star np_step pc2 fp2 pc3->
        @np_predict_star GE pc t I (FP.union fp1 fp2).

  Inductive glob_predict_star_alter{GE}:@ProgConfig GE->tid->Bit->FP.t->Prop:=
  | glob_predict0_star_alter:
      forall pc pc' fp t,
        tau_star glob_npnsw_step ({-|pc,t}) fp pc' ->
        atom_bit pc = O -> atom_bit pc' = O ->
        glob_predict_star_alter pc t O fp
  | glob_predictI_star_alter:
      forall pc pc1 pc2 pc3 fp1 fp2 t,
        tau_star glob_npnsw_step ({-|pc,t}) fp1 pc1 -> atom_bit pc = O -> 
        type_glob_step entat pc1 tau FP.emp pc2 ->
        tau_star (type_glob_step core) pc2 fp2 pc3->
        glob_predict_star_alter pc t I (FP.union fp1 fp2).
  Lemma glob_predict_star_to_alter:
    forall GE pc t b fp,
      @glob_predict_star GE pc t b fp ->
      glob_predict_star_alter pc t b fp.
  Proof.
    inversion 1;subst.
    econstructor;eauto.
    eapply glob_npnsw_star_bitO_preserve in H0;eauto.
    rewrite <-FP.emp_union_fp with (fp:=fp).
    econstructor 2;eauto.
    constructor.
    inversion H0;auto.
  Qed.
  Definition nonhalt_biteq_tau_npstep {GE}(pc:@ProgConfig GE)(l:glabel)(fp:FP.t)(pc':@ProgConfig GE):Prop:=
    type_np_step core pc l fp pc' \/ type_np_step call pc l fp pc' \/ type_np_step ret pc l fp pc'.

  Lemma npstep_nohalt{GE}:
    forall x pc fp pc' fp' pc'',
      @type_np_step GE x pc tau fp pc' ->
      np_step pc' tau fp' pc'' ->
      x <> allhalt.
  Proof.
    intros.
    inversion H;subst;try(intro contra;inversion contra;fail).
    assert(exists c',ThreadPool.get_top thdp' t = Some c').
    inversion H0;eauto.
    destruct H1.
    unfold ThreadPool.get_top in H1.
    destruct ThreadPool.get_cs eqn:?;inversion H1;clear H1;subst.
    inversion H_thread_halt;subst.
    rewrite Heqo in H1;inversion H1;clear H1;subst.
    inversion H2;subst.
    inversion H3.
  Qed.
  Lemma npstep_biteq_nohalt{GE}:
    forall pc fp pc' fp' pc'',
      @np_step GE pc tau fp pc' ->
      atom_bit pc = atom_bit pc' ->
      np_step pc' tau fp' pc'' ->
      nonhalt_biteq_tau_npstep pc tau fp pc'.
  Proof.
    intros.
    apply type_step_exists in H as [].
    destruct x;try (inversion H;subst;inversion H0;fail);unfold nonhalt_biteq_tau_npstep;auto.
    eapply npstep_nohalt in H;eauto.
    contradiction.
  Qed.

  Lemma nptaustar_nohalt{GE}:
    forall pc fp pc' fp' pc'',
      tau_star (@np_step GE) pc fp pc' ->
      atom_bit pc = atom_bit pc' ->
      np_step pc' tau fp' pc'' ->
      tau_star nonhalt_biteq_tau_npstep pc fp pc'.
  Proof.
    intros until pc'';intro H.
    revert pc'' fp'.
    induction H;intros. constructor.
    apply tau_star_tau_N_equiv in H0 as L1.
    destruct L1.
    destruct x.
    inversion H3;clear H3;subst.
    clear H0.
    econstructor;eauto. eapply npstep_biteq_nohalt;eauto.
    eapply GlobSim.GlobSim.tau_N_tau_step_bit_rule in H1 as E1;eauto.
    rewrite E1 in H1.
    eapply IHtau_star in H1;eauto.
    econstructor;eauto.
    inversion H3;subst.
    eapply npstep_biteq_nohalt ;eauto.
  Qed.

  Lemma nohalt_nptaustar{GE}:
    forall pc fp pc',
      tau_star nonhalt_biteq_tau_npstep pc fp pc'->
      tau_star (@np_step GE) pc fp pc' /\ atom_bit pc = atom_bit pc'.
  Proof.
    induction 1;intros.
    split;[constructor|];auto.
    destruct IHtau_star.
    assert(atom_bit s = atom_bit s').
    destruct H as [|[]];inversion H;auto.
    split;try congruence.
    eapply tau_star_star;eauto.
    apply tau_plus2star;constructor.
    destruct H as [|[]];eapply type_step_elim;eauto.
  Qed.
  Lemma nonhalt_biteq_tau_npstep_glob_npnsw_step_equiv{GE}:
    forall pc l fp pc',
      nonhalt_biteq_tau_npstep pc l fp pc' <-> @glob_npnsw_step GE pc l fp pc'.
  Proof.
    intros.
    split;intro;destruct H as [|[]];assert(l=tau);try (inversion H;auto;fail);subst.
    apply core_step_equiv in H;left;auto.
    apply call_step_equiv in H;right;left;auto.
    apply ret_step_equiv in H;right;right;auto.
    apply core_step_equiv in H;left;auto.
    apply call_step_equiv in H;right;left;auto.
    apply ret_step_equiv in H;right;right;auto.
  Qed.
  Lemma nonhalt_biteq_taustar_npnsw_tau_star_equiv{GE}:
    forall pc fp pc',
      tau_star nonhalt_biteq_tau_npstep pc fp pc' <-> tau_star (@glob_npnsw_step GE) pc fp pc'.
  Proof. split;induction 1;intros;econstructor;eauto;eapply nonhalt_biteq_tau_npstep_glob_npnsw_step_equiv;eauto. Qed.

  Inductive race {ge} : (@ProgConfig ge->tid->Bit->FP.t->Prop)->@ProgConfig ge ->Prop :=
    Race: forall (predict:@ProgConfig ge->tid->Bit->FP.t->Prop) pc t1 b1 fp1 t2 b2 fp2,
      t1 <> t2 ->
      predict pc t1 b1 fp1 ->
      predict pc t2 b2 fp2 ->
      b1 <> I \/ b2 <> I ->
      FP.conflict fp1 fp2 ->
      race predict pc.
  Lemma race_equiv:
    forall ge pc,
      @race_config ge pc <-> race predict pc.
  Proof.
    split;intro;inversion H;subst.
    econstructor;eauto.
    econstructor;try apply H0;eauto.
  Qed.
  Lemma nprace_equiv:
    forall ge pc,
      @np_race_config ge pc  <-> race np_predict_star pc.
  Proof.
    split;intro.
    {
      Coqlib.inv H.
      assert(FP.conflict fp10 fp20\/FP.conflict fp11 fp20 \/ FP.conflict fp10 fp21).
      inversion H3;auto.
      clear H3.
      inversion H1;inversion H2;clear H1;clear H2;subst.
      {
        eapply np_normal_iff_tau_star_bitpreservation in H3 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H8 as (?&?&?&?).
        inversion H9;clear H9;subst.
        simpl in *;subst. clear H2 H3 H6 H7.
        econstructor;eauto.
        econstructor;eauto.
        econstructor;eauto.
        left;intro contra;inversion contra.
        destruct H as [|[]];auto;apply FP.emp_never_conflict in H as [];contradiction.        
      }
      {
        eapply np_normal_iff_tau_star_bitpreservation in H3 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H8 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H10 as (?&?&?&?).
        inversion H11;clear H11;subst.
        inversion H9;clear H9;subst.
        simpl in *;subst. clear H2 H3 H6 H7.
        econstructor;eauto.
        econstructor;eauto.
        econstructor 2;eauto.
        apply type_step_exists in H11 as [].
        destruct x;inversion H2;subst;congruence.
        left;intro contra;inversion contra.
        destruct H as [|[]].
        apply conflict_union_ano;auto.
        apply FP.emp_never_conflict in H as [];contradiction.
        rewrite FP.union_comm_eq.
        apply conflict_union_ano;auto.        
      }
      {
        eapply np_normal_iff_tau_star_bitpreservation in H3 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H5 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H10 as (?&?&?&?).
        inversion H11;clear H11;subst.
        inversion H4;clear H4;subst.
        simpl in *;subst. clear H2 H3 H12 H13.
        apply type_step_exists in H8 as [].
        destruct x;try(inversion H2;subst;fail).
        rewrite <- H16 in H9.
        econstructor;eauto.
        econstructor 2;eauto.
        econstructor;eauto.
        right;intro contra;inversion contra.
        destruct H as [|[]].
        eapply conflict_union;eauto.
        rewrite FP.union_comm_eq.
        eapply conflict_union;eauto.
        apply FP.emp_never_conflict in H as [];contradiction.
      }
      {
        eapply np_normal_iff_tau_star_bitpreservation in H3 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H5 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H10 as (?&?&?&?).
        eapply np_normal_iff_tau_star_bitpreservation in H12 as (?&?&?&?).
        inversion H13;clear H13;subst.
        simpl in *;subst. clear H2 H14.
        destruct H as [|[]].
        econstructor;eauto.
        econstructor ;eauto.
        econstructor;eauto.
        left;intro contra;inversion contra.

        econstructor 1 with(fp1:=FP.union fp10 fp11);eauto.
        econstructor 2;eauto.
        inversion H4;subst;simpl in *.
        inversion H2;subst;econstructor;eauto.
        econstructor;eauto.
        right;intro contra;inversion contra.
        rewrite FP.union_comm_eq.
        eapply conflict_union;eauto.

        econstructor 1 with(fp2:=FP.union fp20 fp21);eauto.
        econstructor;eauto.
        econstructor 2;eauto.
        inversion H11;subst;simpl in *.
        inversion H2;subst;econstructor;eauto.
        left;intro contra;inversion contra.
        rewrite FP.union_comm_eq.
        eapply conflict_union_ano;eauto.
      }
    }
    {
      inversion H;subst;clear H.
      destruct pc as [thdp tid tgm tbit].
      Coqlib.inv H1;Coqlib.inv H2;simpl in *;subst.
      econstructor 1 with(fp10:=fp1)(fp11:=FP.emp)(fp20:=fp2)(fp21:=FP.emp);eauto.
      econstructor 1 with(pc':=pc');eauto.
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      econstructor 1 with(pc':=pc'0);eauto.
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      econstructor;eauto.

      econstructor 1 with(fp10:=fp1)(fp11:=FP.emp)(fp20:=fp0)(fp21:=fp3);eauto.
      econstructor 1 with(pc':=pc');eauto.
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      assert(atom_bit pc2 = I). Coqlib.inv H8;auto.
      assert(atom_bit pc3 = I). apply tau_star_tau_N_equiv in H9 as [];eapply GlobSim.GlobSim.tau_N_bit_I_preservation;eauto. 
      assert(cur_tid pc1 = t2). apply GlobSim.GlobSim.tau_star_tid_preservation in H1;auto.

      econstructor 2 with(pc':=pc1)(pc'':=pc2)(pc''':=pc3);eauto.
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      inversion H8;auto.
      inversion H8;simpl in *;subst;simpl in *;subst.
      econstructor;eauto.
      econstructor;eauto.      
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      congruence.
      Coqlib.inv H8;auto.
      assert(FP.conflict fp1 fp0 \/ ~FP.conflict fp1 fp0).
      apply classic.
      destruct H2.
      econstructor;eauto.
      assert(FP.conflict fp1 fp3 \/ ~FP.conflict fp1 fp3).
      apply classic.
      destruct H5.
      econstructor 3;eauto.
      eapply FP.smile_conflict_compat in H5.
      eapply FP.smile_conflict_compat in H2.
      eapply fpsmile_sym in H2.
      eapply fpsmile_sym in H5.
      eapply fpsmile_union with(fp2:=fp3) in H2;eauto.
      eapply fpsmile_sym in H2.
      eapply FP.smile_conflict_compat in H2.
      contradiction.

      econstructor 1 with(fp10:=fp2)(fp11:=FP.emp)(fp20:=fp0)(fp21:=fp3)(t1:=t2)(t2:=t1);eauto.
      econstructor 1 with(pc':=pc');eauto.
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      assert(atom_bit pc2 = I). Coqlib.inv H6;auto.
      assert(atom_bit pc3 = I). apply tau_star_tau_N_equiv in H7 as [];eapply GlobSim.GlobSim.tau_N_bit_I_preservation;eauto. 
      assert(cur_tid pc1 = t1). apply GlobSim.GlobSim.tau_star_tid_preservation in H;auto.
      econstructor 2 with(pc':=pc1)(pc'':=pc2)(pc''':=pc3);eauto.
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      inversion H6;auto.
      inversion H6;simpl in *;subst;simpl in *;subst.
      econstructor;eauto.
      econstructor;eauto.      
      eapply np_normal_iff_tau_star_bitpreservation;repeat match goal with H:_|-_/\_=>split end;eauto.
      congruence.
      Coqlib.inv H6;auto.
      assert(FP.conflict fp0 fp2 \/ ~FP.conflict fp0 fp2).
      apply classic.
      destruct H2.
      econstructor;eauto. apply FP.conflict_sym;auto.
      assert(FP.conflict fp3 fp2 \/ ~FP.conflict fp3 fp2).
      apply classic.
      destruct H5.
      econstructor 3;eauto. apply FP.conflict_sym;auto.
      eapply FP.smile_conflict_compat in H5.
      eapply FP.smile_conflict_compat in H2.
      eapply fpsmile_union with(fp2:=fp3) in H2;eauto.
      eapply FP.smile_conflict_compat in H2.
      contradiction.

      destruct H3;contradiction.
    }
  Qed.
  Lemma predict_equiv_race_equiv:
    forall ge predict1 predict2,
      (forall (pc:@ProgConfig ge) t b fp, predict1 pc t b fp <-> predict2 pc t b fp) ->
      (forall pc,@race ge predict1 pc <-> race predict2 pc).
  Proof.
    split;intro;inversion H0;subst;apply H in H2;apply H in H3;econstructor;eauto.
  Qed.

  Lemma predict_race_to_star:
    forall ge pc,
      @race ge glob_predict pc -> race glob_predict_star pc.
  Proof.
    intros.
    inversion H;subst.
    inversion H1;inversion H2;subst.
    econstructor;eauto.
    rewrite <-FP.fp_union_emp with(fp:=fp1).
    econstructor;eauto. econstructor;eauto;[left;eauto|constructor].
    rewrite <-FP.fp_union_emp with(fp:=fp2).
    econstructor;eauto. econstructor;eauto;[left;eauto|constructor].

    econstructor;eauto.
    rewrite <-FP.fp_union_emp with(fp:=fp1).
    econstructor;eauto. econstructor;eauto;[left;eauto|constructor].
    econstructor;eauto.

    econstructor;eauto.
    econstructor;eauto.
    rewrite <-FP.fp_union_emp with(fp:=fp2).
    econstructor;eauto. econstructor;eauto;[left;eauto|constructor].

    destruct H3;contradiction.
  Qed.
    


  Lemma predict_star_race_to_alter:
    forall ge pc,
      @race ge glob_predict_star pc -> race glob_predict_star_alter pc.
  Proof.
    inversion 1;subst.
    apply glob_predict_star_to_alter in H1.
    apply glob_predict_star_to_alter in H2.
    econstructor;eauto.
  Qed.
  Lemma race_np_predict_starOO_glob_predict_star_alter:
    forall ge pc t1 fp1 pc1 t2 fp2 pc2,
      t1 <> t2 ->
      tau_star (@np_step ge) ({-|pc,t1}) fp1 pc1 ->
      atom_bit pc = O -> atom_bit pc1 = O ->
      tau_star np_step ({-|pc,t2}) fp2 pc2 ->
      atom_bit pc2 = O -> FP.conflict fp1 fp2 ->
      race glob_predict_star_alter pc.
  Proof.
    intros.
    eapply conflict_min_rule_extended in H5;eauto;simpl;try congruence.
    destruct H5 as (pc10&pc11&fp10&fp11&star1&biteq1&step1&biteq2&pc20&pc21&fp20&fp21&star2&biteq3&step2&biteq4&smile1&smile2&smile3&conflict1&subset1&subset2&subset3&subset4).
    eapply nptaustar_nohalt in star1;eauto.
    eapply nptaustar_nohalt in star2;eauto.
    eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star1;eauto.
    eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star2;eauto.
    apply FP.emp_never_conflict in conflict1 as N1.
    destruct N1 as [N1 N2].
    apply type_step_exists in step1 as [x step1].        
    destruct x;try(inversion step1;subst;inversion biteq2;contradiction;fail).
    apply core_step_equiv in step1.
    apply type_step_exists in step2 as [x step2].
    destruct x;try(inversion step2;subst;inversion biteq4;contradiction;fail).
    apply core_step_equiv in step2.
    simpl in *.
    econstructor 1 with(fp1:=FP.union fp10 fp11)(fp2:=FP.union fp20 fp21);eauto.
    econstructor 1 with(pc':=pc11);eauto.
    eapply tau_star_star;eauto. apply tau_plus2star. constructor. left;eauto.
    congruence.
    econstructor 1 with(pc':=pc21);eauto.
    eapply tau_star_star;eauto. apply tau_plus2star. constructor. left;eauto.
    congruence.
    left. intro contra;inversion contra.
    rewrite FP.union_comm_eq.
    apply conflict_union.
    rewrite FP.union_comm_eq.
    apply conflict_union_ano.
    assumption.
  Qed.
  Lemma race_np_predict_starOI_glob_predict_star_alter:
    forall ge pc t1 fp1 pc1 t2 fp2 pc2 pc3 fp3 pc4,
      t1 <> t2 ->
      tau_star (@np_step ge) ({-|pc,t1}) fp1 pc1 ->
      atom_bit pc = O -> atom_bit pc1 = O ->
      tau_star np_step ({-|pc,t2}) fp2 pc2 ->
      atom_bit pc2 = O ->
      type_np_step entat pc2 tau FP.emp pc3->
      tau_star np_step pc3 fp3 pc4 ->
      FP.conflict fp1 (FP.union fp2 fp3) ->
      race glob_predict_star_alter pc.
  Proof.
    intros.
    assert(FP.conflict fp1 fp2 \/ ~ FP.conflict fp1 fp2).
    apply classic.
    destruct H8.
    eapply race_np_predict_starOO_glob_predict_star_alter;eauto.
    apply fpconflict_union in H7.
    destruct H7;try contradiction.

    assert(atom_bit pc3 = I). inversion H5;auto.
    assert(atom_bit pc4 = I).
    eapply tau_star_tau_N_equiv in H6 as [].
    eapply GlobSim.GlobSim.tau_N_bit_I_preservation;eauto.
    eapply conflict_min_rule_extended in H7;eauto;simpl;try congruence.
    destruct H7 as (pc10&pc11&fp10&fp11&star1&biteq1&step1&biteq2&pc20&pc21&fp20&fp21&star2&biteq3&step2&biteq4&smile1&smile2&smile3&conflict1&subset1&subset2&subset3&subset4).
    
    eapply nptaustar_nohalt in star1;eauto.
    eapply nptaustar_nohalt in star2;eauto.
    apply type_step_elim in H5 as step'.
    eapply nptaustar_nohalt in H3;eauto;simpl;try congruence.
    eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star1;eauto.
    eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star2;eauto.
    eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H3;eauto.
    apply entat_step_equiv in H5.
    apply FP.emp_never_conflict in conflict1 as N1.
    destruct N1 as [N1 N2].
    apply type_step_exists in step1 as [x step1].        
    destruct x;try(inversion step1;subst;inversion biteq2;contradiction;fail).
    apply core_step_equiv in step1.
    apply type_step_exists in step2 as [x step2].
    destruct x;try(inversion step2;subst;inversion biteq4;contradiction;fail).
    apply core_step_equiv in step2.
    simpl in *.
    econstructor 1 with(fp1:=FP.union fp10 fp11)(fp2:=FP.union fp2(FP.union fp20 fp21));eauto.
    econstructor 1 with(pc':=pc11);eauto.
    eapply tau_star_star;eauto. apply tau_plus2star. constructor;left;auto.
    congruence.
    econstructor 2 with(pc3:=pc21);eauto.
    eapply tau_star_star;eauto.
    Focus 2. apply tau_plus2star. constructor. eauto.
    revert H9 star2;clear;intros.
    induction star2.
    constructor.
    assert(atom_bit s' = I).
    destruct H as [|[]];Coqlib.inv H;inversion H9;auto.
    specialize (IHstar2 H0).
    destruct H as [|[]];try (Coqlib.inv H;inversion H9;fail).
    econstructor;eauto.

    left. intro contra;inversion contra.

    rewrite FP.union_comm_eq;apply conflict_union.
    do 2 (rewrite FP.union_comm_eq;apply conflict_union_ano).
    assumption.    
  Qed.
  Lemma nppredictrace_globpredictstaraltrace_equiv:
    forall ge pc,
      @race ge np_predict_star pc <-> race glob_predict_star_alter pc.
  Proof.
    split;intro;Coqlib.inv H.
    {
      Coqlib.inv H1;Coqlib.inv H2.
      eapply race_np_predict_starOO_glob_predict_star_alter;eauto.
      eapply race_np_predict_starOI_glob_predict_star_alter;eauto.
      Coqlib.inv H8;auto.
      eapply race_np_predict_starOI_glob_predict_star_alter with(t2:=t1)(t1:=t2);eauto.
      Coqlib.inv H6;auto.
      apply FP.conflict_sym;auto.
      destruct H3;contradiction.      
    }
    {
      Coqlib.inv H1;Coqlib.inv H2.
      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H.
      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H1.
      eapply nohalt_nptaustar in H as (?&_).
      eapply nohalt_nptaustar in H1 as (?&_).
      econstructor;eauto;econstructor;eauto.

      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H.
      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H1.
      eapply nohalt_nptaustar in H as (?&_).
      eapply nohalt_nptaustar in H1 as (?&_).
      eapply entat_step_equiv in H8.
      apply star_core_step_equiv in H9.
      apply tau_star_type_step in H9.
      econstructor;eauto;econstructor;eauto.

      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H.
      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H1.
      eapply nohalt_nptaustar in H as (?&_).
      eapply nohalt_nptaustar in H1 as (?&_).
      eapply entat_step_equiv in H6.
      apply star_core_step_equiv in H7.
      apply tau_star_type_step in H7.
      econstructor;eauto;econstructor;eauto.

      destruct H3;contradiction.
    }
  Qed.
  Definition star_race {ge} (predict:@ProgConfig ge->tid->Bit->FP.t->Prop)(pc:ProgConfig):Prop:=
    exists l fp pc',ETrace.star glob_step pc l fp pc' /\ race predict pc'.
  Lemma star_race_equiv:
    forall ge pc,
      @star_race_config ge pc <-> star_race predict pc.
  Proof.
    split;intro.
    unfold star_race_config in H.
    destruct H as (l&fp&pc'&star1&race1).
    exists l,fp,pc'. split;auto.
    apply race_equiv;auto.

    unfold star_race in H.
    destruct H as (l&fp&pc'&star1&race1).
    exists l,fp,pc'. split;auto.
    apply race_equiv;auto.
  Qed.    
  Lemma predict_equiv_to_star_race_equiv:
     forall ge predict1 predict2,
      (forall (pc:@ProgConfig ge) t b fp, predict1 pc t b fp <-> predict2 pc t b fp) ->
      (forall pc,@star_race ge predict1 pc <-> star_race predict2 pc).
  Proof.
    unfold star_race.
    split;intros;
    destruct H0 as (l&fp&pc'&star1&race1);
    eapply predict_equiv_race_equiv in H;
    apply H in race1;
    exists l,fp,pc';split;auto.
  Qed.
  Lemma glob_predict_to_star:
    forall ge pc fp b t,
      @glob_predict ge pc b t fp -> glob_predict_star pc b t fp.
  Proof.
    intros.
    inversion H;subst; econstructor;eauto.
    rewrite<- FP.fp_union_emp with(fp:=fp).
    econstructor 2;eauto.
    unfold glob_npnsw_step;left;eauto.
    constructor.
  Qed.
  Lemma star_race_to_star_predict_race:
    forall ge pc,
      @star_race ge glob_predict pc -> star_race glob_predict_star pc.
  Proof.
    intros;unfold star_race in *.
    destruct H as (l&fp&pc'&star1&race1).
    induction star1.
    exists nil,FP.emp,s.
    split;[constructor|].
    inversion race1;subst.
    apply glob_predict_to_star in H0.
    apply glob_predict_to_star in H1.
    econstructor;eauto.

    specialize (IHstar1 race1) as (l'&fp'&pc'&star'&race').
    exists (cons e l'),(FP.union fp1 fp'),pc'.
    split;[econstructor 2|];eauto.
  Qed.
  Definition glob_race_prog {NL}{L:@langs NL}{ge}(predict:@ProgConfig ge->tid->Bit->FP.t->Prop)(p:prog L):Prop:=
    exists gm pc t,
      init_config p gm ge pc t /\ star_race predict pc.
  Lemma race_prog_to_glob_race_prog_star_predictt:
    forall NL L p,
      @race_prog NL L p ->
      exists ge,@glob_race_prog NL L ge glob_predict_star p.
  Proof.
    unfold race_prog.
    unfold glob_race_prog.
    intros.
    destruct H as (gm&ge&pc&t&init&race).
    exists ge,gm,pc,t;split;auto.
    apply star_race_equiv in race.
    pose proof predict_equiv.
    eapply predict_equiv_to_star_race_equiv in H.
    apply H in race.
    apply star_race_to_star_predict_race in race.
    assumption.
  Qed.

  
End PRace.
