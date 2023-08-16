Require Import Values.

Require Import Blockset Footprint GMemory InteractionSemantics GAST
        GlobDefs ETrace NPSemantics
        Injections GSimDefs GlobDSim GlobUSim NPSemantics GDefLemmas  NPDet. 

Require Import Arith Wf Classical_Prop FunctionalExtensionality.
(** This file contains proof for flipping.*)
Module GlobSim.

  Notation "{ A , B , C , D } " := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:=D|} (at level 70,right associativity).
  Notation "{'FP'| A , B , C , D } " := {|FP.cmps:=A;FP.reads:=B;FP.writes:=C;FP.frees:=D|} (at level 70,right associativity).
  Local Notation "{-| PC , T }" := 
  ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |})  (at level 70,right associativity).
  Ltac clearfp:=
    repeat rewrite FP.fp_union_emp in *;
    repeat rewrite FP.emp_union_fp in *;
    repeat rewrite FP.fp_union_assoc in *.

  Definition inv {ge}(pc:@ProgConfig ge):= ThreadPool.inv pc.(thread_pool).    
  Lemma init_config_inv_thp:
    forall NL L p gm ge pc t,
      @init_config NL L p gm ge pc t->
      inv pc.
  Proof.
    intros.
    inversion H;subst.
    apply ThreadPool.init_inv in H2.
    auto.
  Qed.
  Lemma thp_inv_preservation:
    forall ge pc o fp pc',
      GlobEnv.wd ge ->
      @np_step ge pc o fp pc' ->
      inv pc ->
      inv pc'.
  Proof. {
    unfold inv.
    intros; destruct pc, pc'.
    
    inversion H0; clear H0; subst; simpl in *.
    (* core step *)
    { eapply ThreadPool.upd_top_inv; eauto. }
    (* call ext *)
    { eapply ThreadPool.push_inv; eauto. }
    (* return *)
    { eapply ThreadPool.upd_top_inv.
      Focus 2. eauto.
      eapply ThreadPool.pop_inv; eauto. eauto. eauto. }
    (* thread halt *)
    { eapply ThreadPool.pop_inv; eauto. }
    (* all halt *)
    { eapply ThreadPool.pop_inv; eauto. }
    (* primitives *)
    eapply ThreadPool.upd_top_inv; eauto.
    eapply ThreadPool.upd_top_inv; eauto.
    eapply ThreadPool.upd_top_inv; eauto.
    }
  Qed.
  Lemma thp_inv_tau_star_preservation:
    forall ge pc fp pc',
      GlobEnv.wd ge ->
      tau_star (@np_step ge) pc fp pc' ->
      inv pc ->
      inv pc'.
  Proof. intros;induction H0;[|apply thp_inv_preservation in H0];auto. Qed.
  Lemma thrddom_eq'_thrd_valid_tid_preservation {sge tge}:
    forall spc tpc,
      @inv sge spc -> @inv tge tpc -> thrddom_eq' spc tpc ->
      forall id, ThreadPool.valid_tid spc.(thread_pool) id ->
            ThreadPool.valid_tid tpc.(thread_pool) id.
  Proof. {
    intros.
    unfold inv in *.
    inversion H1;subst.
    specialize (H5 id).
    inversion H5;subst.
    {
      inversion H;subst.
      apply tp_valid in H2 as [].
      unfold ThreadPool.get_cs in H4.
      rewrite H2 in H4.
      inversion H4.
    }
    rewrite valid_tid_get_cs;eauto.
    }
  Qed.
  Lemma thrddom_eq'_final_state_preservation {sge tge}:
    forall spc tpc,
      @inv sge spc -> @inv tge tpc -> thrddom_eq' spc tpc ->
      final_state tpc ->final_state spc.
  Proof.
    intros.
    inversion H2;subst.
    econstructor 1 with(TP:=spc.(thread_pool));eauto.
    intros.
    inversion H1;subst.
    specialize (H7 i).
    inversion H7;subst.
    {
      rewrite valid_tid_get_cs in H3;auto.
      destruct H3.
      rewrite H3 in H6.
      inversion H6.
    }
    {
      inversion H8;subst.
      econstructor;eauto.
      eapply thrddom_eq'_thrd_valid_tid_preservation in H3;eauto.
      specialize (H4 i H3).
      inversion H4;subst.
      rewrite<- H6 in H11.
      inversion H11;subst.
      contradiction.
    }
  Qed.
  Lemma thrddom_eq'_valid_tid_preservation{sge tge}:
    forall  spc tpc,
      inv spc -> inv tpc -> thrddom_eq' spc tpc ->
      forall id, @pc_valid_tid sge spc id ->
            @pc_valid_tid tge tpc id.
  Proof. {
    intros.
    unfold pc_valid_tid in *.
    destruct H2.
    unfold inv in *.
    rewrite valid_tid_get_cs;auto.
    rewrite valid_tid_get_cs in H2;auto.
    destruct H2.
    inversion H1;subst.
    specialize (H6 id).
    inversion H6;subst.
    {
      rewrite H2 in H5.
      inversion H5.
    }
    {
      split.
      eauto.
      intro.
      contradict H3.
      inversion H8;eapply ThreadPool.Halted; solv_thread'.
      inversion H7;subst;auto.
      contradict H5.
      compute;auto.
    }
    }
  Qed.

  Section Lemmas.
    Lemma sw_step_det{ge}:
      forall pc pc1 o fp pc2 fp2,
        @np_step ge pc o fp pc1 ->
        np_step pc o fp2 pc2 ->
        o<> tau ->
        fp = FP.emp /\ fp2 = FP.emp /\
        pc1.(thread_pool) = pc2.(thread_pool) /\
        pc1.(gm) = pc2.(gm) /\
        pc1.(atom_bit) = pc2.(atom_bit).
    Proof. {
      intros.
      inversion H;subst;inversion H0;subst;try contradiction;simpl;auto.
      {
        rewrite H_tp_pop in H_tp_pop0;inversion H_tp_pop0;subst;auto.
      }
      {
        rewrite H_tp_core in H_tp_core0.
        inversion H_tp_core0;clear H_tp_core0;subst.
        rewrite H_core_aftext in H_core_aftext0.
        rewrite H_core_atext in H_core_atext0.
        inversion H_core_aftext0;clear H_core_aftext0;subst.
        inversion H_core_atext0;clear H_core_atext0;subst.
        assert(c'=c'0).
        destruct c',c'0.
        inversion H_core_update;subst.
        inversion H_core_update0;subst.
        rewrite H2. rewrite H3. auto.
        subst.
        inversion H_tp_upd;subst.
        inversion H_tp_upd0;subst.
        rewrite H2 in H4;inversion H4;clear H4;subst.
        inversion H3;subst.
        inversion H5;subst.
        auto.
      }
      {
        rewrite H_tp_core in H_tp_core0.
        inversion H_tp_core0;clear H_tp_core0;subst.
        rewrite H_core_aftext in H_core_aftext0.
        rewrite H_core_atext in H_core_atext0.
        inversion H_core_aftext0;clear H_core_aftext0;subst.
        inversion H_core_atext0;clear H_core_atext0;subst.
        assert(c'=c'0).
        destruct c',c'0.
        inversion H_core_update;subst.
        inversion H_core_update0;subst.
        rewrite H2. rewrite H3. auto.
        subst.
        inversion H_tp_upd;subst.
        inversion H_tp_upd0;subst.
        rewrite H2 in H4;inversion H4;clear H4;subst.
        inversion H3;subst.
        inversion H5;subst.
        auto.
      }
      }
    Qed.
    Lemma switch_any :  forall(ges:GlobEnv.t) (spc spc1:@ProgConfig ges)o fpS ,
        np_step spc o fpS spc1  ->
        o <> tau ->
        forall t,
          pc_valid_tid spc1 t->
          np_step spc o fpS ({-|spc1,t}).
    Proof. {
      intros.
      destruct H1. 
      inversion H;subst;try contradiction;[eapply Thrd_Halt|eapply Ext_Atom|eapply EF_Print];simpl;eauto.
      }
    Qed.
    Definition language_det (ge:GlobEnv.t): Prop := @NPDet.language_det ge.
    Lemma np_step_det: forall(ge:GlobEnv.t)(pc pc' pc'':@ProgConfig ge) fp fp' l1 l2,
        language_det ge->
        np_step pc l1 fp pc' -> np_step pc l2 fp' pc'' ->
        l1 = l2 /\ fp = fp' /\
        pc'.(thread_pool) = pc''.(thread_pool) /\
        pc'.(gm) = pc''.(gm) /\
        pc'.(atom_bit) = pc''.(atom_bit) /\
        (l1=tau->pc'.(cur_tid)=pc''.(cur_tid)).
    Proof.
      intros.
      pose proof H1 as L.
      eapply @NPDet.np_step_det in H1 as (?&?&?&?&?);try apply H0;auto.
      repeat try (split;auto).
      intro;subst.
      inversion H0;subst;try contradiction;inversion L;subst;try contradiction;auto.
    Qed.
    Lemma  tau_step_det:  forall(ge:GlobEnv.t)(pc pc' pc'':@ProgConfig ge) fp fp' l,
        language_det ge->
        np_step pc tau fp pc' -> np_step pc l fp' pc'' ->
        l = tau /\ fp = fp' /\ pc'=pc''.
    Proof.
      {
        intros.
        eapply np_step_det in H1;try apply H0;auto.
        destruct H1 as [H1[H2[H3[H4 [H5 H6]]]]].
        split;auto. split;auto.
        assert(L:tau=tau). auto.
        apply H6 in L.
        destruct pc'. destruct pc''.
        compute in L,H3,H4,H5.
        congruence.
      }
    Qed.

    Lemma tau_step_bit_rule:
      forall (ge:GlobEnv.t)(pc pc':@ProgConfig ge) fp label,
        np_step pc label fp pc' ->
        label = tau ->
        (atom_bit pc = O /\ atom_bit pc' = O) \/
        (atom_bit pc = O /\ atom_bit pc' = I) \/
        (atom_bit pc = I /\ atom_bit pc' = I).
    Proof. {
      intros.
      pose proof H as step.
      inversion H;compute;auto.
      destruct d;auto.
      rewrite H0 in H2.
      inversion H2.
      }
    Qed.
    Corollary EntAx_bit_rule:
      forall (ge:GlobEnv.t)(pc pc':@ProgConfig ge) fp,
        np_step pc tau fp pc' ->
        atom_bit pc <> atom_bit pc' ->
        (atom_bit pc = O /\ atom_bit pc' = I).
    Proof. {
      intros.
      apply tau_step_bit_rule in H;auto.
      destruct H as[[]|[[]|[]]];auto;try(rewrite H in H0;rewrite H1 in H0;compute in H0;contradiction).
      }
    Qed.
    Corollary tau_step_bit_backwards_preservation :
       forall (ge:GlobEnv.t)(pc pc':@ProgConfig ge) fp label,
         np_step pc label fp pc' -> label=tau ->atom_bit pc' = O -> atom_bit pc' = O.
    Proof. intros;apply tau_step_bit_rule in H;auto. Qed.
    Corollary tau_step_bit_I_preservation :
       forall (ge:GlobEnv.t)(pc pc':@ProgConfig ge) fp label,
         np_step pc label fp pc' -> label=tau ->atom_bit pc = I -> atom_bit pc' = I.
    Proof. {
      intros.
      apply tau_step_bit_rule in H;auto.
      destruct H as[[]|[[]|[]]];try (rewrite H in H1; inversion H1);auto.
      }
    Qed.
    Lemma tau_N_bit_rule:
      forall i (ge:GlobEnv.t)(pc pc':@ProgConfig ge) fp,
        tau_N np_step i pc fp pc'->
        (atom_bit pc = O /\ atom_bit pc' = O) \/
        (atom_bit pc = O /\ atom_bit pc' = I) \/
        (atom_bit pc = I /\ atom_bit pc' = I).
    Proof. {
      induction i.
      {
        intros.
        inversion H;subst.
        destruct pc'.
        compute.
        destruct atom_bit;auto.
      }
      {
        intros.
        inversion H;subst.
        apply IHi in H2.
        apply tau_step_bit_rule in H1;auto.
        destruct pc,pc',s'.
        compute. compute in H1,H2.
        destruct atom_bit,atom_bit0,atom_bit1;auto.
      }
    }
    Qed.
    Lemma tau_N_tau_step_bit_rule:
      forall i (ge:GlobEnv.t)(pc pc' pce:@ProgConfig ge) fp1 fp2,
        np_step pc tau fp1 pc' ->
        tau_N np_step i pc' fp2 pce ->
        atom_bit pc = atom_bit pce ->
        atom_bit pc = atom_bit pc'.
    Proof. {
      intros.
      destruct pc,pce,pc'.
      compute in H1;subst.
      apply tau_step_bit_rule in H;auto.
      apply tau_N_bit_rule in H0.
      destruct atom_bit0,atom_bit1;auto.
      inversion H0 as[[]|[[]|[]]];auto.
      inversion H as[[]|[[]|[]]];auto.
      }
    Qed.
    Lemma tau_N_bit_backwards_preservation:
       forall i (ge:GlobEnv.t)(pc pc':@ProgConfig ge) fp,
        tau_N np_step i pc fp pc'->
        atom_bit pc' = O ->
        atom_bit pc = O.
    Proof. {
      intros;apply tau_N_bit_rule in H;auto.
      destruct H as[[]|[[]|[]]];auto.
      rewrite H0 in H1. inversion H1.
      }
    Qed.
    Lemma tau_N_bit_I_preservation:
      forall i (ge:GlobEnv.t)(pc pc':@ProgConfig ge) fp,
        tau_N np_step i pc fp pc'->
        atom_bit pc = I ->
        atom_bit pc' = I.
    Proof. intros;apply tau_N_bit_rule in H;destruct H as[[]|[[]|[]]];try (rewrite H in H0; inversion H0);auto. Qed.
    Lemma inv_thdp_gettop_valid_tid:
    forall ge pc c,
      ThreadPool.inv pc.(thread_pool) ->
      ThreadPool.get_top pc.(thread_pool) pc.(cur_tid) = Some c->
      @pc_valid_tid ge pc pc.(cur_tid).
    Proof.
      intros until c.
      intros H H_tp_core.
      destruct pc as [thdp t gm bit].
      unfold ThreadPool.valid_tid;split.
      {
        assert(Coqlib.Plt t thdp.(ThreadPool.next_tid) \/ BinPos.Pge t thdp.(ThreadPool.next_tid)).
        apply classic.
        destruct H0;auto.
        inversion H as [tp_finite _ _ _].
        apply tp_finite in H0. simpl in H0.
        clear tp_finite.
        inversion H_tp_core.
        unfold ThreadPool.get_top in H2.
        unfold ThreadPool.get_cs in H2.
        rewrite H0 in H2.
        inversion H2.
      }
      {
        intro.
        inversion H0;subst.
        inversion H_tp_core.
        unfold ThreadPool.get_top in H4.
        simpl in *.
        rewrite H1 in H4.
        inversion H2;subst.
        inversion H4.
      }
    Qed.
    Lemma inv_step_valid_tid:
      forall ge pc fp pc1 o,
        (@np_step ge) pc o fp pc1->
        ThreadPool.inv pc.(thread_pool) ->
        pc_valid_tid pc pc.(cur_tid).
    Proof.
      intros.
      inversion H;subst;eapply inv_thdp_gettop_valid_tid;eauto.
    Qed.
    Lemma step_no_final:forall ge pc pc1 fp o,
        @np_step ge pc o fp pc1 ->
        inv pc ->
        ~final_state pc.
    Proof.
      intros.
      intro.
      inversion H1;subst.
      apply inv_step_valid_tid in H;auto.
      destruct H.
      apply H3 in H.
      contradiction.
    Qed.

    Lemma safe_rule: forall(ge:GlobEnv.t) (pc:@ProgConfig ge),
      ~ np_abort pc -> final_state pc \/(exists gl fp pc',np_step pc gl fp pc').
    Proof. {
      intros.
      unfold np_abort in H.
      apply not_and_or in H.
      inversion H.
      {
        left.
        apply NNPP;auto.
      }
      {
        right.
        apply Classical_Pred_Type.not_all_ex_not in H0 as[gl H0].
        apply Classical_Pred_Type.not_all_ex_not in H0 as[fp H0].
        apply Classical_Pred_Type.not_all_ex_not in H0 as[pc' H0].
        exists gl,fp,pc'.
        apply NNPP;auto.
      }
      }
    Qed.
    Lemma safe_succession: forall sge (spc:@ProgConfig sge) (spc':@ProgConfig sge) (fpS:FP.t),
        tau_star np_step spc fpS spc' ->
        np_safe_config spc ->
        np_safe_config spc'.
    Proof. {
      intros.
      rewrite <- tau_star_tau_N_equiv in H.
      destruct H.
      generalize dependent spc.
      generalize dependent spc'.
      generalize dependent fpS.
      induction x.
      {
        intros.
        inversion H. congruence.
      }
      {
        intros.
        inversion H. inversion H0. apply H8 in H2. eapply IHx;eauto.
      }
    }
    Qed.
    Lemma tau_step_tid_preservation:forall(ge:GlobEnv.t)(pc pc':@ProgConfig ge)(fp:FP.t),
        np_step pc tau fp pc' ->
        cur_tid pc = cur_tid pc'.
    Proof. intros;inversion H;subst;compute;auto. Qed.
    Lemma tau_star_tid_preservation: forall(ge:GlobEnv.t)(pc pc':@ProgConfig ge)(fp:FP.t),
        tau_star np_step pc fp pc' ->
        cur_tid pc = cur_tid pc'.
    Proof. {
      intros.
      apply tau_star_tau_N_equiv in H as[i H].
      generalize dependent pc.
      generalize dependent pc'.
      generalize dependent fp.
      induction i;intros;inversion H;subst;auto.
      apply IHi in H2.
      apply tau_step_tid_preservation in H1.
      rewrite H1. auto.
      }
    Qed.
    Corollary tau_star_tideq_preservation :forall (ges get:GlobEnv.t)(spc spc1:@ProgConfig ges)(tpc tpc1:@ProgConfig get)(fpS fpT:FP.t),
        tau_star np_step spc fpS spc1 ->
        tau_star np_step tpc fpT tpc1 ->
        ( tid_eq spc tpc <-> tid_eq spc1 tpc1).
    Proof. split;intro;apply tau_star_tid_preservation in H;apply tau_star_tid_preservation in H0;inversion H1;subst;constructor;destruct spc,spc1,tpc,tpc1;compute;compute in H,H0,H2;subst;auto. Qed.
    Lemma cs_match_comm:  forall G1 G2 A B,
        @cs_match' G1 G2 A B -> cs_match' B A.
    Proof. intros;induction H;subst;try (apply match_cs_emp';assumption);constructor 2;auto. Qed.
    Lemma ocs_match_comm : forall G1 G2 A B,
        @ocs_match' G1 G2 A B -> ocs_match' B A.
    Proof. intros;inversion H;subst;constructor;apply cs_match_comm;auto. Qed.
    Lemma thrddom_eq_comm: forall sge tge (spc:@ProgConfig sge)(tpc:@ProgConfig tge),
        thrddom_eq' spc tpc -> thrddom_eq' tpc spc.
    Proof. intros;inversion H;econstructor;eauto;subst;intro t;specialize (H2 t);apply ocs_match_comm;auto. Qed.

    Lemma scs_upd_cs_match':
      forall SGE TGE (scs: @CallStack.t SGE) (tcs: @CallStack.t TGE),
        cs_match' scs tcs ->
        forall c' scs',
          CallStack.update scs c' scs' ->
          cs_match' scs' tcs.
    Proof. {
      intros.
      inversion H;subst.
      inversion H1;subst;simpl in *.
      inversion H0.
      econstructor 2;eauto.
      inversion H0;subst.
      intro.
      inversion H4.
      }
    Qed.
    Lemma stp_upd_ocs_match':
      forall SGE TGE (sthdp: @ThreadPool.t SGE) (tthdp:@ThreadPool.t TGE) i,
        ocs_match' (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp i) ->
        (forall i' c' sthdp',
            ThreadPool.update sthdp i' c' sthdp' ->
            ocs_match' (ThreadPool.get_cs sthdp' i) (ThreadPool.get_cs tthdp i)).
    Proof. {
      intros SGE0 TGE0 sthdp tthdp i H i' c' sthdp' H0.
      inversion H0; subst; clear H0.
      unfold ThreadPool.get_cs in *; simpl in *.
      rewrite Maps.PMap.gsspec.
      destruct Coqlib.peq; [subst|auto].
      inversion H. congruence.
      rewrite H1 in H0; inversion H0; clear H0 H3. subst.
      constructor. eapply scs_upd_cs_match'; eauto.
      }
    Qed.
    Lemma tcs_upd_cs_match:
      forall SGE TGE (scs: @CallStack.t SGE) (tcs: @CallStack.t TGE),
        cs_match' scs tcs ->
        forall c' tcs',
          CallStack.update tcs c' tcs' ->
          cs_match' scs tcs'.
    Proof. intros; apply cs_match_comm;apply cs_match_comm in H; eapply scs_upd_cs_match';eauto. Qed.
    Lemma ttp_upd_ocs_match':
      forall SGE TGE (sthdp: @ThreadPool.t SGE) (tthdp:@ThreadPool.t TGE) i,
        ocs_match' (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp i) ->
        (forall i' c' tthdp',
            ThreadPool.update tthdp i' c' tthdp' ->
            ocs_match' (ThreadPool.get_cs sthdp i) (ThreadPool.get_cs tthdp' i)).
    Proof. intros; apply ocs_match_comm in H;apply ocs_match_comm; eapply stp_upd_ocs_match';eauto. Qed.
    Lemma call_ocs_match':
      forall SGE TGE sthdp thdp i,
        @ocs_match' SGE TGE (ThreadPool.get_cs sthdp i)(ThreadPool.get_cs thdp i) ->
        forall t c funid sg args new_ix cc' thdp',
          let: cc := Core.c c in
          let: c_ix := Core.i c in
          let: c_mod := GlobEnv.modules TGE c_ix in
          let: c_lang := ModSem.lang c_mod in
          let: Ge := ModSem.Ge c_mod in
          forall
            (H_tp_core: ThreadPool.get_top thdp t = Some c)
            (H_core_atext: at_external c_lang Ge cc = Some (funid, sg, args))
            (H_mod_id: GlobEnv.get_mod TGE funid = Some new_ix),
            (* init new core with funid *)
            let: new_mod := GlobEnv.modules TGE new_ix in
            let: new_lang := ModSem.lang new_mod in
            let: new_Ge := ModSem.Ge new_mod in
            forall
              (H_new_core: init_core new_lang new_Ge funid args = Some cc')
              (H_tp_push: ThreadPool.push thdp t new_ix cc' sg = Some thdp'),
              ocs_match' (ThreadPool.get_cs sthdp i)(ThreadPool.get_cs thdp' i).
    Proof. {
      intros.
      unfold ThreadPool.get_top,ThreadPool.get_cs,ThreadPool.push in *.
      repeat match goal with
             | H: match ?p with _ => _ end = Some _ |- _ =>
               destruct p eqn:?; inversion H; subst; clear H
         end.
      simpl.
      repeat rewrite Maps.PMap.gsspec;simpl.
      destruct Coqlib.peq.
      subst.
      inversion H;subst. rewrite Heqo in H2;inversion H2.
      rewrite Heqo in H1;inversion H1;clear H1;subst.
      constructor.
      inversion H2;subst.
      unfold CallStack.is_emp in H3;subst.
      inversion H_tp_core.
      unfold CallStack.push.
      constructor 2;auto.
      intro. inversion H4.

      inversion H;subst. constructor.
      constructor;auto.
      }
    Qed.
    Lemma return_ocs_match':
      forall SGE GE sthdp thdp i,
        @ocs_match' SGE GE (ThreadPool.get_cs sthdp i)(ThreadPool.get_cs thdp i) ->
        forall t  c res thdp' c' cc'' c'' thdp'',
          let: cc := Core.c c in
          let: c_ix := Core.i c in
          let: c_sg := Core.sg c in
          let: c_mod := GlobEnv.modules GE c_ix in
          let: c_lang := ModSem.lang c_mod in
          let: Ge := ModSem.Ge c_mod in
          forall
            (H_tp_core: ThreadPool.get_top thdp t = Some c)
            (H_core_halt: halt c_lang cc = Some res)
            (H_tp_pop: ThreadPool.pop thdp t = Some thdp')
            (H_tp_caller: ThreadPool.get_top thdp' t = Some c'),
            let: cc' := Core.c c' in
            let: c'_ix := Core.i c' in
            let: c'_mod := GlobEnv.modules GE c'_ix in
            let: c'_lang := ModSem.lang c'_mod in
            let: Ge' := ModSem.Ge c'_mod in
            forall
              (H_core_aftext: after_external c'_lang cc' (res_sg c_sg res) = Some cc'')
              (H_core_upd: Core.update c' cc'' c'')
              (H_tp_upd: ThreadPool.update thdp' t c'' thdp''),
              @ocs_match' SGE GE (ThreadPool.get_cs sthdp i)(ThreadPool.get_cs thdp'' i).
    Proof. {
      intros.
      unfold ThreadPool.get_top,ThreadPool.get_cs,ThreadPool.pop in *.
      repeat match goal with
             | H: match ?p with _ => _ end = Some _ |- _ =>
               destruct p eqn:?; inversion H; subst; clear H
             end.
      simpl in *.
      rewrite Maps.PMap.gsspec in Heqo;simpl.
      destruct (Coqlib.peq);[|contradiction].
      inversion Heqo;clear e Heqo;subst.
      assert(i=t\/i<>t). apply classic.
      destruct H0.
      subst.
      inversion H;subst. rewrite Heqo0 in H3. inversion H3.
      rewrite Heqo0 in H2;inversion H2;clear H2;subst.
      inversion H_tp_upd;subst;simpl.
      repeat rewrite Maps.PMap.gsspec;simpl.
      destruct Coqlib.peq;[|contradiction].
      constructor.
      inversion H3;subst. inversion H6;subst. inversion Heqo1.
      constructor 2;auto;intro S;inversion S;clear e S;subst;inversion H4.

      inversion H_tp_upd;subst;simpl.
      repeat rewrite Maps.PMap.gsspec;simpl.
      destruct Coqlib.peq;[contradiction|];auto.
      }
    Qed.
    Definition final_pool {ge}(thdp:ThreadPool.t):=
      forall i, @ThreadPool.valid_tid ge thdp i -> ThreadPool.halted thdp i.
    Lemma final_state_rule1:
      forall ge p1 t c p2,
        @final_pool ge p2->
        ThreadPool.update p1 t c p2 ->
        final_pool p1.
    Proof. {
      intros.
      unfold final_pool in *.
      intros.
      inversion H0;clear H0;subst.
      assert(ThreadPool.valid_tid {|ThreadPool.content := Maps.PMap.set t (Some cs') (ThreadPool.content p1);ThreadPool.next_tid := ThreadPool.next_tid p1;ThreadPool.next_fmap := ThreadPool.next_fmap p1 |} i).
      unfold ThreadPool.valid_tid in *.
      simpl in *;auto.
      specialize (H i H0).
      inversion H;subst.
      unfold ThreadPool.get_cs in *;simpl in *.
      rewrite Maps.PMap.gsspec in H4.
      destruct Coqlib.peq.
      subst.
      inversion H4;subst.
      inversion H5;subst.
      inversion H3.
      inversion H5;subst.
      econstructor;eauto.
      }
    Qed.

    Lemma final_state_rule2:
      forall ge p t ix cc sg p',
        @final_pool ge p'->
        ThreadPool.push p t ix cc sg = Some p' ->
        final_pool p.
    Proof. {
      intros.
      unfold final_pool in *.
      intros.
      unfold ThreadPool.push in H0.
      destruct (Maps.PMap.get t (ThreadPool.content p));inversion H0;clear H0.
      assert(ThreadPool.valid_tid p' i).
      unfold ThreadPool.valid_tid in *;rewrite <- H3;simpl;auto.
      specialize (H i H0).
      inversion H;clear H;subst.
      unfold ThreadPool.get_cs in H2;simpl in H2.
      rewrite Maps.PMap.gsspec in H2.
      destruct Coqlib.peq.
      subst.
      inversion H2;clear H2;subst.
      inversion H4.
      econstructor;eauto.
      }
    Qed.

    Lemma final_state_rule3:
      forall ge p t p' c p'',
        @final_pool ge p''->
        ThreadPool.pop p t = Some p' ->
        ThreadPool.update p' t c p'' ->
        final_pool p.
    Proof. {
      intros.
      unfold final_pool in *;intros.
      unfold ThreadPool.pop in H0.
      destruct (Maps.PMap.get t (ThreadPool.content p)) eqn:eq1;[|inversion H0].
      destruct (CallStack.pop t0) eqn:eq2;inversion H0;clear H0;subst.
      inversion H1;clear H1;subst;simpl in *.
      assert(ThreadPool.valid_tid  {|ThreadPool.content := Maps.PMap.set t (Some cs') (Maps.PMap.set t (Some t1) (ThreadPool.content p)); ThreadPool.next_tid := ThreadPool.next_tid p; ThreadPool.next_fmap := ThreadPool.next_fmap p |} i ).
      unfold ThreadPool.valid_tid in *;simpl in *;auto.
      eapply H in H1;eauto;clear H.
      unfold ThreadPool.get_cs in H0;simpl in H0.
      rewrite Maps.PMap.gsspec in H0.
      destruct Coqlib.peq;[|contradiction].
      inversion H0;clear e H0;subst.
      inversion H1;clear H1;subst.
      inversion H0;clear H0;subst.
      unfold ThreadPool.get_cs in H;simpl in H.
      repeat rewrite Maps.PMap.gsspec in H.
      destruct Coqlib.peq.
      inversion H;clear H;subst.
      inversion H3.

      econstructor;eauto.
      compute;auto.
      }
    Qed.

    Lemma tau_step_thrddom_eq_preservation: forall sge tge (spc:@ProgConfig sge) tpc tpc1 fp,
        @np_step tge tpc tau fp tpc1 -> ~final_state tpc1 ->
        thrddom_eq' spc tpc ->
        thrddom_eq' spc tpc1.
    Proof.
      intros.
      inversion H1;subst.
      econstructor 1 with(tp1:=thread_pool spc)(tp2:=thread_pool tpc1);auto;intro.
      specialize (H4 t).
      inversion H;subst;[eapply ttp_upd_ocs_match'|eapply call_ocs_match'|eapply return_ocs_match'|contradict H0 |eapply ttp_upd_ocs_match'];eauto.
      econstructor 1 with(TP:=thdp');auto.
    Qed.

    Corollary final_pool_final_state_equiv :
      forall ge pc,
        @final_state ge pc <-> final_pool pc.(thread_pool).
    Proof.
      destruct pc;unfold final_pool;simpl;split;intros.
      inversion H;subst;simpl in *;auto.
      econstructor 1 with (TP:=(thread_pool));eauto.
    Qed.

    Lemma halt_step_thrddom_eq_preservation: forall sge tge spc spc1 tpc tpc1 fp1 fp2,
        @np_step sge spc tau fp1 spc1 -> final_state spc1 -> inv spc ->
        @np_step tge tpc tau fp2 tpc1 -> final_state tpc1 -> inv tpc ->
        spc.(cur_tid) = tpc.(cur_tid) ->
        thrddom_eq' spc tpc ->
        thrddom_eq' spc1 tpc1.
    Proof. {
      intros.
      apply final_pool_final_state_equiv in H0.
      apply final_pool_final_state_equiv in H3.
      pose proof H as L.
      destruct spc as [sthp sid sgm sbit] eqn:eq.
      inversion H;subst;[eapply final_state_rule1 in H0|eapply final_state_rule2 in H0|eapply final_state_rule3 in H0| |eapply final_state_rule1 in H0];eauto;eapply step_no_final in L;auto;[contradict L;apply final_pool_final_state_equiv;auto|contradict L;apply final_pool_final_state_equiv;auto|contradict L;apply final_pool_final_state_equiv;auto| |contradict L;apply final_pool_final_state_equiv;auto].
      pose proof H2 as R.
      destruct tpc as [tthp tid tgm tbit] eqn:eq.
      compute in H5;subst.
      inversion H2;subst;[eapply final_state_rule1 in H3|eapply final_state_rule2 in H3|eapply final_state_rule3 in H3| |eapply final_state_rule1 in H3];eauto;eapply step_no_final in R;auto;[contradict R;apply final_pool_final_state_equiv;auto|contradict R;apply final_pool_final_state_equiv;auto|contradict R;apply final_pool_final_state_equiv;auto| |contradict R;apply final_pool_final_state_equiv;auto].
      econstructor 1  with(tp1:=thdp')(tp2:=thdp'0);auto.
      intro.
      inversion H6;subst.
      specialize (H8 t).
      simpl in H8.
      unfold ThreadPool.get_cs .
      assert(t = tid \/ t <> tid). apply classic.
      destruct H5;subst.
      inversion H_thread_halt0;subst.
      inversion H_thread_halt;subst.
      unfold ThreadPool.get_cs in H5,H9.
      rewrite H5,H9.
      constructor.
      constructor;auto.

      unfold ThreadPool.pop in H_tp_pop.
      destruct (Maps.PMap.get tid (ThreadPool.content sthp)) eqn:eq1;[|inversion H_tp_pop].
      destruct (CallStack.pop t0) eqn:eq2;inversion H_tp_pop;clear H_tp_pop.
      simpl.
      
      rewrite Maps.PMap.gsspec.
      destruct Coqlib.peq;[contradiction|].
      unfold ThreadPool.pop in H_tp_pop0.
      destruct (Maps.PMap.get tid (ThreadPool.content tthp)) eqn:eq3;[|inversion H_tp_pop0].
      destruct (CallStack.pop t2) eqn:eq4;inversion H_tp_pop0;clear H_tp_pop0.
      simpl.
      rewrite Maps.PMap.gsspec.
      destruct Coqlib.peq;[contradiction|].
      unfold ThreadPool.get_cs in H8.
      auto.
      }
    Qed.

    Lemma tau_star_thrddom_eq_preservation: forall sge tge (spc:@ProgConfig sge) tpc tpc1 fp,
        GlobEnv.wd tge -> inv tpc ->
        tau_star (@np_step tge) tpc fp tpc1 -> ~ final_state tpc1 -> 
        thrddom_eq' spc tpc ->
        thrddom_eq' spc tpc1.
    Proof.
      intros;induction H1;auto.
      inversion H4;subst;auto.
      eapply IHtau_star;eauto. eapply thp_inv_preservation;eauto.
      eapply tau_step_thrddom_eq_preservation;eauto.
      eapply IHtau_star;eauto. eapply thp_inv_preservation;eauto.
      eapply tau_step_thrddom_eq_preservation;eauto.
      eapply step_no_final;eauto.
      eapply thp_inv_preservation;eauto.
    Qed.
    Lemma tau_star_finalstate_thrddom_eq_preservation : forall sge tge spc tpc spc1 tpc1 fp1 fp2,
        cur_tid spc = cur_tid tpc ->
        GlobEnv.wd sge -> GlobEnv.wd tge ->
        tau_star (@np_step sge) spc fp1 spc1 ->
        tau_star (@np_step tge) tpc fp2 tpc1 ->
        inv spc -> inv tpc ->
        final_state spc1 -> final_state tpc1 ->
        thrddom_eq' spc tpc -> thrddom_eq' spc1 tpc1.
    Proof. {
      intros until fp2;intro TMP;intros.
      assert(inv spc1). eapply thp_inv_tau_star_preservation;eauto.
      assert(inv tpc1). eapply thp_inv_tau_star_preservation;eauto.
      apply tau_star_tau_N_equiv in H1 as [];apply tau_star_tau_N_equiv in H2 as [].
      destruct x,x0; inversion H1;inversion H2;subst;auto.
      apply thrddom_eq_comm in H7.
      eapply thrddom_eq'_final_state_preservation in H7;eauto.
      eapply step_no_final in H14;eauto;contradiction.
      eapply thrddom_eq'_final_state_preservation in H7;eauto.
      eapply step_no_final in H11;eauto;contradiction.
      clear s' H11 H12 s'0 H17 H18.
      assert(S x = x + 1). Lia.lia.
      assert(S x0=x0+1). Lia.lia.
      rewrite H10 in H1.
      rewrite H11 in H2.
      apply tau_N_split in H1 as (spc'&fp1&fp2&?&?&?).
      apply tau_N_split in H2 as (tpc'&fp3&gp4&?&?&?).
      clear H10 H11.
      assert(inv tpc'). eapply thp_inv_tau_star_preservation with(pc:=tpc);auto;eapply tau_star_tau_N_equiv;eauto.
      assert(inv spc'). eapply thp_inv_tau_star_preservation with(pc:=spc);auto;eapply tau_star_tau_N_equiv;eauto.
      assert(L:exists x,tau_N np_step x spc fp1 spc'). eauto.
      assert(L2:exists x,tau_N np_step x tpc fp3 tpc'). eauto.
      apply tau_star_tau_N_equiv in L.
      apply tau_star_tau_N_equiv in L2.
      assert(~final_state spc'). intro. inversion H12;subst. apply step_no_final in H18;auto. 
      assert(~final_state tpc'). intro;inversion H14;subst. apply step_no_final in H19;eauto.
      pose proof tau_star_thrddom_eq_preservation sge tge spc tpc tpc' fp3 H0 H4 L2 H17 H7.
      apply thrddom_eq_comm in H18.
      eapply tau_star_thrddom_eq_preservation in H18;eauto.
      apply thrddom_eq_comm in H18.
      inversion H12;inversion H14;subst.
      inversion H21;inversion H27;subst.
      eapply  halt_step_thrddom_eq_preservation;eauto.
      eapply tau_star_tid_preservation in L;eauto.
      eapply tau_star_tid_preservation in L2;eauto.
      congruence.
      }
    Qed.
    Definition valid_tid {ge}(pc:@ProgConfig ge)(t:tid) :Prop:=
      ThreadPool.valid_tid pc.(thread_pool) t /\ ~ThreadPool.halted pc.(thread_pool) t .
    Lemma match_tp_one' : forall sge tge(spc:@ProgConfig sge)( tpc:@ProgConfig tge) (t:tid),
        inv spc -> inv tpc ->thrddom_eq' spc tpc -> valid_tid spc t -> valid_tid tpc t.
    Proof.
      intros.
      eapply thrddom_eq'_valid_tid_preservation in H2;eauto.
    Qed.
    Lemma match_tp_ano' :forall sge tge(spc:@ProgConfig sge)( tpc:@ProgConfig tge) (t:tid),
        inv spc -> inv tpc -> thrddom_eq' spc tpc -> valid_tid tpc t -> valid_tid spc t.
    Proof.
      intros;apply thrddom_eq_comm in H1;eapply thrddom_eq'_valid_tid_preservation in H1;eauto.
    Qed.
    Lemma non_tau_step_tid_rule: forall ge pc pc1 o fp,
        @np_step ge pc o fp pc1 -> o <> tau ->
        valid_tid pc1 pc1.(cur_tid).
    Proof.
      intros.
      inversion H;subst;try contradiction;split;auto.
    Qed.
  End Lemmas.
  Section Simulation.
    Definition Sim_tau_step_case (sge tge:GlobEnv.t)(match_state:Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop) (mu:Mu)(fpS fpT:FP.t)(spc tpc:ProgConfig):Prop:=
        exists fpS1 fpT1 spc1 tpc1,
          tau_plus np_step spc fpS1 spc1 /\ tau_plus np_step tpc fpT1 tpc1 /\
          atom_bit spc = atom_bit spc1 /\
          LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS1) (FP.union fpT fpT1) /\
          match_state mu (FP.union fpS fpS1)(FP.union fpT fpT1) spc1 tpc1.
    Definition Sim_EntAtom_case  (sge tge:GlobEnv.t)(match_state:Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop) (mu:Mu)(fpS fpT:FP.t)(spc tpc:ProgConfig):Prop:=
        exists fpS' fpT' fpS'' fpT'' spc' tpc' spc'' tpc'',
          tau_star np_step spc fpS' spc' /\ np_step spc' tau fpS'' spc'' /\
          tau_star np_step tpc fpT' tpc' /\ np_step tpc' tau fpT'' tpc'' /\
          atom_bit spc' <> atom_bit spc'' /\ atom_bit spc = atom_bit spc' /\
          atom_bit tpc' <> atom_bit tpc'' /\ atom_bit tpc = atom_bit tpc' /\
          LFPG mu tge tpc.(cur_tid) (FP.union fpS (FP.union fpS' fpS'')) (FP.union fpT (FP.union fpT' fpT'')) /\
          match_state mu FP.emp FP.emp spc'' tpc''.
    Definition Sim_final_case  (sge tge:GlobEnv.t)(match_state:Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop) (mu:Mu)(fpS fpT:FP.t)(spc:@ProgConfig sge)( tpc:@ProgConfig tge):Prop:=
        exists fpS' fpT' spc' tpc',
                tau_star np_step spc fpS' spc' /\ final_state spc' /\ 
                tau_star np_step tpc fpT' tpc' /\ final_state tpc' /\
                atom_bit spc = atom_bit spc' /\ atom_bit tpc = atom_bit tpc' /\
                LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS') (FP.union fpT fpT').
    
    Definition Sim_npsw_case  (sge tge:GlobEnv.t)(match_state:Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop) (mu:Mu)(fpS fpT:FP.t)(spc tpc:ProgConfig):Prop:=
      exists spc' fpS' tpc' fpT',
        tau_star np_step spc fpS' spc' /\ atom_bit spc = atom_bit spc' /\
        tau_star np_step tpc fpT' tpc' /\ atom_bit tpc = atom_bit tpc' /\
        exists o t spc'' tpc'',
            valid_tid spc'' t /\
          forall id,  valid_tid spc'' id ->
                 o <> tau /\
                 match_state mu FP.emp FP.emp ({-|spc'',id})({-|tpc'',id}) /\
                 np_step spc' o FP.emp ({-|spc'',id})/\
                 np_step tpc' o FP.emp ({-|tpc'',id})/\
                 LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS') (FP.union fpT fpT').
    Record GSim
           {sge tge:GlobEnv.t}
           (match_state:Mu->FP.t -> FP.t -> 
                        @ProgConfig sge -> @ProgConfig tge -> Prop)
    : Prop :=
      {
        match_tp:
          forall mu fpS fpT spc tpc ,
            match_state  mu fpS fpT spc tpc->
            Bset.inj_inject (inj mu) /\ GlobEnv.wd tge /\ GlobEnv.wd sge /\
            np_safe_config spc /\
            language_det tge /\
            inv spc /\ inv tpc /\thrddom_eq' spc tpc /\
            atombit_eq spc tpc /\
            tid_eq spc tpc;

        match_step:
          forall mu fpS fpT spc tpc,
            match_state mu fpS fpT spc tpc ->
            Sim_final_case sge tge match_state mu fpS fpT spc tpc \/
            Sim_npsw_case sge tge match_state mu fpS fpT spc tpc \/
            Sim_tau_step_case sge tge match_state mu fpS fpT spc tpc\/
            Sim_EntAtom_case sge tge match_state mu fpS fpT spc tpc
      }.

    Definition d2s_match{sge tge}(mu:Mu)(fpS fpT:FP.t)(spc:@ProgConfig sge)(tpc:@ProgConfig tge):Prop:=
      exists I order i match_state,
        @GConfigDSim sge tge I order match_state /\
        match_state i mu fpS fpT spc tpc /\
        np_safe_config spc /\ language_det tge /\
        inv spc /\ inv tpc /\ GlobEnv.wd tge/\ GlobEnv.wd sge.

    Lemma GSim_d2s_match{sge tge}:
      @GSim sge tge d2s_match.
    Proof.
      intros.
      constructor;intros;destruct H as [I[ord[i[match_state[GDSim[match_spc_tpc[safe_spc [LDet[invspc [invtpc [wd1 wd2]]]]]]]]]]].
      inversion GDSim as [_ R _ _ _ _ L].
      split;[eapply L|split;auto;split;auto;split;auto;split;auto;split;auto;split;auto;eapply R];eauto.
      inversion GDSim.
      revert mu fpS fpT spc tpc GDSim match_spc_tpc safe_spc LDet invspc invtpc.
      induction i using(well_founded_induction index_wf).
      intros.
      inversion safe_spc as [nabort safe_succ];apply safe_rule in nabort as [final|[l[fpS'[spc' step_spc_spc']]]].
      {
        left;unfold Sim_final_case.
        pose proof final as Tmp1;eapply match_final in Tmp1;eauto.
        destruct Tmp1 as [tpc1[fpT1[S1[S2[S3 S4]]]]].
        exists FP.emp,fpT1,spc,tpc1.
        clearfp.
        split;constructor;auto.
      }
      {
        assert(L:l<>tau\/l=tau).
        destruct l;[auto|left|left];intro contra;inversion contra.
        destruct L as [ntau|];subst.
        {
          right;left;unfold Sim_npsw_case.
          pose proof step_spc_spc' as Tmp1;eapply match_npsw_step in Tmp1;eauto.
          destruct Tmp1 as [fpT'[tpc'[i'[step_tpc_tpc'[lfpg match_spc'_tpc']]]]].
          exists spc,FP.emp,tpc,FP.emp.
          split;constructor;auto;constructor;auto;constructor;auto.
          exists l,(cur_tid spc'),spc',tpc'.
          split.
          inversion step_spc_spc';subst;try contradiction;unfold valid_tid;auto.
          intros id valid_id.
          eapply switch_any in valid_id;eauto.
          assert(fpS'=FP.emp). inversion valid_id;subst;auto;try contradiction.
          subst.
          clearfp.
          pose proof valid_id as step2.
          eapply match_npsw_step in valid_id as [fpTq'[tpcq'[iq'[step_tpc_tpcq'[lfpgq match_spcq'_tpcq']]]]];eauto.
          pose proof step_tpc_tpcq' as step3.
          eapply sw_step_det in step_tpc_tpcq';try apply step_tpc_tpc';auto.
          destruct step_tpc_tpcq' as [eq1[eq2[eq3 [eq4 eq5]]]].
          subst.
          clearfp.
          assert(tpcq' = {-|tpc',id}).
          destruct tpcq'.
          simpl in *.
          rewrite eq3,eq4,eq5.
          apply match_tp0 in match_spcq'_tpcq' as [_[_ Eq]];inversion Eq;simpl in H0;congruence.
          subst;clear eq3 eq4 eq5.
          assert(d2s_match mu FP.emp FP.emp ({-|spc', id}) ({-|tpc', id})).
          exists I,ord,iq',match_state.
          pose proof step2 as R.
          apply safe_succ in step2;auto.
          apply thp_inv_preservation in step3;auto.
          apply thp_inv_preservation in R;auto.          
          repeat try (split;auto).
          auto.
        }
        {
          assert(L:atom_bit spc <> atom_bit spc' \/ atom_bit spc = atom_bit spc').
          destruct spc,spc';destruct atom_bit,atom_bit0;compute;auto;left;intro contra;inversion contra.
          destruct L as [neqbit|].
          {
            right;right;right;unfold Sim_EntAtom_case.
            pose proof neqbit as Tmp1;eapply match_ent_atom in neqbit;eauto.
            destruct neqbit as [tpc1[fpT1[tpc2[fpT2[j [S1[S2[S3[S4 S5]]]]]]]]].
            exists FP.emp,fpT1,fpS',fpT2,spc,tpc1,spc',tpc2.
            clearfp.
            split;constructor;auto.
            split;auto;split;auto;split;auto;split;auto;split.
            apply match_tp0 in S5 as [_[Eq _]];inversion Eq;clear Eq;subst.
            apply match_tp0 in match_spc_tpc as [_[Eq _]];inversion Eq;clear Eq;subst.
            rewrite <-H0;rewrite <-S2;rewrite <-H1;auto.
            split;auto.
            split;auto.
            unfold d2s_match.
            exists I,ord,j,match_state.
            assert(np_safe_config spc').
            eapply safe_succ;eauto.
            assert(inv spc'). eapply thp_inv_preservation ;eauto.
            assert(inv tpc2). apply thp_inv_tau_star_preservation in S1;auto. eapply thp_inv_preservation;eauto.
            repeat try (split;auto).
          }
          {
            pose proof H0 as H1.
            eapply match_tau_step in H1;eauto.
            destruct H1 as [[tpc'[fpT'[i'[S1[S2 S3]]]]]|[j[S1 S2]]].
            {
              right;right;left;unfold Sim_tau_step_case.
              exists fpS',fpT',spc',tpc'.
              split;[econstructor;eauto|split];auto;split;auto;split;auto.
              exists I,ord,i',match_state.
              pose proof step_spc_spc' as R.
              apply safe_succ in R.
              repeat try(split;[auto|]);auto.
              eapply thp_inv_preservation;eauto.
              apply tau_plus2star in S1;eapply thp_inv_tau_star_preservation;eauto.
            }
            {
              assert(invspc':inv spc'). eapply thp_inv_preservation;eauto.
              pose proof safe_succ tau fpS' spc' step_spc_spc' as safe_spc'.
              pose proof H j S1 mu (FP.union fpS fpS') fpT spc' tpc GDSim S2 safe_spc' LDet invspc' invtpc.
              destruct H1 as [|[|[|]]].
              {
                left;unfold Sim_final_case in *.
                destruct H1 as [fpS'1[fpT'1[spc'1[tpc'1[Q1[Q2[Q3[Q4[Q5[Q6 Q7]]]]]]]]]].
                exists (FP.union fpS' fpS'1),fpT'1,spc'1,tpc'1.
                clearfp.
                split;[econstructor 2|split];eauto;split;auto;split;auto;split;try congruence;auto.
              }
              {
                right;left;unfold Sim_npsw_case in *.
                destruct H1 as [spc1[fpS1[tpc1[fpT1[star1[eq1[star2[eq2[o[t[spc2[tpc2[vt]]]]]]]]]]]]].
                exists spc1,(FP.union fpS' fpS1),tpc1,fpT1.
                split;[econstructor 2;eauto|split;[congruence|split];auto;split;auto].
                exists o,t,spc2,tpc2. split;auto.
                clearfp.
                auto.                
              }
              {
                right;right;left;unfold Sim_tau_step_case in *.
                destruct H1 as [fpS1[fpT1[spc1[tpc1[]]]]].
                exists (FP.union fpS' fpS1),fpT1,spc1,tpc1.
                clearfp.
                rewrite H0.
                split;[econstructor 2|];eauto.
              }
              {
                right;right;right;unfold Sim_EntAtom_case in *.
                destruct H1 as [fpS1[fpT1[fpS2[fpT2[spc1[tpc1[spc2[tpc2[]]]]]]]]].
                exists (FP.union fpS' fpS1),fpT1,fpS2,fpT2,spc1,tpc1,spc2,tpc2.
                clearfp.
                rewrite H0.
                split;[econstructor 2|];eauto.
              }
            }
          }
        }
      }
    Qed.    
  End Simulation.
  Section GlobIndexSim.
    Definition ISim_tau_step_case (sge tge:GlobEnv.t)(match_state:nat->Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop)(i:nat) (mu:Mu)(fpS fpT:FP.t)(spc tpc:ProgConfig):Prop:=
        exists fpS1 fpT1 spc1 tpc1 j,
          tau_plus np_step spc fpS1 spc1 /\ tau_N np_step (S i) tpc fpT1 tpc1 /\
          atom_bit spc = atom_bit spc1 /\
          LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS1) (FP.union fpT fpT1) /\
          match_state j mu (FP.union fpS fpS1)(FP.union fpT fpT1) spc1 tpc1.
    Definition ISim_EntAtom_case  (sge tge:GlobEnv.t)(match_state:nat->Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop)(i:nat) (mu:Mu)(fpS fpT:FP.t)(spc tpc:ProgConfig):Prop:=
        exists fpS' fpT' fpS'' fpT'' spc' tpc' spc'' tpc'' j,
          tau_star np_step spc fpS' spc' /\ np_step spc' tau fpS'' spc'' /\
          tau_N np_step i tpc fpT' tpc' /\ np_step tpc' tau fpT'' tpc'' /\
          atom_bit spc' <> atom_bit spc'' /\ atom_bit spc = atom_bit spc' /\
          atom_bit tpc' <> atom_bit tpc'' /\ atom_bit tpc = atom_bit tpc' /\
          LFPG mu tge tpc.(cur_tid) (FP.union fpS (FP.union fpS' fpS'')) (FP.union fpT (FP.union fpT' fpT'')) /\
          match_state j mu FP.emp FP.emp spc'' tpc''.
    Definition ISim_final_case  (sge tge:GlobEnv.t)(match_state:nat->Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop) (i:nat)(mu:Mu)(fpS fpT:FP.t)(spc:@ProgConfig sge)( tpc:@ProgConfig tge):Prop:=
        exists fpS' fpT' spc' tpc',
                tau_star np_step spc fpS' spc' /\ final_state spc' /\ 
                tau_N np_step i tpc fpT' tpc' /\ final_state tpc' /\
                atom_bit spc = atom_bit spc' /\ atom_bit tpc = atom_bit tpc' /\
                LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS') (FP.union fpT fpT').
    
    Definition ISim_npsw_case  (sge tge:GlobEnv.t)(match_state:nat->Mu->FP.t -> FP.t -> @ProgConfig sge -> @ProgConfig tge -> Prop)(i:nat) (mu:Mu)(fpS fpT:FP.t)(spc tpc:ProgConfig):Prop:=
      exists spc' fpS' tpc' fpT',
        tau_star np_step spc fpS' spc' /\ atom_bit spc = atom_bit spc' /\
        tau_N np_step i tpc fpT' tpc' /\ atom_bit tpc = atom_bit tpc' /\
        exists o t spc'' tpc'',
          valid_tid spc'' t/\
          forall id,  valid_tid spc'' id ->
                 o <> tau /\
                 exists j,match_state j mu FP.emp FP.emp ({-|spc'',id})({-|tpc'',id}) /\
                 np_step spc' o FP.emp ({-|spc'',id})/\
                 np_step tpc' o FP.emp ({-|tpc'',id})/\
                 LFPG mu tge tpc.(cur_tid) (FP.union fpS fpS') (FP.union fpT fpT').
    Definition d2s_match_index {sge tge}(i:nat):= @d2s_match sge tge.
      
    Record index_match {sge tge} (i:nat)(mu:Mu)(fpS fpT:FP.t)(spc:@ProgConfig sge)(tpc:@ProgConfig tge):Prop:=
      {
        match_tp':
           Bset.inj_inject (inj mu) /\ GlobEnv.wd tge /\ GlobEnv.wd sge /\
           np_safe_config spc /\
           language_det tge /\
           inv spc /\ inv tpc /\thrddom_eq' spc tpc /\
           atombit_eq spc tpc /\
           tid_eq spc tpc;
        match_step':
          ISim_final_case sge tge d2s_match_index i mu fpS fpT spc tpc \/
          ISim_npsw_case sge tge d2s_match_index i mu fpS fpT spc tpc \/
          ISim_tau_step_case sge tge d2s_match_index i mu fpS fpT spc tpc \/
          ISim_EntAtom_case sge tge d2s_match_index i mu fpS fpT spc tpc
      }.

 
    Lemma d2s_match_index_exists :
      forall  (sge tge:GlobEnv.t)(spc:@ProgConfig sge)(tpc:@ProgConfig tge) fpS fpT mu,
        d2s_match mu fpS fpT spc tpc ->
        exists i, index_match i mu fpS fpT spc tpc.
    Proof. {
      intros.
      pose proof @GSim_d2s_match sge tge.
      inversion H0.
      pose proof match_step0 mu fpS fpT spc tpc H as match_step0.
      destruct match_step0 as [final|[sw|[tau|EntAx]]].
      {
        destruct final as [fpS' [fpT'[spc'[tpc'[star_spc_spc'[final_spc'[star_tpc_tpc'[final_tpc' lfpg]]]]]]]].
        apply tau_star_tau_N_equiv in star_tpc_tpc' as [n ].
        exists n. constructor;intros.
        eapply match_tp0;eauto.
        auto.
        left. exists fpS',fpT',spc',tpc'. auto. 
      }
      {
        unfold Sim_npsw_case in sw.
        destruct sw as [spc'[fpS'[tpc'[fpT'[star1[b1[star2[b2[o[t[spc2[tpc2[vt]]]]]]]]]]]]].
        apply tau_star_tau_N_equiv in star2 as [x ].
        exists x.
        constructor;intros.
        eapply match_tp0;eauto.
        auto.
        right;left.
        unfold ISim_npsw_case.
        exists spc',fpS',tpc',fpT'.
        split;auto;split;auto;split;auto;split;auto.
        exists o,t,spc2,tpc2;split;auto.
        intros.
        specialize (H1 id H3) as [].
        split;auto.
        exists 0;auto.
      }
      {
        destruct tau as[fpS'[fpT'[spc'[tpc'[plus_spc_spc'[plus_tpc_tpc']]]]]].
        apply tau_plus_tau_N_equiv in plus_tpc_tpc'.
        destruct plus_tpc_tpc' as[n plus_tpc_tpc'].
        exists n. constructor;intros;auto.
        eapply match_tp0;eauto.
        right;right; left;exists fpS',fpT',spc',tpc',0;auto. 
      }
      {
        destruct EntAx as[fpS'[fpT'[fpS''[fpT''[spc'[tpc'[spc''[tpc''[star_spc_spc'[step_spc'_spc''[star_tpc_tpc'[step_tpc'_tpc''[bit_neq_spc'_spc''[bit_eq_spc_spc'[lfpg match_spc''_tpc'']]]]]]]]]]]]]]].
        apply tau_star_tau_N_equiv in star_tpc_tpc'.
        destruct star_tpc_tpc' as[x star_tpc_tpc'].
        exists x. constructor;auto.
        eapply match_tp0;eauto.
        right;right;right.
        unfold ISim_EntAtom_case.
        exists fpS',fpT',fpS'',fpT'',spc',tpc',spc'',tpc'',0.
        unfold d2s_match_index.
        split;auto;split;auto;split;auto.
      }
    } 
    Qed.


    Lemma GUSim_index_match{sge tge}:
      @GConfigUSim sge tge nat lt index_match.
    Proof. {
      constructor.
      apply lt_wf.
      {
        intros;inversion H;firstorder.
      }
      Focus 6.
      intros;inversion H;destruct match_tp'0;auto.
      Focus 5.
      {
        intros;inversion H.
        destruct match_tp'0 as [H0[wd1[wd2[[H1 _][ldet[inv1[inv2[theq1[biteq1 tideq1]]]]]]]]];split;auto.
        destruct match_step'0 as [|[|[|]]].
        {
          unfold ISim_final_case in H2.
          destruct H2 as [_[fpT'[_[tpc'[_[_[S1[S2 _]]]]]]]].
          destruct i.
          inversion S1;subst. intro. destruct H2. contradiction.
          inversion S1;subst. intro. destruct H2. apply H5 in H3. auto.
        }
        {
          unfold ISim_npsw_case in H2.
          destruct H2 as [spc'[fpS'[tpc'[fpT'[S1[S2[S3[S4[o[t[spc2[tpc2[vt]]]]]]]]]]]]].
          specialize (H2 t vt) as [ntau[j[S5[S6[S7 S8]]]]].
          destruct i.
          inversion S3;subst. intro. destruct H2. apply H3 in S7. auto.
          inversion S3;subst. intro. destruct H2. apply H5 in H3. auto.
        }
        {
          unfold ISim_tau_step_case in H2.
          destruct H2 as [fpS1[fpT1[spc1[tpc1[j[S1[S2[S3[S4 S5]]]]]]]]].
          inversion S2;subst. intro;destruct H2. apply H5 in H3;auto.
        }
        {
          unfold ISim_EntAtom_case in H2.
          destruct H2 as [_[fpT1[_[fpT2[_[tpc1[_[tpc2[j[_[_[N1[N2 _]]]]]]]]]]]]].
          destruct i.
          inversion N1;subst. intro;destruct H2;apply H3 in N2;auto.
          inversion N1;subst. intro;destruct H2;apply H5 in H3;auto.
        }
      }
      Unfocus.
      Focus 4.
      {
        intros.
        inversion H.
        assert(invtpc:inv tpc). destruct match_tp'0 as [_[_[_[_[_[_ []]]]]]];auto.
        destruct match_step'0 as [|[|[|]]].
        {
          unfold ISim_final_case in H1.
          destruct H1 as [fpS'[fpT'[spc'[tpc'[S1[S2[S3[S4[S5[S6 S7]]]]]]]]]].
          destruct i.
          inversion S3;subst;clearfp. exists spc',fpS';auto.
          inversion S3;subst;apply step_no_final in H2;try contradiction;auto.
        }
        {
          unfold ISim_npsw_case in H1.
          destruct H1 as [spc'[fpS'[tpc'[fpT'[S1[S2[S3[S4[o[t[spc2[tpc2[vt]]]]]]]]]]]]].
          specialize (H1 t vt) as [ntau[j[S5[S6[S7 S8]]]]].
          destruct i.
          inversion S3;subst. apply step_no_final in S7;auto;contradiction.
          inversion S3;subst. apply step_no_final in H2;auto;contradiction.
        }
        {
          unfold ISim_tau_step_case in H1.
          destruct H1 as [fpS1[fpT1[spc1[tpc1[j[S1[S2[S3[S4 S5]]]]]]]]].
          inversion S2;subst. apply step_no_final in H2;auto;contradiction.
        }
        {
          unfold ISim_EntAtom_case in H1.
          destruct H1 as [_[fpT1[_[fpT2[_[tpc1[_[tpc2[j[_[_[N1[N2 _]]]]]]]]]]]]].
          destruct i;inversion N1;subst.
          apply step_no_final in N2;auto;contradiction.
          apply step_no_final in H2;auto;contradiction.
        }
      }
      Unfocus.
      Focus 3.
      {
        intros;inversion H.
        assert(invtpc:inv tpc). firstorder.
        destruct match_step'0 as [|[|[|]]].
        {
          unfold ISim_final_case in H2.
          destruct H2 as [fpS1[fpT1[spc1[tpc1[S1[S2[S3[S4[S5[S6 S7]]]]]]]]]].
          destruct i.
          inversion S3;subst. apply step_no_final in H1;auto;try contradiction.
          
          inversion S3;subst. eapply np_step_det in H3 as[contra _];try apply H1;eauto;try contradiction. destruct match_tp'0 as [_[_[_[_[]]]]];auto.
        }
        {
          unfold ISim_npsw_case in H2.
          destruct H2 as [spc'[fpS'[tpc1[fpT1[S1[S2[S3[S4[l[t[spc2[tpc2[vt]]]]]]]]]]]]].
          pose proof (H2 t vt) as [ntau[j[S5[S6[S7 S8]]]]].
          destruct i.
          {
            inversion S3;clear S3;subst.
            eapply np_step_det in S7;try apply H1;auto.
            destruct S7 as [E1[E2[E3[E4[E5 _]]]]].
            subst.
            exists fpS',spc',FP.emp,({-|spc2,t}),t.
            split;auto;split;auto;split;auto.
            pose proof H2 t vt as [_[_[_[St _]]]].
            split;auto.
            intros t2 vt2.
            specialize (H2 t2 vt2) as [_[j2[Q1[Q2[Q3 Q4]]]]].
            clearfp.
            split;auto.
            split;auto.
            apply d2s_match_index_exists in Q1.
            assert({-|tpc2,t2} = {-|tpc',t2}).
            destruct tpc2,tpc';simpl in *;congruence.
            rewrite <-H2;auto.
            destruct match_tp'0 as [_[_[_[_[]]]]];auto.            
          }
          {
            inversion S3;subst.
            eapply np_step_det in H4 as [contra _];try apply H1;eauto;try contradiction.
            destruct match_tp'0 as (_&_&_&_&?&_);auto.
          }
        }
        {
          unfold ISim_tau_step_case in H2.
          destruct H2 as [fpS1[fpT1[spc1[tpc1[j[S1[S2[S3[S4 S5]]]]]]]]].
          inversion S2;subst. eapply np_step_det in H3 as [];try apply H1;eauto;try contradiction.
          destruct match_tp'0 as (_&_&_&_&?&_);auto.
        }
        {
          unfold ISim_EntAtom_case in H2.
          destruct H2 as [_[fpT1[_[fpT2[_[tpc1[_[tpc2[j[_[_[N1[N2 _]]]]]]]]]]]]].
          destruct i;inversion N1;subst;[eapply np_step_det in N2 as []|eapply np_step_det in H3 as []];try apply H1;try contradiction; destruct match_tp'0 as (_&_&_&_&?&_);auto.
        }
      }
      Unfocus.
      Focus 2.
      {
        intros;inversion H.
        inversion match_tp'0 as (_&_&_&_&LDET&_&invtpc&_);auto.
        destruct match_step'0 as [|[|[|]]].
         {
          unfold ISim_final_case in H2.
          destruct H2 as [fpS1[fpT1[spc1[tpc1[S1[S2[S3[S4[S5[S6 S7]]]]]]]]]].
          destruct i.
          inversion S3;subst. apply step_no_final in H0;auto;contradiction.
          inversion S3;subst. eapply tau_N_tau_step_bit_rule in H4;eauto. eapply tau_step_det in H3 as [_[_]];try apply H0;eauto;subst;try contradiction.
         }
         {
           unfold ISim_npsw_case in H2.
           destruct H2 as [spc'[fpS'[tpc1[fpT1[S1[S2[S3[S4[l[t[spc2[tpc2[vt]]]]]]]]]]]]].
           specialize (H2 t vt) as [ntau[j[S5[S6[S7 S8]]]]].
           destruct i;inversion S3;subst.
           eapply np_step_det in H0 as [];try apply S7;eauto;try contradiction;firstorder.
           eapply tau_step_det in H0 as [_[]];try apply H3;eauto;subst.
           eapply tau_N_tau_step_bit_rule in H4;eauto;contradiction.
         }
         {
           unfold ISim_tau_step_case in H2.
           destruct H2 as [fpS1[fpT1[spc1[tpc1[j[S1[S2[S3[S4 S5]]]]]]]]].
           inversion S2;subst.
           eapply tau_N_tau_step_bit_rule in H4;eauto.
           eapply tau_step_det in H3 as [_[_]];try apply H0;eauto;subst;try contradiction.
           unfold d2s_match_index in S5.
           unfold d2s_match in S5.
           destruct S5 as [I'[ord'[i'[matchstate'[[_ R _ _ _ _ _][match' _]]]]]].
           apply R in match' as [_[E _]];inversion E;clear E;subst.
           destruct match_tp'0 as [_[_[_[_[_[_[_[_[E _]]]]]]]]].
           inversion E;subst.
           congruence.
         }
         {
           unfold ISim_EntAtom_case in H2.
           destruct H2 as [fpS1[fpT1[fpS2[fpT2[spc1[tpc1[spc2[tpc2[j[N1[N2[N3[N4[N5[N6[N7[N8[N9 N10]]]]]]]]]]]]]]]]]].
           destruct i.
           {
             inversion N3;clear N3;subst.
             eapply tau_step_det in N4 as [_[]];try apply H0;eauto;subst.
             apply d2s_match_index_exists in N10 as [].
             exists fpS1,spc1,fpS2,spc2,x.
             clearfp.
             auto.
           }
           {
             inversion N3;clear N3;subst.
             eapply tau_N_tau_step_bit_rule in H4;eauto.
             eapply tau_step_det in H3 as [_[_]];try apply H0;eauto;subst;try contradiction.
           }
         }
      }
      Unfocus.
      {
        intros;inversion H.
        assert(invtpc:inv tpc). firstorder.
        assert(LT:cur_tid tpc = cur_tid tpc'). inversion H0;subst;auto;contradiction.
        inversion match_tp'0 as [_[wd1[wd2[_[LDet _]]]]].
        destruct match_step'0 as [|[|[|]]].
        {
          unfold ISim_final_case in H2.
          destruct H2 as [fpS1[fpT1[spc1[tpc1[S1[S2[S3[S4[S5[S6 S7]]]]]]]]]].
          destruct i.
          inversion S3;subst. apply step_no_final in H0;auto;contradiction.
          inversion S3;subst.
          assert(LDET:language_det tge). firstorder.
          eapply tau_step_det in H0 as [_[]];try apply H3;eauto;subst.
          pose proof S1 as L.
          apply tau_star_tau_N_equiv in L as [].
          destruct x.
          inversion H0;subst.
          inversion match_tp'0 as (_&_&_&_&_&E1&E2&E3&_&_).
          apply thrddom_eq_comm in E3.
          eapply thrddom_eq'_final_state_preservation in S2;eauto.
          apply step_no_final in H3;auto;contradiction.
          destruct i.
          {
            inversion H4;subst.
            left.
            exists spc1,fpS1,0.
            split;auto. eapply tau_plus_tau_N_equiv;eauto.
            split. clearfp;auto.
            constructor.
            {
              destruct match_tp'0 as (?&?&?&?&?&?&?&?&?&?).
              repeat try (split;[assumption|]);auto.
              split. eapply safe_succession in S1;eauto.
              split;auto.
              split. eapply thp_inv_tau_star_preservation in S1;eauto.
              split. eapply thp_inv_preservation;eauto.
              split. apply tau_plus_1 in H3. apply tau_plus2star in H3.
              eapply tau_star_finalstate_thrddom_eq_preservation;eauto.
              inversion H13;auto.
              split. inversion H12;subst. constructor. congruence.
              inversion H13;subst. constructor.
              rewrite<- LT. rewrite <- H14.
              symmetry.
              eapply tau_star_tid_preservation. eapply tau_star_tau_N_equiv;eexists;eauto.
            }
            {
              left.
              unfold ISim_final_case.
              exists FP.emp,FP.emp,spc1,tpc1.
              split;constructor;auto.
              split;constructor;auto.
              clearfp.
              assert(cur_tid tpc = cur_tid tpc1).
              eapply tau_star_tid_preservation;eapply tau_star_tau_N_equiv;eexists;eauto.
              rewrite <- H2;auto.
            }
          }

          right.
          exists (S i). split;auto.
          constructor.
          {
            destruct match_tp'0 as [E1[E2[E0[E3[E4 [E5 [E6 [E7 [E8 E9]]]]]]]]].
            repeat try (split;[auto|]);auto.
            eapply thp_inv_preservation;eauto.
            eapply tau_step_thrddom_eq_preservation;eauto.
            intro. inversion H4;subst. apply step_no_final in H6. contradiction.
            eapply thp_inv_preservation;eauto.
            constructor. inversion E8;subst. rewrite H2. inversion H3;subst;auto;try contradiction.
            constructor;inversion E9;subst;rewrite H2;inversion H3;subst;auto;try contradiction.
          }
          {
            left;unfold ISim_final_case.
            pose proof H3 as L.
            pose proof L as L2.
            eapply tau_N_tau_step_bit_rule in L;eauto.
            apply tau_step_tid_preservation in L2.
            rewrite <- L. rewrite <- L2.
            exists fpS1,fp',spc1,tpc1.
            clearfp;auto.
            repeat try (split;auto).
          }
          
        }
        {
          unfold ISim_npsw_case in H2.
          destruct H2 as [spc'[fpS'[tpc1[fpT1[S1[S2[S3[S4[l[t[spc2[tpc2[vt]]]]]]]]]]]]].
          assert(i>0).
          {
            destruct i;try Lia.lia.
            inversion S3;subst. specialize (H2 t vt) as [nt[j[Q1[Q2[Q3 Q4]]]]].
            eapply np_step_det in Q3 as [];try apply H0;eauto.
            rewrite H2 in nt; contradiction.
          }
          destruct i. inversion H3.
          inversion S3;subst.
          eapply tau_step_det in H0 as [_[]];try apply H5;eauto;subst.
          right.
          exists i;split;auto.
          constructor;auto.
          {
            destruct match_tp'0 as [E1[E2[_[E3[E4[E5[E6[E7[E8 E9]]]]]]]]].
            repeat try (split;[assumption|]).
            split. eapply thp_inv_preservation;eauto.
            split. eapply tau_step_thrddom_eq_preservation;eauto.
            specialize (H2 t vt) as (_&_&_&_&s&_).
            destruct i. inversion H6;subst. apply step_no_final in s;auto. inversion S3;subst. eapply thp_inv_preservation;eauto.
            inversion H6;subst. apply step_no_final in H2;auto. inversion S3;subst. eapply thp_inv_preservation;eauto.
            split. constructor;inversion E8;subst;rewrite H0;inversion H3;subst;auto;try contradiction.
            constructor;inversion E9;subst;rewrite H0;inversion H3;subst;auto;try contradiction.
          }
          {
            right;left.
            unfold ISim_npsw_case.
            exists spc',fpS',tpc1, fp'.
            split;auto;split;auto;split;auto;split.
            rewrite <- S4;inversion H5;subst;auto;try contradiction.
            exists l,t,spc2,tpc2;split;auto.
            clearfp.
            rewrite<- LT.
            auto.
          }
        }
        {
          unfold ISim_tau_step_case in H2.
          destruct H2 as [fpS1[fpT1[spc1[tpc1[j[S1[S2[S3[S4 S5]]]]]]]]].
          destruct i.
          {
            inversion S2;clear S2;subst.
            inversion H4;clear H4;subst.
            eapply tau_step_det in H0 as [_[]];try apply H3;eauto;subst.
            clearfp.
            apply d2s_match_index_exists in S5 as [].
            left.
            exists spc1,fpS1,x;auto.
          }
          {
            right.
            exists i;split;auto.
            constructor.
            {
              destruct match_tp'0 as [E1[E2[_[E3[E4[E5[E6[E7[E8 E9]]]]]]]]].
              repeat try (split;[assumption|]).
              split. eapply thp_inv_preservation;eauto.
              split. eapply tau_step_thrddom_eq_preservation;eauto.
              inversion S2;subst. eapply tau_step_det in H3 as [_[]];try apply H0;eauto;subst.
              inversion H4;subst. apply step_no_final in H3;auto.
              eapply thp_inv_preservation;eauto.
              split. constructor;inversion E8;subst. congruence.
              constructor;inversion E9;subst. congruence.
            }
            {
              right;right;left.
              unfold ISim_tau_step_case.
              inversion S2;subst.
              eapply tau_step_det in H0 as [_[]];try apply H3;eauto;subst.
              exists fpS1,fp',spc1,tpc1,j.
              clearfp;rewrite <- LT;auto.
            }
          }
        }
        {
          unfold ISim_EntAtom_case in H2.
          destruct H2 as [fpS1[fpT1[fpS2[fpT2[spc1[tpc1[spc2[tpc2[j[S1[S2[N1[N2[S3[S4[R1[R2 [S5 S6]]]]]]]]]]]]]]]]]].
          destruct i.
          inversion N1;subst. eapply tau_step_det in H0 as [_[]];try apply N2;eauto;subst;contradiction.
          right.
          exists i;split;auto.
          constructor.
          {
            destruct match_tp'0 as [E1[E2[_[E3[E4[E5[E6[E7[E8 E9]]]]]]]]].
            repeat try (split;[assumption|]).
            split. eapply thp_inv_preservation;eauto.
            split. eapply tau_step_thrddom_eq_preservation;eauto.
            inversion N1;subst. eapply tau_step_det in H0 as [_[]];try apply H3;eauto;subst.
            destruct i;inversion H4;clear H4;subst.
            apply step_no_final in N2;auto. eapply thp_inv_preservation;eauto.
            apply step_no_final in H2;eauto. eapply thp_inv_preservation;eauto.
            split. constructor;inversion E8;subst. congruence.
            constructor;inversion E9;subst. congruence.
          }
          {
            right;right;right.
            inversion N1;subst.
            eapply tau_step_det in H0 as [_[]];try apply H3;eauto;subst.
            unfold ISim_EntAtom_case.
            exists fpS1,fp',fpS2,fpT2,spc1,tpc1,spc2,tpc2,j.
            repeat rewrite <- LT.
            clearfp.
            rewrite<- H1.
            repeat try (split;[assumption|]);auto.
          }
        }
      }
      }
    Qed.
  End GlobIndexSim.
  Section Flip.
    Lemma Language_Det: forall NL (L:@langs NL)(tp:prog L),
      det_langs (fst tp) ->
      wd_langs (fst tp) ->
      forall gm ge pc t,
        init_config tp gm ge pc t->
        language_det ge.
    Proof.
      intros.
      eapply NPDet.init_det;eauto.
    Qed.
    Lemma flipping':
      forall NL (L: @langs NL) (sprog tprog: prog L),
        GlobDSim sprog tprog ->
        det_langs (fst tprog) ->
        wd_langs (fst tprog) ->
        np_safe_prog sprog ->
        GlobUSim sprog tprog.
    Proof.
      intros.
      unfold GlobUSim .
      intros.
      unfold GlobDSim in H.
      specialize (H mu sgm sge spc tgm tge tpc t H3 H4 H5).
      destruct H as[I[order[match_state [i [GDsim match_spc_tpc]]]]].
      inversion H2.
      specialize (H sgm sge spc t H4).
      pose proof Language_Det NL L tprog H0 H1 tgm tge tpc t H5.
      assert(d2s_match mu FP.emp FP.emp spc tpc).
      unfold d2s_match.
      exists I,order,i,match_state.
      repeat try (split;[assumption|]).
      split;[|split];try eapply init_config_inv_thp;eauto.
      inversion H4;inversion H5;subst.      
      inversion H17;inversion H7;subst.
      auto.
      apply d2s_match_index_exists in H7 as [k].
      exists nat,lt,index_match,k.
      split;auto.
      apply GUSim_index_match;auto.      
    Qed.
  End Flip.
End GlobSim.
