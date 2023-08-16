Require Import InteractionSemantics GlobDefs Footprint Injections GAST ETrace GlobUSim NPSemantics  GlobSim GDefLemmas Coqlib Maps List Lia.
Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Ltac clear_get:=
  repeat (rewrite Maps.PMap.gsspec in *;(destruct Coqlib.peq;subst;try contradiction; simpl in *; subst)).
Ltac clear_set:=
  repeat (rewrite Maps.PMap.set2 in *;(destruct Coqlib.peq;subst;try contradiction; simpl in *; subst)).
Ltac solv_thread:=
  repeat
    match goal with
    | H:ThreadPool.update _ _ _ _ |- _ => Coqlib.inv H
    | H:CallStack.update _ _ _ |- _ => Coqlib.inv H
    | H:ThreadPool.halted _ _ |- _ => Coqlib.inv H
    end;
  unfold ThreadPool.get_top, ThreadPool.pop, ThreadPool.get_cs, ThreadPool.push,ThreadPool.valid_tid ,
  CallStack.pop, CallStack.top, CallStack.is_emp, CallStack.emp_cs in *; simpl in *; subst;
  repeat (rewrite Maps.PMap.gsspec in *;(destruct Coqlib.peq;subst;try contradiction; simpl in *; subst));
  repeat 
  match goal with
    H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try (inversion H; fail)
  | H: Some _ = Some _ |- _ => inversion H; clear H; subst
  | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
  | H:?P = ?Q |- context [ ?P ] => rewrite H 
  end;
  simpl in *;
  GDefLemmas.solv_eq; eauto;
  clear_set;simpl in *.
Section thdp.

  Definition is_active {GE: GlobEnv.t} (thdp: @ThreadPool.t GE) (t: tid) : nat :=
  match ThreadPool.get_cs thdp t with
  | None => 0%nat
  | Some nil => 0%nat
  | Some (_ :: _) => 1%nat
  end.

Program Fixpoint count_rec {GE: GlobEnv.t} (thdp: @ThreadPool.t GE) (cur: tid)
  {measure (Pos.to_nat cur)} : nat :=
  match cur with
  | 1%positive => is_active thdp cur
  | _ => is_active thdp cur + (count_rec thdp (Pos.pred cur))
  end.
Next Obligation. rewrite Pos2Nat.inj_pred; lia. Qed.

Definition count {GE: GlobEnv.t} (thdp: @ThreadPool.t GE): nat :=
  count_rec thdp (ThreadPool.next_tid thdp).

Lemma count_rec_succ:
  forall GE (thdp: @ThreadPool.t GE) t,
    count_rec thdp (Pos.succ t) = (is_active thdp (Pos.succ t) + (count_rec thdp t))%nat.
Proof.
  intros. 
  unfold count_rec at 1. unfold count_rec_func. rewrite Program.Wf.Fix_eq.
  destruct t; simpl; fold count_rec_func; auto.
  unfold count_rec. f_equal. f_equal. f_equal. rewrite Pos.pred_double_succ. reflexivity.
  intros. destruct x. destruct s. simpl. 
  destruct t0; auto.
Qed.
  
Lemma pop_emp_count_decr:
  forall GE (thdp: @ThreadPool.t GE) t thdp',
    ThreadPool.inv thdp ->
    ThreadPool.pop thdp t = Some thdp' ->
    ThreadPool.halted thdp' t ->
    count thdp = S (count thdp').
Proof.
  intros. unfold count.
  assert (ThreadPool.next_tid thdp = ThreadPool.next_tid thdp' /\ ThreadPool.valid_tid thdp t).
  { unfold ThreadPool.pop in H0.
    repeat match goal with
           | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?Hx; try discriminate
           end.
    inv H0. split. auto. destruct (plt t (ThreadPool.next_tid thdp)); auto.
    rewrite ThreadPool.tp_finite in Hx; try discriminate; auto.
  }
  destruct H2 as [TIDEQ VALID].
  assert (forall t', t <> t' -> ThreadPool.get_cs thdp t' = ThreadPool.get_cs thdp' t').
  { intros. unfold ThreadPool.get_cs, ThreadPool.pop in *.
    repeat match goal with H:context[match ?x with _ => _ end] |- _ => destruct x; try discriminate end.
    inv H0. simpl. rewrite PMap.gso; auto. }
  assert (exists c, ThreadPool.get_cs thdp t = Some (c :: nil) /\ ThreadPool.get_cs thdp' t = Some nil).
  { inv H1. unfold ThreadPool.get_cs, ThreadPool.pop in *.
    repeat match goal with H:context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try discriminate end.
    inv H0. simpl in *. unfold CallStack.pop in *. destruct t0. discriminate. inv Heqo0.
    rewrite PMap.gss in H3. inv H3. inv H4. rewrite PMap.gss. eauto. }
  destruct H3 as [c [GET0 GET]]. rename H2 into GETEQ. clear H H0 H1.
  assert (REC0: forall B, Plt B t -> count_rec thdp B = count_rec thdp' B).
  { intros B BOUND.
    revert c GET0 GET BOUND GETEQ. intros c ? ? . unfold Plt.
    pattern B. apply positive_Peano_ind; intros.
    exploit (GETEQ 1%positive). apply Plt_ne in BOUND. auto.
    unfold count_rec. cbn. unfold is_active. intro. rewrite H. auto.
    repeat rewrite count_rec_succ. rewrite H; auto.
    unfold is_active. rewrite GETEQ. auto. apply Plt_ne in BOUND. auto.
    unfold Plt in *. lia. }
  assert (REC: forall B, Ple t B -> count_rec thdp B = S (count_rec thdp' B)).
  { intros B BOUND.
    (* induction *)
    revert c GET0 GET BOUND GETEQ. intros c ? ? . unfold Ple.
    pattern B. apply positive_Peano_ind; intros.
    assert (t = 1)%positive. pose proof (Pos.le_1_l t). apply Pos.le_antisym; auto. subst.
    unfold count_rec. cbn. unfold is_active. rewrite GET0, GET; auto.
    repeat rewrite count_rec_succ. 
    apply Pos.lt_eq_cases in BOUND. destruct BOUND as [BOUND|BOUND].
    rewrite plus_n_Sm. unfold is_active. f_equal.
    rewrite (GETEQ (Pos.succ x)); auto with coqlib. apply H; auto. lia.
    subst. rewrite REC0. rewrite <- plus_Sn_m. f_equal.
    unfold is_active. rewrite GET, GET0. auto.
    unfold Plt. lia.
  }
  rewrite <- TIDEQ. apply REC. auto with coqlib.
Qed.

Lemma upd_count_eq':
  forall i GE (thdp: @ThreadPool.t GE) t thdp' c,
    ThreadPool.inv thdp ->
    ThreadPool.update thdp t c thdp' ->
    count_rec thdp i= count_rec thdp' i.
Proof.
  induction i using positive_Peano_ind.
  intros.
  {
    enough(is_active thdp 1%positive = is_active thdp' 1%positive).
    eauto.
    
    inversion H0;subst.
    destruct (peq t 1).
    {
      subst. unfold is_active.
      rewrite H1.
      unfold ThreadPool.get_cs. simpl.
      rewrite PMap.gsspec. destruct peq;try contradiction.
      inversion H2;subst;auto.
    }
    {
      unfold is_active.
      unfold ThreadPool.get_cs. simpl.
      rewrite PMap.gso;auto.
    }
  }
  {
    intros.
    rewrite count_rec_succ.
    rewrite count_rec_succ.
    erewrite IHi;eauto.
    f_equal.
    destruct (peq t (Pos.succ i));inversion H0;subst.
    {
      unfold is_active.
      rewrite H1.
      unfold ThreadPool.get_cs. simpl.
      rewrite PMap.gsspec. destruct peq;try contradiction.
      inversion H2;subst;auto.
    }
    {
      unfold is_active.
      unfold ThreadPool.get_cs. simpl.
      rewrite PMap.gso;auto.
    }
  }
Qed.
Lemma upd_count_eq:
  forall GE (thdp: @ThreadPool.t GE) t thdp' c,
    ThreadPool.inv thdp ->
    ThreadPool.update thdp t c thdp' ->
    count thdp = count thdp'.
Proof.
  unfold count. intros.
  assert(ThreadPool.next_tid thdp = ThreadPool.next_tid thdp').
  inversion H0;subst;auto.
  rewrite H1.
  eapply upd_count_eq';eauto.
Qed.
End thdp.
Section simetr.
  Variable GE:GlobEnv.t.
  Hypothesis wdge:GlobEnv.wd GE.
  Inductive sw_list : nat->@ProgConfig GE->Prop:=
  |sw_0:forall pc, sw_list 0 pc
  |sw_1:forall i pc pc',
      np_step pc sw FP.emp pc'->
      sw_list i pc'->
      sw_list (S i) pc.

  Definition active_thread_num := fun pc => @count GE pc.(thread_pool).
       
  Lemma active_thread_num_exists:
    forall pc,
      ThreadPool.inv pc.(thread_pool)->
      exists i, active_thread_num pc = i.
  Proof. intros. eexists;eauto. Qed.
  Lemma active_thread_num_dec:
    forall pc pc',
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = O->
      np_step pc sw FP.emp pc'->
      active_thread_num pc = S (active_thread_num pc').
  Proof.
    intros. unfold active_thread_num.
    inversion H1;subst;try inversion H0. simpl.
    eapply pop_emp_count_decr;eauto.
  Qed.
  Lemma active_thread_num_eq:
    forall pc pc',
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = I->
      np_step pc sw FP.emp pc'->
      active_thread_num pc = active_thread_num pc'.
  Proof.
    unfold active_thread_num;intros. inversion H1;subst;try inversion H0.
    eapply upd_count_eq;eauto.
  Qed.
  Lemma sw_time_limit:
    forall pc,
      ThreadPool.inv pc.(thread_pool)->
      @atom_bit GE pc = O->
      forall j,
        sw_list j pc->
        (j <= active_thread_num pc)%nat.
  Proof.
    intros.
    induction H1;subst.
    Lia.lia.
    
    erewrite active_thread_num_dec;eauto.
    apply Le.le_n_S.
    apply IHsw_list.
    inversion H1;subst.
    eapply ThreadPool.pop_inv;eauto.
    eapply ThreadPool.upd_top_inv;eauto.
    inversion H1;auto.
  Qed.
  
  CoInductive Sdiverge :@ProgConfig GE->Prop:=
  |SDiverge:
     forall pc fp pc' o,
       o = tau \/ o = sw->
       np_step pc o fp pc'->
       Sdiverge pc'->
       Sdiverge pc.
  
  CoInductive SWdiverge:@ProgConfig GE->Prop:=
  |SWDiverge:
     forall pc fp pc',
       np_step pc sw fp pc'->
       SWdiverge pc'->
       SWdiverge pc.
  
  Lemma SWdiverge_swlist_i:
    forall i pc ,
      SWdiverge pc->
      sw_list i pc.
  Proof.
    induction i.
    intros. constructor.
    intros. inversion H;subst.
    apply IHi in H1.
    econstructor 2;eauto.
    enough(fp=FP.emp);try congruence.
    
    inversion H0;auto.
  Qed.
  Lemma thdp_inv_not_swdiverge:
    forall pc,
      ThreadPool.inv pc.(thread_pool)->
      ~ SWdiverge pc.
  Proof.
    intros. intro.
    destruct (atom_bit pc) eqn:?.
    apply SWdiverge_swlist_i with (i:= S(active_thread_num pc)) in H0.
    apply sw_time_limit in H0;auto. contradict H0. Lia.lia.
    inversion H0;subst.
    eapply GlobSim.GlobSim.thp_inv_preservation in H as ?;eauto;try apply wdge.
    apply SWdiverge_swlist_i with(i:=S(active_thread_num pc)) in H2.
    assert(fp=FP.emp). inversion H1;auto. subst.
    assert(atom_bit pc' = O). inversion H1;auto.
    apply sw_time_limit in H2;auto.
    eapply active_thread_num_eq in Heqb as ?;eauto.
    rewrite H5 in H2. contradict H2.
    Lia.lia.
  Qed.
  
  
  Lemma Sdiverge_inv:
    forall pc,
      ThreadPool.inv pc.(thread_pool)->
      Sdiverge pc->
      exists pc' fp pc'',
        sw_star np_step pc pc'/\
        np_step pc' tau fp pc'' /\
        ThreadPool.inv pc''.(thread_pool) /\
        Sdiverge pc''.
  Proof.
    intros pc H0 H1. pose proof active_thread_num_exists pc H0 as [i H].
    revert pc H H0 H1.
    pose wdge.
    induction i;intros.
    inversion H1;subst.
    destruct H2;subst.
    Esimpl;eauto.  constructor. eapply GlobSim.GlobSim.thp_inv_preservation;eauto. 
    {
      assert(fp=FP.emp). inversion H3;auto. subst.
      destruct (atom_bit pc) eqn:?.
      {
        assert(sw_list 1 pc).
        econstructor 2;eauto. constructor.
        apply sw_time_limit in H2;auto. rewrite H in H2. inversion H2.
      }
      {
        assert(atom_bit pc' = O). inversion H3;auto.
        inversion H4;subst. destruct H5;subst.
        Esimpl;eauto. econstructor 2;eauto. constructor. eapply GlobSim.GlobSim.thp_inv_preservation in H6;eauto.  eapply GlobSim.GlobSim.thp_inv_preservation in H3;eauto.
        eapply GlobSim.GlobSim.thp_inv_preservation in H0 as ?;eauto;try apply wdge.
        assert(fp=FP.emp). inversion H6;auto. subst.
        assert(sw_list 1 pc'). econstructor 2;eauto. constructor.
        apply sw_time_limit in H8;auto.
        erewrite <-active_thread_num_eq in H8;try apply Heqb;eauto.
        rewrite H in H8. inversion H8.
      }
    }
    {
      inversion H1;subst. destruct H2;subst.
      Esimpl;eauto. constructor. eapply GlobSim.GlobSim.thp_inv_preservation ;eauto.
      
      assert(fp=FP.emp). inversion H3;auto. subst.
      destruct (atom_bit pc) eqn:?.
      {
        apply active_thread_num_dec in H3 as ?;eauto.
        rewrite H in H2.
        inversion H2. clear H2. symmetry in H6.
        apply GlobSim.GlobSim.thp_inv_preservation in H3 as ?;eauto.
        apply IHi in H6 as ?;eauto.
        Hsimpl.
        eapply sw_star_cons in H3;eauto.
        Esimpl;eauto.
      }
      {
        assert(atom_bit pc' = O). inversion H3;auto.
        inversion H4;subst. destruct H5;subst.
        apply GlobSim.GlobSim.thp_inv_preservation in H3 as ?;auto.
        apply GlobSim.GlobSim.thp_inv_preservation in H6 as ?;auto.
        Esimpl;eauto. econstructor 2;eauto. constructor.
        
        assert(fp=FP.emp). inversion H6;auto. subst.
        
        assert(active_thread_num pc'0 = i).
        apply GlobSim.GlobSim.thp_inv_preservation in H3 as ?;auto.

        apply active_thread_num_eq in H3;auto.
        apply active_thread_num_dec in H6 as ?;auto.
        rewrite <- H3 ,H in H8.
        congruence.
        eapply IHi in H5;eauto.
        Hsimpl.
        eapply sw_star_cons in H5;eauto.
        eapply sw_star_cons in H3;eauto.
        Esimpl;eauto.
        apply GlobSim.GlobSim.thp_inv_preservation in H3 as ?;auto.
        apply GlobSim.GlobSim.thp_inv_preservation in H6 as ?;auto.
      }
    }
  Qed.
  
  

  Lemma Sdiverge_sound:
    forall pc,
      ThreadPool.inv pc.(thread_pool) ->
      Sdiverge pc->
      silent_diverge np_step pc.
  Proof.
    cofix.
    intros. apply Sdiverge_inv in H0;auto. Hsimpl.
    econstructor;eauto.
  Qed.
  
  Lemma sw_star_cons_Sdiverge:
    forall pc pc',
      sw_star np_step pc pc'->
      Sdiverge pc'->
      Sdiverge pc.
  Proof.
    induction 1;intros. auto.
    econstructor;eauto.
  Qed.
  
  Lemma Sdiverge_exists:
    forall  pc,
      silent_diverge np_step pc->
      Sdiverge pc.
  Proof.
    intros. inversion H;clear H;subst.
    revert pc s' fp' s'' H0 H1 H2.
    cofix.
    intros.
    inversion H0;subst.
    {
      inversion H2;subst.
      inversion H;subst.
      econstructor 1 with(o:=tau);eauto.
      
      econstructor 1 with(o:=tau);eauto. 
    }
    {
      econstructor ;eauto.
    }
  Qed.  

  Inductive non_evt_plus {State:Type}(step:State->glabel->FP.t->State->Prop): State -> FP.t -> State -> Prop :=
  | ne_plus1: forall s o fp s',
      o = tau \/ o = sw ->
      step s o fp s'->
      non_evt_plus step s fp s'
  | ne_star_step: forall s1 o fp1 s2 fp2 s3,
      o = tau \/ o = sw ->
      step s1 o fp1 s2  ->
      non_evt_plus step s2 fp2 s3 ->
      non_evt_plus step s1 (FP.union fp1 fp2) s3.
  
  CoInductive Pdiverge (pc:@ProgConfig GE):Prop:=
  |PDiverge:
     forall fp pc',
       non_evt_plus np_step pc fp pc'->
       Pdiverge pc'->
       Pdiverge pc.

  Lemma Pdiverge_sound:
    forall pc, Pdiverge pc ->Sdiverge pc.
  Proof.
    inversion 1;subst. clear H.
    revert pc fp pc' H0 H1. cofix. intros.

    inversion H0;subst.
    {
      inversion H1.
      econstructor;eauto.
    }
    {
      econstructor;eauto.
    }
  Qed.
  Lemma Pdiverge_exists:
    forall pc, Sdiverge pc->Pdiverge pc.
  Proof. cofix;inversion 1;subst. econstructor;eauto. econstructor;eauto. Qed.
  CoInductive SEtr (pc:@ProgConfig GE) : behav->Prop:=
  | SEtr_done :
      forall fp pc',
        non_evt_star np_step pc fp pc' ->
        final_state pc' -> SEtr pc Behav_done
  | SEtr_abort :
      forall fp pc',
        non_evt_star np_step pc fp pc' ->
        np_abort pc' ->
        SEtr pc Behav_abort
  | SEtr_diverge :
      Sdiverge pc ->
      SEtr pc Behav_diverge
  | SEtr_cons:
      forall fp pc' v pc'' b,
        non_evt_star np_step pc fp pc'->
        np_step pc' (evt v) FP.emp pc''->
        SEtr pc'' b->
        SEtr pc (Behav_cons v b).

  Lemma non_evt_star_star{State:Type}:
    forall step s fp s',
      @non_evt_star State step s fp s'->
      exists l,star step s l fp s'.
  Proof.
    induction 1.
    eexists. constructor.
    destruct IHnon_evt_star.
  destruct H;eexists;econstructor;eauto.
  Qed.
  Lemma GE_mod_wd_npstar_tp_inv:
    forall ge pc l fp pc',
      star (@np_step ge) pc l fp pc' ->
      GlobEnv.wd ge ->
      ThreadPool.inv pc.(thread_pool) ->
      ThreadPool.inv pc'.(thread_pool).
  Proof.
    induction 1;auto;intros.
    eapply IHstar;auto.
    eapply GlobSim.GlobSim.thp_inv_preservation;eauto.
  Qed.
  Lemma non_evt_star_thdp_inv:
    forall ge pc fp pc',
      GlobEnv.wd ge->
      ThreadPool.inv pc.(thread_pool)->
      non_evt_star (@np_step ge) pc fp pc'->
      ThreadPool.inv pc'.(thread_pool).
  Proof.
    intros.
    apply non_evt_star_star in H1 as [].
    eapply GE_mod_wd_npstar_tp_inv;eauto.
  Qed.
  Lemma SEtr_sound:
    forall pc b,
      ThreadPool.inv pc.(thread_pool)->
      SEtr pc b->
      Etr np_step np_abort final_state pc b.
  Proof.    
    cofix.
    intros.
    inversion H0;subst.
    econstructor;eauto.
    econstructor 2;eauto.
    econstructor 3;eauto. eapply Sdiverge_sound;eauto.
    
    econstructor. eauto. eauto.
    eapply SEtr_sound;eauto.
    pose wdge.
    eapply non_evt_star_thdp_inv in H1;eauto.
    eapply GlobSim.GlobSim.thp_inv_preservation;eauto.
  Qed.
  
  Lemma SEtr_exists:
    forall pc b,
      Etr np_step np_abort final_state pc b->
      SEtr pc b.
  Proof.
    cofix.
    intros.
    inversion H;subst;econstructor;eauto.
    eapply Sdiverge_exists;eauto.
  Qed.
End simetr.
