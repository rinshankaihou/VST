Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics GlobSemantics_Lemmas NPSemantics TypedSemantics .

Require Import DRF USimDRF NPDRF Init FPLemmas PRaceLemmas SmileReorder.

Require Import Classical Wf Arith.
(** This file contains lemmas about reordering under the condition of data-race, used in the equivalence of DRF and NPDRF and also the equivalence of Safe and NPSafe.*)
Local Notation "'<<' i ',' c ',' sg ',' F '>>'" := {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|} (at level 60, right associativity).
Local Definition pc_valid_tid {ge}:= @GSimDefs.pc_valid_tid ge.
Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:= D|}(at level 70,right associativity).  Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).


Section CReorder.
  Variable GE:GlobEnv.t.
  Hypothesis wdge:forall ix,mod_wd (GlobEnv.modules GE ix).
  Hypothesis wdge':GlobEnv.wd GE.
  
  Lemma npnswstep_pc_valid_tid_backwards_preservation:
    forall pc l fp pc',
      @glob_npnsw_step GE pc l fp pc'->
      forall t,pc_valid_tid pc' t->pc_valid_tid pc t.
  Proof.
    inversion 1 as [|[]];destruct 1;split;inversion H0;subst;simpl in *.

    eapply valid_tid_backwards_preserve;eauto.
    intro;contradict H2.
    eapply halted_preserve;eauto.
    
    eapply valid_tid_backwards_preserve in H1;eauto.
    right;right;eauto.
    intro;contradict H2. eapply halted_preserve;eauto. right;right;eauto.
    do 5 eexists;eauto.
    
    eapply valid_tid_backwards_preserve with(thdp1:=thdp') in H1;eauto.
    eapply valid_tid_backwards_preserve ;eauto.
    intro;contradict H2. eapply halted_preserve with(thdp2:=thdp') in H3;eauto.
    eapply halted_preserve;eauto.
  Qed.

  Lemma npnsw_taustar_pc_valid_tid_backwards_preservation:
    forall pc fp pc',
      tau_star (@glob_npnsw_step GE) pc fp pc'->
      forall t,pc_valid_tid pc' t->pc_valid_tid pc t.
  Proof.
    induction 1;intros;auto.
    apply IHtau_star in H1.
    eapply npnswstep_pc_valid_tid_backwards_preservation;eauto.
  Qed.
  Lemma npnsw_taustar_to_taustar:
    forall pc fp pc',
      tau_star glob_npnsw_step pc fp pc'->
      tau_star (@glob_step GE) pc fp pc'.
  Proof.
    induction 1;intros. constructor.
    econstructor;eauto. inversion H as [|[|]];eapply type_glob_step_elim;eauto.
  Qed.

  
  Lemma corestar_globstar:
    forall pc fp pc',
      tau_star (type_glob_step core) pc fp pc'->
      tau_star (@glob_step GE) pc fp pc'.
  Proof.
    induction 1;intros.
    constructor.
    econstructor;eauto. apply type_glob_step_elim in H;auto.
  Qed.
  Lemma corestar_coretaustar:
    forall l pc fp pc',
      star (@type_glob_step GE core) pc l fp pc'->
      tau_star (type_glob_step core) pc fp pc'.
  Proof.
    induction 1;intros. constructor.
    econstructor;eauto. inversion H;subst;auto.
  Qed.

  Lemma type_glob_step_cur_valid_id:
    forall x pc l fp pc',
      type_glob_step x pc l fp pc'->
      invpc GE pc->
      x <> glob_sw ->
      cur_valid_id GE pc.
  Proof.
    intros.
    assert(exists c, getcurcore GE pc = Some c).
    inversion H;subst;try contradiction;eauto.
    destruct H2.
    split. eapply gettop_valid_tid;eauto.
    intro;unfold getcurcore in H2;solv_thread.
  Qed.
  
  Lemma corestar_Glocality:
    forall l pc fp pc' pc1,
      star (@type_glob_step GE core) pc l fp pc' ->
      thread_sim GE pc pc1 ->
      ThreadPool.inv pc.(thread_pool)->
      ThreadPool.inv pc1.(thread_pool)->
      GPre GE pc.(gm) pc1.(gm) fp pc.(cur_tid) ->
      exists pc1',star (@type_glob_step GE core) pc1 l fp pc1' /\ GPost GE pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim GE pc' pc1'.
  Proof.
    induction l;intros.
    inversion H;subst. exists pc1. split. constructor.
    split;auto.
    inversion H3;subst.
    econstructor;eauto.
    destruct H4;constructor;auto.
    intros. inversion H4.

    inversion H;subst.
    eapply GPre_subset in H3 as R;[|eapply FP.union_subset].
    
    eapply corestep_Glocality in H7 as ?;eauto.
    Hsimpl.
    apply type_glob_step_elim in H4 as ?.
    apply globstep_eff in H8;auto.
    apply type_glob_step_elim in H7 as ?.
    apply globstep_eff in H9;auto.
    assert(cur_tid pc = cur_tid pc1).
    inversion H0;auto.
    rewrite <- H11 in *;clear H11.
    eapply GPre_GEffect_GPost_Rule in H5 as ?;eauto.

    assert(cur_tid pc = cur_tid s2).
    inversion H7;auto.
    rewrite H12 in H11.
    assert(ThreadPool.inv x.(thread_pool)).
    eapply GE_mod_wd_tp_inv;eauto. eapply type_glob_step_elim;eauto.
    assert(ThreadPool.inv s2.(thread_pool)).
    eapply type_glob_step_elim in H7;eauto.
    eapply GE_mod_wd_tp_inv in H7;eauto.
    
    eapply IHl in H10 as ?;eauto.
    Hsimpl.
    Esimpl;eauto. econstructor;eauto.
    rewrite <- H12 in *.
    apply corestar_taustar in H15.
    apply corestar_globstar in H15.
    apply taustar_eff in H15;auto.
    apply corestar_taustar in H10. apply corestar_globstar in H10.
    apply taustar_eff in H10;auto.

    rewrite <- H12 in *.
    assert(cur_tid x =cur_tid pc). inversion H6. congruence.
    rewrite H18 in *.
    eapply GPost_GEffect_GPost_Rule1 in H16 ;eauto.
  Qed.

  Lemma core_taustar_Glocality:
     forall pc fp pc' pc1,
      tau_star (@type_glob_step GE core) pc fp pc' ->
      thread_sim GE pc pc1 ->
      ThreadPool.inv pc.(thread_pool)->
      ThreadPool.inv pc1.(thread_pool)->
      GPre GE pc.(gm) pc1.(gm) fp pc.(cur_tid) ->
      exists pc1',tau_star (@type_glob_step GE core) pc1 fp pc1' /\ GPost GE pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim GE pc' pc1'.
  Proof.
    intros.
    apply tau_star_to_star in H as [].
    eapply corestar_Glocality in H3;eauto.
    Hsimpl.
    eapply corestar_coretaustar in H3.
    Esimpl;eauto.
  Qed.



  Lemma npnswstep_half_I_smile:
    forall pc fp pc',
      invpc GE pc->
      glob_npnsw_step pc tau fp pc'->
      forall t pc1 fp' pc2,
        type_glob_step entat ({-|pc',t}) tau FP.emp pc1->
        tau_star (type_glob_step core) pc1 fp' pc2 ->
        FP.smile fp fp'->
        cur_tid pc' <> t->
        exists pc1' pc2' pc3',
          type_glob_step entat ({-|pc, t}) tau FP.emp pc1' /\
          tau_star (type_glob_step core) pc1' fp' pc2' /\
          glob_npnsw_step (changepc GE pc2' (cur_tid pc') O) tau fp pc3' /\
          thread_pool pc3' = thread_pool pc2 /\
          GMem.eq' (gm pc3')(gm pc2).
  Proof.
    intros.
    apply npnsw_step_tid_preservation in H0 as ?.
    apply npnswstep_l2 in H0 as ?.
    apply npnswstep_l1 in H0;Hsimpl.
    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    eapply atomblock_open_reorderstep1 in H0 as ?;eauto;try congruence;Hsimpl.
    assert(mem_eq_pc GE pc1 (changepc GE x1 t I) ).
    unfold mem_eq_pc;Esimpl;eauto;inversion H1;subst;auto.
    rewrite <-H11. apply GMem.eq'_refl.
    eapply mem_eq_corestar in H12 as ?;eauto;Hsimpl.
    eapply atomblock_open_reorder_corestar in H9 as ?;eauto.
    Hsimpl.
    apply npnswstep_l3 in H16;auto.
    assert(x0 = changepc GE x0 t I). inversion H8;subst;auto.
    rewrite <- H19 in *.
    rewrite H5 in H16.
    unfold mem_eq_pc in H14;Hsimpl.

    Esimpl;try apply H16;eauto;try congruence.
    try eapply GMem.eq'_trans;eauto. apply GMem.eq'_sym;auto.

    apply npnswstep_l3 in H9;auto. apply npnswstep_l2 in H9;auto.
    intro R;inversion R.
    congruence.
    apply type_glob_step_elim in H8.
    eapply GE_mod_wd_tp_inv in H8;eauto.
  Qed.    
  Lemma localstep_locality2:
    forall i_x F cc m fp cc' m',
      step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m fp cc' m' ->      
      forall m1 fp1,
      (exists (fp0 : FP.t) (q1 : InteractionSemantics.core (ModSem.lang (GlobEnv.modules GE i_x)))  (m0 : gmem),step (ModSem.lang (GlobEnv.modules GE i_x))
      (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F)
      cc m1 fp0 q1 m0) ->
        (forall fp2 cc2 m2,step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m1 fp2 cc2 m2 -> FP.subset fp2 fp1) ->
        LPre m m1 fp1 (FLists.get_fl (GlobEnv.freelists GE) F) ->
        exists m1', step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m1 fp cc' m1'.
  Proof.
    intros.
    specialize (wdge i_x).
    pose proof step_locality_2 _ wdge.
    unfold corestep_locality_2 in H3.
    apply LPre_comm in H2.
    eapply H3 in H2;eauto.
  Qed.
  Lemma corestep_locality2:
    forall pc pc' c,
      getcurcore GE pc = Some c ->
      getcurcore GE pc' = Some c ->
      forall (H_corestep:
           exists fp0 pc0,
             type_glob_step core pc tau fp0 pc0),
      forall fp,
        (forall fp' pc',type_glob_step core pc tau fp' pc'->FP.subset fp' fp) ->
        LPre pc.(gm) pc'.(gm) fp (getfl GE c) ->
        forall fp1 pc'1,
          type_glob_step core pc' tau fp1 pc'1 ->
          exists pc1,type_glob_step core pc tau fp1 pc1.
  Proof.
    unfold getcurcore;intros.
    inversion H3;subst;simpl in *.
    rewrite H_tp_core in H0;inversion H0;clear H0;subst.
    unfold getfl in H2.
    apply LPre_comm in H2.
    eapply localstep_locality2 in H_core_step as [];try apply H2;eauto.
    
    assert(exists thdp'',ThreadPool.update pc.(thread_pool) pc.(cur_tid) c' thdp'').
    unfold ThreadPool.get_top in H.
    destruct (ThreadPool.get_cs pc.(thread_pool) pc.(cur_tid)) eqn:eq3;[|inversion H].
    destruct t0;inversion H;clear H;subst.
    eexists;econstructor;eauto.
    econstructor;eauto.
    destruct H4.
    exists {|thread_pool:=x0;cur_tid:=pc.(cur_tid);gm:=x;atom_bit:=pc.(atom_bit)|}.
    
    assert(pc={|thread_pool:=pc.(thread_pool);cur_tid:=pc.(cur_tid);gm:=pc.(GlobDefs.gm);atom_bit:=pc.(atom_bit) |}). destruct pc;auto.
    rewrite H5. simpl.
    econstructor;eauto.

    destruct H_corestep as (?&?&?).
    inversion H0;subst;simpl in *.
    rewrite H in H_tp_core0. inversion H_tp_core0;subst.
    eauto.
    
    revert H H1;clear;intros.
    assert(exists c',Core.update c cc2 c').
    eexists. econstructor;eauto.
    destruct H2 as [c'].
    assert(exists thdp'',ThreadPool.update pc.(thread_pool) pc.(cur_tid) c' thdp'').
    unfold ThreadPool.get_top in H.
    destruct (ThreadPool.get_cs pc.(thread_pool) pc.(cur_tid)) eqn:eq3;[|inversion H].
    destruct t;inversion H;clear H;subst.
    eexists;econstructor;eauto.
    econstructor;eauto.
    destruct H3.
    eapply H1 with (pc':=( {|thread_pool:=x;cur_tid:=pc.(cur_tid);gm:=m2;atom_bit:=pc.(atom_bit)|}));eauto.
    assert(pc={|thread_pool:=pc.(thread_pool);cur_tid:=pc.(cur_tid);gm:=pc.(GlobDefs.gm);atom_bit:=pc.(atom_bit) |}). destruct pc;auto.
    rewrite H4. simpl.
    econstructor;eauto.
  Qed.
  Lemma safe_succeed:
    forall step abort (pc:@ProgConfig GE) l fp pc',
      safe_state step abort pc->
      star step pc l fp pc'->
      safe_state step abort pc'.
  Proof.
    unfold safe_state;intros.
    eapply cons_star_star in H1;eauto.
  Qed.


  
  Lemma safe_state_tau_process:
    forall pc t c, 
    forall
      (H_atomO: atom_bit pc = O)
      (H_safe:safe_state glob_step abort pc)
      (H_invthdp:ThreadPool.inv pc.(thread_pool))
      (H_cexists:ThreadPool.get_top pc.(thread_pool) t = Some c)
      (H_cstep: exists m fp cc' gm', step (ModSem.lang (GlobEnv.modules GE (Core.i c))) (ModSem.Ge (GlobEnv.modules GE (Core.i c)))  (FLists.get_fl(GlobEnv.freelists GE)(Core.F c)) (Core.c c) m fp cc' gm'),
      
      exists fp pc1,
        @type_glob_step GE core ({-|pc,t}) tau fp pc1 /\ safe_state glob_step abort pc1.
  Proof.
    intros.
    unfold safe_state in H_safe.
    assert(star glob_step pc (cons sw nil) (FP.union FP.emp FP.emp) ({-|pc,t})).
    econstructor;[|constructor].
    destruct pc;simpl in *;subst.
    
    (*Really need inv thdp?*)
    econstructor.
    eapply gettop_valid_tid;eauto.
    intro. solv_thread.

    eapply safe_succeed in H;eauto.
    unfold safe_state in H.
    assert(star glob_step ({-|pc,t}) nil FP.emp ({-|pc,t})). constructor.
    apply H in H0.
    unfold abort in H0.
    apply not_and_or in H0.
    destruct H0.
    apply NNPP in H0.
    solv_thread.

    apply not_all_ex_not in H0;Hsimpl.
    apply not_all_ex_not in H0;Hsimpl.
    apply not_all_ex_not in H0;Hsimpl.
    apply imply_to_and in H0;Hsimpl.

    specialize (wdge (Core.i c)).
    apply step_not_atext in H1 as T1; auto.
    apply step_not_halt in H1 as T2; auto.
    destruct x;[|contradiction|].
    Focus 2.
    {
      inversion H0;subst.
      rewrite H_cexists in H_tp_core. inversion H_tp_core;subst.
      rewrite T1 in H_core_atext. inversion H_core_atext.
    }
    Unfocus.
    apply type_glob_step_exists in H0;Hsimpl.
    destruct x.
    do 3 eexists;eauto.
    unfold safe_state. intros.
    apply type_glob_step_elim in H0.
    eapply star_step in H0;eauto.

    inversion H0;subst. rewrite H_cexists in H_tp_core;inversion H_tp_core;subst.
    rewrite T1 in H_core_atext. inversion H_core_atext.
    
    inversion H0;subst. rewrite H_cexists in H_tp_core;inversion H_tp_core;subst.
    rewrite T2 in H_core_halt. inversion H_core_halt.

    inversion H0;subst. rewrite H_cexists in H_tp_core;inversion H_tp_core;subst.
    rewrite T1 in H_core_atext. inversion H_core_atext.

    inversion H0;subst. rewrite H_cexists in H_tp_core;inversion H_tp_core;subst.
    rewrite T1 in H_core_atext. inversion H_core_atext.

    inversion H0;subst.

    inversion H0;subst.
    inversion H0;subst.
    inversion H0;subst.
    inversion H0;subst.
    rewrite H_cexists in H_tp_core;inversion H_tp_core;subst.
    rewrite T2 in H_core_halt. inversion H_core_halt.
  Qed.
    
    
    


  Lemma not_abort_rule:
    forall pc,
      ~ @abort GE pc->
      (ThreadPool.halted pc.(thread_pool) pc.(cur_tid)) \/ (exists l fp pc',glob_step pc l fp pc' /\ l <> sw).
  Proof.
    intros.
    unfold abort in H.
    apply not_and_or in H.
    destruct H. left. apply NNPP;auto.
    repeat (apply not_all_ex_not in H;Hsimpl).
    right. eauto.
  Qed.

  Lemma type_restrict_core:
    forall pc pc',
      getcurcore GE pc = getcurcore GE pc'->
      forall x l fp pc1
        (H_a: x <> ret)(H_b: x <> glob_halt),
        type_glob_step x pc l fp pc1 ->
        l <> sw ->
        forall y l' fp' pc1',
          type_glob_step y pc' l' fp' pc1'->
          l' <> sw ->
          y = x.
  Proof.
    unfold getcurcore;intros.
    inversion H0;subst;try contradiction;specialize (wdge (Core.i c));
      try(inversion H2;subst;auto;simpl in *;rewrite H in H_tp_core;
          try (rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;subst);
          try (apply step_not_atext in H_core_step; auto;
               rewrite H_core_step in H_core_atext;
               inversion H_core_atext);
          try (apply step_not_halt in H_core_step; auto;
              rewrite H_core_step in H_core_halt;
              inversion H_core_halt);
          try contradiction;
          try (edestruct atext_not_halt; eauto;
              [erewrite H4 in H_core_atext;inversion H_core_atext|
               rewrite H4 in H_core_halt;inversion H_core_halt]);
          try (rewrite H_core_atext in H_core_atext0;
               inversion H_core_atext0;subst;inversion H_not_prim)).
  Qed.

  
  Lemma corestep_reorder_rule_alter:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE core ({-|pc,t1}) tau fp1 pc1 ->
      type_glob_step core ({-|pc1,t2}) tau fp2 pc2 ->
      t1 <> t2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool) ->
      (abort ({-|pc,t2})) \/
      ((exists fp pc',type_glob_step core ({-|pc,t2}) tau fp pc' /\ FP.conflict fp1 fp) \/
      exists pc' ,@type_glob_step GE core ({-|pc,t2}) tau fp2 pc' /\ FP.smile fp2 fp1).
  Proof.
    intros.
    assert(abort({-|pc,t2}) \/ ~abort ({-|pc,t2})). apply classic.
    destruct H4;auto.
    right.
    apply not_abort_rule in H4 as [|].
    inversion H;subst;inversion H0;subst.
    solv_thread.

    Hsimpl.
    apply type_glob_step_exists in H4 as [].
    assert(R1:getcurcore GE ({-|pc1,t2}) = getcurcore GE ({-|pc,t2})).
    inversion H;subst. unfold getcurcore. solv_thread.
    eapply type_restrict_core in R1;eauto;try(intro contra;inversion contra;fail).
    subst.
    destruct x;try(inversion H4;fail). clear H5. rename H4 into R0.
    
    assert( (exists (fp : FP.t) (pc' : ProgConfig),type_glob_step core ({-|pc, t2}) tau fp pc' /\ FP.conflict fp1 fp) \/ ~  (exists (fp : FP.t) (pc' : ProgConfig), type_glob_step core ({-|pc, t2}) tau fp pc' /\ FP.conflict fp1 fp)).
    apply classic.
    destruct H4;auto.
    right.
    
    assert(forall fp pc',type_glob_step core ({-|pc,t2}) tau fp pc' -> FP.smile fp fp1).
    intros.
    apply FP.smile_conflict_compat;intro.
    apply FP.conflict_sym in H6.
    contradict H4;eauto.
    clear H4.
    assert(exists c,ThreadPool.get_top pc.(thread_pool) t1 = Some c).
    Coqlib.inv H;eauto.
    destruct H4 as (c&?).
    assert(exists c2,ThreadPool.get_top pc.(thread_pool) t2 = Some c2 /\ ThreadPool.get_top pc1.(thread_pool) t2 = Some c2).
    Coqlib.inv H;Coqlib.inv H0.
    eapply gettop_backwards_preserve in H_tp_core0 as R1;eauto.
    destruct H6 as (c2&?&?).
    assert(forall fp pc',type_glob_step core ({-|pc,t2}) tau fp pc'->LPre pc'.(gm) pc.(gm) fp1 (getfl GE c)).
    intros.
    specialize (H5 fp pc' H8).
    apply fpsmile_sym in H5.
    eapply corestep_eff in H;eauto.
    eapply corestep_eff in H8;eauto.
    simpl in *.
    eapply LEffect_fpsmile_LPre_Rule;eauto.
    eapply dif_thd_disj_fl;eauto.
    apply fpsmile_sym;auto.

    
    pose corestep_locality2.
    assert(forall fp'' pc'',type_glob_step core ({-|pc,t2}) tau fp'' pc'' -> FP.subset fp'' (FP.maxsmile fp1)).
    intros.
    eapply H5 in H9;eauto. eapply FP.maxsmile_smile_subset;eauto.

    assert(L1:LPre (gm ({-|pc,t2}))(gm pc1)(FP.maxsmile fp1)(getfl GE c2)).
    assert(exists c3,ThreadPool.get_top pc1.(thread_pool) t1 = Some c3).
    inversion H;subst;simpl.
    exists c'. solv_thread. destruct Coqlib.peq;try contradiction;auto.
    destruct H10.
    assert(ThreadPool.inv pc1.(thread_pool)).
    inversion H;clear H;subst. eapply ThreadPool.upd_top_inv;eauto.
    eapply corestep_eff in H as E1;eauto.
    assert(getfl GE c = getfl GE x).
    eapply core_Fpreservation with(pc:=({-|pc,t1}));eauto.
    unfold getcurcore. assert(cur_tid pc1 = t1). inversion H;auto.
    rewrite H12. eauto.
    rewrite H12 in E1.
    pose proof FP.maxsmile_smile fp1.
    apply LPre_comm.
    eapply LEffect_fpsmile_LPre_Rule;eauto.
    
    eapply dif_thd_disj_fl with(t1:=t2)(t2:=t1);eauto.
    eapply corestep_locality2 in H0;try apply L1;eauto.
    destruct H0 as [].
    exists x;split;auto.
    eapply H5;eauto.
  Qed.

  Corollary corestep_reorder_rule_alter2:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE core ({-|pc,t1}) tau fp1 pc1 ->
      type_glob_step core ({-|pc1,t2}) tau fp2 pc2 ->
      t1 <> t2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool) ->
      (abort ({-|pc,t2})) \/ 
      ((exists fp pc',type_glob_step core ({-|pc,t2}) tau fp pc' /\ FP.conflict fp1 fp) \/
      (FP.smile fp1 fp2 /\ exists pc1',type_glob_step core ({-|pc,t2}) tau fp2 pc1'/\
              exists pc2',type_glob_step core ({-|pc1',t1}) tau fp1 pc2' /\
                     mem_eq_pc GE pc2 ({-|pc2',t2}))).
  Proof.
    intros.
    eapply corestep_reorder_rule_alter in H1 as L1;eauto.
    destruct L1 as [|[]];auto.
    right;right.
    destruct H4 as (_&_&?).
    apply fpsmile_sym in H4.
    eapply corestep_reorder_rule in H1;eauto.
  Qed.

  
  Lemma corestep_conflict:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE core ({-|pc,t1}) tau fp1 pc1 ->
      type_glob_step core ({-|pc1,t2}) tau fp2 pc2 ->
      t1 <> t2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      FP.conflict fp1 fp2 ->
      (abort ({-|pc,t2})) \/
      exists fp pc',type_glob_step core ({-|pc,t2}) tau fp pc' /\ FP.conflict fp1 fp.
  Proof.
    intros.
    eapply corestep_reorder_rule_alter in H1 as L1;eauto.
    destruct L1 as [|[]];auto.
    destruct H5 as (?&?&?). eauto.    
  Qed.
  Lemma npnswstep_fpnotemp:
    forall pc fp pc',
      @glob_npnsw_step GE pc tau fp pc'->
      fp<> FP.emp->
      type_glob_step core pc tau fp pc'.
  Proof.  destruct 1 as [|[]];auto;intro;inversion H;subst;contradiction. Qed.
  Lemma npnswstep_conflict:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @glob_npnsw_step GE ({-|pc,t1}) tau fp1 pc1->
      glob_npnsw_step ({-|pc1,t2}) tau fp2 pc2->
      t1 <> t2->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      FP.conflict fp1 fp2 ->
      (abort({-|pc,t2})) \/
      exists fp pc',glob_npnsw_step ({-|pc,t2}) tau fp pc' /\ FP.conflict fp1 fp.
  Proof.
    intros.
    apply FP.emp_never_conflict in H4 as L1.
    destruct L1.
    apply npnswstep_fpnotemp in H;auto.
    apply npnswstep_fpnotemp in H0;auto.
    eapply corestep_conflict in H4;eauto.
    destruct H4;auto.
    Hsimpl. right;Esimpl;eauto.
    left;eauto.
  Qed.
  Lemma npnswstep_reorder_rule_alter:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @glob_npnsw_step GE ({-|pc,t1}) tau fp1 pc1->
      glob_npnsw_step ({-|pc1,t2}) tau fp2 pc2->
      t1 <> t2->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      (abort ({-|pc,t2})) \/ 
      ((exists fp pc',glob_npnsw_step ({-|pc,t2}) tau fp pc' /\ FP.conflict fp1 fp)\/
      exists pc',glob_npnsw_step ({-|pc,t2}) tau fp2 pc').
  Proof.
    intros.
    apply glob_npnsw_step_type in H as (x&step1&type1).
    apply glob_npnsw_step_type in H0 as (y&step2&type2).
    assert(FP.smile fp1 fp2 \/ ~FP.smile fp1 fp2).
    apply classic.
    destruct H.

    assert(atom_bit pc = atom_bit pc1).
    inversion type1 as [|[]];inversion step1;subst;auto;try inversion H4.
    assert(atom_bit pc1 = atom_bit pc2).
    inversion type2 as [|[]];inversion step2;subst;auto;try inversion H5.

    assert(tau <> sw). intro L;inversion L.
    eapply  globstep_reorder_rule in H;eauto.
    destruct H as (pc'&step'&_).
    right;right;exists pc'.
    inversion type2 as [|[]];subst;unfold glob_npnsw_step;auto.

    apply smile_conflict in H.
    apply FP.emp_never_conflict in H as [].
    assert(x = core).
    inversion type1 as [|[]];inversion step1;subst;auto;try contradiction.
    assert(y = core).
    inversion type2 as [|[]];inversion step2;subst;auto;try contradiction.
    subst.
    eapply corestep_reorder_rule_alter in H1;eauto.
    destruct H1 as [|[|]];eauto;Hsimpl;unfold glob_npnsw_step;eauto.
    right;left;eauto.
  Qed.
    

      
  Lemma npnsw_conflict_min_rule:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @glob_npnsw_step GE ({-|pc,t1}) tau fp1 pc1->
      tau_star glob_npnsw_step ({-|pc1,t2}) fp2 pc2 ->
      t1 <> t2 ->
      FP.conflict fp1 fp2 ->
      exists fp20 fp21 pc20 pc21,
        tau_star glob_npnsw_step ({-|pc1,t2}) fp20 pc20 /\
        glob_npnsw_step pc20 tau fp21 pc21 /\
        FP.smile fp1 fp20 /\ FP.conflict fp1 fp21.
  Proof.
    intros.
    apply tau_star_tau_N_equiv in H0 as [].
    revert t1 t2 pc pc1 pc2 fp1 fp2 H H0 H1 H2.
    induction x;intros.
    Coqlib.inv H0.
    apply FP.emp_never_conflict in H2 as [];contradiction.

    assert(S x = x + 1). Lia.lia.
    rewrite H3 in H0. apply tau_N_split in H0.
    destruct H0 as (pc'&fp&fp'&N1&N2&?).

    assert(FP.conflict fp1 fp \/ ~FP.conflict fp1 fp).
    apply classic.
    destruct H4.
    eapply IHx in H4;eauto.

    apply FP.smile_conflict_compat in H4.
    assert(~FP.smile fp1 fp').
    rewrite <- H0 in H2.
    apply fpsmile_sym in H4.
    intro.
    apply fpsmile_sym in H5.
    eapply fpsmile_union in H4;eauto.
    apply fpsmile_sym in H4.
    apply FP.smile_conflict_compat in H4.
    rewrite FP.union_comm_eq in H4.
    contradiction.

    apply smile_conflict in H5.
    exists fp,fp',pc',pc2.
    split;auto. apply tau_star_tau_N_equiv;eauto.
    split;auto.
    inversion N2;subst;auto.
    inversion H8;subst;auto.
    rewrite FP.fp_union_emp in *;auto.
  Qed.
    


  Definition halfatomblockstep:=
      fun pc l fp pc'=> l = tau /\ exists pc1 ,type_glob_step entat pc tau FP.emp pc1 /\
                                        tau_star (@type_glob_step GE core) pc1 fp pc'.

  Lemma halfatomblockstep_cur_valid_id:
    forall pc l fp pc',
      halfatomblockstep pc l fp pc'->
      invpc GE pc->
      cur_valid_id GE pc.
  Proof.
    unfold halfatomblockstep;intros;Hsimpl.
    eapply type_glob_step_cur_valid_id;eauto.
    intro R;inversion R.
  Qed.
  Definition halfatomblock_abort (pc:@ProgConfig GE):Prop:=
    exists fp pc', halfatomblockstep pc tau fp pc' /\ abort pc'.

  Lemma halfatomblockabort_sw:
    forall pc,
      invpc GE pc ->
      halfatomblock_abort pc ->
      forall t,
        glob_step ({-|pc,t}) sw FP.emp pc.
  Proof.
    intros. unfold halfatomblock_abort in H0. Hsimpl.
    apply halfatomblockstep_cur_valid_id in H0 as ?;auto.
    assert(atom_bit pc = O).
    destruct H0;Hsimpl. inversion H3;auto.
    destruct pc,H2;simpl in *;subst;econstructor;eauto.
  Qed.
  Lemma halfatomblockstep_star:
    forall pc l fp pc',
      halfatomblockstep pc l fp pc'->
      exists l', star glob_step pc l' fp pc'.
  Proof.
    unfold halfatomblockstep;intros.
    Hsimpl.
    apply corestar_globstar in H1.
    apply tau_star_to_star in H1.
    apply type_glob_step_elim in H0.
    Hsimpl.
    rewrite <- FP.emp_union_fp with(fp:=fp).
    Esimpl;eauto.
    econstructor;eauto.
  Qed.

  Definition npnsw_star_abort (pc:@ProgConfig GE):Prop:=
    exists fp pc',tau_star glob_npnsw_step pc fp pc'/\ abort pc'.

  
  Definition star_abort (pc:@ProgConfig GE):Prop:=
    exists l fp pc', star glob_step pc l fp pc' /\ abort pc'.

  Inductive predicted_abort1 (pc:@ProgConfig GE):Prop:=
  |atomblock_abort_mk:
     forall fp pc',
       tau_star glob_npnsw_step pc fp pc' ->halfatomblock_abort pc'->
       predicted_abort1 pc
  |npnsw_star_abort_mk:
     forall pc',
       glob_step pc' sw FP.emp pc->
       npnsw_star_abort pc ->
       predicted_abort1 pc.
  Definition predicted_abort:= fun pc=> atom_bit pc = O /\  cur_valid_id GE pc /\ (abort pc \/ halfatomblock_abort pc).

  Lemma predicted_abort_predicted_abort1:
    forall pc,
      predicted_abort pc ->
      predicted_abort1 pc.
  Proof.
    unfold predicted_abort;intros;Hsimpl.
    destruct H1.
    
    econstructor 2;eauto.
    instantiate(1:=pc).
    destruct pc,H0;simpl in *;subst;econstructor;eauto.
    unfold npnsw_star_abort. Esimpl;eauto. constructor.
    econstructor 1;eauto. constructor.
  Qed.
  Lemma step_star_abort_suc:
    forall pc l fp pc',
      glob_step pc l fp pc'->
      star_abort pc'->
      star_abort pc.
  Proof. unfold star_abort;intros;Hsimpl;Esimpl;eauto;econstructor;eauto. Qed.
  Lemma taustar_abort_suc:
    forall pc fp pc',
      tau_star glob_step pc fp pc'->
      abort pc'->
      star_abort pc.
  Proof. intros;apply tau_star_to_star in H as [];do 3 eexists;eauto. Qed.
  Lemma npnsw_taustar_abort_suc:
    forall pc fp pc',
      tau_star glob_npnsw_step pc fp pc'->
      abort pc'->
      star_abort pc.
  Proof. intros;apply npnsw_taustar_to_taustar in H;eapply taustar_abort_suc;eauto. Qed.
  
  Lemma npnsw_star_abort_suc:
    forall pc fp pc',
      glob_npnsw_step pc tau fp pc'->
      npnsw_star_abort pc'->
      npnsw_star_abort pc.
  Proof. unfold npnsw_star_abort;intros;Hsimpl;Esimpl;eauto;econstructor;eauto. Qed.
  Lemma npnsw_taustar_star_abort_suc:
    forall pc fp pc',
      tau_star glob_npnsw_step pc fp pc'->
      npnsw_star_abort pc'->
      npnsw_star_abort pc.
  Proof. unfold npnsw_star_abort;intros;Hsimpl. eapply tau_star_star in H0;eauto. Qed.
  Lemma npnsw_star_abort_elim:
    forall pc,
      npnsw_star_abort pc -> star_abort pc.
  Proof.
    unfold npnsw_star_abort;intros;Hsimpl. apply npnsw_taustar_to_taustar in H. apply tau_star_to_star in H as []. econstructor;eauto. Qed.

  Lemma halfatomblock_abort_elim:
    forall pc,
      halfatomblock_abort pc -> star_abort pc.
  Proof.
    unfold halfatomblock_abort;intros.
    Hsimpl. apply halfatomblockstep_star in H;Hsimpl.
    econstructor. Esimpl;eauto.
  Qed.
  
  Lemma npnswstep_star_conflict:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @glob_npnsw_step GE ({-|pc,t1}) tau fp1 pc1->
      tau_star glob_npnsw_step ({-|pc1,t2}) fp2 pc2 ->
      t1 <> t2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool) ->
      FP.conflict fp1 fp2 ->
      npnsw_star_abort ({-|pc,t2}) \/
      exists fp pc', tau_star glob_npnsw_step ({-|pc,t2}) fp pc' /\ FP.conflict fp1 fp.
  Proof.
    intros.
    assert(V0:pc_valid_tid pc t2).
    apply FP.emp_never_conflict in H4 as ?.
    destruct H5 as [_ ?].
    apply npnsw_step_thdpinv in H as ?;auto.
    eapply npnsw_star_fpnotemp_cur_valid_id in H5;try apply H0;eauto.
    assert(pc_valid_tid pc1 t2). destruct H5. split;auto.
    eapply npnswstep_pc_valid_tid_backwards_preservation in H;eauto.
    
    eapply npnsw_conflict_min_rule in H0;eauto.
    clear fp2 H4.
    destruct H0 as (fp20&fp21&pc20&pc21&star1&step1&smile1&conflict1).
    eapply npnswstep_star_reorder in smile1 as E1;eauto.
    destruct E1 as (pc1'&star1'&pc2'&step2'&memeq).
    apply npnsw_taustar_tid_preservation in star1 as Eq1.
    simpl in *.
    rewrite <- Eq1 in memeq.
    assert(exists pc22,glob_npnsw_step ({-|pc2',t2}) tau fp21 pc22).
    eapply mem_eq_npnsw_step_starN in memeq;auto.
    Focus 2.
    econstructor 2;eauto. constructor.
    destruct memeq as (pc22&step'&memeq).
    rewrite FP.fp_union_emp in step'.
    Coqlib.inv step'.
    Coqlib.inv H5.
    rewrite FP.fp_union_emp.
    eauto.
    destruct H0.
    apply FP.emp_never_conflict in conflict1 as E1.
    destruct E1.
    apply npnswstep_fpnotemp in step2';auto.
    apply npnswstep_fpnotemp in H0;auto.
    eapply corestep_conflict in conflict1;try apply step2';eauto.
    destruct conflict1 as [abort0|conflict1].
    left. unfold star_abort.
    apply npnsw_taustar_tid_preservation in star1' as eq1.
    simpl in eq1.
    rewrite eq1 in abort0. rewrite pc_cur_tid in abort0.
    unfold npnsw_star_abort.
    Esimpl;eauto.
    destruct conflict1 as (fp&pc'&?&?).
    right.
    exists (FP.union fp20 fp),pc'.
    split.
    eapply tau_star_star;eauto. apply tau_plus2star.
    apply npnsw_taustar_tid_preservation in star1'.
    simpl in star1'.
    assert( pc1' = ({-|pc1',t2})). rewrite star1'. destruct pc1';auto.
    rewrite H8;auto.
    constructor. left;auto.
    rewrite FP.union_comm_eq.
    apply conflict_union_ano;auto.

    eapply npnsw_taustar_thdpinv;eauto.
  Qed.


  Lemma globstep_reorder_rule_alter:
    forall x y t1 t2 l1 l2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE y ({-|pc,t1}) l1 fp1 pc1->
      @type_glob_step GE x ({-|pc1,t2}) l2 fp2 pc2->
      atom_bit pc = atom_bit pc1 ->
      atom_bit pc1 = atom_bit pc2->
      t1 <> t2->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      l1 <> sw->
      l2 <> sw->
      (abort ({-|pc,t2})) \/
      (exists fp pc',type_glob_step core ({-|pc,t2}) tau fp pc' /\ FP.conflict fp1 fp) \/
      (FP.smile fp1 fp2 /\ exists pc1',type_glob_step x ({-|pc,t2}) l2 fp2 pc1'/\
             exists pc2',type_glob_step y ({-|pc1',t1}) l1 fp1 pc2' /\
                    mem_eq_pc GE pc2 ({-|pc2',cur_tid pc2})).
  Proof.
    intros.
    assert(FP.smile fp1 fp2 \/ ~ FP.smile fp1 fp2).
    apply classic.
    destruct H8.
    right. right. split;try eapply globstep_reorder_rule;eauto.
    apply smile_conflict in H8.
    apply FP.emp_never_conflict in H8 as [].
    destruct x,l2;try (inversion H0;subst;try contradiction;fail).
    destruct y,l1;try (inversion H;subst;try contradiction;fail).
    eapply corestep_reorder_rule_alter2 in H3;eauto.
    assert(cur_tid pc2 = t2).
    inversion H0;auto.
    subst;auto.
  Qed.

(*  Lemma atomblock_open_reorder_globstep_alter:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      t1 <> t2->
      ThreadPool.inv pc.(thread_pool) ->
      @glob_npnsw_step GE (changepc GE pc t1 O) tau fp1 pc1->
      type_glob_step core (changepc GE pc1 t2 I) tau fp2 pc2->
      (exists fp pc',type_glob_step core (changepc GE pc t2 I) tau fp pc' /\ FP.conflict fp fp1) \/ exists pc',type_glob_step core (changepc GE pc t2 I) tau fp2 pc'.
  Proof.
    intros.
    apply glob_npnsw_step_type in H1 as [?[]].
    remember (changepc GE pc t1 O) as pc0.
    assert(pc0 = ({-|pc0,t1})). rewrite Heqpc0. destruct pc;auto.
    rewrite H4 in H1.
    assert(atom_bit pc1 = O). destruct H3 as [|[]];subst;Coqlib.inv H1;auto.
    assert(type_glob_step core ({-|pc1,t2}) tau fp2 (changepc GE pc2 t2 O)).
    destruct pc1;Coqlib.inv H2;simpl in *;subst;econstructor;eauto.
    assert(FP.smile fp1 fp2 \/ ~FP.smile fp1 fp2).
    apply classic.
    destruct H7.
    {
      eapply globstep_reorder_rule in H7;eauto.
      destruct H7 as (?&?&_).
      rewrite Heqpc0 in H7.
      right.
      exists (changepc GE x0 t2 I).
      destruct pc;Coqlib.inv H7;econstructor;eauto.

      rewrite Heqpc0;auto.
      rewrite Heqpc0;auto.
      intro L;inversion L.
      intro L;inversion L.
    }
    {
      apply smile_conflict in H7.
      apply FP.emp_never_conflict in H7 as L1.
      destruct L1.
      destruct H3 as [|[]];subst;try (inversion H1;subst;contradiction;fail).
      eapply corestep_conflict in H7;eauto.
      destruct H7 as (fp&pc'&step'&conflict').
      left. exists fp,(changepc GE pc' t2 I).
      apply FP.conflict_sym in conflict'.
      split;auto.
      destruct pc;Coqlib.inv step';econstructor;eauto.
    }
  Qed.

  Lemma atomblock_open_reorder_globstar_alter:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      t1 <> t2->
      ThreadPool.inv pc.(thread_pool) ->
      @glob_npnsw_step GE (changepc GE pc t1 O) tau fp1 pc1->
      tau_star (type_glob_step core) (changepc GE pc1 t2 I) fp2 pc2->
      (exists fp pc',tau_star (type_glob_step core) (changepc GE pc t2 I) fp pc' /\ FP.conflict fp fp1) \/ exists pc',tau_star (type_glob_step core) (changepc GE pc t2 I) fp2 pc'.
  Proof.
    intros.
    apply glob_npnsw_step_type in H1 as [?[]].
    assert(FP.smile fp1 fp2\/~FP.smile fp1 fp2).
    apply classic.
    destruct H4.
    {
      eapply atomblock_open_reorder_corestar in H4;eauto.
      destruct H4 as (?&?&_).
      right;eauto.

      destruct H3 as [|[]];subst;Coqlib.inv H1;auto.
      intro L;inversion L.
    }
    {
      apply smile_conflict in H4.
      apply FP.conflict_sym in H4.
      eapply taustar_fpconflict_split in H2;eauto.
      destruct H2 as (fp10&fp11&pc10&pc11&star1&step1&smile1&conflict1&_).
      assert(cur_tid pc10 = t2).
      revert star1;clear;intros.
      remember (changepc GE pc1 t2 I) as pc.
      assert(cur_tid pc = t2). rewrite Heqpc;auto.
      clear pc1 Heqpc.
      induction star1;auto.
      apply IHstar1.
      inversion H0;subst;auto.
      
      apply changeatombit_corestar_preserve in star1.
      simpl in *.
      assert(changepc GE (changepc GE pc1 t2 I) t2 O = changepc GE pc1 t2 O).
      auto.
      rewrite H5 in star1;clear H5.
      apply changeatombit_corestep_preserve in step1.
      rewrite H2 in *.

      assert(changepc GE pc1 t2 O = ({-|pc1,t2})).
      destruct H3 as [|[]];subst;Coqlib.inv H1;auto.
      rewrite H5 in *;clear H5.

      remember (changepc GE pc t1 O) as pc0.
      assert(pc0 = ({-|pc0,t1})). rewrite Heqpc0;auto.
      rewrite H5 in H1.
      assert(glob_npnsw_step ({-|pc0,t1}) tau fp1 pc1).
      destruct H3 as [|[]];subst;unfold glob_npnsw_step;auto.
      eapply npnswstep_corestar_reorder in H6;eauto.

      destruct H6 as (pc1'&star1'&pc2'&step2&memeq).
      simpl in memeq.
      eapply mem_eq_corestep in memeq;eauto.
      destruct memeq as (pce&step'&memeq).

      assert(glob_npnsw_step ({-|pc2',t2}) tau fp11 pce).
      left;auto.
      eapply npnswstep_conflict in conflict1 as L1;eauto.
      destruct L1 as (fp'&pc''&step''&conflict').
      left.
      exists (FP.union fp10 fp'),(changepc GE pc'' t2 I).
      split.

      apply changeatombitI_corestar_preserve in star1'.
      rewrite Heqpc0 in star1'.
      assert( (changepc GE ({-|changepc GE pc t1 O, t2})(cur_tid ({-|changepc GE pc t1 O, t2})) I) = changepc GE pc t2 I). auto.
      rewrite H7 in star1';clear H7.
      simpl in star1'.
      apply FP.emp_never_conflict in conflict' as L1.
      destruct L1.
      apply glob_npnsw_step_type in step'' as [?[]].
      destruct H10 as [|[]]; rewrite H10 in H9;try(inversion H9;subst;contradiction;fail).
      assert(tau_plus (type_glob_step core)({-|pc1',t2}) fp' pc''). constructor;auto.
      apply tau_plus2star in H11.
      apply changeatombitI_corestar_preserve in H11.
      simpl in H11.
      assert(changepc GE ({-|pc1',t2}) t2 I = changepc GE pc1' t2 I);auto.
      rewrite H12 in H11.
      eapply tau_star_star;eauto.

      rewrite FP.union_comm_eq.
      apply FP.conflict_sym in conflict'.
      eapply conflict_union in conflict';eauto.

      eapply GE_mod_wd_star_tp_inv with(pc:=({-|pc0,t2}))(fp:=fp10);eauto.
      rewrite Heqpc0;auto.
      revert star1';clear;induction 1;auto.
      constructor.
      econstructor;eauto. apply type_glob_step_elim in H;auto.

      rewrite Heqpc0;auto.
    }

  Qed.
*)
  Lemma npnsw_step_glob_predict_star_alter_cons_tideq:
    forall pc fp pc',
      @glob_npnsw_step GE pc tau fp pc'->
      forall b fp',
        glob_predict_star_alter pc' (cur_tid pc') b fp'->
        glob_predict_star_alter pc (cur_tid pc) b (FP.union fp fp').
  Proof.
    intros.
    apply npnsw_step_tid_preservation in H as eq1.
    assert(atom_bit pc = atom_bit pc').
    destruct H as [|[]];Coqlib.inv H;auto.
    assert(L1:pc' = ({-|pc',cur_tid pc'})). destruct pc';auto.
    assert(L2:pc = ({-|pc,cur_tid pc})). destruct pc;auto.
    Coqlib.inv H0.
    econstructor;eauto;try rewrite <-L1 in *;try rewrite <- L2 in *.
    eapply tau_star_star;eauto.
    apply tau_plus2star;constructor;auto.
    congruence.

    rewrite FP.fp_union_assoc.
    econstructor;eauto.
    rewrite <- L2. rewrite <- L1 in H2.
    eapply tau_star_star;eauto.
    apply tau_plus2star;constructor;auto.
    congruence.
  Qed.

  Lemma safe_state_not_abort:
    forall pc,
      safe_state glob_step abort pc <->
      ~ star_abort pc.
  Proof.
    unfold safe_state;unfold star_abort.
    split;intros;intro;Hsimpl.
    eapply H in H0;contradiction.
    contradict H;eauto.
  Qed.
  
  Lemma npnsw_step_glob_predict_star_alter_O_cons_tidneq:
    forall pc fp pc',
    forall (*H_safe: safe_state glob_step abort pc*)
      (H_safe: forall t, pc_valid_tid pc t-> ~ predicted_abort1 ({-|pc,t}))
      (H_atomO: atom_bit pc = O),
      ThreadPool.inv pc.(thread_pool) ->
      @glob_npnsw_step GE pc tau fp pc'->
      forall t fp',
        t <> cur_tid pc ->
        glob_predict_star_alter pc' t O fp'->
        glob_predict_star_alter pc t O fp' \/
        exists fp0, glob_predict_star_alter pc t O fp0 /\ FP.conflict fp0 fp.
  Proof.
    intros.
    Coqlib.inv H2.
    {
      assert(FP.smile fp fp' \/~FP.smile fp fp').
      apply classic.
      assert(pc = ({-|pc,cur_tid pc})). destruct pc;auto.
      rewrite H6 in H0.
      destruct H2.
      {        
        eapply npnswstep_star_reorder in H2;eauto.
        destruct H2 as (pc1'&star1&pc2'&step2&eq').
        left.
        assert(atom_bit pc = O).
        destruct H0 as [|[]];Coqlib.inv H0;auto.
        assert(atom_bit pc1' = O).
        apply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star1.
        apply nohalt_nptaustar in star1 as [].
        simpl in *.
        congruence.
        econstructor;eauto.
      }
      {
        apply smile_conflict in H2.
        eapply npnswstep_star_conflict in H2 as ?;try apply H0;eauto.
        destruct H7.
        apply FP.emp_never_conflict in H2 as [].
        apply npnsw_star_fpnotemp_cur_valid_id in H3 as ?;auto.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H0 as ?;eauto.
        clear H2 H8 H9.
        simpl in H10. rewrite pc_cur_tid in H10.
        assert(Step1:glob_step pc sw FP.emp ({-|pc,t})).
        destruct pc;simpl in *;subst;destruct H10;econstructor;eauto.
        (*eapply safe_succeed in H_safe;[|try eapply star_step;[eauto|constructor]].
        apply safe_state_not_abort in H_safe.*)
        eapply H_safe in H10;eauto.
        contradict H10. econstructor 2;eauto.
        eapply npnsw_step_thdpinv in H0;eauto.
        
        clear H2.
        destruct H7 as (fp0&pc''&star1&conflict1).
        apply FP.conflict_sym in conflict1.
        right;exists fp0;split;auto.
        assert(atom_bit pc = O).
        destruct H0 as [|[]];Coqlib.inv H0;auto.
        assert(atom_bit pc'' = O).
        apply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star1.
        apply nohalt_nptaustar in star1 as [].
        simpl in *.
        congruence.
        econstructor;eauto.
      }
    }
  Qed.

  Lemma corestep_I_conflict:
    forall pc fp pc',
      invpc GE pc->
      type_glob_step core pc tau fp pc'->
      forall t pc1 fp' pc2,
        type_glob_step entat ({-|pc',t}) tau FP.emp pc1->
        tau_star (type_glob_step core) pc1 fp' pc2 ->
        FP.conflict fp fp'->
        cur_tid pc' <> t->
        (halfatomblock_abort ({-|pc,t})) \/
        exists pc1' fp1' pc2',
          type_glob_step entat ({-|pc, t}) tau FP.emp pc1' /\
          tau_star (type_glob_step core) pc1' fp1' pc2' /\
          FP.conflict fp fp1'.
  Proof.
    intros.
    apply type_glob_step_elim in H0 as R1.
    eapply GE_mod_wd_tp_inv in R1;eauto.
    assert(pc_valid_tid pc' t).
    inversion H1;subst. split.
    eapply gettop_valid_tid;eauto.
    intro;solv_thread.

    assert(glob_npnsw_step pc tau fp pc'). left;auto.
    eapply npnswstep_pc_valid_tid_backwards_preservation in H6;eauto.
    clear H5.
    assert(atom_bit pc' = O).
    inversion H1;auto.
    assert(swstep:glob_step pc sw FP.emp ({-|pc,t})).
    inversion H0;subst;simpl in *;subst;destruct H6;econstructor;eauto.
    apply FP.conflict_sym in H3.
    eapply taustar_fpconflict_split in H2 as ?;eauto.
    Hsimpl.
    clear H2 H3 H5 H6 H11 H12.

    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    eapply atomblock_open_reorderstep1 in H1 as ?;try apply H0;try(inversion H0;subst;auto;fail);try(intro contra;inversion contra;fail).

    Hsimpl.

    assert(mem_eq_pc GE pc1 (changepc GE x4 t I)).
    unfold mem_eq_pc. split;auto. split;auto. inversion H1;subst;auto.
    split. inversion H1;subst;auto.
    rewrite <- H6. apply GMem.eq'_refl.

    eapply mem_eq_corestar in H11;try apply H7;eauto;Hsimpl.
    eapply mem_eq_corestep in H12;try apply H8;eauto;Hsimpl.

    clear H13.
    assert(cur_tid pc <> t). inversion H0;subst;auto.
    assert(invpc GE x3). apply type_glob_step_elim in H2. apply GE_mod_wd_tp_inv in H2;auto.
    eapply atomblock_open_reorder_corestar in H11 as ?;eauto;try(intro contra;inversion contra;fail);try(inversion H3;subst;auto;fail);Hsimpl.

    assert(mem_eq_pc GE x5 (changepc GE x8 t I)).
    split;auto.
    apply corestar_tid_bit_preserve in H11 as [].
    split;auto. split;auto. simpl. apply GMem.eq'_sym;auto.

    eapply mem_eq_corestep in H19;eauto;Hsimpl.

    assert(changepc GE x3 t I = x3).
    inversion H2;subst;auto.
    rewrite H21 in H15.

    apply corestep_changebit with(x:=I) in H16.
    rewrite changepc_again in H16.
    simpl in H16.

    assert(changepc GE x7 (cur_tid pc) I = ({-|x7,cur_tid pc})).
    apply corestar_tid_bit_preserve in H15 as [].
    unfold changepc in H21. destruct x3;simpl in *;subst;inversion H21;subst;auto.

    rewrite H22 in H16.
    assert(changepc GE x8 t I = ({-|changepc GE x8 (cur_tid pc) I, t})).
    auto.
    rewrite H23 in H19.

    eapply corestep_conflict in H19 as ?;try apply H16;eauto.
    apply corestar_tid_bit_preserve in H15 as ?. destruct H25.
    assert(cur_tid x3 = t). destruct x3;simpl in *;subst;inversion H21;auto.
    rewrite <- H27,H25,pc_cur_tid in H24.
    destruct H24.
    left.

    unfold halfatomblock_abort.
    unfold halfatomblockstep.
    
    Esimpl;eauto.

    Hsimpl.
    right.
    apply tau_plus_1 in H24. apply tau_plus2star in H24.
    eapply tau_star_star in H24;eauto.
    Esimpl;eauto.
    rewrite FP.union_comm_eq.
    eapply conflict_union_ano;eauto.

    apply corestar_globstar in H15.
    eapply GE_mod_wd_star_tp_inv;eauto.
  Qed.


  Lemma npnsw_step_glob_predict_star_alter_I_cons_tidneq:
    forall pc fp pc',
    forall (*H_safe: safe_state glob_step abort pc*)
      (H_safe: forall t, pc_valid_tid pc t-> ~ predicted_abort1 ({-|pc,t})),
      ThreadPool.inv pc.(thread_pool) ->
      @glob_npnsw_step GE pc tau fp pc'->
      forall t fp',
        t <> cur_tid pc ->
        glob_predict_star_alter pc' t I fp'->
        glob_predict_star_alter pc t I fp' \/
        exists fp0 b, glob_predict_star_alter pc t b fp0 /\ FP.conflict fp0 fp.
  Proof.
    intros.
    Coqlib.inv H2.
    assert(FP.smile fp(FP.union fp1 fp2) \/ ~ FP.smile fp (FP.union fp1 fp2)).
    apply classic.
    destruct H2.
    {
      assert(FP.smile fp fp1). eapply fpsmile_subset;eauto. apply FP.union_subset.
      assert(FP.smile fp fp2). rewrite FP.union_comm_eq in H2. eapply fpsmile_subset in H2;eauto. apply FP.union_subset.
      assert(pc = ({-|pc,cur_tid pc})). destruct pc;auto.
      rewrite H9 in H0.
      eapply npnswstep_star_reorder in H7 as L1;eauto.
      destruct L1 as (pc1'&star1&pc2'&step1&memeq).

      assert(cur_tid pc1 = t).
      revert H3;clear;intros.
      remember ({-|pc',t}) as pc.
      assert(cur_tid pc = t). rewrite Heqpc;auto.
      clear pc' Heqpc.
      induction H3;auto.
      apply IHtau_star.
      destruct H0 as [|[]];Coqlib.inv H0;auto.

      rewrite H10 in *.
      eapply mem_eq_globstep in memeq;eauto.
      destruct memeq as (pc3'&step2&memeq).
      eapply mem_eq_corestar in memeq;eauto.
      destruct memeq as (pc4'&star2&_).

      apply glob_npnsw_step_type in step1 as [x[step' type']].
      eapply atomblock_open_reorderstep1 in step' as E1;eauto.
      destruct E1 as [pc10[entstep[pc20[step3[thdpeq gmeq]]]]].

      assert(mem_eq_pc GE pc3' (changepc GE pc20 t I)).
      unfold mem_eq_pc.
      repeat match goal with H:_|-_/\_ => split end;simpl;auto.
      Coqlib.inv step2;auto.
      Coqlib.inv step2;auto.
      rewrite gmeq; apply GMem.eq'_refl.

      eapply mem_eq_corestar in H11 as [pce[star3 memeq]];eauto.
      assert(step3alt:glob_npnsw_step (changepc GE pc10 (cur_tid pc) O) tau fp pc20).
      unfold glob_npnsw_step. destruct type' as [|[]];subst;auto.
      remember (changepc GE pc10 (cur_tid pc) O) as pc10'.
      assert(pc10'=({-|pc10',cur_tid pc})). rewrite Heqpc10';auto.
      rewrite H11 in step3alt.
      apply changeatombit_corestar_preserve in star3 as star3'.
      simpl in star3'.
      
      assert(changepc GE (changepc GE pc20 t I) t O = ({-|pc20,t})).
      unfold changepc;simpl.
      destruct pc20;simpl.
      assert(atom_bit = O).
      destruct type' as [|[]];subst;Coqlib.inv step3;auto.
      congruence.
      rewrite H12 in star3'.
      eapply npnswstep_corestar_reorder in star3';eauto.
      destruct star3' as [pc11[star3' _]].
      rewrite Heqpc10' in star3'.
      apply changeatombitI_corestar_preserve in star3'.
      simpl in star3'.
      assert(  (changepc GE ({thread_pool pc10, t, gm pc10, O}) t I) = pc10).
      unfold changepc.
      simpl.
      destruct pc10;f_equal;Coqlib.inv entstep;auto.
      rewrite H13 in star3';clear H13.
      apply npnsw_taustar_tid_preservation in star1 as L1.
      simpl in L1.
      assert(({-|pc1',t}) = pc1').
      destruct pc1';subst;auto.
      rewrite H13 in *.
      left.
      econstructor;eauto.

      destruct H0 as [|[]];Coqlib.inv H0;auto.
      rewrite Heqpc10';simpl.
      apply type_glob_step_elim in entstep.
      eapply GE_mod_wd_tp_inv in entstep;eauto.
      simpl.
      eapply npnsw_taustar_thdpinv;eauto.
      destruct type' as [|[]];subst;Coqlib.inv step';auto.
      intro L;inversion L.
    }
    {
      apply smile_conflict in H2.
      apply fpconflict_union in H2.
      assert(FP.conflict fp fp1 \/ ~ FP.conflict fp fp1).
      apply classic.
      destruct H7.
      {
        assert(O1:atom_bit pc = O).
        destruct H0 as [|[]];Coqlib.inv H0;auto.
        rewrite <- pc_cur_tid with(pc:=pc) in H0.
        eapply npnswstep_star_conflict in H7;eauto.
        destruct H7.
        apply npnsw_step_thdpinv in H0 as ?;auto.
        apply npnsw_taustar_thdpinv in H3 as ?;auto.
        apply type_glob_step_cur_valid_id in H5;auto;[|intro contra;inversion contra].
        eapply npnsw_taustar_pc_valid_tid_backwards_preservation in H5;eauto.
        apply npnsw_taustar_tid_preservation in H3.
        rewrite <- H3 in H5;simpl in *.
        assert(pc_valid_tid pc' t).
        destruct H5. split;auto.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H0;eauto.
        rewrite pc_cur_tid in H0.
        specialize (H_safe t H0).
        contradict H_safe.
        econstructor 2;eauto. instantiate(1:=pc). destruct pc,H0;simpl in *;subst;econstructor;eauto.
        
        destruct H7 as (fp1'&pc1'&star1&conflict1).
        right. exists fp1',O. split;[econstructor|apply FP.conflict_sym];eauto.
        eapply npnsw_taustar_O_preservation;eauto.
      }
      {
        destruct H2;[contradiction|].
        
        assert(pc = ({-|pc,cur_tid pc})). destruct pc;auto.
        rewrite H8 in H0.
        assert(O1:atom_bit pc = O).
        destruct H0 as [|[]];Coqlib.inv H0;auto.
        apply FP.smile_conflict_compat in H7.
        eapply npnswstep_star_reorder in H7 as L1;eauto.
        destruct L1 as (pc1'&star1'&pc2'&step1'&memeq').
        eapply mem_eq_globstep in H5 as L1;eauto.
        destruct L1 as (pc3'&entstep&memeq2).
        eapply mem_eq_corestar in H6 as L2;eauto.
        destruct L2 as (pc4'&star2'&memeq3).

        assert(cur_tid pc1 = t).
        apply npnsw_taustar_tid_preservation in H3;auto.
        
        apply glob_npnsw_step_type in step1' as L3.
        destruct L3 as (x&step1''&type').
        apply FP.emp_never_conflict in H2 as ?.
        destruct H10.
        destruct type' as [|[]];subst;try(inversion step1'';subst;contradiction).
        
        eapply corestep_I_conflict in step1'' as ?;eauto.
        simpl in H9.
        destruct H9.
        {
          revert wdge' O1 star1' H9 H_safe H H1 step1';clear;intros.
          
          apply npnsw_taustar_thdpinv in star1' as inv1;auto.
          apply npnsw_step_cur_valid_id in step1' as v1;auto.
          apply npnsw_taustar_O_preservation in star1' as O2;auto.
          assert(glob_step pc1' sw FP.emp ({-|pc1',cur_tid pc})).
          destruct pc1',v1;simpl in *;subst;econstructor;eauto.
          inversion star1';subst.
          {
            simpl in *.
            
            eapply halfatomblockabort_sw with(t:=cur_tid pc) in H9 as ? ;eauto.
            assert(pc_valid_tid pc (cur_tid pc1)). inversion H2;subst;split;auto.
            specialize (H_safe (cur_tid pc1) H3).
            contradict H_safe.
            econstructor ;eauto.
          }
          {
            apply npnsw_step_cur_valid_id in H2 as v2;auto.
            assert(glob_step pc sw FP.emp ({-|pc,cur_tid pc1})).
            destruct pc,v2;simpl in *;subst;econstructor;eauto.

            specialize (H_safe (cur_tid pc1) v2).
            contradict H_safe.
            apply npnsw_taustar_tid_preservation in star1' as ?. simpl in H5.
            rewrite H5,pc_cur_tid in H9.
            econstructor;eauto.
          }
        }
        {
          Hsimpl.
          assert(cur_tid pc1' = cur_tid pc1).
          apply npnsw_taustar_tid_preservation in star1';auto.
          rewrite <- H14,pc_cur_tid in H9.
          right.
          exists (FP.union fp1 x0),I.
          split.
          econstructor;eauto.
          rewrite FP.union_comm_eq.
          apply conflict_union.
          apply FP.conflict_sym;auto.
        }
        apply npnsw_taustar_thdpinv in star1';auto.
        inversion step1'';subst;auto.
      }
    }
  Qed.
  Lemma npnsw_step_race_glob_predict_star_alter_cons:
    forall pc fp pc'
      (H_safe: forall t, pc_valid_tid pc t-> ~ predicted_abort1 ({-|pc,t})),
      (*H_safe: safe_state glob_step abort pc*)
      ThreadPool.inv pc.(thread_pool)->
      @glob_npnsw_step GE pc tau fp pc'->
      race glob_predict_star_alter pc'->
      race glob_predict_star_alter pc.
  Proof.
    intros.
    inversion H1;clear H1;subst.
    assert(cur_tid pc' = t1 \/ cur_tid pc' <> t1).
    apply classic.
    destruct H1.
    {
      subst.
      eapply npnsw_step_glob_predict_star_alter_cons_tideq in H0 as L1;eauto.
      apply npnsw_step_tid_preservation in H0 as L0.
      destruct b2.
      {
        eapply npnsw_step_glob_predict_star_alter_O_cons_tidneq in H4;eauto.
        destruct H4.
        eapply conflict_union with(fp3:=fp) in H6.
        rewrite FP.union_comm_eq in H6.
        econstructor;eauto;try congruence.
        destruct H1 as (fp'&?&?).
        apply conflict_union_ano with(fp3:=fp1) in H4.
        apply FP.conflict_sym in H4.
        econstructor;eauto;try congruence.
        assert(atom_bit pc' = O). inversion H4;auto.
        inversion H0 as [|[]];inversion H7;subst;auto.
        rewrite L0;auto.
      }
      {
        eapply npnsw_step_glob_predict_star_alter_I_cons_tidneq in H4;eauto.
        destruct H4.
        eapply conflict_union with(fp3:=fp) in H6.
        rewrite FP.union_comm_eq in H6.
        econstructor;eauto;try congruence.
        destruct H1 as (fp'&b'&?&?).
        apply conflict_union_ano with(fp3:=fp1) in H4.
        apply FP.conflict_sym in H4.
        rewrite L0 in L1.
        econstructor;eauto.
        destruct H5;try contradiction;auto.
        rewrite L0;auto.
      }
    }

    assert(cur_tid pc' = t2 \/ cur_tid pc' <> t2).
    apply classic.
    destruct H7.
    {
      subst.
      eapply npnsw_step_glob_predict_star_alter_cons_tideq in H0 as L1;eauto.
      apply npnsw_step_tid_preservation in H0 as L0.
      destruct b1.
      {
        eapply npnsw_step_glob_predict_star_alter_O_cons_tidneq in H3;eauto.
        destruct H3.
        eapply conflict_union_ano with(fp3:=fp) in H6.
        rewrite FP.union_comm_eq in H6.
        apply FP.conflict_sym in H6.
        rewrite L0 in L1.
        econstructor;eauto;try congruence.
        destruct H5;auto.
        destruct H3 as (fp'&?&?).
        apply conflict_union_ano with(fp3:=fp2) in H7.
        apply FP.conflict_sym in H7.
        rewrite L0 in L1;auto.
        econstructor;eauto;try congruence.
        destruct H5;auto.
        assert(atom_bit pc' = O). inversion H4;auto.
        inversion H0 as [|[]];inversion H8;subst;auto.
        rewrite L0;auto.
      }
      {
        rewrite L0 in L1.
        eapply npnsw_step_glob_predict_star_alter_I_cons_tidneq in H3;eauto.
        destruct H3.
        eapply conflict_union_ano with(fp3:=fp) in H6.
        rewrite FP.union_comm_eq in H6.
        apply FP.conflict_sym in H6.
        econstructor;eauto;try congruence.
        destruct H5;auto.
        destruct H3 as (fp'&b'&?&?).
        apply conflict_union_ano with(fp3:=fp2) in H7.
        apply FP.conflict_sym in H7.
        econstructor;eauto.
        destruct H5;try contradiction;auto.
        rewrite L0;auto.
      }
    }


    apply npnsw_step_tid_preservation in H0 as Eq0.
    destruct b1.
    {
      eapply npnsw_step_glob_predict_star_alter_O_cons_tidneq in H0 as L1;eauto.
      destruct L1.
      destruct b2.
      eapply npnsw_step_glob_predict_star_alter_O_cons_tidneq in H0 as L2;eauto.
      destruct L2.
      econstructor 1 with(t1:=t1)(t2:=t2);eauto.

      destruct H9 as (fp0&p1&conflict1).
      apply FP.conflict_sym in H6.
      econstructor 1 with(t1:=cur_tid pc')(t2:=t2);eauto.
      rewrite <-Eq0.
      econstructor;eauto. apply tau_plus2star;constructor.
      assert(({-|pc,cur_tid pc}) = pc).
      destruct pc;auto.
      rewrite H9;eauto.
      Coqlib.inv H8;auto.
      Coqlib.inv H3;auto.
      apply FP.conflict_sym;auto.
      assert(atom_bit pc' = O). inversion H4;auto.
      inversion H0 as [|[]];inversion H10;subst;auto.
      rewrite Eq0;auto.

      eapply npnsw_step_glob_predict_star_alter_I_cons_tidneq in H4;eauto.
      destruct H4.
      econstructor 1 with(t1:=t1)(t2:=t2);eauto.
      destruct H4 as (fp0&b0&p0&c0).
      econstructor 1 with(t1:=cur_tid pc')(t2:=t2);eauto.
      rewrite <-Eq0.
      econstructor;eauto. apply tau_plus2star;constructor.
      assert(({-|pc,cur_tid pc}) = pc). destruct pc;auto.
      rewrite H4;eauto.
      Coqlib.inv H8;auto.
      Coqlib.inv H3;auto.
      destruct H5;try contradiction;auto.
      apply FP.conflict_sym;auto.
      rewrite Eq0;auto.

      destruct H8 as (fp0&p0&c0).
      econstructor 1 with(t1:=cur_tid pc')(t2:=t1);eauto.
      rewrite <- Eq0. econstructor;eauto. apply tau_plus2star;constructor.
      assert(({-|pc,cur_tid pc}) = pc). destruct pc;auto.
      rewrite H8;eauto.
      Coqlib.inv p0;auto.
      Coqlib.inv H3;auto.
      left;intro L;inversion L.
      apply FP.conflict_sym;auto.

      assert(atom_bit pc' = O). inversion H4;auto.
      inversion H0 as [|[]];inversion H9;subst;auto.
      rewrite Eq0;auto.
    }
    {
      assert(Eq1:({-|pc,cur_tid pc}) = pc). destruct pc;auto.
      destruct H5,b2;try contradiction.
      eapply npnsw_step_glob_predict_star_alter_I_cons_tidneq in H0 as L1;eauto.
      eapply npnsw_step_glob_predict_star_alter_O_cons_tidneq in H0 as L2;eauto.
      destruct L1.
      destruct L2.
      econstructor 1 with(t1:=t1)(t2:=t2);eauto.
      destruct H9 as (?&?&?).
      econstructor 1 with(t1:=cur_tid pc')(t2:=t2);eauto.
      rewrite <- Eq0. econstructor;eauto. apply tau_plus2star;constructor.
      rewrite Eq1;eauto.
      Coqlib.inv H9;auto.
      Coqlib.inv H4;auto.
      apply FP.conflict_sym;auto.

      destruct H8 as (?&?&?&?).
      econstructor 1 with(t1:=cur_tid pc')(t2:=t1);eauto.
      rewrite <- Eq0;econstructor;eauto.
      apply tau_plus2star;constructor;rewrite Eq1;eauto.
      Coqlib.inv H8;auto.
      Coqlib.inv H3;auto.
      apply FP.conflict_sym;auto.

      assert(atom_bit pc' = O). inversion H4;auto.
      inversion H0 as [|[]];inversion H9;subst;auto.

      rewrite Eq0;auto.
      rewrite Eq0;auto.
    }
  Qed.
  
  Lemma npnsw_step_race_glob_predict_star_alter_cons_2:
    forall pc fp pc',
      ThreadPool.inv pc.(thread_pool)->
      @glob_npnsw_step GE pc tau fp pc'->
      race glob_predict_star_alter pc'->
      (exists t, pc_valid_tid pc t /\ predicted_abort1 ({-|pc,t})) \/
      race glob_predict_star_alter pc.
  Proof.
    intros.
    assert((forall t, pc_valid_tid pc t-> ~ predicted_abort1 ({-|pc,t})) \/ ~(forall t, pc_valid_tid pc t-> ~ predicted_abort1 ({-|pc,t}))).
    apply classic.
    destruct H2. right. eapply npnsw_step_race_glob_predict_star_alter_cons;eauto.
    left.
    eapply not_all_not_ex;eauto.
    intro. contradict H2.
    intros.
    specialize (H3 t). intro.
    contradict H3. split;auto.
  Qed.

  
  Lemma swstep_glob_predict_star_alter_preserve:
    forall pc pc',
      @type_glob_step GE glob_sw pc sw FP.emp pc'->
      forall t b fp,
        glob_predict_star_alter pc' t b fp ->
        glob_predict_star_alter pc t b fp.
  Proof.
    intros.
    assert(pc' = ({-|pc,cur_tid pc'})).
    inversion H;auto.
    rewrite H1 in H0.
    Coqlib.inv H0;econstructor;eauto.
  Qed.

  Lemma swstep_race_glob_predict_star_alter_cons:
    forall pc  pc',
      @type_glob_step GE glob_sw pc sw FP.emp pc'->
      race glob_predict_star_alter pc'->
      race glob_predict_star_alter pc.
  Proof.
    inversion 2;subst.
    eapply swstep_glob_predict_star_alter_preserve in H2;eauto.
    eapply swstep_glob_predict_star_alter_preserve in H3;eauto.
    econstructor;eauto.
  Qed.
  Lemma mem_eq_abort:
    forall ge pc pc',
      (forall ix,mod_wd (GlobEnv.modules ge ix))->
      mem_eq_pc ge pc pc'->
      abort pc'->
      abort pc.
  Proof.
    unfold abort;destruct 3;split.
    inversion H0 as (?&?&?&?). congruence.
    intros.
    apply type_glob_step_exists in H3 as [].
    eapply mem_eq_globstep in H3;eauto;Hsimpl.
    apply type_glob_step_elim in H3.
    eauto.
  Qed.

  Definition bitC:Bit->@ProgConfig GE->@ProgConfig GE:=
    fun b pc=> changepc GE pc (cur_tid pc) b.

  Inductive onesteprace (pc:@ProgConfig GE)(t':tid)(fp:FP.t):Prop:=
  |mkrace:
     forall pc' pc'' fp',
       type_glob_step core ({-|pc,cur_tid pc}) tau fp pc'->
       type_glob_step core ({-|pc,t'}) tau fp' pc''->
       FP.conflict fp fp'->
       cur_tid pc <> t'->
       atom_bit pc = O->
       onesteprace pc t' fp.
  Lemma onesteprace_race_glob_predict:
    forall pc t fp,
      onesteprace pc t fp-> race glob_predict pc.
  Proof.
    inversion 1;subst.
    econstructor;eauto. econstructor;eauto. econstructor;eauto.
    left;intro R;inversion R.
  Qed.

  Lemma corestep_abort_lemma:
    forall pc fp pc' t,
      ThreadPool.inv pc.(thread_pool)->
      @type_glob_step GE core pc tau fp pc'->
      cur_tid pc <> t->
      abort ({-|pc',t}) ->
      abort ({-|pc,t}) \/ (exists fp2 pc2, type_glob_step core ({-|pc,t}) tau fp2 pc2 /\ FP.conflict fp fp2).
  Proof.
    unfold abort;intros;Hsimpl.
    apply NNPP. intro.

    apply not_or_and in H4 as [].
    apply not_and_or in H4.
    destruct H4.
    apply NNPP in H4.
    contradict H2. inversion H4;subst. inversion H0;subst.
    solv_thread. econstructor;eauto. solv_thread. solv_thread.

    contradict H4. intros.
    apply type_glob_step_exists in H4;Hsimpl.
    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    assert(FP.conflict fp fp0 \/ ~FP.conflict fp fp0).
    apply classic.
    destruct H6.
    apply FP.emp_never_conflict in H6 as ?. destruct H7.
    destruct x;try(inversion H4;subst;contradiction).
    assert(gl = tau). inversion H4;subst;auto. subst.
    contradict H5. Esimpl;eauto.

    apply FP.smile_conflict_compat in H6.
    apply NNPP;intro.
    eapply predict_step_ex in H6 as ?;eauto;Hsimpl.
    eapply type_glob_step_elim in H8.
    apply H3 in H8. contradiction.
  Qed.
     

  Lemma npnswstep_abort:
    forall pc fp pc' x t
      (Hx:x = core \/ x = call \/ x = ret)
      (Hinv:ThreadPool.inv pc.(thread_pool)),
      @type_glob_step GE x pc tau fp pc'->
      ~ onesteprace pc t fp->
      atom_bit pc = O->
      cur_tid pc <> t->
      abort ({-|pc',t}) ->
      abort ({-|pc,t}).
  Proof.
    unfold abort;intros;Hsimpl.

    split. intro. contradict H3. destruct Hx as [|[]];subst;inversion H;subst;inversion H5;subst;econstructor;solv_thread;solv_thread;solv_thread.

    intros.
    apply type_glob_step_exists in H5;Hsimpl.
    rewrite <- pc_cur_tid with(pc:=pc) in H.
    apply NNPP.
    intro.
    assert(FP.smile fp fp0).
    apply NNPP;intro. apply smile_conflict in H7.
    contradict H0.
    apply FP.emp_never_conflict in H7 as ?;Hsimpl.
    destruct x0;subst;try (inversion H5;subst;contradiction).
    destruct Hx as [|[]];subst;try(inversion H;subst;contradiction).
    assert(gl = tau). inversion H5;auto. subst.
    econstructor;try apply H7;eauto. 

    eapply predict_step_ex in H7 as ?;eauto;Hsimpl.
    eapply type_glob_step_elim in H8.
    apply H4 in H8. contradiction.
  Qed.

  Lemma npnswstep_abort_alt:
    forall pc fp pc',
      @glob_npnsw_step GE pc tau fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = O->
      forall t,
        cur_tid pc <> t->
        abort ({-|pc',t}) ->
        abort ({-|pc,t}) \/ onesteprace pc t fp.
  Proof.
    intros.
    apply npnswstep_l1 in H;Hsimpl.
    assert(onesteprace pc t fp\/ ~ onesteprace pc t fp).
    apply classic. destruct H5;auto.
    eapply npnswstep_abort in H5;eauto.
  Qed.

    

  Lemma npnsw_step_cons_star_abort:
    forall j pc fp pc' t fp' pc'',
      @glob_npnsw_step GE pc tau fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = O->
      cur_tid pc <> t->
      pc_valid_tid pc t->
      tau_N glob_npnsw_step j ({-|pc',t}) fp' pc''->
      abort pc''->
      (exists k pc1 fp1, tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1 /\ abort pc1 /\ k<= j /\ FP.subset fp1 fp') \/
      (exists k pc1 fp1, tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1 /\ FP.conflict fp fp1 /\
                    k<= S j).
  Proof.
    induction j using(well_founded_induction lt_wf).
    intros.
    destruct j.
    {
      (*j=0*)
      inversion H5;subst;clear H5.
      eapply npnswstep_abort_alt in H0;eauto.
      destruct H0.
      + left. exists 0;Esimpl;eauto. constructor. apply FP.subset_emp.
      + right. inversion H0;subst. exists 1;Esimpl;eauto.
        apply npnswstep_l3 in H7;auto. rewrite <- FP.fp_union_emp with(fp:=fp').
        econstructor 2;eauto. constructor.
    }
    {
      (*j+1*)
      inversion H5;subst;clear H5.
      assert(FP.conflict fp fp0 \/ ~FP.conflict fp fp0). apply classic.
      destruct H5.
      + rewrite <- pc_cur_tid with(pc:=pc) in H0.
        eapply npnswstep_conflict in H8;eauto.
        destruct H8.
        - left. exists 0;Esimpl;eauto. constructor. Lia.lia. apply FP.subset_emp.
        - Hsimpl. right. exists 1;Esimpl;eauto.
          rewrite <- FP.fp_union_emp with(fp:=x).
          econstructor 2;eauto. constructor. Lia.lia.
      + apply FP.smile_conflict_compat in H5.
        rewrite <- pc_cur_tid with(pc:=pc) in H0.
        eapply npnswstep_reorder in H8 as ?;eauto.
        Hsimpl.
        eapply mem_eq_npnsw_step_starN in H11;eauto;Hsimpl.
        apply mem_eq_pc_sym in H12.
        eapply mem_eq_abort in H12;eauto.
        apply npnsw_step_tid_preservation in H8 as ?.
        simpl in H13;subst.
        eapply H in H11 as ?;eauto.
        simpl in H13;destruct H13;Hsimpl.
        - apply npnsw_step_tid_preservation in H7 as ?.
          simpl in H17. rewrite H17,pc_cur_tid in H13.
          eapply tau_N_S in H13 as ?;eauto.
          left. Esimpl;try apply H18;eauto. Lia.lia.
          do 2 rewrite FP.union_comm_eq with(fp1:=fp0).
          apply FP.union2_subset;auto.
        - apply npnsw_step_tid_preservation in H7 as ?.
          simpl in H16. rewrite H16,pc_cur_tid in H13.
          eapply tau_N_S in H13 as ?;eauto.
          right. Esimpl;try apply H17;eauto.
          rewrite FP.union_comm_eq.
          apply conflict_union_ano;auto.
          Lia.lia.

        simpl. apply npnsw_step_thdpinv in H7;auto.
        apply npnswstep_l2 in H7;auto. simpl in *. congruence.
        eapply npnsw_step_pc_valid_tid_preservation in H7;eauto.
    }
  Qed.

  Lemma empsmile:forall fp, FP.smile FP.emp fp.
  Proof. intro;apply NNPP;intro;apply smile_conflict in H; apply FP.emp_never_conflict in H as [];contradiction. Qed.
  Lemma tau_N_conflict_split:
    forall (State:Type) (Step:State->glabel->FP.t->State->Prop) i pc fp pc' fp0,
      tau_N Step i pc fp pc'->
      FP.conflict fp fp0->
      exists j fp1 fp2 pc1 pc2,
        tau_N Step j pc fp1 pc1/\ j<i /\
        Step pc1 tau fp2 pc2 /\
        FP.smile fp0 fp1 /\FP.conflict fp0 fp2 /\
        FP.subset (FP.union fp1 fp2) fp.
  Proof.
    induction i;intros.
    inversion H;subst;clear H.
    apply FP.emp_never_conflict in H0 as [];contradiction.

    inversion H;subst.
    assert(FP.smile fp1 fp0 \/ ~ FP.smile fp1 fp0).
    apply classic. destruct H1.

    apply FP.conflict_sym in H0. apply fpsmile_sym in H1.
    eapply fpconflict_dif_trans in H0;eauto.
    apply FP.conflict_sym in H0. eapply IHi in H3 as ?;eauto.
    Hsimpl. exists (S x). Esimpl.
    econstructor 2;eauto. Lia.lia.
    eauto.
    apply fpsmile_sym.
    eapply fpsmile_union;apply fpsmile_sym;auto. auto.
    rewrite<- FP.fp_union_assoc.
    eapply FP.subset_parallel_union;eauto.
    apply FP.subset_refl.

    apply smile_conflict in H1.
    exists 0;Esimpl;eauto. constructor. Lia.lia.
    apply fpsmile_sym;apply empsmile.
    apply FP.conflict_sym;auto.
    rewrite FP.union_comm_eq.
    eapply FP.subset_parallel_union;eauto.
    apply FP.subset_refl. apply FP.subset_emp.
  Qed.

  Lemma npnswstep_tauN_reorder:
    forall j pc fp pc' t fp' pc'',
      ThreadPool.inv pc.(thread_pool)->
      @glob_npnsw_step GE pc tau fp pc'->
      cur_tid pc <> t->
      tau_N glob_npnsw_step j ({-|pc',t}) fp' pc''->
      FP.smile fp fp'->
      (exists pc1 pc2, tau_N glob_npnsw_step j ({-|pc,t}) fp' pc1/\
                  glob_npnsw_step ({-|pc1,cur_tid pc}) tau fp pc2/\
                  mem_eq_pc GE pc'' ({-|pc2,t})).
  Proof.
    induction j;intros.
    inversion H2;subst. Esimpl;eauto. constructor.
    simpl. rewrite pc_cur_tid. eauto. apply mem_eq_pc_refl.

    inversion H2;subst.
    apply fpsmile_union_elim in H3 as ?.
    apply fpsmile_union_elim2 in H3 as ?.
    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    simpl in *.
    eapply npnswstep_reorder in  H5 as ?;eauto.
    Hsimpl.
    
    eapply mem_eq_npnsw_step_starN in H10;eauto;Hsimpl.
    eapply IHj in H10;try apply H9;eauto.
    Hsimpl.
    simpl in *.
    assert(cur_tid s' = cur_tid x).
    apply npnsw_step_tid_preservation in H5.
    apply npnsw_step_tid_preservation in H8.
    simpl in *;congruence.
    rewrite H14,pc_cur_tid in H10.
    eapply tau_N_S in H10;eauto.
    Esimpl;eauto.
    eapply mem_eq_pc_trans;eauto.
    assert(cur_tid s' =t ). apply npnsw_step_tid_preservation in H5;auto.
    congruence.

    simpl. apply npnsw_step_thdpinv in H8;auto.
    simpl. apply npnsw_step_tid_preservation in H5;auto. simpl in *. congruence.
  Qed.
  Lemma npnswstep_tauN_conflict:
    forall j pc fp pc' t fp' pc'',
      ThreadPool.inv pc.(thread_pool)->
      @glob_npnsw_step GE pc tau fp pc'->
      cur_tid pc <> t->
      tau_N glob_npnsw_step j ({-|pc',t}) fp' pc''->
      FP.conflict fp fp'->
      (exists k pc1 fp1, tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1 /\ abort pc1 /\ k< j /\ FP.subset fp1 fp') \/
      (exists k pc1 fp1, tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1 /\ FP.conflict fp fp1/\ k<= j).
  Proof.
    induction j as [j IHj] using(well_founded_induction lt_wf);intros.
    destruct j.
    inversion H2;subst. contradict H3. apply FP.smile_conflict_compat;apply fpsmile_sym;apply empsmile.
    inversion H2;subst.
    assert(FP.conflict fp fp0 \/ ~ FP.conflict fp fp0).
    apply classic. destruct H4.
    {
      rewrite <- pc_cur_tid with(pc:=pc) in H0.
      eapply npnswstep_conflict in H5 as ?;eauto.
      destruct H7.
      left. exists 0;Esimpl;eauto. constructor. Lia.lia. apply FP.subset_emp.
      Hsimpl. right. exists 1;Esimpl;eauto. rewrite <- FP.fp_union_emp with(fp:=x); econstructor 2;[eauto|constructor]. Lia.lia.
    }
    {
      rewrite <- pc_cur_tid with(pc:=pc) in H0.
      apply FP.smile_conflict_compat in H4.
      eapply fpconflict_dif_trans in H3 as ?;eauto.
      eapply npnswstep_reorder in H5 as ?;eauto;Hsimpl.
      eapply mem_eq_npnsw_step_starN in H10;eauto;Hsimpl.

      assert(R1:cur_tid s' =t). apply npnsw_step_tid_preservation in H5. auto.
      assert(R2:cur_tid x = t). apply npnsw_step_tid_preservation in H8;auto.
      eapply IHj in H10;try apply H9;eauto.
      simpl in H10;destruct H10;Hsimpl;rewrite R1, <- R2,pc_cur_tid in H10.
      {
        eapply tau_N_S in H10;eauto.
        left. Esimpl;eauto. Lia.lia.
        apply FP.subset_parallel_union;[apply FP.subset_refl|];auto.
      }
      {
        eapply tau_N_S in H10;eauto.
        right. Esimpl;eauto.
        rewrite FP.union_comm_eq; apply conflict_union_ano;auto.
        Lia.lia.
      }
      apply npnsw_step_thdpinv in H8;auto.
      simpl. congruence.
    }
  Qed.
      
      
      
  
  Lemma npnsw_star_cons_star_abort:
    forall i j pc fp pc' t fp' pc'',
      tau_N glob_npnsw_step i pc fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      @atom_bit GE pc = O->
      cur_tid pc <> t->
      pc_valid_tid pc t->
      tau_N glob_npnsw_step j ({-|pc',t}) fp' pc''->
      abort pc''->
      (exists k pc1 fp1, tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1 /\ abort pc1 /\ k<= j) \/
      (exists k pc1 fp1, tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1 /\ FP.conflict fp fp1 /\
                    k<= S j).
  Proof.
    induction i;intros.
    {
      inversion H;subst;clear H.
      left. Esimpl;eauto. 
    }
    {
      inversion H;subst;clear H.
      eapply IHi in H8 as ?;eauto.
      destruct H.
      {
        Hsimpl.
        eapply npnsw_step_cons_star_abort in H;eauto.
        destruct H. left. Hsimpl. Esimpl;eauto. 
        Lia.lia. 

        Hsimpl. right. Esimpl;eauto.
        apply conflict_union. auto.
        Lia.lia.
      }
      {
        Hsimpl.
        assert(FP.smile fp0 x1 \/ ~ FP.smile fp0 x1).
        apply classic.
        destruct H10.
        eapply npnswstep_tauN_reorder in H7 as ?;eauto.
        Hsimpl. right. Esimpl;eauto. rewrite FP.union_comm_eq;apply conflict_union;auto.

        apply smile_conflict in H10.
        eapply npnswstep_tauN_conflict in H7 as ?;eauto.
        destruct H11;Hsimpl.
        left. Esimpl;eauto. Lia.lia.

        right. Esimpl;eauto. apply conflict_union;auto.
        Lia.lia.
      }
      eapply npnsw_step_thdpinv;eauto.
      apply npnswstep_l2 in H7;auto. congruence.
      apply npnsw_step_tid_preservation in H7;congruence.
      eapply npnsw_step_pc_valid_tid_preservation;eauto.
    }
  Qed.

    
    
  Lemma corestep_bitC_again:
    forall pc fp pc' b b',
      @type_glob_step GE core (bitC b pc) tau fp (bitC b pc')->
      type_glob_step core (bitC b' pc) tau fp (bitC b' pc').
  Proof.
    destruct pc,pc'. unfold bitC,changepc;simpl.
    inversion 1;subst.
    econstructor;eauto.
  Qed.
  Lemma npnswstep_cons_onesteprace:
    forall pc fp pc' t,
      ThreadPool.inv pc.(thread_pool)->
      glob_npnsw_step pc tau fp pc'->
      onesteprace pc' t fp->
      cur_tid pc <> t->
      race glob_predict_star_alter pc \/
      abort ({-|pc,t}).
  Proof.
    intros. inversion H1;clear H1;subst.
    assert(FP.smile fp fp' \/ ~FP.smile fp fp').
    apply classic. destruct H1.
    {
      apply npnswstep_l2 in H0 as ?. 
      apply npnswstep_l1 in H0;Hsimpl.
      rewrite <- pc_cur_tid with(pc:=pc) in H0.
      eapply globstep_reorder_rule in H4 as ?;try apply H0;eauto;try (intro R;inversion R;fail);try (inversion H4;subst;auto;fail).
      Hsimpl.
      left.
      apply npnswstep_l3 in H0 as ?;auto.
      apply npnsw_step_tid_preservation in H13 as ?.
      econstructor. eauto. econstructor. econstructor 2;eauto. rewrite <- H14.
      rewrite pc_cur_tid;eauto. econstructor 2. rewrite pc_cur_tid in H3;eauto.
      left. eauto.
      apply npnswstep_l2 in H13 as ?;simpl in *.
      constructor. congruence.
      inversion H3;subst;auto.

      econstructor. econstructor 2. left;eauto. constructor.
      congruence. inversion H10;subst. simpl. congruence.
      left;intro R;inversion R.
      repeat rewrite FP.fp_union_emp.
      apply conflict_union.  auto.
    }
    {
      apply smile_conflict in H1.
      apply FP.emp_never_conflict in H1 as ?.
      Hsimpl.
      destruct H0 as [|[]];try(inversion H0;subst;contradiction).
      rewrite <- pc_cur_tid with(pc:=pc) in H0.
      eapply corestep_conflict in H4;eauto.
      destruct H4;auto.
      Hsimpl. left.
      apply predict_star_race_to_alter.
      apply predict_race_to_star.
      assert(atom_bit pc = O). inversion H0;subst;auto.
      econstructor;[|econstructor;try apply H0|econstructor;try apply H4| |];eauto.
      left;intro R;inversion R.
    }
  Qed.
  Lemma npnswstar_npnswstep_reorder:
    forall pc fp pc'  t fp' pc'' x (Hx:x = core \/ x = call \/ x = ret),
      tau_star glob_npnsw_step pc fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = O->
      GlobEnv.wd GE->
      cur_tid pc <> t ->
      type_glob_step x ({-|pc',t}) tau fp' ({-|pc'',t})->
      FP.smile fp fp'->
      exists pc1', type_glob_step x ({-|pc,t}) tau fp' pc1'/\
              exists pc2', tau_star glob_npnsw_step ({-|pc1',cur_tid pc}) fp pc2'/\
                      mem_eq_pc GE ({-|pc'',t}) ({-|pc2',t}).
  Proof.
    induction 2;intros.

    Esimpl;eauto. constructor. simpl. apply mem_eq_pc_refl.
    apply npnsw_step_thdpinv in H as ?;auto.
    apply npnsw_step_O_preservation in H as ?;auto.
    apply npnsw_step_tid_preservation in H as ?;auto.
    rewrite H9 in H4.

    apply fpsmile_sym in H6.
    apply fpsmile_union_elim in H6 as ?.
    apply fpsmile_union_elim2 in H6 as ?.
    apply fpsmile_sym in H10;apply fpsmile_sym in H11.
    Hsimpl.

    apply npnswstep_l1 in H;Hsimpl.
    rewrite <- pc_cur_tid with(pc:=s) in H.
    eapply globstep_reorder_rule in H12;eauto;try congruence.
    Hsimpl.
    apply mem_eq_pc_change with(t:=cur_tid s') in H17.
    eapply mem_eq_npnsw_step_star in H17;eauto.
    Hsimpl. simpl in *.
    apply npnswstep_l3 in H16;auto.
    apply npnsw_step_tid_preservation in H16 as ?. simpl in H19.
    rewrite <- H9,H19,pc_cur_tid in H17.
    eapply tau_star_cons in H17;eauto.
    Esimpl;eauto.
    eapply mem_eq_pc_trans;eauto.
    eapply mem_eq_pc_change;eauto.
    destruct Hx as [|[]];subst;inversion H12;auto.
  Qed.

  Lemma npnswstar_corestep_reorder:
    forall pc fp pc'  t fp' pc'',
      tau_star glob_npnsw_step pc fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = O->
      GlobEnv.wd GE->
      cur_tid pc <> t ->
      type_glob_step core ({-|pc',t}) tau fp' ({-|pc'',t})->
      FP.smile fp fp'->
      exists pc1', type_glob_step core ({-|pc,t}) tau fp' pc1'/\
              exists pc2', tau_star glob_npnsw_step ({-|pc1',cur_tid pc}) fp pc2'/\
                      mem_eq_pc GE ({-|pc'',t}) ({-|pc2',t}).
  Proof.
    intros.
    eapply npnswstar_npnswstep_reorder in H4;eauto.
  Qed.
  Lemma npnswstar_corestep_conflict:
    forall pc fp pc' t fp' pc'',
      tau_star glob_npnsw_step pc fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      @atom_bit GE pc = O->
      GlobEnv.wd GE->
      cur_tid pc <> t ->
      type_glob_step core ({-|pc',t}) tau fp' ({-|pc'',t})->
      FP.conflict fp fp'->
      abort({-|pc,t}) \/
      exists fp1 pc1,type_glob_step core ({-|pc,t}) tau fp1 pc1 /\ FP.conflict fp fp1.
  Proof.
    intros until pc''. intro. apply tau_star_tau_N_equiv in H as [].
    revert pc fp pc' t fp' pc'' H.
    induction x;intros.
    inversion H;subst;clear H. right. Esimpl;eauto.

    inversion H;subst;clear H.

    assert(FP.conflict fp'0 fp' \/ ~ FP.conflict fp'0 fp'). apply classic. destruct H.
    {
      assert(atom_bit s' = O). apply npnswstep_l2 in H7;congruence.
      apply npnsw_step_thdpinv in H7 as ?;auto.
      apply npnsw_step_tid_preservation in H7 as ?.
      rewrite H10 in H3.
      eapply IHx in H8 as ?;eauto.
      destruct H11.
      {
        eapply npnswstep_abort_alt in H7;eauto;try congruence.
        destruct H7;auto.
        inversion H7;subst.
        right. Esimpl;eauto. apply conflict_union;auto.
      }
      {
        Hsimpl.
        apply npnswstep_l1 in H7;Hsimpl.
        rewrite <- pc_cur_tid with(pc:=pc) in H7.
        eapply globstep_reorder_rule_alter in H11;try apply H7;eauto;try congruence.
        destruct H11 as [|[]];auto;Hsimpl;right;Esimpl;eauto;try (apply conflict_union;assumption). rewrite FP.union_comm_eq. apply conflict_union;auto.

        inversion H11;subst;auto.
      }
    }
    {
      apply FP.smile_conflict_compat in H.
      apply FP.conflict_sym in H5.
      rewrite FP.union_comm_eq in H5. 
      eapply fpconflict_dif_trans in H5;eauto;try apply fpsmile_sym;eauto.
      apply tauN_taustar in H8.
      destruct H7 as [|[]];try(inversion H6;subst;apply FP.emp_never_conflict in H5 as [];contradiction).
      
      eapply npnswstar_corestep_reorder in H;eauto;try congruence.
      Hsimpl.
      rewrite <- pc_cur_tid with(pc:=pc) in H6.
      apply FP.conflict_sym in H5.
      eapply corestep_conflict in H;try apply H6;eauto.
      destruct H;auto;Hsimpl.
      right. Esimpl;eauto. apply conflict_union;auto.
      eapply GE_mod_wd_tp_inv;eauto. eapply type_glob_step_elim;eauto.
      inversion H6;subst;auto.
      inversion H6;subst;auto.
    }
  Qed.


    
  Lemma npnswstep_sw_halfatomblockabort:
    forall pc fp pc' t ,
      @glob_npnsw_step GE pc tau fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      cur_tid pc <> t->
      halfatomblock_abort ({-|pc',t})->
      halfatomblock_abort ({-|pc,t}) \/
      exists fp1 pc1,
        halfatomblockstep ({-|pc,t}) tau fp1 pc1 /\ FP.conflict fp fp1.
  Proof.
    unfold halfatomblock_abort,halfatomblockstep;intros.
    Hsimpl. clear H2.

    assert(FP.conflict fp x \/ ~ FP.conflict fp x).
    apply classic.
    destruct H2.
    {
      destruct H as [|[]];try(inversion H;subst;apply FP.emp_never_conflict in H2 as [];contradiction).
      eapply corestep_I_conflict in H as ?;eauto.
      destruct H6;auto;Hsimpl.
      right. Esimpl;eauto.
      inversion H4;subst;inversion H;subst;auto.
    }
    {
      apply FP.smile_conflict_compat in H2.
      eapply npnswstep_half_I_smile in H as ?;eauto.
      Hsimpl. 
      assert(( exists fp1 pc1, halfatomblockstep ({-|pc,t}) tau fp1 pc1 /\ FP.conflict fp fp1) \/ ~ ( exists fp1 pc1,halfatomblockstep ({-|pc,t}) tau fp1 pc1 /\ FP.conflict fp fp1)).
      apply classic. destruct H11;auto. left.
      Esimpl;eauto.
      assert(mem_eq_pc GE (changepc GE x4 t I) x0).
      apply corestar_tid_bit_preserve in H5 as [].
      inversion H4;subst.
      unfold mem_eq_pc,changepc;simpl;Esimpl;eauto.
      pose proof H12 as T1.
      apply mem_eq_abort in H12;auto.
      unfold abort in *. Hsimpl. unfold changepc in H12. simpl in H12.
      rewrite H9 in H12.
      split. apply corestar_tid_bit_preserve in H7 as [].
      assert(cur_tid x3 = t).
      inversion H6;subst;auto. subst. apply npnsw_step_tid_preservation in H.
      rewrite H in H1.
      revert H12 H8 H1 H9;clear;intros.
      intro;contradict H12.
      inversion H;subst. rewrite <- H9 in *;clear H9.
      destruct H8 as [|[]];  inversion H3;subst;inversion H;subst;econstructor ;solv_thread;solv_thread. auto.
      intros.
      apply type_glob_step_exists in H15;Hsimpl.
      apply corestar_tid_bit_preserve in H7 as ?;Hsimpl.
      destruct x5;subst;try(inversion H6;subst;inversion H15;subst;inversion H17;fail).
      Focus 2.
      assert(fp0=FP.emp). inversion H15;subst;auto. subst.
      assert(gl=tau). inversion H15;subst;auto. subst.
      apply npnswstep_l1 in H8 ;Hsimpl.
      rewrite <- pc_cur_tid with(pc:=x3) in H15.
      eapply predict_step_ex_alt in H8;eauto.
      Hsimpl.
      apply type_glob_step_elim in H8.
      assert(cur_tid x2 = t). inversion H6;auto.

      rewrite <- H16,H19 in H8.
      eapply H13 in H8;eauto.

      apply type_glob_step_elim in H6.
      apply GE_mod_wd_tp_inv in H6;auto.
      apply corestar_globstar in H7.
      eapply GE_mod_wd_star_tp_inv in H7;eauto.
      assert(cur_tid x2 = t). inversion H6;auto.
      rewrite <- H16,H19.
      apply npnsw_step_tid_preservation in H. congruence.

      apply NNPP;intro.
      assert(FP.smile fp0 fp \/ ~ FP.smile fp0 fp).
      apply classic.
      destruct H19.

      Focus 2.
      {
        apply smile_conflict in H19.
        contradict H11.
        rewrite <-pc_cur_tid with(pc:=pc) in H.
        destruct H as [|[]];try(inversion H;subst;apply FP.emp_never_conflict in H19 as [];contradiction).
        assert(gl=tau). inversion H15;subst;auto. subst.
        unfold halfatomblockstep.
        apply FP.conflict_sym in H19.
        
        apply tau_plus_1 in H15. apply tau_plus2star in H15. eapply tau_star_star in H15;eauto.
        assert(FP.conflict fp (FP.union x fp0)).
        rewrite FP.union_comm_eq. apply conflict_union_ano. auto.
        Esimpl;eauto.
      }
      Unfocus.
      assert(cur_tid x3 = t /\ atom_bit x3 = I).
      inversion H6;subst. auto.
      assert(cur_tid pc' <> t). apply npnsw_step_tid_preservation in H;auto. congruence.
      assert(v1:ThreadPool.inv x3.(thread_pool)). apply type_glob_step_elim in H6.
      apply GE_mod_wd_tp_inv in H6;auto. apply corestar_globstar in H7.
      eapply GE_mod_wd_star_tp_inv in H7;eauto.
      revert wdge wdge' H8 H19 H15 H13 H18 H20 H21 v1. clear;intros.
      destruct H20;subst.
      assert(gl = tau). inversion H15;auto. subst.
      assert(exists pc'', type_glob_step core (changepc GE x4 (cur_tid x3) I) tau fp0 pc'' ).

      apply npnswstep_l1 in H8. Hsimpl.
      destruct H1;subst;unfold changepc.
      {
        assert(type_glob_step core ({-|x3,cur_tid pc'}) tau fp (changepc GE x4 (cur_tid pc') I)).
        destruct x3;inversion H;subst. unfold changepc. simpl in *;subst. econstructor;eauto.
        rewrite <- pc_cur_tid with(pc:=x3) in H15.
        eapply predict_step_ex in H15;try apply H1;eauto.
        apply fpsmile_sym;auto.
      }
      {
        assert(type_glob_step core (changepc GE x3 (cur_tid x3) O) tau fp0 (changepc GE pc'0 (cur_tid x3) O)).
        inversion H15;subst. econstructor;eauto.
        remember (changepc GE x3 (cur_tid x3) O) as pc0.
        assert((changepc GE x3 (cur_tid pc') O) = ({-|pc0,cur_tid pc'})).
        rewrite Heqpc0. auto.
        rewrite H3 in H.
        rewrite <- pc_cur_tid with(pc:=pc0) in H2.
        eapply predict_step_ex in H2;try apply H;eauto.
        Hsimpl.
        rewrite Heqpc0 in H2.
        inversion H2;subst.
        eexists;econstructor;eauto.

        rewrite Heqpc0. unfold changepc. auto.
        apply fpsmile_sym;auto.
        rewrite Heqpc0. unfold changepc. auto.
      }
      
      Hsimpl.
      apply type_glob_step_elim in H.
      eapply H13 in H. inversion H.
      apply npnsw_step_tid_preservation in H;congruence.
    }
  Qed.
  Lemma halfatomblock_abort_atom:
    forall pc ,
      halfatomblock_abort pc ->
      atom_bit pc = O.
  Proof.
    unfold halfatomblock_abort,halfatomblockstep;intros.
    Hsimpl.
    inversion H1;auto.
  Qed.
  Lemma race_predict_sw:
    forall pc,
      race (@glob_predict GE) pc ->
      forall t,
        race glob_predict ({-|pc,t}).
  Proof.
    inversion 1;subst;econstructor;eauto.
    inversion H1;subst;[econstructor|econstructor 2];eauto.
    inversion H2;subst;[econstructor|econstructor 2];eauto.
  Qed.
  Lemma mem_eq_halfatomblock_abort:
    forall pc pc',
      mem_eq_pc GE pc' pc->
      halfatomblock_abort pc'->
      halfatomblock_abort pc.
  Proof.
    unfold halfatomblock_abort,halfatomblockstep;intros;Hsimpl.
    eapply mem_eq_globstep in H;eauto;Hsimpl.
    eapply mem_eq_corestar in H4;eauto;Hsimpl.
    Esimpl;eauto.
    eapply mem_eq_abort;eauto. apply mem_eq_pc_sym.
    auto.
  Qed.

  Lemma npnswstep_sw_star_halfatomblockabort:
    forall j pc fp pc' t fp' pc'',
      @glob_npnsw_step GE pc tau fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      cur_tid pc <> t->
      tau_N glob_npnsw_step j ({-|pc',t}) fp' pc'' ->
      halfatomblock_abort pc''->
      exists k fp1 pc1,
        tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1 /\ FP.smile fp fp1 /\
        ((k<= j /\ (halfatomblock_abort pc1 \/ abort pc1)) \/
        ((exists fp2 pc2, FP.conflict fp fp2 /\ (( k< j /\glob_npnsw_step pc1 tau fp2 pc2)\/ (k<S j /\halfatomblockstep pc1 tau fp2 pc2 ))))).
  Proof.
    induction j using(well_founded_induction lt_wf).
    intros.
    destruct j.
    {
      inversion H3;subst;clear H3.
      eapply npnswstep_sw_halfatomblockabort in H0 as ?;eauto.
      destruct H3.
      Esimpl;eauto. constructor.
      Hsimpl. apply fpsmile_sym;apply empsmile.
      exists 0;Esimpl;auto. constructor. apply fpsmile_sym;apply empsmile.
      right. Hsimpl.  Esimpl;eauto.
    }
    {
      assert(o1:atom_bit pc = O). apply npnswstep_l2 in H0.
      eapply tauN_taustar in H3. apply npnswstar_bit in H3.
      apply halfatomblock_abort_atom in H4;simpl in H3 ;try congruence.
      inversion H3;subst;clear H3.
      assert(FP.conflict fp fp0 \/ ~FP.conflict fp fp0).
      apply classic.
      destruct H3.
      {
        rewrite <- pc_cur_tid with(pc:=pc) in H0.
        eapply npnswstep_conflict in H6 as ?;eauto.
        destruct H5. exists 0;Esimpl;eauto. constructor.
        apply fpsmile_sym;apply empsmile.

        left. split;[Lia.lia|auto].
        Hsimpl.
        Esimpl;auto. constructor.
        apply fpsmile_sym;apply empsmile.
        right. Esimpl;eauto.
        left. Esimpl;eauto. Lia.lia.
      }
      {
        apply FP.smile_conflict_compat in H3.
        rewrite <- pc_cur_tid with(pc:=pc)in H0.
        eapply npnswstep_reorder in H6 as ?;try apply H0;eauto.
        Hsimpl.
        eapply mem_eq_npnsw_step_starN in H9;eauto;Hsimpl.
        eapply mem_eq_halfatomblock_abort in H10;eauto;Hsimpl.
        apply npnsw_step_tid_preservation in H6 as ?;simpl in *.
        apply npnsw_step_thdpinv in H5 as v1;auto.
        eapply H in H9 as ?;eauto;simpl;try congruence.
        Hsimpl.
        apply npnsw_step_tid_preservation in H5 as ?. simpl in *.
        rewrite <- H11,H15,pc_cur_tid in H12.
        eapply tau_N_S in H12;eauto.
        Esimpl;eauto.
        destruct H14;Hsimpl;try( eapply fpsmile_sym;eapply fpsmile_union;eapply fpsmile_sym;eauto).
        destruct H14;Hsimpl;[left|right];try split;auto.
        Lia.lia.
        destruct H16;Hsimpl.
        Esimpl;eauto. left;split;eauto. Lia.lia.
        Esimpl;eauto. right;split;eauto. Lia.lia.
      }
    }
  Qed.
  Lemma mem_eq_halfatomstep:
    forall pc pc' fp pc1 ,
      mem_eq_pc GE pc pc'->
      halfatomblockstep pc tau fp pc1->
      exists pc1', halfatomblockstep pc' tau fp pc1' /\ mem_eq_pc GE pc1 pc1'.
  Proof.
    unfold halfatomblockstep;intros;Hsimpl.
    eapply mem_eq_globstep in H;eauto;Hsimpl.
    eapply mem_eq_corestar in H3;eauto;Hsimpl.
    Esimpl;eauto.
  Qed.

  Lemma npnswstar_sw_star_halfatomblockabort:
    forall i j pc fp pc' t fp' pc''
      (HO:atom_bit pc = O),
      tau_N (@glob_npnsw_step GE) i pc fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      cur_tid pc <> t->
      tau_N glob_npnsw_step j ({-|pc',t}) fp' pc'' ->
      halfatomblock_abort pc''  \/ abort pc''->
      exists k fp1 pc1,
        k<= j /\tau_N glob_npnsw_step k ({-|pc,t}) fp1 pc1  /\
        ((halfatomblock_abort pc1 \/ abort pc1) \/
         ((exists fp2 pc2, FP.conflict fp fp2 /\ (glob_npnsw_step pc1 tau fp2 pc2 \/halfatomblockstep pc1 tau fp2 pc2 )))).
  Proof.
    induction i;intros.
    {
      inversion H;subst;clear H.
      Esimpl;eauto. 
    }
    {
      inversion H;subst.
      eapply IHi in H6 as ?;eauto.
      Hsimpl.
      assert(FP.conflict fp0 x0 \/ ~ FP.conflict fp0 x0).
      apply classic.
      destruct H9.
      {
        clear H8.
        rewrite <- pc_cur_tid with(pc:=pc) in H5;eapply npnswstep_tauN_conflict in H5 as ?;eauto.
        destruct H8;Hsimpl.
        {
          simpl in *.
          Esimpl;try apply H8;eauto.
          Lia.lia.
        }
        {
          simpl in *.
          apply FP.conflict_sym in H10.
          eapply tau_N_conflict_split in H8 as ?;eauto.
          Hsimpl.
          Esimpl;try apply H12;eauto.
          Lia.lia.

          right. Esimpl;eauto. apply conflict_union. auto.
        }
      }
      {
        apply FP.smile_conflict_compat in H9.
        eapply npnswstep_tauN_reorder in H5 as ?;eauto.
        Hsimpl.
        destruct H8.
        {
          assert(halfatomblock_abort ({-|x3,t}) \/ abort ({-|x3,t})).
          destruct H8;[left;eapply mem_eq_halfatomblock_abort|right;eapply mem_eq_abort];eauto. apply mem_eq_pc_sym;auto.
          destruct H13.
          {
            eapply npnswstep_sw_halfatomblockabort in H11 as ?;eauto.
            destruct H14.
            simpl in H14.
            apply tauN_taustar in H10 as ?.
            apply npnsw_taustar_tid_preservation in H15. simpl in H15;rewrite H15,pc_cur_tid in H14.
            Esimpl;try apply H10;eauto.
            apply tauN_taustar in H10 as ?.
            apply npnsw_taustar_tid_preservation in H15. simpl in *;rewrite H15,pc_cur_tid in H14.
            Hsimpl.
            Esimpl;try apply H10;eauto. right. Esimpl;eauto. apply conflict_union;auto.
            apply tauN_taustar in H10.
            eapply npnsw_taustar_thdpinv in H10;eauto.
          }
          {
            eapply npnswstep_abort_alt in H11 as ?;eauto.
            apply tauN_taustar in H10 as ?.
            apply npnsw_taustar_tid_preservation in H15. simpl in *;rewrite H15,pc_cur_tid in H14.
            simpl in H14. destruct H14.
            {
              Esimpl;eauto. 
            }
            {
              inversion H14;clear H14;subst.
              simpl in *.
              Esimpl;eauto. right.
              apply npnswstep_l3 in H17;auto. rewrite pc_cur_tid in H17.
              Esimpl;eauto. apply conflict_union;auto.
            }
            apply tauN_taustar in H10.
            eapply npnsw_taustar_thdpinv in H10;eauto.
            apply tauN_taustar in H10.
            apply npnswstar_bit in H10. simpl in *;subst;try congruence.
          }
        }
        {
          Hsimpl.
          assert(exists pc',mem_eq_pc GE x5 pc' /\ (glob_npnsw_step ({-|x3,t}) tau x4 pc' \/ halfatomblockstep ({-|x3,t}) tau x4 pc')).
          destruct H13.
          + apply npnswstep_l1 in H13. Hsimpl. eapply mem_eq_globstep in H12;eauto;Hsimpl.
            Esimpl;eauto. left;eauto. eapply npnswstep_l3;eauto.
          + eapply mem_eq_halfatomstep in H12;eauto;Hsimpl.
            Esimpl;eauto.

          Hsimpl.
          assert(FP.conflict fp0 x4 \/ ~ FP.conflict fp0 x4). apply classic.
          destruct H15,H16.
          {
            eapply npnswstep_conflict in H15 as ?;eauto.
            assert(cur_tid x2 = t). apply tauN_taustar in H10. apply npnsw_taustar_tid_preservation in H10;auto.
            rewrite <- H18,pc_cur_tid in H17.

            destruct H17;Hsimpl.
            Esimpl;eauto.
            
            Esimpl;eauto. right.
            Esimpl;eauto.
            apply conflict_union;auto.
            apply tauN_taustar in H10. apply npnsw_taustar_thdpinv in H10;auto.
          }
          {
            apply FP.smile_conflict_compat in H16.
            eapply npnswstep_reorder in H15 as ?;eauto.
            Hsimpl. Esimpl;eauto.
            assert(cur_tid x2 = t). apply tauN_taustar in H10. apply npnsw_taustar_tid_preservation in H10;auto.
            rewrite <- H20,pc_cur_tid in H17.
            
            right. Esimpl;eauto.
            rewrite FP.union_comm_eq.
            apply conflict_union;auto.
            apply tauN_taustar in H10;apply npnsw_taustar_thdpinv in H10;auto.
          }
          {
            unfold halfatomblockstep in H15.
            Hsimpl. clear H15.
            destruct H11 as [|[]];try(inversion H11;subst;apply FP.emp_never_conflict in H16 as [];contradiction).
            eapply corestep_I_conflict in H11 as ?;eauto.
            Hsimpl. simpl in H15.
            destruct H15;Hsimpl.
            {
              Esimpl;eauto. left.
              apply tauN_taustar in H10.
              apply npnsw_taustar_tid_preservation in H10. simpl in H10;subst.
              rewrite pc_cur_tid in H15;auto.
            }
            {
              Esimpl;eauto. apply tauN_taustar in H10.
              apply npnsw_taustar_tid_preservation in H10. simpl in H10;subst.
              rewrite pc_cur_tid in H15.
              unfold halfatomblockstep.
              right. Esimpl;eauto. apply conflict_union. auto.
            }
            apply tauN_taustar in H10;apply npnsw_taustar_thdpinv in H10;auto.
            inversion H11;subst;simpl in *;congruence.
          }
          {
            apply FP.smile_conflict_compat in H16.
            unfold halfatomblockstep in H15.
            Hsimpl.
            eapply npnswstep_half_I_smile in H11 as ?;eauto.
            Hsimpl.
            simpl in*.
            assert(cur_tid x2 = t). apply tauN_taustar in H10;apply npnsw_taustar_tid_preservation in H10;auto.
            rewrite <- H24,pc_cur_tid in H19.
            Esimpl;eauto. right.
            unfold halfatomblockstep.
            Esimpl;eauto. rewrite FP.union_comm_eq;apply conflict_union;auto.
            apply tauN_taustar in H10;apply npnsw_taustar_thdpinv in H10;auto.
            apply npnsw_step_tid_preservation in H11.
            simpl in *;subst;congruence.
          }
        }
      }
      apply npnsw_step_O_preservation in H5;auto.
      eapply npnsw_step_thdpinv;eauto.
      apply npnsw_step_tid_preservation in H5;auto.
      congruence.
    }
  Qed.

    
  Local Arguments invpc [GE].
  Inductive race' {ge} : (@ProgConfig ge->tid->Bit->FP.t->Prop)->@ProgConfig ge->tid->tid->FP.t->FP.t ->Bit->Bit->Prop :=
    Race: forall (predict:@ProgConfig ge->tid->Bit->FP.t->Prop) pc t1 b1 fp1 t2 b2 fp2,
      t1 <> t2 ->
      predict pc t1 b1 fp1 ->
      predict pc t2 b2 fp2 ->
      b1 <> I \/ b2 <> I ->
      FP.conflict fp1 fp2 ->
      race' predict pc t1 t2 fp1 fp2 b1 b2 .

  Lemma race'_sound:
    forall predict pc t1 t2 b1 b2 fp1 fp2,
      race' predict pc t1 t2 fp1 fp2 b1 b2->
      @race GE predict pc.
  Proof. inversion 1;subst;econstructor;eauto. Qed.
  

      
  Lemma predicted_abort1_sw:
    forall pc,
      predicted_abort1 pc->
      @invpc GE pc ->
      cur_valid_id GE pc.
  Proof.
    intros.
    inversion H;subst.
    {
      apply npnsw_taustar_thdpinv in H1 as ?;eauto.
      unfold halfatomblock_abort in H2.
      Hsimpl. unfold halfatomblockstep in H2.
      Hsimpl. apply type_glob_step_cur_valid_id in H5;auto;[|intro R;inversion R].
      apply npnsw_taustar_tid_preservation in H1 as ?.
      eapply npnsw_taustar_pc_valid_tid_backwards_preservation in H1 as ?;eauto.
      rewrite H7;auto.
    }
    {
      unfold npnsw_star_abort in H2.
      Hsimpl.
      inversion H1;subst. split;auto.
    }
  Qed.

  Lemma npnswstep_predicted_abort:
    forall pc fp pc'
      (Hinv:invpc  pc),
      atom_bit pc = O->
      @glob_npnsw_step GE pc tau fp pc'->
      predicted_abort1 pc'->
      predicted_abort1 pc.
  Proof.
    intros.
    inversion H1;subst.
    {
      unfold halfatomblock_abort in H3.
      Hsimpl.
      eapply tau_star_cons in H0;eauto.
      econstructor;eauto. unfold halfatomblock_abort.
      Esimpl;eauto.
    }
    {
      unfold npnsw_star_abort in H3.
      Hsimpl.
      eapply tau_star_cons in H0 as ?;eauto.
      econstructor 2.
      instantiate(1:=({-|pc,cur_tid pc})).
      apply npnsw_step_cur_valid_id in H0;auto.
      destruct pc,H0;simpl in *;subst;econstructor;eauto.
      econstructor;eauto.
    }
  Qed.


  Lemma predicted_abort1_predicted_abort:
    forall pc,
      invpc  pc->
      predicted_abort1 pc ->
      exists fp pc',
        tau_star glob_npnsw_step pc fp pc' /\ predicted_abort pc'.
  Proof.
    unfold predicted_abort.
    inversion 2;subst.
    {
      unfold halfatomblock_abort,halfatomblockstep in H2.
      Esimpl;eauto.
      Hsimpl. inversion H4;subst;auto.
      Hsimpl. eapply type_glob_step_cur_valid_id ;eauto.
      eapply npnsw_taustar_thdpinv;eauto.
      intro R;inversion R.
    }
    {
      unfold npnsw_star_abort in H2.
      Hsimpl;Esimpl;eauto. inversion H1;subst;auto.
      eapply npnsw_taustar_O_preservation in H2;eauto.
      assert(pc_valid_tid pc (cur_tid pc)). inversion H1;subst;split;auto.
      eapply npnsw_taustar_pc_valid_tid_preservation in H2;eauto.
      apply npnsw_taustar_tid_preservation in H2;eauto.
      rewrite <- H2;auto.
    }
  Qed.

  Lemma predicted_abort_predicted_abort1':
    forall pc fp pc',
      invpc  pc->
      tau_star glob_npnsw_step pc fp pc'->
      predicted_abort pc' ->
      predicted_abort1 pc.
  Proof.
    induction 2;intros;auto.
    apply predicted_abort_predicted_abort1;auto.
    apply npnsw_step_thdpinv in H0 as ?;auto.
    Hsimpl.
    eapply npnswstep_predicted_abort;eauto.
    inversion H2;subst.
    apply npnswstar_bit in H1.
    apply npnswstep_l2 in H0.
    congruence.
  Qed.

  Lemma mem_eq_predicted_abort:
    forall pc pc',
      mem_eq_pc GE pc pc'->
      predicted_abort pc'->
      predicted_abort pc.
  Proof.
    unfold predicted_abort. intros. Hsimpl.
    pose proof H as R.
    unfold mem_eq_pc in R;Hsimpl.
    split;auto. congruence.
    split. inversion H1;subst. split;congruence.
    destruct H2;[left;eapply mem_eq_abort|right;eapply mem_eq_halfatomblock_abort];eauto.
    apply mem_eq_pc_sym;auto.
  Qed.

  Lemma mem_eq_predicted_abort1:
    forall pc pc',
      mem_eq_pc GE pc pc'->
      predicted_abort1 pc->
      predicted_abort1 pc'.
  Proof.
    inversion 2;subst.
    {
      eapply mem_eq_npnsw_step_star in H ;eauto;Hsimpl.
      eapply mem_eq_halfatomblock_abort in H3;eauto;Hsimpl.
      econstructor;eauto.
    }
    {
      destruct H2;Hsimpl. pose proof H as R.
      eapply mem_eq_npnsw_step_star in H;eauto. Hsimpl.
      apply mem_eq_pc_sym in H4.
      eapply mem_eq_abort in H4;eauto;Hsimpl.
      econstructor 2;eauto.
      instantiate(1:=pc'). assert(atom_bit pc = O). inversion H1;auto.
      assert(pc_valid_tid pc (cur_tid pc)).
      inversion H1;subst;auto. split;auto.
      assert(pc_valid_tid pc' (cur_tid pc')).
      destruct H6,R;Hsimpl.
      split;try congruence.
      assert(atom_bit pc' = O). destruct R;Hsimpl;congruence.
      destruct pc',H7;simpl in *;subst;econstructor;eauto.
      econstructor. Esimpl;eauto.
    }
  Qed.

  Lemma npnswstep_sw_predicted_abort:
    forall i pc fp fp2 pc' pc'' pc''',
      forall (Hneq:      cur_tid pc' <> cur_tid pc''),
        invpc pc->
        glob_npnsw_step pc tau fp pc'->
        glob_step pc' sw FP.emp pc''->
        tau_N glob_npnsw_step i pc'' fp2 pc'''->
        predicted_abort pc'''->
        (exists j t fp' pc1, pc_valid_tid pc t /\ tau_N glob_npnsw_step j ({-|pc,t}) fp' pc1 /\  predicted_abort pc1 /\ j<= i) \/
        race glob_predict_star_alter pc.
  Proof.
    destruct 6 as [?[]].
    assert(tau_N glob_npnsw_step 1 pc fp pc').
    rewrite <- FP.fp_union_emp with(fp:=fp). econstructor ;eauto. constructor.
    remember (cur_tid pc'') as t.
    assert(pc'' = ({-|pc',t})). inversion H1;subst;auto.
    rewrite H7 in *;simpl in *.
    clear pc'' H7.
    
    eapply npnswstar_sw_star_halfatomblockabort in H6;eauto.
    Hsimpl.
    destruct H8.
    {
      left. Esimpl;eauto.
      eapply npnswstep_pc_valid_tid_backwards_preservation in H0;eauto.
      inversion H1;subst;split;auto.
      unfold predicted_abort. split;auto.
      assert(atom_bit pc' = O). inversion H1;auto.
      apply npnswstep_l2 in H0.
      apply tauN_taustar in H7;apply npnswstar_bit in H7.
      simpl in *;subst;congruence.
      split;[|destruct H8;auto].
      apply tauN_taustar in H2. apply npnsw_taustar_tid_preservation in H2 as ?.
      simpl in H9. eapply npnsw_taustar_pc_valid_tid_backwards_preservation in H2;eauto.
      subst.
      eapply npnswstep_pc_valid_tid_backwards_preservation in H0;eauto.
      apply tauN_taustar in H7.
      apply npnsw_taustar_tid_preservation in H7 as ?.
      eapply npnsw_taustar_pc_valid_tid_preservation in H7;eauto.
      rewrite <- H9. simpl. auto.
    }
    {
      Hsimpl.
      destruct H9;right.
      {
        apply npnsw_step_tid_preservation in H0 as ?.
        assert(atom_bit pc'=O). inversion H1;auto.
        apply npnswstep_l2 in H0 as ?. simpl in *.
        apply tauN_taustar in H7.
        apply tau_plus_1 in H9. apply tau_plus2star in H9. eapply tau_star_star in H9;eauto.
        econstructor. eauto.
        econstructor;eauto. rewrite <- H10,pc_cur_tid. apply tau_plus2star. econstructor;eauto. congruence.
        econstructor. eauto. congruence.
        eapply npnswstar_bit in H9;simpl in *;try congruence.
        left;intro R;inversion R.
        rewrite FP.union_comm_eq;apply conflict_union_ano;auto.
      }
      {
        unfold halfatomblockstep in H9.
        Hsimpl.
        apply npnsw_step_tid_preservation in H0 as ?.
        assert(atom_bit pc'=O). inversion H1;auto.
        apply npnswstep_l2 in H0 as ?. simpl in *. rewrite H13 in H14.
        apply tauN_taustar in H7.
        econstructor. eauto.
        econstructor;eauto. rewrite <- H12,pc_cur_tid. eapply tau_plus2star;econstructor;eauto.
        econstructor 2;eauto.
        left;intro R;inversion R.
        rewrite FP.union_comm_eq;apply conflict_union_ano;auto.
      }
    }
    assert(atom_bit pc'=O). inversion H1;auto.
    apply npnswstep_l2 in H0 as ?. simpl in *.
    congruence.
    apply npnsw_step_tid_preservation in H0. congruence.
    destruct H5;auto.
  Qed.

  Lemma npnswstep_sw_predicted_abort1:
    forall  pc fp pc' pc'',
    forall (Hneq:      cur_tid pc' <> cur_tid pc''),
      invpc pc->
      glob_npnsw_step pc tau fp pc'->
      glob_step pc' sw FP.emp pc''->
      predicted_abort1 pc''->
      (exists t, pc_valid_tid pc t/\  predicted_abort1 ({-|pc,t}) ) \/
      race glob_predict_star_alter pc.
  Proof.
    intros.
    apply npnsw_step_thdpinv in H0 as v1;auto.
    apply GE_mod_wd_tp_inv in H1 as v2;auto.
    apply predicted_abort1_predicted_abort in H2;auto.
    Hsimpl.
    apply tau_star_tau_N_equiv in H2 as [].
    eapply npnswstep_sw_predicted_abort in H0;eauto.
    destruct H0;auto.
    Hsimpl. apply tauN_taustar in H4.
    eapply predicted_abort_predicted_abort1' in H5;eauto.
  Qed.

 
End CReorder.
    
    
