Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics GlobSemantics_Lemmas NPSemantics TypedSemantics .

Require Import DRF USimDRF NPDRF.

Require Import Classical Wf Arith.

Require Import FPLemmas PRaceLemmas Init SmileReorder ConflictReorder.

(** This file consists results of equivalence of DRF and NPDRF and some lemmas about safety.
- Lemma NPDRF_DRF_Config: [NPSafe(S)] /\ [NPDRF(S)] => DRF(S)
- Lemma DRF_NPDRF_Config: [DRF(S)] => [NPDRF(S)]
- Lemma NPSafe_Safe': [NPSafe(S)] => [Safe(S)]

Many other lemmas used in this file are located in the following files:
FPLemmas.v PRaceLemmas.v SmileReorder.v ConflictReorder.v
*)
Local Notation "'<<' i ',' c ',' sg ',' F '>>'" := {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|} (at level 60, right associativity).
Local Definition pc_valid_tid {ge}:= @GSimDefs.pc_valid_tid ge.
Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:= D|}(at level 70,right associativity).  Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).

  Lemma pc_valid_tid_back:
    forall ge pc l fp pc',
      ThreadPool.inv pc.(thread_pool)->
      GlobEnv.wd ge->
      @glob_step ge pc l fp pc'->
      pc_valid_tid pc (cur_tid pc').
  Proof.
    intros.
    apply type_glob_step_exists in H1 as [].
    destruct x;inversion H1;subst;split;try (eapply gettop_valid_tid;solv_thread;fail);try(intro;solv_thread;fail);auto.
  Qed.
  Lemma pc_valid_tid_back_norm:
    forall ge pc l fp pc' t,
      ThreadPool.inv pc.(thread_pool)->
      GlobEnv.wd ge->
      @glob_step ge pc l fp pc'->
      pc_valid_tid pc' t->
      pc_valid_tid pc t.
  Proof.
    intros.
    destruct H2.
    apply type_glob_step_exists in H1 as [].
    destruct x;inversion H1;subst;simpl in *;split;try (solv_thread;fail);try (intro;contradict H3;solv_thread;econstructor;solv_thread;solv_thread;fail).
    intro. contradict H3.
    unfold ThreadPool.pop in H_tp_pop.
    destruct Maps.PMap.get;[|inversion H_tp_pop].
    destruct CallStack.pop;inversion H_tp_pop;clear H_tp_pop.
    simpl in *.
    inversion H4;subst.
    assert(t = t0 \/ t <> t0).
    apply classic.
    destruct H5.
    econstructor;solv_thread.
    econstructor;solv_thread.
    destruct Coqlib.peq;auto.
    Unshelve.
    auto.
  Qed.
    
  Lemma  pc_valid_tid_back_star:
    forall ge pc l fp pc' t,
      ThreadPool.inv pc.(thread_pool)->
      GlobEnv.wd ge->
      star (@glob_step ge) pc l fp pc'->
      pc_valid_tid pc' t->
      pc_valid_tid pc t.
  Proof.
    induction 3;intros. auto.
    assert(ThreadPool.inv s2.(thread_pool)).
    eapply GE_mod_wd_tp_inv;eauto.
    specialize (IHstar H4 H3).
    eapply pc_valid_tid_back_norm in H1;eauto.
  Qed.
Section Complex_reorder.
  Variable GE:GlobEnv.t.
  Hypothesis wdge:GlobEnv.wd GE.
  Hypothesis modwdge:forall ix,mod_wd (GlobEnv.modules GE ix).
  Definition Step:Type:=@ProgConfig GE->glabel->FP.t->@ProgConfig GE->Prop.
(*  Definition invpc (pc:@ProgConfig GE):Prop:=ThreadPool.inv pc.(thread_pool).
  Definition cur_valid_id (pc:@ProgConfig GE):=pc_valid_tid pc pc.(cur_tid).*)
  Local Arguments cur_valid_id [GE] . 
  Local Arguments invpc [GE].





  Local Arguments predicted_abort1 [GE].
  Lemma glob_sw_star_I:
    forall pc pc',
      sw_star (@glob_step GE) pc pc'-> atom_bit pc = I->pc = pc'.
  Proof.
    induction 1;intros. auto.
    inversion H;subst;inversion H1.
  Qed.
  Lemma glob_sw_star_bit_preservation:
    forall pc pc',sw_star(@glob_step GE)pc pc'->atom_bit pc = atom_bit pc'.
  Proof.
    induction 1;intros;auto.
    inversion H;subst. auto.
  Qed.
  
  Lemma swstar_l1:forall pc pc',sw_star (@glob_step GE) pc pc'-> pc'=({-|pc,cur_tid pc'}).
  Proof. induction 1;intros. rewrite pc_cur_tid;auto. rewrite IHsw_star. simpl. inversion H;subst;auto. Qed.
  Lemma swstar_l2:
    forall pc pc',sw_star (@glob_step GE) pc pc'->cur_valid_id pc'->atom_bit pc = O->glob_step pc sw FP.emp pc'.
  Proof.
    intros.
    apply glob_sw_star_bit_preservation in H as L.
    apply swstar_l1 in H.
    destruct pc. simpl in *;subst. rewrite H;simpl. rewrite H1.
    rewrite H in H0;destruct H0;simpl in *.
    econstructor;eauto.
  Qed.

  Record Trace :Type:= { trpc:@ProgConfig GE;trlabel:glabel;trfp:FP.t;trpc':@ProgConfig GE;trtype:steptype }.
  
  Inductive noevt_stepN :Step->nat->@ProgConfig GE->FP.t->@ProgConfig GE->Prop:=
  |base_emp:
     forall step pc,noevt_stepN step 0 pc FP.emp pc
  |cons_sw:
     forall (step:Step) pc fp pc',
       step pc sw fp pc'->
       forall i fp' pc'',
         noevt_stepN step i pc' fp' pc''->
         noevt_stepN step i pc (FP.union fp fp') pc''
  |cons_tau:
     forall (step:Step) pc fp pc',
       step pc tau fp pc'->
       forall i fp' pc'',
         noevt_stepN step i pc' fp' pc''->
         noevt_stepN step (S i) pc (FP.union fp fp') pc''.
  Lemma noevt_stepN_sound:
    forall step i pc fp pc', noevt_stepN step i pc fp pc'-> non_evt_star step pc fp pc'.
  Proof. induction 1;intros;econstructor;eauto. Qed.
  Lemma noevt_stepN_exists:
    forall step pc fp pc',non_evt_star step pc fp pc'->exists i,noevt_stepN step i pc fp pc'.
  Proof.
    induction 1;intros. eexists;econstructor;eauto.
    destruct IHnon_evt_star,H;[exists (S x);econstructor 3|exists x;econstructor 2];eauto.
  Qed.
  Lemma mem_eq_noevt_stepN:
    forall pc pc',
      mem_eq_pc GE pc pc'->
      forall i fp pc'',
        noevt_stepN glob_step i pc fp pc''->
        exists pc2,noevt_stepN glob_step i pc' fp pc2 /\ mem_eq_pc GE pc'' pc2.
  Proof.
    intros. remember glob_step.
    revert pc' H.
    induction H0;subst;intros.
    eexists;split;eauto. constructor. 
    apply type_glob_step_exists in H as [].
    eapply mem_eq_globstep in H as (?&?&?);eauto.
    eapply IHnoevt_stepN in H2 as (?&?&?);eauto.
    eexists;split;eauto. econstructor 2;eauto. eapply type_glob_step_elim;eauto.
    apply type_glob_step_exists in H as [].
    eapply mem_eq_globstep in H as (?&?&?);eauto.
    eapply IHnoevt_stepN in H2 as (?&?&?);eauto.
    eexists;split;eauto. econstructor 3;eauto. eapply type_glob_step_elim;eauto.
  Qed.

  Definition npnsw_or_sw_step:Step:=
    fun pc l fp pc'=>glob_npnsw_step pc l fp pc' \/ type_glob_step glob_sw pc l fp pc'.
  
  Definition npnsw_or_sw_star:=
    fun pc fp pc'=> exists l,star npnsw_or_sw_step pc l fp pc'.
    
  Lemma npnsw_or_sw_star_not_cur_valid_tid:
    forall pc fp pc',
      npnsw_or_sw_star pc fp pc'->
      invpc pc->
      atom_bit pc = O->
      ~ cur_valid_id pc->
      pc = pc'/\ fp = FP.emp  \/ exists pc1,glob_step pc sw FP.emp pc1 /\ npnsw_or_sw_star pc1 fp pc'.
    Proof.
      intros. destruct H.
      induction H;intros;auto.
      
      destruct H.
      {
        contradict H2.
        eapply npnsw_step_cur_valid_id;eauto.
      }
      {
        right.
        assert(e=sw /\ fp1 = FP.emp). inversion H;auto.
        destruct H4;subst.
        apply type_glob_step_elim in H.
    
        eexists;split;eauto.
        rewrite FP.emp_union_fp. eexists;eauto.
      }
    Qed.  
    
    Lemma swstar_cons_npnsw_or_sw_star:
      forall pc pc',
        sw_star glob_step pc pc'->
        forall fp pc'',
          npnsw_or_sw_star pc' fp pc''->
          npnsw_or_sw_star pc  fp pc''.
    Proof.
      induction 1;intros. auto.
      specialize (IHsw_star _ _ H1).
      eapply type_glob_step_exists in H as [].
      destruct x;try (inversion H;fail).
      destruct IHsw_star.
      exists (cons sw x).
      rewrite <- FP.emp_union_fp with(fp:=fp).
      econstructor;eauto.
      right. auto.
    Qed.
    Lemma npnsw_step_cons_npnsw_or_sw_star:
      forall pc l fp pc',
        glob_npnsw_step pc l fp pc'->
        forall fp2 pc'',
          npnsw_or_sw_star pc' fp2 pc''->
          npnsw_or_sw_star pc (FP.union fp fp2) pc''.
    Proof.
      inversion 2. exists (cons tau x). econstructor;eauto. left.
      inversion H as [|[]];inversion H2;subst;auto.
    Qed.
    Lemma mem_eq_npnsw_or_sw_star:
      forall pc pc',
        mem_eq_pc GE pc pc'->
        forall fp pc'',
          npnsw_or_sw_star pc fp pc''->
          exists pc''',npnsw_or_sw_star pc' fp pc'''/\ mem_eq_pc GE pc'' pc'''.
    Proof.
      pose wdge . pose modwdge.
      intros.
      destruct H0. revert pc' H.
      induction H0;intros. exists pc'. split;auto. exists nil; econstructor.
      destruct H.
      
      apply npnswstep_l1 in H as (?&?&?).
      eapply mem_eq_globstep in H as (?&?&?);eauto.
      apply npnswstep_l3 in H;auto.
      
      eapply IHstar in H3 as (?&?&?).
      exists x1;split;auto. destruct H3. exists (cons e x2);econstructor;eauto. left;auto.
      
      eapply mem_eq_globstep in H as (?&?&?);eauto.
      eapply IHstar in H2 as (?&?&?).
      exists x0;split;auto. destruct H2. exists (cons e x1);econstructor;eauto. right;auto.
    Qed.
    
    Definition atomblockstep :Step:=
      fun pc l fp pc'=>l = tau /\ exists i,atomblockN GE i pc fp pc'.
    Lemma atomblockstep_tid_preservation:
      forall pc l fp pc',atomblockstep pc l fp pc'->cur_tid pc' = cur_tid pc.
    Proof.
      inversion 1 as (?&?&?&?&?&?&?).
      apply tauN_taustar in H2.
      apply corestar_tid_bit_preserve in H2 as [].
      inversion H1;subst;inversion H3;subst;simpl in *;subst;auto.
    Qed.
    Lemma mem_eq_atomblockstep:
      forall pc pc',
        mem_eq_pc GE pc pc'->
        forall l fp pc1,
          atomblockstep pc l fp pc1->
          exists pc2,atomblockstep pc' l fp pc2 /\ mem_eq_pc GE pc1 pc2.
    Proof.
      pose proof modwdge as R.
      intros.
      inversion H0 as (?&?&?&?&?&?&?).
      eapply mem_eq_globstep in H2 as (?&?&?);eauto.
      eapply mem_eq_coreN in H3 as (?&?&?);eauto.
      eapply mem_eq_globstep in H4 as (?&?&?);eauto.
      eexists;split;eauto.
      split;auto.
      exists x. esplit;split;eauto.
    Qed.
    Lemma atomblockstep_cur_valid_id:
      forall pc l fp pc', invpc pc->atomblockstep pc l fp pc'->cur_valid_id pc.
    Proof.
      inversion 2 as (?&?&?&?&?);subst.
      inversion H2;subst. split. eapply gettop_valid_tid;eauto. intro;solv_thread.
    Qed.
    Lemma atomblockstep_bitO:
      forall pc l fp pc',atomblockstep pc l fp pc'->atom_bit pc = O /\ atom_bit pc' = O.
    Proof. inversion 1 as (?&?&?&?&?&?&?). inversion H1;inversion H3;auto. Qed.

    Lemma atomblockstep_globstar:
      forall pc l fp pc',atomblockstep pc l fp pc'->
                    exists l1,star glob_step pc l1 fp pc'.
    Proof.
      inversion 1 as (?&?&?&?&?&?&?);subst.
      apply coretauN_globtauN in H2.  apply tauN_taustar in H2. apply tau_star_to_star in H2 as [].
      apply type_glob_step_elim in H1. apply type_glob_step_elim in H3.
      eapply star_step in H1;eauto.
      eapply star_cons_step in H3 as [];eauto.
      rewrite FP.fp_union_emp in H2. rewrite FP.emp_union_fp in H2. eauto.
    Qed.

    Lemma atomblockstep_invpc_preserve:
      forall pc l fp pc',atomblockstep pc l fp pc'->invpc pc->invpc pc'.
    Proof. intros. apply atomblockstep_globstar in H as []. eapply GE_mod_wd_star_tp_inv2;eauto.  Qed.
    Definition haltstep := @type_glob_step GE glob_halt.
    Inductive atomblockstarN:nat->list tid->@ProgConfig GE->FP.t->@ProgConfig GE->Prop:=
    | base_emp_1:
        forall pc,atom_bit pc = O->atomblockstarN 0 nil pc FP.emp pc
    | cons_atomblock_1:
        forall pc fp1 pc1 fp2 pc2 pc3,
          tau_star glob_npnsw_step pc fp1 pc1 ->
          atomblockstep pc1 tau fp2 pc2 \/ haltstep pc1 tau fp2 pc2 ->
          sw_star glob_step pc2 pc3 ->
          forall i l fp pce,
            atomblockstarN i l pc3 fp pce->
            atomblockstarN (S i)(cons (cur_tid pc) l) pc (FP.union (FP.union fp1 fp2) fp) pce.
    Lemma npnswstep_cons_atomblockstarN:
      forall pc l fp pc',
        glob_npnsw_step pc l fp pc'->
        forall i t fp' pc'',
          atomblockstarN i (cons (cur_tid pc') t) pc' fp' pc''->
          atomblockstarN i (cons (cur_tid pc') t) pc (FP.union fp fp') pc''.
    Proof.
      intros.
      remember (cons (cur_tid pc') t).
      inversion H0;subst. inversion H3.
      inversion H6;subst.
      assert(l=tau). inversion H as [|[]];inversion H5;auto. subst.
      assert(cur_tid pc = cur_tid pc'). inversion H as [|[]];inversion H5;subst;auto. 
      eapply tau_star_cons in H1;eauto.
      rewrite <- H5.
      eapply cons_atomblock_1 in H4;eauto.
      repeat rewrite FP.fp_union_assoc;auto.
    Qed.
    Lemma atomblockstarN_atomO:
      forall i l pc fp pc',atomblockstarN i l pc fp pc'->atom_bit pc = O /\ atom_bit pc' = O.
    Proof.
      induction 1;intros;auto. destruct IHatomblockstarN;split;auto.
      assert(atom_bit pc1 = O). destruct H0. apply atomblockstep_bitO in H0 as [];auto. inversion H0;auto. revert H H5;clear;induction 1;intros;auto.
      destruct H as [|[]];inversion H;subst;auto.
    Qed.
    Lemma sw_star_invpc_preservation:
      forall pc pc',sw_star (@glob_step GE) pc pc'->invpc pc->invpc pc'.
    Proof. induction 1;intros;auto. apply IHsw_star. eapply GE_mod_wd_tp_inv;eauto. Qed.
    Lemma atomblockstarN_invpc_preservation:
      forall i l pc fp pc',
        atomblockstarN i l pc fp pc'->
        invpc pc->
        invpc pc'.
    Proof.
      induction 1;intros;auto.
      eapply npnsw_taustar_thdpinv in H;eauto.
      apply IHatomblockstarN.
      eapply sw_star_invpc_preservation;eauto.
      destruct H0.
      eapply atomblockstep_invpc_preserve;eauto.
      eapply type_glob_step_elim in H0;eauto.
      eapply GE_mod_wd_tp_inv in H0;eauto.
    Qed.
    Lemma atomblockstarN_cur_valid_tid:
      forall i l pc fp pc',
        i > 0 ->
        invpc pc->
        atomblockstarN i l pc fp pc'->
        cur_valid_id pc.
    Proof.
      pose wdge.
      inversion 3;subst. inversion H.
      inversion H2;subst;[|eapply npnswstep_cur_valid_tid;eauto].
      destruct H3. apply atomblockstep_cur_valid_id in H3;auto.
      inversion H3;subst;split;[eapply gettop_valid_tid|intro];solv_thread.
    Qed.

    Lemma atomblockstarN_SN_N1_split:
      forall i l pc fp pc',
        atomblockstarN (S i) l pc fp pc'->
        exists fp1 fp2 pc1 l' l'',
          atomblockstarN i l' pc fp1 pc1 /\
          atomblockstarN 1 l'' pc1 fp2 pc' /\
          l = app l' l'' /\ fp = FP.union fp1 fp2.
    Proof.
      intros. remember (S i).
      revert i l pc fp pc' H Heqn.
      induction n;intros.
      inversion Heqn.
      inversion H;subst.
      
      destruct n. inversion Heqn;subst.
      inversion H4;subst.
      do 6 eexists. constructor. apply atomblockstarN_atomO in H as [];auto.
      split;eauto.
      
      eapply IHn in H4;eauto.
      destruct H4 as (?&?&?&?&?&?&?&?&?).
      eapply cons_atomblock_1 in H0;eauto.
      inversion Heqn;subst.
      do 6 eexists;eauto. split;eauto.
      rewrite FP.fp_union_assoc;auto.
    Qed.
  
    Lemma atomblockstarN_1_cons_sw:
      forall l pc fp pc' pc'',
        atomblockstarN 1 l pc fp pc'->
        glob_step pc' sw FP.emp pc''->
        atomblockstarN 1 l pc fp pc''.
    Proof.
      inversion 1;subst. inversion H4;subst.
      intro.
      assert(sw_star glob_step pc2 pc'').
      revert H3 H5;clear;intros.
      induction H3;subst. econstructor;eauto. constructor.
      specialize (IHsw_star H5).
      econstructor;eauto.
      econstructor;eauto. constructor.
      inversion H5;auto.
    Qed.
    Lemma atomblockstarN_cons:
      forall i ltids0 pc0 fp0 ltids pc fp pc1,
        atomblockstarN 1 ltids0 pc0 fp0 pc->
        atomblockstarN i ltids pc fp pc1->
        atomblockstarN (S i) (cons (cur_tid pc0) ltids) pc0 (FP.union fp0 fp) pc1.
    Proof. inversion 1;subst;inversion H4;subst;intros;rewrite FP.fp_union_emp;econstructor;eauto. Qed.
    
    Lemma atomblockstarN_SN_inv:
      forall i ltids pc fp pc',
        atomblockstarN (S i) ltids pc fp pc'->
        exists fp1 fp2 pc1 l,
          atomblockstarN 1 (cons (cur_tid pc) nil) pc fp1 pc1 /\ atomblockstarN i l pc1 fp2 pc' /\  FP.union fp1 fp2 = fp /\ ltids = cons (cur_tid pc) l .
    Proof.
      inversion 1;subst.
      do 5 eexists;eauto.
      rewrite <- FP.fp_union_emp with (fp:=(FP.union fp1 fp2)).
      econstructor;eauto.
      constructor.
      apply atomblockstarN_atomO in H4 as [];auto.
    Qed.
    
    Lemma atomblockstarN_cons':
      forall i j l1 l2 pc fp1 pc1 fp2 pc2,
        atomblockstarN i l1 pc fp1 pc1->
        atomblockstarN j l2 pc1 fp2 pc2->
        atomblockstarN (i+j) (app l1 l2)pc (FP.union fp1 fp2)pc2.
    Proof.
      induction i;intros.
      inversion H;subst;auto. simpl. rewrite FP.emp_union_fp;auto.
      
      apply atomblockstarN_SN_inv in H as (?&?&?&?&?&?&?&?).
      eapply IHi in H0;eauto.
      eapply atomblockstarN_cons in H0;eauto.
      rewrite H3. rewrite <- H2. rewrite <- FP.fp_union_assoc.
      assumption.
    Qed.
    Lemma atomblockstarN_cons_sw:
      forall i l pc fp pc' pc'',
        i <> 0 ->
        atomblockstarN i l pc fp pc'->
        glob_step pc' sw FP.emp pc''->
        atomblockstarN i l pc fp pc''.
    Proof.
      intros.
      destruct i. contradiction.
      apply atomblockstarN_SN_N1_split in H0 as (?&?&?&?&?&?&?&?&?).
      eapply atomblockstarN_1_cons_sw in H2;eauto.
      eapply atomblockstarN_cons' in H2;eauto.
      assert(i+1=S i). Omega.omega.
      congruence.
    Qed.
    Lemma atomblockstarN_cons_swstar:
      forall i l pc fp pc' pc'',
        i <> 0->
        atomblockstarN i l pc fp pc'->
        sw_star glob_step pc' pc''->
        atomblockstarN i l pc fp pc''.
    Proof.
      induction 3;intros. auto.
      apply IHsw_star. eapply atomblockstarN_cons_sw;eauto.
    Qed.
    Lemma mem_eq_atomblockstarN:
      forall pc pc',
        mem_eq_pc GE pc pc'->
        forall i l fp pc1,
          atomblockstarN i l pc fp pc1->
          exists pc2,atomblockstarN i l pc' fp pc2 /\ mem_eq_pc GE pc1 pc2.
    Proof.
      pose modwdge.
      intros. revert pc' H.
      induction H0;intros. eexists;split. constructor;auto.
      inversion H0 as (?&?&?&?);congruence. auto.
      eapply mem_eq_npnsw_step_star in H as (?&?&?);eauto.
      
      destruct H0.
      {
        eapply mem_eq_atomblockstep in H0 as (?&?&?);eauto.
        eapply mem_eq_swstar in H1 as (?&?&?);eauto.
        eapply IHatomblockstarN in H6 as (?&?&?);eauto.
        eexists;split;eauto. inversion H3 as (_&_&?&_).
        rewrite H8. econstructor;eauto.
      }
      {
        eapply mem_eq_globstep in H0 as (?&?&?);eauto.
        eapply mem_eq_swstar in H1 as (?&?&?);eauto.
        eapply IHatomblockstarN in H6 as (?&?&?);eauto.
        eexists;split;eauto. inversion H3 as (_&_&?&_).
        rewrite H8. econstructor;eauto.
      }
    Qed.  
    

    Corollary glob_npnsw_step_star_ex:
      forall pc l fp pc' t fp2 pc2,
        glob_npnsw_step pc l fp pc'-> invpc pc->
        t <> cur_tid pc ->
        tau_star glob_npnsw_step ({-|pc',t}) fp2 pc2->
        (FP.conflict fp fp2 /\
         ((npnsw_star_abort GE ({-|pc,t}))\/
         (exists fp1 pc1', tau_star glob_npnsw_step ({-|pc, t}) fp1 pc1' /\ FP.conflict fp fp1)))\/
        FP.smile fp fp2 /\ exists pc1' : ProgConfig, tau_star glob_npnsw_step ({-|pc, t}) fp2 pc1' /\ (exists pc2' : ProgConfig,  glob_npnsw_step ({-|pc1', cur_tid pc}) tau fp pc2' /\ mem_eq_pc GE pc2 ({-|pc2', cur_tid pc2})).
    Proof.
      pose proof modwdge as B1.
      pose proof wdge as B2.
      intros.
      assert(L:FP.smile fp fp2 \/ ~FP.smile fp fp2). apply classic.
      destruct L.
      right. split;auto.
      eapply npnswstep_star_reorder;eauto.
      rewrite pc_cur_tid. apply npnswstep_taustep in H as L;congruence.
      
      apply smile_conflict in H3.
      left. split;auto.
      eapply npnswstep_star_conflict in H3;eauto.
      rewrite pc_cur_tid. apply npnswstep_taustep in H as L;congruence.
    Qed.
    
    Corollary glob_npnsw_step_star_ex_alter:
      forall pc l fp pc' t fp2 pc2,
        glob_npnsw_step pc l fp pc'-> invpc pc-> atom_bit pc = O->
        t <> cur_tid pc ->
        tau_star glob_npnsw_step ({-|pc',t}) fp2 pc2->
        (npnsw_star_abort GE ({-|pc,t})) \/
        race glob_predict_star_alter pc \/
        FP.smile fp fp2 /\ exists pc1' : ProgConfig, tau_star glob_npnsw_step ({-|pc, t}) fp2 pc1' /\ (exists pc2' : ProgConfig,  glob_npnsw_step ({-|pc1', cur_tid pc}) tau fp pc2' /\ mem_eq_pc GE pc2 ({-|pc2', cur_tid pc2})).
    Proof.
      intros.
      eapply glob_npnsw_step_star_ex in H3 as ?;eauto.
      destruct H4;eauto.
      Hsimpl.
      destruct H5;auto.
      right;left;Hsimpl.
      
      apply npnswstep_taustep in H as ?;subst.
      apply FP.conflict_sym in H6.
      econstructor 1 with(t1:=t)(fp1:=x);eauto.
      econstructor;eauto. apply npnswstar_bit in H5. simpl in H5. congruence.
      econstructor.
      rewrite pc_cur_tid.
      rewrite <- FP.fp_union_emp with(fp:=fp).
      econstructor;eauto.
      constructor. auto.
      apply npnswstep_l2 in H;congruence.
      left;intro R;inversion R.
    Qed.
    
    Lemma glob_npnsw_step_star_evt_ex:
      forall pc l fp pc' t fp2 pc2 v pc3,
        glob_npnsw_step pc l fp pc'->invpc pc->
        t <> cur_tid pc ->
        tau_star glob_npnsw_step ({-|pc',t}) fp2 pc2 ->
        glob_step pc2 (evt v) FP.emp pc3->
        (npnsw_star_abort GE ({-|pc,t})) \/
        race glob_predict_star_alter pc \/
        FP.smile fp fp2 /\ exists pc1',tau_star glob_npnsw_step ({-|pc,t}) fp2 pc1' /\ exists pc2',glob_step pc1' (evt v) FP.emp pc2' /\ exists pc3',glob_npnsw_step ({-|pc2',cur_tid pc}) l fp pc3' /\ mem_eq_pc GE pc3 ({-|pc3',cur_tid pc3}).
    Proof.
      intros.
      pose wdge. pose modwdge.
      assert(atom_bit pc = O).
      assert(atom_bit pc2 = O). inversion H3;auto.
      apply npnswstar_bit in H2. apply npnswstep_l2 in H.
      simpl in *;congruence.
      
      eapply glob_npnsw_step_star_ex_alter in H as ?;eauto.
      destruct H5 as [|[|]];auto.
      Hsimpl.
      apply type_glob_step_exists in H3 as [].
      destruct x1;subst;try(inversion H3;fail).
      eapply mem_eq_globstep in H3;eauto.
      Hsimpl.
     
      apply npnswstep_l1 in H7;Hsimpl.
      assert(L1:cur_tid x1= cur_tid pc2). inversion H3;auto.
      eapply globstep_reorder_rule in H3;eauto;Hsimpl.
     
      apply npnsw_taustar_tid_preservation in H2 as ?.
      simpl in H13. rewrite <- H13 in *.
      apply npnsw_taustar_tid_preservation in H6 as ?.
      simpl in H14. rewrite H14,pc_cur_tid in H3.
      
      apply type_glob_step_elim in H3.
      apply npnswstep_taustep in H as ?;subst.
      apply npnswstep_l3 in H11;auto.
      right;right;Esimpl;eauto.
      eapply mem_eq_pc_trans;eauto.
      inversion H9 as (?&?&?&?);congruence.
      
      apply npnswstep_l3 in H7;auto;apply npnswstep_l2 in H7;auto.
      inversion H3;auto.
      apply npnsw_taustar_tid_preservation in H2. simpl in *;subst;auto.
      
      apply NNPP;intro. apply smile_conflict in H11;apply FP.emp_never_conflict in H11 as [];contradiction.
      
      eapply npnsw_taustar_thdpinv in H6;eauto.
      intro R;inversion R.
      intro R;inversion R.
    Qed.  
        
      

    




    (*Local Definition halfatomblockstep := ConflictReorder.halfatomblockstep GE.
     *)
    Local Arguments halfatomblockstep [GE].
    Lemma glob_npnsw_step_atomblockstep_ex:
      forall pc l fp pc' t fp2 pc2,
        glob_npnsw_step pc l fp pc'->invpc pc->
        t <> cur_tid pc->
        atomblockstep ({-|pc',t}) tau fp2 pc2->
        (halfatomblock_abort GE ({-|pc,t})) \/
        (FP.conflict fp fp2 /\ exists fp1 pc1,halfatomblockstep ({-|pc,t}) tau fp1 pc1 /\ FP.conflict fp fp1) \/
        FP.smile fp fp2 /\ exists pc1,atomblockstep ({-|pc,t}) tau fp2 pc1 /\ exists pc2',glob_npnsw_step ({-|pc1,cur_tid pc}) tau fp pc2' /\ mem_eq_pc GE pc2 ({-|pc2',cur_tid pc2}) .
    Proof.
      unfold atomblockstep.
      intros;Hsimpl.
      
      assert(R3:tau<>sw). intro T;inversion T.
      intros.
      apply npnswstep_taustep in H as ?;subst.
      apply npnswstep_l2 in H as ?.
      apply npnswstep_l1 in H as [?[]].
      rewrite <- pc_cur_tid with (pc:=pc) in H.
      assert(FP.smile fp fp2 \/ ~ FP.smile fp fp2). apply classic.
      destruct H6.
      right;right. split;auto.

      rewrite <- pc_cur_tid with(pc:=pc) in H.
      eapply atomblock_reorder in H as (?&?&?&?&?);eauto.
      eexists;split;eauto. 
      apply npnswstep_l3 in H7;auto.
      eexists;split;eauto.

      unfold atomblockN in H3.
      Hsimpl.
      apply tauN_taustar in H7.
      apply smile_conflict in H6.

      apply FP.emp_never_conflict in H6 as R;destruct R as [R _].
      destruct H5 as [|[|]];subst;try(inversion H;subst;contradiction).
      rewrite pc_cur_tid in H.
      assert(cur_tid pc' <> t). inversion H;subst;auto.
      eapply corestep_I_conflict in H6 as ?;eauto.
      destruct H9;auto.
      Hsimpl.
      right;left.
      Esimpl;eauto. econstructor;eauto.
    Qed.


 
    
    Lemma glob_npnsw_step_atomblockstarN_inv_ex_case1:
      forall pc l fp pc',
        invpc pc->
        glob_npnsw_step pc l fp pc'->
        forall t fp1 pc1 fp2 pc2,
          t <> cur_tid pc->
          tau_star glob_npnsw_step ({-|pc',t}) fp1 pc1 ->
          atomblockstep pc1 tau fp2 pc2->
          predicted_abort1 ({-|pc,t}) \/
          race glob_predict_star_alter pc \/
          FP.smile fp (FP.union fp1 fp2) /\ exists pc1',tau_star glob_npnsw_step ({-|pc,t}) fp1 pc1' /\ exists pc2',atomblockstep pc1' tau fp2 pc2'  /\ exists pc3',glob_npnsw_step ({-|pc2',cur_tid pc}) l fp pc3' /\ mem_eq_pc GE pc2 ({-|pc3',t}).
    Proof.
      intros. 
      eapply glob_npnsw_step_star_ex in H0 as ?;eauto.
      assert(R1:atom_bit pc1 = O).
      inversion H3 as (?&?&?&?&?).  inversion H6;auto.
      assert(R2:atom_bit ({-|pc',t}) = O).
      apply npnswstar_bit in H2;congruence.
      simpl in R2.
      assert(R:atom_bit pc = O). apply npnswstep_l2 in H0;congruence.
      apply npnswstep_taustep in H0 as ?;subst.
      destruct H4.
      {
        Hsimpl.
        destruct H5.
        left.

        apply FP.emp_never_conflict in H4 as R3.
        destruct R3.
        apply npnsw_step_thdpinv in H0 as ?;auto.
        apply npnsw_star_fpnotemp_cur_valid_id in H2;auto.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H0 as ?;eauto.
        simpl in H9.
        econstructor 2;eauto. instantiate(1:=pc).
        destruct pc,H9;simpl in *;subst;econstructor;eauto.
        
        right;left. Hsimpl.
        destruct pc as [thdp t0 m b]. simpl in R;subst.
        econstructor 1 with(t1:=t0)(t2:=t)(b1:=O)(b2:=O)(fp1:=fp)(fp2:=x);eauto.
        econstructor;eauto. simpl. apply tau_plus2star. eapply tau_plus_1;eauto.
        econstructor;eauto. apply npnswstar_bit in H5;auto.
        left;intro contra;inversion contra.
      }
      {
        destruct H4 as (?&?&?&?&?&?).
        eapply mem_eq_atomblockstep in H7 as ?;eauto.
        destruct H8 as (?&?&?).
    
        apply npnsw_taustar_tid_preservation in H2 as ?. simpl in H10.
        rewrite <- H10 in *.
        apply npnsw_taustar_thdpinv in H5 as ?;auto.
        eapply glob_npnsw_step_atomblockstep_ex in H6 as ?;eauto.
    
        destruct H12 as [|[|]].
        {
          left. econstructor;eauto. apply npnsw_taustar_tid_preservation in H5.
          simpl in *. rewrite H5,pc_cur_tid in H12. auto.
        }
        {
          destruct H12 as (?&?&?&?&?).
          destruct H13 as (?&?&?&?). simpl in *.
          right;left.
          apply npnsw_taustar_tid_preservation in H5 as ?.
          simpl in H17. rewrite H17 in H15. rewrite pc_cur_tid in H15.
          destruct pc as [thdp id m b];simpl in *. rewrite R in *.
          econstructor 1 with(t1:=t)(t2:=id)(b1:=I)(b2:=O)(fp1:=(FP.union fp1 x2))(fp2:=fp);eauto.
          econstructor;eauto.
          econstructor;eauto. rewrite pc_cur_tid.
          apply tau_plus2star. apply tau_plus_1. auto.
          right. intro contra;inversion contra.
    
          eapply conflict_union_ano in H14.
          rewrite FP.union_comm_eq. rewrite FP.conflict_sym. eauto.
        }
        {
          destruct H12 as (?&?&?&?&?&?).
          simpl in *.
          right;right. split.  apply fpsmile_sym;eapply fpsmile_union;eauto;apply fpsmile_sym;auto.
    
          apply npnsw_taustar_tid_preservation in H5 as ?.
          simpl in H16. rewrite H16 in H13. rewrite pc_cur_tid in H13.
          eexists;split;eauto.
          eexists;split;eauto.
          eexists;split;eauto.
          eapply mem_eq_pc_trans;eauto.
          apply atomblockstep_tid_preservation in H8.
          simpl in H8. congruence.
        }
      }
    Qed.
    
    Lemma glob_npnsw_step_atomblockstarN_inv_ex_case2:
      forall pc l fp pc',
        invpc pc->
        glob_npnsw_step pc l fp pc'->
        forall t fp1 pc1 fp2 pc2,
          t <> cur_tid pc->
          tau_star glob_npnsw_step ({-|pc',t}) fp1 pc1 ->
          haltstep pc1 tau fp2 pc2->
          predicted_abort1 ({-|pc,t})\/
          race glob_predict_star_alter pc \/
          FP.smile fp (FP.union fp1 fp2) /\ exists pc1',tau_star glob_npnsw_step ({-|pc,t}) fp1 pc1' /\ exists pc2',haltstep pc1' tau fp2 pc2' /\ exists pc3',glob_npnsw_step ({-|pc2',cur_tid pc}) l fp pc3' /\ mem_eq_pc GE pc2 ({-|pc3',t}).
    Proof.
      pose proof wdge as wdge.
      pose proof modwdge as modwdge.
      intros. 
      assert(R1:atom_bit pc1 = O). inversion H3;auto.
      assert(R2:atom_bit ({-|pc',t}) = O).
      apply npnswstar_bit in H2;congruence.
      simpl in R2.
      assert(R:atom_bit pc = O). apply npnswstep_l2 in H0;congruence.
      assert(R3:tau<>sw). intro R3;inversion R3.
      apply npnswstep_taustep in H0 as ?;subst.
      eapply glob_npnsw_step_star_ex in H0 as ?;eauto.
      destruct H4.
      {
        destruct H4 as [?[|]].
        left;auto. econstructor 2;eauto. instantiate(1:=pc).
        apply FP.emp_never_conflict in H4 as [].
        apply npnsw_step_thdpinv in H0 as ?;auto.
        apply npnsw_star_fpnotemp_cur_valid_id in H2 as ?;auto.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H0 as ?;eauto.
        destruct pc,H9;simpl in *;subst;econstructor;eauto.
        
        Hsimpl.
        destruct pc as [thdp t0 m b]. simpl in *;subst.
        right;left.
        econstructor 1 with(t1:=t0)(t2:=t)(b1:=O)(b2:=O)(fp1:=fp)(fp2:=x);eauto.
        econstructor;eauto. simpl. apply tau_plus2star. eapply tau_plus_1;eauto.
        econstructor;eauto. apply npnswstar_bit in H5;auto.
        left;intro contra;inversion contra.
      }
      destruct H4 as (?&?&?&?&?&?).
    
      eapply mem_eq_globstep in H7 as ?;eauto.
      destruct H8 as (?&?&?).
      apply npnswstep_l1 in H6 as [?[]].
      assert(fp2=FP.emp). inversion H8;auto. subst.
      eapply globstep_reorder_rule in H8 as ?;eauto.
      destruct H11 as (?&?&?&?&?).
    
      right;right. split. rewrite FP.fp_union_emp;auto.
      eexists;split;eauto.
      apply npnsw_taustar_tid_preservation in H2 as ?. simpl in H14.
      apply npnsw_taustar_tid_preservation in H5 as ?.
      rewrite H14 in H15. simpl in H15. rewrite H15 in H11.
      rewrite pc_cur_tid in H11.
    
      eexists;split;eauto.
      exists x4;split;eauto.
      destruct H10 as [|[]];subst;unfold glob_npnsw_step;auto.
      eapply mem_eq_pc_trans;eauto.
      assert(t = cur_tid x1). inversion H8;subst;simpl in *;subst;congruence.
      congruence.
    
      destruct H10 as [|[]];subst;inversion H6;auto.
      inversion H8;auto.
      apply npnsw_taustar_tid_preservation in H2.
      simpl in H2. rewrite <- H2. auto.
      apply FP.smile_conflict_compat;intro. apply FP.emp_never_conflict in H11 as [];contradiction.
      eapply npnsw_taustar_thdpinv in H5;eauto.
    Qed.
    
    
    
    Lemma atomblockstarN_length:
      forall i ltids pc fp pc',
        atomblockstarN i ltids pc fp pc'->
        length ltids=i.
    Proof.
      induction 1;intros;auto.
      simpl. rewrite IHatomblockstarN. auto.
    Qed.
    Lemma swstar_memeqpc:
      forall pc pc', sw_star glob_step pc pc'->mem_eq_pc GE pc' ({-|pc,cur_tid pc'}).
    Proof. induction 1;intros. rewrite pc_cur_tid. apply mem_eq_pc_refl. inversion H;subst. simpl in *. inversion IHsw_star as (?&?&?&?). simpl in *. repeat (split;auto). Qed.

    Lemma glob_npnsw_step_atomblockstarN_inv_ex_case:
      forall pc l fp pc',
        invpc pc->
        glob_npnsw_step pc l fp pc'->
        forall t fp1 pc1 ltids,
          t <> cur_tid pc->
          atomblockstarN 1 ltids ({-|pc',t}) fp1 pc1->
          (predicted_abort1 ({-|pc,t})) \/
          race glob_predict_star_alter pc \/
          FP.smile fp fp1 /\ exists pc',atomblockstarN 1 ltids ({-|pc,t}) fp1 pc'/\ exists pc'',glob_npnsw_step pc' l fp pc'' /\ mem_eq_pc GE pc1 ({-|pc'',cur_tid pc1}) /\ cur_tid pc'' = cur_tid pc.
    Proof.
      intros.
      inversion H2;subst.
      destruct H5.
      {
        eapply glob_npnsw_step_atomblockstarN_inv_ex_case1 in H0 as L1;eauto.
        destruct L1;auto.
        destruct H5;auto.
        destruct H5 as (?&?&?&?&?&?&?&?).
        right;right. split. inversion H7;subst. rewrite FP.fp_union_emp. auto.
        exists ({-|x0,cur_tid pc}).
        inversion H7;subst.
        split;simpl.
        assert(cur_tid ({-|pc,t}) = t). auto. rewrite <- H13.
        econstructor 2;eauto;[|try constructor].
        apply npnsw_taustar_thdpinv in H8 as L1;auto.
        apply atomblockstep_invpc_preserve in H9 as L2;auto.
        apply npnswstep_cur_valid_tid in H10 as L3;auto.
        apply atomblockstep_bitO in H9 as [].
        econstructor;[|constructor].
        destruct x0,L3;simpl in *;subst;econstructor;eauto.
        apply atomblockstep_bitO in H9 as [];auto.
        eexists;split;eauto. split.
        eapply swstar_memeqpc in H6.
        eapply mem_eq_pc_trans;eauto.
        eapply mem_eq_pc_change in H11;eauto.
    
        apply npnswstep_l1 in H10 as (?&?&?).
        destruct H13 as [|[]];subst;inversion H10;auto.
      }
      {
        eapply glob_npnsw_step_atomblockstarN_inv_ex_case2 in H0 as L1;eauto.
        destruct L1;auto.
        destruct H5;auto.
        right;right.
        destruct H5 as (?&?&?&?&?&?&?&?).
        split. inversion H7;subst. rewrite FP.fp_union_emp. auto.
        exists ({-|x0,cur_tid pc}).
        inversion H7;subst.
        split;simpl.
        assert(cur_tid ({-|pc,t}) = t). auto. rewrite <- H13.
        econstructor 2;eauto;[|try constructor].
        apply npnsw_taustar_thdpinv in H8 as L1;auto.
        apply type_glob_step_elim in H9 as L2.
        apply GE_mod_wd_tp_inv in L2;auto.
        apply npnswstep_cur_valid_tid in H10 as L3;auto.
        assert(atom_bit x0 = O). inversion H9;auto.
        econstructor;[|constructor].
        destruct x0,L3;simpl in *;subst;econstructor;eauto.
        inversion H9;auto.
        eexists;split;eauto. split.
        eapply swstar_memeqpc in H6.
        eapply mem_eq_pc_trans;eauto.
        eapply mem_eq_pc_change in H11;eauto.
    
        apply npnswstep_l1 in H10 as (?&?&?).
        destruct H13 as [|[]];subst;inversion H10;auto.
      }
    Qed.
    Lemma glob_npnsw_step_atomblockstarN_inv_ex_listnotmatch:
      forall i ltids fp1 pc3 pc l fp pc1 pc2,
        invpc pc->
        glob_npnsw_step pc l fp pc1->
        glob_step pc1 sw FP.emp pc2->
        atomblockstarN i ltids pc2 fp1 pc3->
        (forall j,List.nth_error ltids j <> Some (cur_tid pc))->
        (exists i l fp' pc',atomblockstarN i l ({-|pc,cur_tid pc2}) fp' pc' /\ predicted_abort1 pc') \/
        (race glob_predict_star_alter pc) \/ 
        (exists i l fp' pc',atomblockstarN (S i) l ({-|pc,cur_tid pc2}) fp' pc' /\ race glob_predict_star_alter pc' )\/
        exists pc',
          atomblockstarN i ltids ({-|pc,cur_tid pc2}) fp1 pc' /\
          exists pc'',
            glob_npnsw_step ({-|pc',cur_tid pc}) l fp pc'' /\
            mem_eq_pc GE pc3 ({-|pc'',cur_tid pc3}).
    Proof.
      pose wdge.
      induction i;intros.
      {
        inversion H2;subst.
        right;right;right. eexists;split;econstructor.
        apply npnswstep_l2 in H0 .
        inversion H1;subst;auto.
        split.
        simpl. rewrite pc_cur_tid. eauto.
        inversion H1;subst. apply mem_eq_pc_refl.
      }
      {
        apply atomblockstarN_SN_inv in H2 as (?&?&?&?&?&?&?&?).
        assert(cur_tid pc2 <> cur_tid pc). specialize (H3 0). rewrite H6 in H3. simpl in H3. intro. contradict H3. rewrite H7. reflexivity.
    
        assert(pc2=({-|pc1,cur_tid pc2})).
        inversion H1;subst;auto.
        rewrite H8 in H2. simpl in H2.
        eapply glob_npnsw_step_atomblockstarN_inv_ex_case in H2 as L;eauto.
        destruct L.
        
        left. Esimpl;eauto. econstructor. inversion H1;subst. simpl in *;subst.
        destruct H0 as [|[]];inversion H0;auto.
        
        destruct H9;auto.
    
        destruct H9 as (?&?&?&?&?&?&?).
        eapply mem_eq_atomblockstarN in H12 as ?;eauto.
        destruct H14 as (?&?&?).
    
        destruct i.
        inversion H14;subst.
        right;right;right. rewrite FP.fp_union_emp. eexists;split;eauto.
        apply npnsw_step_tid_preservation in H11 as ?.
        rewrite <- H13. rewrite <- H5. rewrite pc_cur_tid.
        eexists;split;eauto. inversion H4;subst;auto.
    
        apply atomblockstarN_invpc_preservation in H10 as ?;auto.
        apply npnsw_step_thdpinv in H11 as ?;auto.
        apply atomblockstarN_cur_valid_tid in H14 as ?;auto.
    
        apply atomblockstarN_atomO in H14 as L;destruct L.
        
        assert(glob_step x4 sw FP.emp ({-|x4,cur_tid x1})).
        destruct x4,H18;simpl in *;subst;econstructor;eauto.
        assert(pc_valid_tid x4 (cur_tid x1)). auto.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H11 as ?;eauto.
        apply atomblockstarN_atomO in H10 as ?.
        destruct H24.
        assert(glob_step x3 sw FP.emp ({-|x3,cur_tid x1})).
        destruct x3,H23;simpl in *;subst;econstructor;eauto.
    
        eapply IHi in H14 as ?;try apply H11;eauto.
        simpl in H27.
        destruct H27 as [|[|[]]].
        {
          Hsimpl. left.
          eapply atomblockstarN_1_cons_sw in H10;eauto.
          eapply atomblockstarN_cons' in H27;try apply H10;eauto.
          Esimpl;eauto.
        }
        {
          right;right;left.
          do 5 eexists;eauto. 
        }
        {
          destruct H27 as (?&?&?&?&?&?).
          simpl in H27.
          eapply atomblockstarN_1_cons_sw in H10;eauto.
          eapply atomblockstarN_cons in H27;eauto.
          right;right;left. do 5 eexists;eauto.
        }
        {
          destruct H27 as (?&?&?&?&?).
          eapply atomblockstarN_1_cons_sw in H10;eauto.
          eapply atomblockstarN_cons in H27;eauto.
          right;right;right. simpl in *. rewrite <- H6 in H27. rewrite  H5 in H27.
          eexists;split;eauto.
          apply npnsw_step_tid_preservation in H11.
          rewrite H13 in H11.
          rewrite H11 in *.
          eexists;split;eauto.
          eapply mem_eq_pc_trans;eauto.
          inversion H15 as (?&?&?&?);congruence.
        }
        apply npnsw_step_tid_preservation in H11.
        rewrite H11,H13.
        revert H6 H3;clear;intros.
        intro.
        specialize (H3 (S j)). subst.
        simpl in H3. contradiction.
    
        Omega.omega.
      }
    Qed.
    Definition list_matched{A:Type}(l:list A)(p:A):=
      exists i,List.nth_error l i = Some p.
    
    Lemma list_match:
      forall (A:Type)(l:list A)(p:A),
        list_matched l p->
        exists i,
          List.nth_error l i = Some p /\
          forall j,
            j<i->List.nth_error l j <> Some p.
    Proof.
      intros.
      destruct H.
      revert H.
      induction x using(well_founded_induction lt_wf);intros.
      assert((exists j,List.nth_error l j = Some p/\j<x) \/ ~(exists j,List.nth_error l j = Some p/\j<x)).
      apply classic.
      destruct H1.
      destruct H1 as (?&?&?).
      eapply H in H2;eauto.
      exists x. split;eauto.
    Qed.
    
    Lemma list_match_split:
      forall (A:Type)(i:nat)(l:list A)(p:A),
        List.nth_error l i = Some p->
        (forall j,j<i->List.nth_error l j <> Some p)->
        exists l1 l2,
          l = app l1 (cons p l2) /\ length l1 = i /\
          forall j,List.nth_error l1 j <> Some p.
    Proof.
      induction i;intros.
      inversion H;subst.
      destruct l eqn:?. inversion H2.
      inversion H2;subst.
      exists nil,l0. split;auto.
      split;auto.
      intros.
      rewrite Coqlib.nth_error_nil.
      intro. inversion H1.
    
      inversion H;subst.
      destruct l. inversion H2.
      eapply IHi in H2;eauto.
      destruct H2 as (?&?&?&?&?).
      exists (cons a x),x0. split;auto. rewrite H1. auto.
      split;auto. simpl. rewrite H2. auto.
    
      inversion H. rewrite H5.
      assert(length (cons a x) = S i). simpl. rewrite H2. auto.
    
      intros.
      assert(0<S i). Omega.omega.
      specialize (H0 0 H6).
      intro.
      unfold List.nth_error in H0.
      destruct j.
      compute in H7. contradiction.
      simpl in H7. apply H3 in H7;auto.
    
      intros.
      assert(List.nth_error (cons a l) (S j) = List.nth_error l j). auto.
      rewrite <- H3.
      apply H0.
      Omega.omega.
    Qed.
      
      
    
    
    
    Lemma nil_l1:
      forall A l1 l2,
        @app A l1 l2 = nil->
        l1 = nil /\ l2 = nil.
    Proof. destruct l1 eqn:?,l2 eqn:?;auto;inversion 1. Qed.
    Lemma atomblockstarN_ltid_split:
      forall i ltids pc fp pc',
        atomblockstarN i ltids pc fp pc'->
        forall l1 l2,
          ltids = app l1 l2 ->
          exists fp1 pc1 fp2,
            atomblockstarN (length l1) l1 pc fp1 pc1 /\
            atomblockstarN (length l2) l2 pc1 fp2 pc' /\
            FP.union fp1 fp2 =fp.
    Proof.
      intros. apply atomblockstarN_atomO in H as ?.
      destruct H1.
      revert l1 l2 H0.
      induction H;intros.
      symmetry in H0.
    
      apply nil_l1 in H0 as [];subst.
      do 3 eexists;split;econstructor;eauto. constructor;auto. rewrite FP.emp_union_fp;auto.
    
      destruct l1 eqn:?.
      {
        destruct l2 eqn:?;inversion H5;subst.
        exists FP.emp,pc,(FP.union (FP.union fp1 fp2) fp). split;constructor;auto.
        simpl.    
        econstructor 2;eauto.
        apply atomblockstarN_length in H4 as ?. rewrite H6. congruence.
      }
      {
        inversion H5;subst.
        apply atomblockstarN_atomO in H4 as ?.
        destruct H6 as (?&_).
        specialize (IHatomblockstarN H6 H2 l0 l2) as (?&?&?&?&?&?);auto.
        eapply cons_atomblock_1 in H7;eauto.
        do 3 eexists. split;eauto.
        split;eauto.
        rewrite <- H9.
        rewrite FP.fp_union_assoc;auto.
      }
    Qed.
    
    Lemma glob_npnsw_step_atomblockstarN_inv_ex:
      forall i ltids fp1 pc3 pc l fp pc1 pc2,
        invpc pc->
        glob_npnsw_step pc l fp pc1->
        glob_step pc1 sw FP.emp pc2->
        atomblockstarN i ltids pc2 fp1 pc3->
        (exists i l fp' pc',atomblockstarN i l ({-|pc,cur_tid pc2}) fp' pc' /\ predicted_abort1 pc') \/
        (race glob_predict_star_alter pc) \/ 
        (exists i l fp' pc',atomblockstarN (S i) l ({-|pc,cur_tid pc2}) fp' pc' /\ race glob_predict_star_alter pc' )\/
        (exists pc',
            atomblockstarN i ltids ({-|pc,cur_tid pc2}) fp1 pc' /\
            exists pc'',
              glob_npnsw_step ({-|pc',cur_tid pc}) l fp pc'' /\
              mem_eq_pc GE pc3 ({-|pc'',cur_tid pc3})) \/
        exists pc',
          atomblockstarN i ltids ({-|pc,cur_tid pc2}) (FP.union fp1 fp) pc' /\
          mem_eq_pc GE pc3 ({-|pc',cur_tid pc3}).
    Proof.
      intros.
      assert((exists j,List.nth_error ltids j = Some (cur_tid pc)) \/ ~ (exists j,List.nth_error ltids j = Some (cur_tid pc))).
      apply classic.
      destruct H3.
      {
        apply list_match in H3 as (j&?&?).
        apply list_match_split in H3 as (?&?&?&?&?);auto.
        clear H4.
        destruct j.
        {
          destruct x;inversion H5.
          simpl in H3.
          clear H5 H6. subst.
          apply atomblockstarN_length in H2 as ?.
          simpl in H3. rewrite <- H3 in H2.
          assert(cur_tid pc2 = cur_tid pc). inversion H2;auto.
          apply npnsw_step_tid_preservation in H0 as ?.
          assert(pc1 = pc2). inversion H1;subst;simpl in *;subst;auto.
          subst.
          rewrite H5 in H2.
          eapply npnswstep_cons_atomblockstarN in H0;eauto.
          right;right;right;right.
          eexists;split;eauto. rewrite H4. rewrite pc_cur_tid. rewrite H5. rewrite FP.union_comm_eq;eauto.
          rewrite pc_cur_tid. apply mem_eq_pc_refl.
        }
        
        eapply atomblockstarN_ltid_split in H3 as ?;eauto.
        destruct H4 as (?&?&?&?&?&?).
    
        rewrite H5 in H4.
        eapply glob_npnsw_step_atomblockstarN_inv_ex_listnotmatch in H4 as ?;eauto.
    
        destruct H9 as [|[|[]]];eauto.
        destruct H9 as (?&?&?&?&?).
        eapply atomblockstarN_invpc_preservation in H9 as L;eauto.
        eapply npnswstep_cur_valid_tid in H10 as L1;eauto.
        apply atomblockstarN_atomO in H9 as L2.  destruct L2 as [_ L2].
        assert(L3:glob_step x4 sw FP.emp ({-|x4,cur_tid pc})).
        destruct x4,L1;simpl in *;subst;econstructor;eauto.
        eapply atomblockstarN_cons_sw in H9;eauto.
        
        eapply mem_eq_atomblockstarN in H11 as ?;eauto.
        destruct H12 as (?&?&?).
    
        assert(cur_tid x5 =cur_tid pc). inversion H10 as [|[]];inversion H14;subst;auto.
        assert(cur_tid ({-|x5,cur_tid x2}) = cur_tid pc). inversion H12;auto.
        simpl in H15. rewrite H15 in *. rewrite <- H14 in H12. rewrite pc_cur_tid in H12.
    
        eapply npnswstep_cons_atomblockstarN in H10 as ?;eauto.
        eapply atomblockstarN_cons' in H16 as ?;eauto.
        simpl in H17.
    
        right;right;right;right.
        exists x6. inversion H13 as (_&_&?&_). rewrite H18. rewrite pc_cur_tid. split;auto.
    
        apply atomblockstarN_length in H2.
        rewrite <- H2.
        rewrite H3.
        rewrite H14 in H17.
        rewrite<- H8. rewrite FP.union_comm_eq with(fp1:=fp) in H17. rewrite FP.fp_union_assoc in H17.
        assert(S(j+S(length x0)) = (S j) + S(length x0)). auto.
        rewrite <- H5 in H19. rewrite H19 in H17.
        
        assert(length (app x (cons (cur_tid pc ) x0)) = length x + S(length x0)).
        apply List.app_length.
        rewrite H20.
        auto.
      }
      {
        assert(forall j,List.nth_error ltids j <> Some (cur_tid pc)).
        intro. intro. contradict H3. eauto.
        clear H3.
    
        eapply  glob_npnsw_step_atomblockstarN_inv_ex_listnotmatch in H0;eauto.
        destruct H0 as [|[|[]]];eauto.
      }
    Qed.  
    
    
    Lemma noevt_stepN_0:
      forall pc fp pc',
        noevt_stepN glob_step 0 pc fp pc'->
        fp=FP.emp /\ sw_star glob_step pc pc'.
    Proof.
      intros. remember 0. remember glob_step.
      induction H.
      split;auto. constructor.
      specialize (IHnoevt_stepN Heqn HeqP) as [];subst.
      rewrite FP.fp_union_emp. inversion H;subst.
      split;auto.
      eapply sw_star_cons;eauto.
      inversion Heqn.
    Qed.
    Lemma noevt_stepN_Si_inv:
      forall i pc fp pc',
        noevt_stepN glob_step (S i) pc fp pc'->
        exists pc1,sw_star glob_step pc pc1 /\
              exists fp1 pc2,glob_step pc1 tau fp1 pc2 /\
                        exists fp2,noevt_stepN glob_step i pc2 fp2 pc'/\
                              FP.union fp1 fp2 = fp.
    Proof.
      intros.
      remember (S i). remember glob_step.
      induction H. inversion Heqn.
      Hsimpl;subst.
      assert(fp=FP.emp). inversion H;auto. subst.
      eapply sw_star_cons in H;eauto.
    
      Esimpl;eauto.
    
      clear IHnoevt_stepN;subst.
      
      eexists;split. constructor. inversion Heqn;subst.
      do 3 eexists;eauto.
    Qed.
    
    Lemma noevt_stepN_IO:
      forall i pc fp pc',
        noevt_stepN glob_step i pc fp pc'->
        atom_bit pc = I ->
        atom_bit pc' = O->
        exists pc1 fp1,tau_star (type_glob_step core) pc fp1 pc1 /\
                  exists pc2,type_glob_step extat pc1 tau FP.emp pc2 /\
                        exists j fp2,noevt_stepN glob_step j pc2 fp2 pc' /\ j<i /\ FP.union fp1 fp2 = fp.
    Proof.
      induction i;intros.
      remember glob_step. remember 0.
      induction H. rewrite H0 in H1;inversion H1.
      subst. inversion H;subst. inversion H0.
      inversion Heqn.
      apply noevt_stepN_Si_inv in H .
      Hsimpl.
      eapply glob_sw_star_I in H;eauto. subst.
    
      destruct (atom_bit x1) eqn:?.
      {
        exists x,FP.emp;split. constructor.
        apply type_glob_step_exists in H2 as [j];destruct j;subst;try(inversion H;subst;simpl in *;subst;try inversion H0;try inversion Heqb;fail).
        assert(x0=FP.emp). inversion H;auto. subst.
        Esimpl;eauto.
      }
      {
        apply type_glob_step_exists in H2 as [j];destruct j;try(inversion H;subst;inversion H0;simpl in *;subst;try inversion Heqb;fail).
        eapply IHi in H3 as ?;eauto;Hsimpl.
        eapply tau_star_cons in H;eauto.
        Esimpl;eauto.
        rewrite <- H7. rewrite FP.fp_union_assoc;auto.
      }
    Qed.

    Lemma swstar_noevt_stepN:
      forall  pc pc',
        sw_star glob_step pc pc'->
        noevt_stepN glob_step 0 pc FP.emp pc'.
    Proof.
      induction 1. constructor.
      rewrite <- FP.fp_union_emp with(fp:=FP.emp).
      econstructor 2;eauto.
    Qed.
    Lemma swstar_l3:
      forall ge pc pc',
        sw_star (@glob_step ge) pc pc'->
        pc = pc' \/ glob_step pc sw FP.emp pc'.
    Proof.
      induction 1;intros.
      auto.
      destruct IHsw_star.
      subst;auto.
      right;inversion H;subst;inversion H1;subst;econstructor;eauto.
    Qed.
    Lemma noevt_stepN_Si_sp:
      forall i pc fp pc',
        noevt_stepN glob_step (S i) pc fp pc'->
        exists fp1 pc1,noevt_stepN glob_step i pc fp1 pc1/\
                  exists fp2 pc2,glob_step pc1 tau fp2 pc2 /\
                            sw_star glob_step pc2 pc' /\ FP.union fp1 fp2 = fp.
    Proof.
      induction i;intros.
      apply noevt_stepN_Si_inv in H.
      Hsimpl. apply noevt_stepN_0 in H1 as [];subst.
      apply swstar_noevt_stepN in H.
      Esimpl;eauto. rewrite FP.union_comm_eq;auto.
      
      apply noevt_stepN_Si_inv in H.
      Hsimpl.
      apply IHi in H1.
      Hsimpl.
      eapply cons_tau in H1;eauto.
      apply swstar_l3 in H as [].
      subst. Esimpl;eauto. rewrite FP.fp_union_assoc;auto.
      eapply cons_sw in H;eauto.
      Esimpl;eauto. rewrite <- H2, <- H5,FP.emp_union_fp,FP.fp_union_assoc;auto.
    Qed.
    Lemma noevt_stepN_cons_taustep:
      forall i pc fp pc' fp' pc'',
        noevt_stepN glob_step i pc fp pc'->
        glob_step pc' tau fp' pc''->
        noevt_stepN glob_step (S i) pc (FP.union fp fp') pc''.
    Proof.
      induction i;intros.
      apply noevt_stepN_0 in H as [];subst.
      apply swstar_l3 in H1 as [].
      subst. rewrite FP.union_comm_eq.  econstructor 3;eauto. constructor.
      econstructor;eauto. rewrite <- FP.fp_union_emp with(fp:=fp'). econstructor 3;eauto. constructor.
      
      apply noevt_stepN_Si_inv in H.
      Hsimpl.
      eapply IHi in H2;eauto.
      apply swstar_l3 in H as [].
      subst. rewrite<- FP.fp_union_assoc. econstructor 3;eauto.
      eapply cons_tau in H2;eauto.
      eapply cons_sw in H2;eauto.
      rewrite FP.emp_union_fp in H2.
      rewrite <- H3, <-FP.fp_union_assoc;auto.
    Qed.
    

    Lemma noevt_stepN_OI:
      forall i pc fp pc',
        noevt_stepN glob_step i pc fp pc'->
        atom_bit pc = O->
        atom_bit pc' = I->
        exists i1 fp1 pc1,noevt_stepN glob_step i1 pc fp1 pc1 /\
                   exists pc2, type_glob_step entat pc1 tau FP.emp pc2/\
                          exists i2 fp2,tau_N (type_glob_step core) i2 pc2 fp2 pc'/\
                                   i1+i2+1=i/\FP.union fp1 fp2 =fp.
    Proof.
      induction i;intros.
      apply noevt_stepN_0 in H as [].
      apply swstar_l1 in H2. rewrite H2 in H1;simpl in H1.
      rewrite H0 in H1;inversion H1.
      
      apply noevt_stepN_Si_sp in H.
      Hsimpl.
      apply glob_sw_star_I in H3;auto. subst.
      destruct (atom_bit x0) eqn:?.
      {
        eapply type_glob_step_exists in H2 as [j ];destruct j;subst;try(inversion H2;subst;simpl in *;subst;try inversion Heqb;try inversion H1;fail).
        assert(x1=FP.emp). inversion H2;auto. subst.
        rewrite FP.fp_union_emp.
        Esimpl;eauto. constructor.
        Omega.omega.
        rewrite FP.fp_union_emp. auto.
      }
      {
        eapply IHi in H;eauto.
        Hsimpl.
        apply type_glob_step_exists in H2 as [].
        destruct x8;subst;try(inversion H2;subst;inversion Heqb;inversion H1;fail).
        assert(tau_N (type_glob_step core) 1 x0 x1 pc').
        rewrite <- FP.fp_union_emp with(fp:=x1).
        econstructor;eauto. constructor.
        eapply tau_N_cons in H5;eauto.
        Esimpl;eauto. 
        Omega.omega.
        rewrite <- FP.fp_union_assoc;auto.
      }
      apply swstar_l3 in H3 as [];subst;auto.
      inversion H3;subst. inversion H1.
    Qed.
    
    Lemma noevt_stepN_Si_inv2:
      forall i pc fp pc',
        invpc pc->
        noevt_stepN glob_step (S i) pc fp pc'->
        atom_bit pc = O->
        atom_bit pc' = O ->
        exists pc1,sw_star glob_step pc pc1 /\
              (( exists fp1 pc2 fp2 j,glob_step pc1 tau fp1 pc2 /\ atom_bit pc2 = atom_bit pc1 /\noevt_stepN glob_step j pc2 fp2 pc' /\ j<=i /\ FP.union fp1 fp2 = fp) \/
              (exists fp1 pc2 fp2 j, atomblockstep pc1 tau fp1 pc2/\ cur_valid_id pc2 /\ noevt_stepN glob_step j pc2 fp2 pc' /\ j<=i /\ FP.union fp1 fp2 = fp)).
    Proof.
      induction i using (well_founded_induction lt_wf);intros pc fp pc' invpc0;intros.
      pose proof H0 as T1.
      apply noevt_stepN_Si_inv in H0;Hsimpl.
      exists x;split;auto.
    
      destruct (atom_bit x1) eqn:?.
      {
        {
          apply glob_sw_star_bit_preservation in H0.
          left.
          Esimpl;eauto.
          congruence.
        }
      }
      {
        apply noevt_stepN_IO in H4 as (?&?&?&?&?&?&?&?&?);auto.
        apply type_glob_step_exists in H3 as [].
        apply glob_sw_star_bit_preservation in H0 as L.
        rewrite H1 in L.
        destruct x8;try(inversion H3;simpl in *;subst;inversion H0;simpl in *;subst;inversion Heqb;fail).
        right.
        assert(x0=FP.emp). inversion H3;auto. subst.
        apply tau_star_tau_N_equiv in H4 as [].
        destruct H8 as (H8&T2).
        do 5 eexists;[|split];eauto.
        split;auto. eexists. esplit;esplit;eauto.
        pose wdge.
        assert(invpc x5).
        assert(invpc x). apply swstar_l1 in H0. rewrite H0;auto.
        assert(invpc x1). apply type_glob_step_elim in H3. eapply GE_mod_wd_tp_inv;eauto.
        assert(invpc x3). apply tauN_taustar in H4. apply core_tau_star_star in H4 as [].
        eapply GE_mod_wd_star_tp_inv2;eauto.
        apply type_glob_step_elim in H6. eapply GE_mod_wd_tp_inv;eauto.
        
        split. inversion H6;subst. eapply gettop_valid_tid;eauto. solv_thread.
        intro. inversion H6;solv_thread.
        Esimpl;eauto.
        Omega.omega.
        rewrite T2,FP.emp_union_fp;auto.
      }
    Qed.

      
    Lemma globstep_nothalted:
      forall ge pc l fp pc',
        @glob_step ge pc l fp pc'->
        l <> sw->
        ~ThreadPool.halted pc.(thread_pool) pc.(cur_tid).
    Proof.
      intros.
      intro.
      inversion H;subst;solv_thread.
    Qed.
    Lemma npstep_nothalted:
      forall ge pc l fp pc',
        @np_step ge pc l fp pc'->
        ~ ThreadPool.halted pc.(thread_pool) pc.(cur_tid).
    Proof.
      intros;intro.
      inversion H;subst;solv_thread.
    Qed.
    Lemma globstep_validtid:
      forall ge pc l fp pc',
        @glob_step ge pc l fp pc'->
        l <> sw ->
        ThreadPool.inv pc.(thread_pool)->
        ThreadPool.valid_tid pc.(thread_pool) pc.(cur_tid).
    Proof. intros;inversion H;subst;try contradiction;eapply gettop_valid_tid;eauto. Qed.
    Lemma globstep_pc_valid_curtid:
      forall ge pc l fp pc',
        ThreadPool.inv pc.(thread_pool)->
        @glob_step ge pc l fp pc'->
        l <> sw->
        pc_valid_tid pc pc.(cur_tid).
    Proof.
      intros. eapply globstep_nothalted in H0 as L1;auto. eapply globstep_validtid in H0 as L2;eauto. split;auto. Qed.
    Lemma noevt_stepN_cur_tid_not_valid_Si:
      forall i pc fp pc',
        invpc pc->
        noevt_stepN glob_step i pc fp pc'->
        i > 0 ->
        ~ cur_valid_id pc->
        exists pc1,
          glob_step pc sw FP.emp pc1 /\ cur_valid_id pc1 /\
          noevt_stepN glob_step i pc1 fp pc'.
    Proof.
      pose wdge. pose modwdge.
      intros i pc fp pc' R;intros. inversion H;subst. inversion H0.
      assert(fp0=FP.emp). inversion H2;auto. subst.
      rewrite FP.emp_union_fp.
      exists pc'0. split;auto. split;auto.
    
      inversion H2;subst;split;auto.
    
      contradict H1.
      eapply globstep_pc_valid_curtid;eauto. intro contra;inversion contra.
    Qed.  
    
    
    Lemma race_changetid:
      forall pc,
        race (@glob_predict_star_alter GE )pc->
        forall t,
          race glob_predict_star_alter ({-|pc,t}).
    Proof.
      inversion 1;subst.
      intros.
      econstructor;eauto.
      inversion H1;subst;econstructor;eauto.
      inversion H2;subst;econstructor;eauto.
    Qed.
    Lemma mem_eq_predict:
      forall pc pc',
        mem_eq_pc GE pc pc'->
        forall t b fp,
          glob_predict_star_alter pc t b fp->
          glob_predict_star_alter pc' t b fp.
    Proof.
      pose wdge. pose modwdge.
      intros. apply mem_eq_pc_change with(t:=t) in H.
      inversion H0;subst.
      eapply mem_eq_npnsw_step_star in H1 as (?&?&?);eauto.
      econstructor;eauto. inversion H as (?&?&?&?);simpl in *;subst;congruence.
      inversion H4 as (?&?&?&?);simpl in *;subst;congruence.
    
      eapply mem_eq_npnsw_step_star in H1 as (?&?&?);eauto.
      eapply mem_eq_globstep in H3 as (?&?&?);eauto.
      eapply mem_eq_corestar in H4 as (?&?&?);eauto.
      econstructor;eauto. inversion H as (?&?&?&?);simpl in *;subst;congruence.
    Qed.
    Lemma mem_eq_race:
      forall pc pc',
        mem_eq_pc GE pc pc'->
        race glob_predict_star_alter pc ->
        race glob_predict_star_alter pc'.
    Proof. inversion 2;subst;econstructor;eauto;eapply mem_eq_predict;eauto. Qed.

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
    Lemma swstar_l:
      forall pc pc',
        sw_star glob_step pc pc'->
        pc = pc' \/ @glob_step GE pc sw FP.emp pc' /\ cur_tid pc <> cur_tid pc'.
    Proof.
      induction 1;intros. auto.
      destruct IHsw_star. subst.
      assert(cur_tid s1 = cur_tid s3 \/ ~ cur_tid s1 = cur_tid s3).
      apply classic.
      destruct H1;auto. inversion H;subst. left. simpl in *;congruence.
      assert(cur_tid s1 = cur_tid s3 \/ ~ cur_tid s1 = cur_tid s3).
      apply classic.
      assert(glob_step s1 sw FP.emp s3).
      inversion H;subst;inversion H1. inversion H3;subst;auto.
      econstructor;eauto.
      destruct H2. inversion H3;subst;left;eauto. simpl in *;auto. congruence.
      right;eauto.
    Qed.
    
    Lemma atomblockstarN_pc_valid_tid_last:
      forall i l fp pc pc',
      forall (v1:ThreadPool.inv pc.(thread_pool)),
        atomblockstarN (S i) l pc fp pc'-> 
        pc_valid_tid pc (cur_tid pc').
    Proof.
      induction i;intros.
      inversion H;subst. inversion H4;clear H4;subst.
      apply swstar_l in H3.
      
      assert(cur_tid pc2 = cur_tid pc1). destruct H2.
      eapply atomblockstep_tid_preservation;eauto.
      inversion H2;subst;auto.
      destruct H3. subst.
      assert(cur_valid_id pc1). destruct H2.
      apply atomblockstep_cur_valid_id in H2;auto. eapply npnsw_taustar_thdpinv;eauto.
      unfold haltstep in H2. apply type_glob_step_cur_valid_id in H2;auto.
      apply npnsw_taustar_thdpinv in H1;auto.
      intro R;inversion R.
      rewrite H4. eapply npnsw_taustar_pc_valid_tid_backwards_preservation in H1;eauto.
      destruct H3. assert(pc_valid_tid pc' pc'.(cur_tid)).
      inversion H3;subst;split;auto.
      eapply npnsw_taustar_pc_valid_tid_backwards_preservation;eauto.
      destruct H2.
      unfold atomblockstep in H2. Hsimpl. unfold atomblockN in H7.
      Hsimpl.
      apply type_glob_step_elim in H9. apply type_glob_step_elim in H7.
      apply tauN_taustar in H8. apply corestar_globstar in H8.
      apply tau_star_to_star in H8 as [].
      eapply star_cons_step in H9 as [];eauto.
      eapply star_step in H7;eauto.
      eapply star_cons_step in H3 as [];eauto.
      eapply pc_valid_tid_back_star in H3;eauto.
      apply npnsw_taustar_thdpinv in H1;auto.

      apply npnsw_taustar_thdpinv in H1 as ?;auto.
      apply type_glob_step_elim in H2.
      eapply GE_mod_wd_tp_inv in H2 as ?;eauto.
      eapply pc_valid_tid_back_norm in H3;eauto.
      eapply pc_valid_tid_back_norm in H2;eauto.

      inversion H;subst.
      apply npnsw_taustar_thdpinv in H1 as ?;auto.
      assert (tau_star glob_step pc1  fp2 pc2).
      destruct H2. unfold atomblockstep in H2. Hsimpl. unfold atomblockN in H5;Hsimpl.
      apply type_glob_step_elim in H5. apply type_glob_step_elim in H7.
      apply tauN_taustar in H6. apply corestar_globstar in H6.
      apply tau_plus_1 in H7.
      eapply tau_star_plus in H7;eauto.
      eapply tau_plus_cons in H5;eauto.
      eapply tau_plus2star in H5.
      rewrite FP.fp_union_emp in H5. rewrite FP.emp_union_fp in H5.
      eauto.

      eapply type_glob_step_elim in H2;eauto.
      apply tau_plus2star.
      econstructor;eauto. 

      eapply GE_mod_wd_star_tp_inv in H5 as ?;auto.
      
      eapply IHi in H4;eauto.
      eapply tau_star_to_star in H5 as [].
      eapply pc_valid_tid_back_star in H5;eauto. eapply npnsw_taustar_pc_valid_tid_backwards_preservation;eauto.
      apply swstar_l in H3. destruct H3. congruence.
      destruct H3. eapply pc_valid_tid_back_norm ;eauto.
      apply swstar_l in H3;destruct H3;subst;auto.
      destruct H3. apply GE_mod_wd_tp_inv in H3;eauto.
    Qed.
    Lemma atomblockstarN_globstar:
      forall i l fp pc pc',
        atomblockstarN i l pc fp pc'->
        exists l',
          star glob_step pc l' fp pc'.
    Proof.
      induction i;intros.
      inversion H;subst. eexists;econstructor.
      inversion H;subst.
      apply IHi in H4 as [].
      apply swstar_l in H3.
      assert(exists l, star glob_step pc2 l FP.emp pc3).
      destruct H3. subst. eexists;econstructor.
      destruct H3. eexists. rewrite <- FP.fp_union_emp with(fp:=FP.emp);econstructor 2;eauto. constructor.
      assert(exists l,star glob_step pc1 l fp2 pc2).
      destruct H2. eapply atomblockstep_globstar in H2;eauto.
      apply type_glob_step_elim in H2. eexists. rewrite <- FP.fp_union_emp with(fp:=fp2). econstructor 2;eauto. constructor.
      apply npnsw_taustar_to_taustar in H1. apply tau_star_to_star in H1 as [].
      Hsimpl.
      eapply cons_star_star in H5;eauto.
      eapply cons_star_star in H4;eauto.
      eapply cons_star_star in H0. eauto.
      rewrite FP.fp_union_emp in H4.
      eauto.
    Qed.
    Lemma noevt_stepN_Si_to_atomblockstarN:
      forall i pc fp pc',
        noevt_stepN glob_step i pc fp pc'->i>0->atom_bit pc = O -> atom_bit pc' = O->invpc pc->
        exists pc1,sw_star glob_step pc pc1 /\
              (
                (exists i l fp' pc2,atomblockstarN i l pc1  fp' pc2 /\ predicted_abort1 pc2) \/
                (race glob_predict_star_alter pc1) \/ 
                (exists j l fp' pc2,atomblockstarN (S j) l pc1 fp' pc2 /\ race glob_predict_star_alter pc2 )\/
                (exists j l fp' pc2,atomblockstarN j l pc1 fp' pc2 /\ 
                               exists fp'' pc3, npnsw_or_sw_star pc2 fp'' pc3 /\
                               mem_eq_pc GE pc' ({-|pc3,cur_tid pc'}) /\ FP.union fp' fp'' = fp)).
    Proof.
      pose wdge. pose modwdge.
      induction i using (well_founded_induction lt_wf).
      intros.
    
      destruct i.
      inversion H1.
      clear H1. rename H2 into H1. rename H3 into H2. rename H4 into H3.
      apply noevt_stepN_Si_inv2 in H0 as ?;auto.
      destruct H4 as (?&?&?).
      
      destruct H5.
      {
        destruct H5 as (?&?&?&?&?&?&?&?&T1).
        apply type_glob_step_exists in H5 as [].
        apply glob_tau_no_atom_type in H5 as ?;auto.
        destruct H9.
        {
          eexists;split;eauto.
          subst.
          assert(x0=FP.emp). inversion H5;auto. subst.
          assert(atomblockstarN 1 (cons (cur_tid x) nil) x (FP.union (FP.union FP.emp FP.emp) FP.emp) x1).
          econstructor. constructor. right;eauto. constructor. constructor. inversion H5;auto.
          assert(atom_bit x1 = O). inversion H5;auto.
          destruct x3.
          {
            apply noevt_stepN_0 in H7 as [].
            right;right;right. do 5 eexists;eauto.
            exists FP.emp,pc'. rewrite pc_cur_tid.
            Esimpl.
            eapply swstar_cons_npnsw_or_sw_star;eauto. econstructor;constructor.
            apply mem_eq_pc_refl.
            subst.
            repeat rewrite FP.fp_union_emp;auto.
          }
          
          apply H in H7 as (?&?&?);auto.
          eapply atomblockstarN_cons_swstar in H9;eauto.
          destruct H11 as [|[|[]]].
          {
            left. Hsimpl. eapply atomblockstarN_cons' in H11;eauto. Esimpl;eauto.
          }
          {
            right;right;left.
            do 5 eexists;eauto.  
          }
          {
            right;right;left.
            destruct H11 as (?&?&?&?&?&?).
            eapply atomblockstarN_cons in H11;eauto.
            do 5 eexists;eauto.
          }
          {
            right;right;right.
            destruct H11 as (?&?&?&?&?&?).
            eapply atomblockstarN_cons in H11;eauto.
            repeat rewrite FP.emp_union_fp in *.
            do 5 eexists;eauto.
          }
          Omega.omega.
          Omega.omega.
          apply swstar_l1 in H4.
          apply type_glob_step_elim in H5.
          eapply GE_mod_wd_tp_inv in H5;eauto.
          rewrite H4;auto.
        }
        {
          apply npnswstep_l3 in H5;auto. clear H9.
          assert(atom_bit x1 = O). apply swstar_l1 in H4. rewrite H4 in H6. simpl in H6. congruence.
          assert(x3<S i). Omega.omega.
          apply swstar_l1 in H4 as ?.
          assert(invpc x). rewrite H11. auto.
          apply npnsw_step_thdpinv in H5 as ?;auto.
          destruct x3.
          apply noevt_stepN_0 in H7 as [];subst.
          eexists;split;eauto.
          right;right;right.
          exists 0,nil,FP.emp,x. split. constructor.
          destruct H5 as [|[]];inversion H5;subst;auto.
          exists (FP.union x0 FP.emp),x1. split. exists (cons tau nil). eapply star_step;eauto.
          left;eauto. constructor.
    
          apply swstar_memeqpc in H14;auto.
          
          eapply H in H7 as ?;eauto.
          destruct H14 as (?&?&?).
          
          destruct H15 as [|[|[]]].
          {
            Hsimpl.
            destruct x6.
            {
              inversion H15;subst;clear H15.
              apply swstar_l in H14.
              destruct H14. subst.
              eapply npnswstep_predicted_abort in H16;eauto;try congruence.
              Esimpl;eauto. left;Esimpl;eauto. constructor. congruence.

              destruct H14.
              eapply npnswstep_sw_predicted_abort1 in H16;eauto.
              destruct H16.
              Hsimpl.
              assert(sw_star glob_step pc ({-|x,x5})).
              rewrite H11;simpl. rewrite H11 in H16;simpl in H16.
              econstructor 2;[|constructor].
              destruct pc,H16;simpl in *;subst;econstructor;eauto.
              Esimpl;eauto. left;Esimpl;eauto.
              constructor.
              rewrite H11;simpl;congruence.

              Esimpl;eauto.
            }
            
            apply swstar_l1 in H14 as ?.
            assert(invpc x5). rewrite H17;auto.
            apply atomblockstarN_cur_valid_tid in H15 as ?;auto;try Omega.omega.
            assert(glob_step x1 sw FP.emp x5).
            destruct x1,x5,H19;simpl in *;subst;inversion H17;subst;rewrite H9;econstructor;eauto.
            
            eapply glob_npnsw_step_atomblockstarN_inv_ex in H5 as ?;try apply H15;eauto.
            destruct H21 as [|[|[|[]]]];Hsimpl.
            {
              enough(sw_star glob_step pc ({-|x,cur_tid x5})).
              Esimpl;eauto. left;Esimpl;eauto.
              assert(pc_valid_tid x1 (cur_tid x5)).
              inversion H20;subst;split;auto.
              eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
              rewrite H11 in *;simpl in *.
              econstructor 2;[|constructor].
              destruct pc,H5;simpl in *;subst. rewrite H1. econstructor;eauto.
            }
            {
              enough(sw_star glob_step pc ({-|x,cur_tid x5})).
              Esimpl;eauto. right;left.
              inversion H21;subst;econstructor;eauto.
              inversion H24;subst;[econstructor|econstructor 2];eauto.
              inversion H25;subst;[econstructor|econstructor 2];eauto.

              
              assert(pc_valid_tid x1 (cur_tid x5)).
              inversion H20;subst;split;auto.
              eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
              rewrite H11 in *;simpl in *.
              econstructor 2;[|constructor].
              destruct pc,H5;simpl in *;subst. rewrite H1. econstructor;eauto.
            }
            {
              enough(sw_star glob_step pc ({-|x,cur_tid x5})).
              Esimpl;eauto. right;right;left.
              Esimpl;eauto.
              assert(pc_valid_tid x1 (cur_tid x5)).
              inversion H20;subst;split;auto.
              eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
              rewrite H11 in *;simpl in *.
              econstructor 2;[|constructor].
              destruct pc,H5;simpl in *;subst. rewrite H1. econstructor;eauto.
            }
            {
              pose proof H23 as R1.
              apply mem_eq_predicted_abort1 in H23;auto.
              assert(sw_star glob_step pc ({-|x,cur_tid x5})).
              assert(pc_valid_tid x1 (cur_tid x5)).
              inversion H20;subst;split;auto.
              eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
              rewrite H11 in *;simpl in *.
              econstructor 2;[|constructor].
              destruct pc,H5;simpl in *;subst. rewrite H1. econstructor;eauto.

              assert(cur_tid x11 = cur_tid x9 \/ cur_tid x11 <> cur_tid x9).
              apply classic.
              destruct H25.
              {
                rewrite <- H25,pc_cur_tid in H23.
                enough(invpc x10). enough(atom_bit x10 = O).
                eapply npnswstep_predicted_abort in H22;eauto.
                apply predicted_abort1_sw in H22 as ?;auto.
                assert(glob_step x10 sw FP.emp ({-|x10,cur_tid x})).
                destruct x10,H28;simpl in *;subst;econstructor;eauto.
                eapply atomblockstarN_cons_sw in H21;eauto.
                Esimpl;eauto. left;Esimpl;eauto.
                apply atomblockstarN_atomO in H21 as [];auto.
                apply atomblockstarN_invpc_preservation in H21;auto.
              }
              {
                enough(invpc x10). enough(atom_bit x10 = O).
                eapply npnswstep_sw_predicted_abort1 in H22 as ?;try apply H23;eauto.
                destruct H28.
                {
                  Hsimpl. simpl in *.
                  assert(glob_step x10 sw FP.emp ({-|x10,x12})).
                  destruct x10,H28;simpl in *;subst;econstructor;eauto.
                  eapply atomblockstarN_cons_sw in H21;eauto.
                  Esimpl;eauto. left;Esimpl;eauto.
                }
                {
                  assert(race glob_predict_star_alter x10).
                  inversion H28;subst;econstructor;eauto.
                  inversion H30;subst;[econstructor|econstructor 2];eauto.
                  inversion H31;subst;[econstructor|econstructor 2];eauto.
                  Esimpl;eauto. right;right;left;Esimpl;eauto.
                }
                apply atomblockstarN_atomO in H21 as ?.
                apply atomblockstarN_pc_valid_tid_last in H15;auto.
                rewrite H17 in H15.
                eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
                rewrite H11 in H5.
                apply npnswstep_l2 in H22 as ?.
                simpl in H29;rewrite H27 in H29.
                enough(pc_valid_tid x11 (cur_tid x9)).
                destruct x11,H30;simpl in *;subst;econstructor;eauto.
                rewrite H11 in H21. simpl in H21.

                apply predicted_abort1_sw in H16;auto.
                destruct R1;Hsimpl;simpl in *.
                destruct H16. split;congruence.
                apply npnsw_step_thdpinv in H22;auto.
                destruct R1. simpl in *. unfold invpc. congruence.
                apply atomblockstarN_atomO in H21 as [];auto.
                apply atomblockstarN_invpc_preservation in H21;auto.
              }
            }
            {
              eapply mem_eq_predicted_abort1 in H22;eauto.
              enough(sw_star glob_step pc ({-|x,cur_tid x5})).
              apply predicted_abort1_sw in H22 as ?;auto.
              assert(glob_step x10 sw FP.emp ({-|x10,cur_tid x9})).
              apply atomblockstarN_atomO in H21 as [].
              destruct x10,H24;simpl in *;subst. econstructor;eauto.
              eapply atomblockstarN_cons_sw in H21 as ?;eauto.
              Esimpl;eauto. left. Esimpl;eauto.
              apply atomblockstarN_invpc_preservation in H21;eauto.
              assert(pc_valid_tid x1 (cur_tid x5)).
              inversion H20;subst;split;auto.
              eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
              rewrite H11 in *;simpl in *.
              econstructor 2;[|constructor].
              destruct pc,H5;simpl in *;subst. rewrite H1. econstructor;eauto.
            }
          }
          {
            apply swstar_l1 in H14.
            rewrite H14 in H15.
            apply race_changetid with (t:=cur_tid x1) in H15. simpl in H15.
            rewrite pc_cur_tid in H15.
            eapply npnsw_step_race_glob_predict_star_alter_cons_2 in H15;eauto.
            destruct H15;eauto.
            Hsimpl.
            rewrite H11 in H15.
            assert(sw_star glob_step pc ({-|x,x6})).
            rewrite H11. simpl.
            econstructor 2;[|constructor].
            destruct pc,H15;simpl in *;subst.
            econstructor;eauto.
            Esimpl;eauto. left. Esimpl;eauto. constructor.
            rewrite H11;simpl;congruence.
          }
          {
            destruct H15 as (?&?&?&?&?&?).
            apply swstar_l1 in H14 as ?.
            assert(invpc x5). rewrite H17;auto.
            apply atomblockstarN_cur_valid_tid in H15 as ?;auto;try Omega.omega.
            assert(glob_step x1 sw FP.emp x5).
            destruct x1,x5,H19;simpl in *;subst;inversion H17;subst;rewrite H9;econstructor;eauto.
            eapply glob_npnsw_step_atomblockstarN_inv_ex in H5 as ?;eauto.
    
            destruct H21 as [|[|[|[]]]].
            {
              Hsimpl.
              enough(sw_star glob_step pc ({-|x,cur_tid x5})).
              Esimpl;eauto. left. Esimpl;eauto.
              econstructor 2;[|constructor].
              enough(pc_valid_tid pc (cur_tid x5)). destruct pc,H23;simpl in *;subst.
              rewrite H11;econstructor;eauto.
              rewrite H11 in H5.
              eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
              rewrite H17 in H19. auto.
            }
            {
              eexists;split;eauto.
            }
            {
              destruct H21 as (?&?&?&?&?&?).
              assert(glob_step x sw FP.emp ({-|x,cur_tid x5})).
              apply atomblockstarN_atomO in H21 as ?;auto. destruct H23.
              apply atomblockstarN_cur_valid_tid in H21;auto.
              destruct x,H21;simpl in *;subst;rewrite H23;econstructor;eauto.
              Omega.omega.
    
              assert(sw_star glob_step pc ({-|x,cur_tid x5})).
              revert H4 H23. clear.
              induction 1;intros. econstructor;eauto. constructor.
              econstructor;eauto.
              exists ({-|x,cur_tid x5});split;auto.
              right;right;left.
              do 5 eexists;eauto.
            }
            {
              destruct H21 as (?&?&?&?&?).
              eapply mem_eq_race in H16;try apply H23.
              eapply race_changetid with(t:=cur_tid x11) in H16.
              simpl in H16. rewrite pc_cur_tid in H16.
              eapply npnsw_step_race_glob_predict_star_alter_cons_2 in H22;eauto.
              assert(glob_step x sw FP.emp ({-|x,cur_tid x5})).
              apply atomblockstarN_atomO in H21 as ?;auto. destruct H24.
              apply atomblockstarN_cur_valid_tid in H21;auto.
              destruct x,H21;simpl in *;subst;rewrite H24;econstructor;eauto.
              Omega.omega.
              
              assert(sw_star glob_step pc ({-|x,cur_tid x5})).
              revert H4 H24. clear.
              induction 1;intros. econstructor;eauto. constructor.
              econstructor;eauto.
              destruct H22.
              Focus 2.
              {
                apply race_changetid with(t:=cur_tid x10) in H22.
                simpl in H22. rewrite pc_cur_tid in H22.
                eexists;split;eauto.
                right;right;left.
                do 5 eexists;eauto.
              }
              Unfocus.
              Hsimpl. simpl in *.
              Esimpl;eauto. left.
              assert(glob_step x10 sw FP.emp ({-|x10,x12})).
              apply atomblockstarN_atomO in H21 as [].
              destruct x10,H22;simpl in *;subst;econstructor;eauto.
              eapply atomblockstarN_cons_sw in H21;eauto.
              Esimpl;eauto. simpl. eapply atomblockstarN_invpc_preservation;eauto.
            }
            {
              destruct H21 as (?&?&?).
              assert(glob_step x sw FP.emp ({-|x,cur_tid x5})).
              apply atomblockstarN_atomO in H21 as ?;auto. destruct H23.
              apply atomblockstarN_cur_valid_tid in H21;auto.
              destruct x,H21;simpl in *;subst;rewrite H23;econstructor;eauto.
              Omega.omega.
              
              assert(sw_star glob_step pc ({-|x,cur_tid x5})).
              revert H4 H23. clear.
              induction 1;intros. econstructor;eauto. constructor.
              econstructor;eauto.
              
              eapply mem_eq_race in H22;eauto.
              apply race_changetid with (t:=cur_tid x10) in H22;simpl in H22;rewrite pc_cur_tid in H22.
              eexists;split;eauto.
              right;right;left.
              do 5 eexists;eauto.
            }
          }
          {
            destruct H15 as (?&?&?&?&?&?&?&?&?).
            destruct x6.
            {
              inversion H15;subst.
              eexists;split;eauto.
              right;right;right.
              do 5 eexists. constructor. apply npnswstep_l2 in H5;congruence.
              eapply swstar_cons_npnsw_or_sw_star in H14;eauto.
              eapply npnsw_step_cons_npnsw_or_sw_star in H5;eauto.
              destruct H17.
              rewrite <-H19,FP.emp_union_fp.
              Esimpl;eauto.
            }
            {
              assert(invpc x5).
              apply swstar_l1 in H14 as ?. rewrite H18;auto.
              apply atomblockstarN_cur_valid_tid in H15 as ?;auto;try Omega.omega.
              apply swstar_l2 in H14;auto.
              
              eapply glob_npnsw_step_atomblockstarN_inv_ex in H5 as ?;eauto.
              destruct H20 as [|[|[|[]]]].
              {
                Hsimpl.
                enough(sw_star glob_step pc ({-|x,cur_tid x5})).
                Esimpl;eauto. left;Esimpl;eauto.
                rewrite H11 in *;simpl in *.
                econstructor 2;[|constructor].
                assert(pc_valid_tid x1 (cur_tid x5)). inversion H14;split;auto.
                eapply npnswstep_pc_valid_tid_backwards_preservation in H5;eauto.
                destruct pc,H5;simpl in *;subst. rewrite H9.
                econstructor;eauto.
              }
              {
                eexists;split;eauto.
              }
              {
                destruct H20 as (?&?&?&?&?&?).
                
                apply atomblockstarN_cur_valid_tid in H20 as ?.
                assert(type_glob_step glob_sw x sw FP.emp ({-|x,cur_tid x5})).
                destruct H22. destruct x;simpl in *;subst. rewrite H9. econstructor;eauto.
                rewrite H11 in H23.
                simpl in H23.
                assert(glob_step pc sw FP.emp ({-|x,cur_tid x5})).
                rewrite H11.
                destruct pc;inversion H23;subst. econstructor;eauto.
                
                assert(sw_star glob_step pc ({-|x,cur_tid x5})).
                econstructor;eauto. constructor.
                eexists;split;eauto.
                right;right;left. do 5 eexists;eauto.
                Omega.omega.
                auto.
              }
              {
                destruct H20 as (?&?&?&?&?).
                apply atomblockstarN_cur_valid_tid in H20 as ?;auto;try Omega.omega.
                assert(type_glob_step glob_sw x sw FP.emp ({-|x,cur_tid x5})).
                destruct H23. destruct x;simpl in *;subst. rewrite H9. econstructor;eauto.
                rewrite H11 in H24.
                simpl in H24.
                assert(glob_step pc sw FP.emp ({-|x,cur_tid x5})).
                rewrite H11.
                destruct pc;inversion H24;subst. econstructor;eauto.
                
                assert(sw_star glob_step pc ({-|x,cur_tid x5})).
                econstructor;eauto. constructor.
    
                eexists;split;eauto.
                right;right;right.
    
                do 5 eexists;eauto.
    
                assert(L1:invpc x12).
                eapply atomblockstarN_invpc_preservation in H20;eauto.
                assert(L2:glob_step x12 sw FP.emp ({-|x12,cur_tid x})).
                assert(pc_valid_tid x12 (cur_tid x)).
                apply npnswstep_cur_valid_tid in H21;auto.
                apply atomblockstarN_atomO in H20 as [].
                destruct x12,H27;simpl in *;subst;econstructor;eauto.
                
                assert(cur_valid_id x9 \/~cur_valid_id x9).
                apply classic.
                destruct H27.
                {
                  assert(cur_valid_id ({-|x13,cur_tid x9})).
                  inversion H22 as (?&?&?&?). destruct  H27.
                  split;simpl in *;subst;congruence.
    
                  assert(type_glob_step glob_sw x13 sw FP.emp ({-|x13,cur_tid x9})).
                  apply atomblockstarN_atomO in H20 as [].
                  eapply glob_npnsw_step_bitO_preserve in H21;eauto.
                  destruct x13,H28;simpl in *;subst;econstructor;eauto.
    
                  eapply mem_eq_npnsw_or_sw_star in H22 as (?&?&?);eauto.
                  assert(sw_star glob_step x13 ({-|x13,cur_tid x9})).
                  econstructor;eauto. eapply type_glob_step_elim;eauto. constructor.
                  eapply swstar_cons_npnsw_or_sw_star in H22;eauto.
    
                  eapply npnsw_step_cons_npnsw_or_sw_star in H22;eauto.
                  assert(sw_star glob_step x12 ({-|x12,cur_tid x})).
                  econstructor;eauto. constructor.
                  eapply swstar_cons_npnsw_or_sw_star in H32;try apply H22;eauto.
                  do 2 eexists;split;eauto;split.
                  destruct H17.
                  eapply mem_eq_pc_trans;eauto.
                  apply mem_eq_pc_change;auto.
                  destruct H17.
                  rewrite <- T1.
                  rewrite <- H33.
                  rewrite FP.union_comm_eq with(fp1:=x0).
                  rewrite  FP.fp_union_assoc. rewrite FP.union_comm_eq with (fp1:=x0).
                  auto.
                }
                {
                  eapply npnsw_or_sw_star_not_cur_valid_tid in H27;eauto.
                  destruct H27.
                  {
                    subst.
                    
                    assert(npnsw_or_sw_star ({-|x12,cur_tid x}) x0 x13).
                    eexists. rewrite <- FP.fp_union_emp with(fp:=x0). econstructor. left. eauto. constructor.
                    assert(sw_star glob_step x12 ({-|x12,cur_tid x})).
                    econstructor;eauto. constructor.
                    eapply swstar_cons_npnsw_or_sw_star in H28;try apply H27;eauto.
                    do 2 eexists;split;eauto;split;destruct H17,H27;subst.
                    eapply mem_eq_pc_trans;eauto.
                    eapply mem_eq_pc_change in H22;eauto.
                    rewrite FP.fp_union_emp.
                    rewrite FP.union_comm_eq;auto.
                  }
                  {
                    destruct H27 as (?&?&?).
                    apply type_glob_step_exists in H27 as [].
                    destruct x15;subst;try(inversion H27;fail).
                    assert(type_glob_step glob_sw ({-|x9,cur_tid x13}) sw FP.emp x14).
                    inversion H27;subst. econstructor;eauto.
                    apply mem_eq_pc_change with(t:=cur_tid x13) in H22 as ?.
                    simpl in H30. rewrite pc_cur_tid in H30.
                    eapply mem_eq_globstep in H30 as (?&?&?);eauto.
                    eapply mem_eq_npnsw_or_sw_star in H31 as (?&?&?);eauto.
                    exists (FP.union FP.emp (FP.union x0 (FP.union FP.emp x10))),x16.
                    apply type_glob_step_exists in L2 as [].
                    destruct x17;subst;try(inversion H33;fail).
                    destruct H31.
                    split;auto.
                    econstructor;eauto.
                    econstructor;eauto. right;eauto.
                    econstructor;eauto. left;eauto.
                    econstructor;eauto. right;eauto.
                    destruct H17;subst;split.
                    eapply mem_eq_pc_trans;eauto.
                    eapply mem_eq_pc_change;eauto.
                    repeat rewrite FP.emp_union_fp.
                    rewrite FP.union_comm_eq with(fp1:=x0) .
                    rewrite FP.fp_union_assoc.
                    rewrite FP.union_comm_eq with(fp1:=x0).
                    auto.
                  }
                  apply atomblockstarN_invpc_preservation in H15;auto.
                  apply atomblockstarN_atomO in H15 as [];auto.
                }
              }
              {
                destruct H20 as (?&?&?).
                apply atomblockstarN_cur_valid_tid in H20 as ?;auto;try Omega.omega.
                assert(type_glob_step glob_sw x sw FP.emp ({-|x,cur_tid x5})).
                destruct H22. destruct x;simpl in *;subst. rewrite H9. econstructor;eauto.
                rewrite H11 in H22.
                simpl in H22.
                assert(glob_step pc sw FP.emp ({-|x,cur_tid x5})).
                rewrite H11.
                destruct pc;inversion H22;simpl in *;subst.
                econstructor;eauto.
                
                assert(sw_star glob_step pc ({-|x,cur_tid x5})).
                econstructor;eauto. constructor.
    
                eexists;split;eauto.
                right;right;right.
    
                do 5 eexists;eauto.
    
                assert(cur_valid_id x9 \/~cur_valid_id x9).
                apply classic.
                destruct H26.
                {
                  assert(pc_valid_tid x12 (cur_tid x9)).
                  inversion H21 as (?&?&?&?). destruct H26.
                  simpl in *;subst;split;congruence.
                  assert(type_glob_step glob_sw x12 sw FP.emp ({-|x12,cur_tid x9})).
                  apply atomblockstarN_atomO in H20 as [].
                  destruct x12,H27;simpl in *;subst;econstructor;eauto.
    
                  eapply mem_eq_npnsw_or_sw_star in H21 as (?&?&?);eauto.
                  destruct H21.
                  do 3 eexists. eexists. eapply star_step;eauto. right;eauto.
                  destruct H17;split.
                  eapply mem_eq_pc_trans;eauto.
                  eapply mem_eq_pc_change;eauto.
                  subst. rewrite FP.emp_union_fp.
                  rewrite  FP.fp_union_assoc .
                  rewrite FP.union_comm_eq with(fp1:=x8).
                  auto.
                }
                {
                  eapply npnsw_or_sw_star_not_cur_valid_tid in H26;eauto.
                  destruct H26.
                  {
                    subst.
                    exists FP.emp,x12. split. eexists. constructor.
                    destruct H17,H26;subst;split.
                    eapply mem_eq_pc_trans;eauto.
                    eapply mem_eq_pc_change in H21;eauto.
                    do 2 rewrite FP.fp_union_emp.
                    rewrite FP.union_comm_eq;auto.
                  }
                  {
                    destruct H26 as (?&?&?).
                    apply type_glob_step_exists in H26 as [].
                    destruct x14;subst;try(inversion H26;fail).
    
                    apply mem_eq_pc_change with(t:=cur_tid x12) in H21 as ?.
                    simpl in H28. rewrite pc_cur_tid in H28.
                    assert(type_glob_step glob_sw ({-|x9,cur_tid x12}) sw FP.emp x13).
                    inversion H26;subst;econstructor;eauto.
    
                    eapply mem_eq_globstep in H29 as (?&?&?);eauto.
                    eapply mem_eq_npnsw_or_sw_star in H30 as (?&?&?);eauto.
                    destruct H30.
                    do 3 eexists. esplit. eapply star_step. right;eauto. eauto.
                    destruct H17. split.
                    eapply mem_eq_pc_trans;eauto.
                    eapply mem_eq_pc_change in H31;eauto.
                    rewrite FP.emp_union_fp.
                    subst.
                    rewrite FP.fp_union_assoc.
                    rewrite FP.union_comm_eq with(fp1:=x0);auto.
                  }
                  apply atomblockstarN_invpc_preservation in H15;auto.
                  apply atomblockstarN_atomO in H15 as [];auto.
                }
              }
            }
          }
          Omega.omega.
        }
      }
      {
        destruct H5 as (?&?&?&?&?&?&?&?).
        
        destruct x3.
        {
          apply noevt_stepN_0 in H7 as [];subst.
          eexists;split;eauto.
          right;right;right.
          do 5 eexists;eauto.
          eapply cons_atomblock_1. constructor.
          left;eauto.
          eauto.
          constructor. auto.
          do 3 eexists. eexists. constructor.
          destruct H8. split.
          rewrite pc_cur_tid. apply mem_eq_pc_refl.
          repeat rewrite FP.emp_union_fp.
          repeat rewrite FP.fp_union_emp in *;auto.
        }
        {
          apply swstar_l1 in H4 as ?.
          rewrite H9 in H5.
          apply atomblockstep_invpc_preserve in H5 as ?;auto.
          apply atomblockstep_bitO in H5 as ?. destruct H11 as [_].
          assert(atomblockstarN 1 (cons (cur_tid ({-|pc,cur_tid x})) nil) ({-|pc,cur_tid x}) (FP.union (FP.union FP.emp x0) FP.emp) x1).
          econstructor 2;eauto. constructor. constructor. constructor. auto.
          eapply H in H7;eauto;try Omega.omega.
          destruct H7 as (?&?&?).
          destruct H13 as [|[|[]]].
          {
            Hsimpl.
            eapply atomblockstarN_cons_swstar in H12;eauto.
            eapply atomblockstarN_cons in H13;eauto.
            eexists;split;eauto.
            rewrite <- H9 in H13. simpl in *.
            left. Esimpl;eauto.
          }
          {
            apply swstar_l1 in H7.
            rewrite H7 in H13.
            apply race_changetid with(t:=cur_tid x1) in H13. simpl in H13;rewrite pc_cur_tid in H13.
    
            eexists;split;eauto.
            right;right;left.
            do 5 eexists;eauto. rewrite H9;eauto.
          }
          {
            destruct H13 as (?&?&?&?&?&?).
            eapply atomblockstarN_cons_swstar in H12;eauto.
            eapply atomblockstarN_cons in H13;eauto.
            eexists;split;eauto.
            right;right;left. do 5 eexists;eauto. rewrite H9;eauto.
          }
          {
            destruct H13 as (?&?&?&?&?&?&?&?&?).
            
            eapply atomblockstarN_cons_swstar in H12;eauto.
            eapply atomblockstarN_cons in H13;eauto.
            
            eexists;split;eauto.
            right;right;right.
            destruct H15,H8;subst. simpl in *.
            rewrite H9;eauto.
            Esimpl;eauto.
            repeat rewrite FP.emp_union_fp.
            rewrite FP.fp_union_emp.
            rewrite FP.fp_union_assoc.
            auto.
          }
        }
      }
    Qed.
    
    Lemma noevt_stepN_Si_to_atomblockstarN2:
      forall i pc fp pc',
        noevt_stepN glob_step i pc fp pc'->i>0->atom_bit pc = O->invpc pc->atom_bit pc' = I ->
        exists pc1,sw_star glob_step pc pc1 /\
              ( (exists i l fp' pc2,atomblockstarN i l pc1  fp' pc2 /\ predicted_abort1 pc2) \/
                (exists j l fp' pc2,atomblockstarN j l pc1 fp' pc2 /\ race glob_predict_star_alter pc2 )\/
                (exists j l fp' pc2,atomblockstarN j l pc1 fp' pc2 /\ 
                               exists fp'' pc3, npnsw_or_sw_star pc2 fp'' pc3 /\
                                           exists fp''' pc4,halfatomblockstep pc3 tau fp''' pc4 /\ mem_eq_pc GE pc' pc4 /\ FP.union (FP.union fp' fp'') fp''' = fp)).
    Proof.
      intros.
      apply noevt_stepN_OI in H;auto.
      Hsimpl.
      destruct x.
      apply noevt_stepN_0 in H as [];subst.
      Esimpl;eauto. right;right.
      Esimpl;eauto. econstructor. inversion H4;auto. econstructor;constructor.
      unfold halfatomblockstep.  Esimpl;eauto. apply tau_star_tau_N_equiv;eauto.
      apply mem_eq_pc_refl.
      rewrite FP.fp_union_emp. auto.
      assert(L1:invpc x1).
      apply noevt_stepN_sound in H.
      apply non_evt_star_star in H. destruct H.
      eapply GE_mod_wd_star_tp_inv2;eauto.
      assert(L2:cur_valid_id x1).
      inversion H4;subst. split;[eapply gettop_valid_tid;eauto|intro;solv_thread].
      

      assert(atom_bit x1 = O). inversion H4;auto.
      eapply noevt_stepN_Si_to_atomblockstarN in H;eauto;[|Omega.omega].
      Hsimpl. Esimpl;eauto.
      
      destruct H9 as [|[|[]]];Hsimpl.
      left. Esimpl;eauto.
      right. left. Esimpl;eauto.
      constructor. inversion H9. inversion H11;auto.
      right. left. Esimpl;eauto.
      eapply mem_eq_globstep in H4;eauto.
      Hsimpl.
      eapply mem_eq_coreN in H13;eauto.
      Hsimpl.
      assert(L3:pc_valid_tid x11 (cur_tid x1)).
      destruct L2. inversion H11 as (?&?&?&?). rewrite H17 in *;simpl in *;split;try congruence.
      assert(npnsw_or_sw_step x11 sw FP.emp ({-|x11,cur_tid x1})).
      constructor 2.
      destruct x11,L3;inversion H4;simpl in *;subst. econstructor;eauto.

      unfold npnsw_or_sw_star in *.
      destruct H10. eapply star_cons_step in H15 as [];eauto.
      apply tauN_taustar in H13.
       
      unfold halfatomblockstep;Esimpl;eauto.
      right;right;Esimpl;eauto.
      rewrite FP.fp_union_emp.
      rewrite <- H7. rewrite <- H12.
      auto.
    Qed.
      
      
    Lemma globrace_equiv:
      forall pc,
        @race GE glob_predict_star_alter pc ->
        invpc pc->
        star_race glob_predict pc.
    Proof.
      intros.
      assert(atom_bit pc = O). inversion H;subst;auto. inversion H2;auto.
      eapply nppredictrace_globpredictstaraltrace_equiv in H.
      apply nprace_equiv in H.
      apply np_race_config_np_race_config_base_equiv in H;auto.
      eapply np_race_config_base_star_race;eauto.
    Qed.
    
    
    Definition evtstep:=@type_glob_step GE efprint.
    Inductive npnsw_or_sw_stepN:nat->list tid->@ProgConfig GE->FP.t->@ProgConfig GE->Prop:=
    | npnsworsw_emp: forall pc,atom_bit pc = O -> npnsw_or_sw_stepN 0 nil pc FP.emp pc
    | npnsworsw_consnpnsw:
        forall pc l fp pc',
          glob_npnsw_step pc l fp pc'->
          forall i l' fp' pc'',
            npnsw_or_sw_stepN i l' pc' fp' pc''->
            npnsw_or_sw_stepN (S i)(cons (cur_tid pc) l') pc (FP.union fp fp') pc''
    | npnsworsw_conssw:
        forall pc l fp pc',
          type_glob_step glob_sw pc l fp pc'->
          forall i l' fp' pc'',
            npnsw_or_sw_stepN i l' pc' fp' pc''->
            npnsw_or_sw_stepN i l' pc (FP.union fp fp') pc''.
    Lemma npnsw_or_sw_stepN_exists:
      forall pc fp pc',npnsw_or_sw_star pc fp pc'->atom_bit pc = O->exists i l,npnsw_or_sw_stepN i l pc fp pc'.
    Proof.
      destruct 1.
      induction H;intro.
      Esimpl. constructor;auto.
      destruct H.
      apply npnswstep_l2 in H as ?. rewrite H2 in H1.
      Hsimpl.
      Esimpl. econstructor 2;eauto.
      assert(atom_bit s2 = O). inversion H;auto.
      Hsimpl.
      Esimpl. econstructor 3;eauto.
    Qed.
    Lemma npnsw_or_sw_stepN_sound:
      forall i l pc fp pc',npnsw_or_sw_stepN i l pc fp pc'->npnsw_or_sw_star pc fp pc'.
    Proof. induction 1;intros. exists nil;constructor. destruct IHnpnsw_or_sw_stepN. exists (cons l x). econstructor;eauto. left;auto. destruct IHnpnsw_or_sw_stepN. exists (cons l x). econstructor;eauto. right;eauto. Qed.
    Lemma npnsw_or_sw_stepN_bitO:
      forall i l pc fp pc',npnsw_or_sw_stepN i l pc fp pc'->atom_bit pc = O /\ atom_bit pc' = O.
    Proof. induction 1;intros;auto;destruct IHnpnsw_or_sw_stepN;split;auto. apply npnswstep_l2 in H;congruence. inversion H;auto. Qed.
    
    Lemma npnsw_or_sw_stepN_0:
      forall pc l fp pc',npnsw_or_sw_stepN 0 l pc fp pc'->l=nil/\fp=FP.emp /\ sw_star glob_step pc pc'.
    Proof.
      remember 0.
      induction 1;intros. Esimpl;auto. constructor.
      inversion Heqn.
      Hsimpl. subst.
      inversion H;subst.
      Esimpl;auto.
      econstructor;eauto. eapply type_glob_step_elim;eauto.
    Qed.
    Lemma swstar_npnsw_or_sw_stepN:
      forall pc pc',sw_star glob_step pc pc' -> atom_bit pc = O -> npnsw_or_sw_stepN 0 nil pc FP.emp pc'.
    Proof.
      induction 1;intros. constructor;auto.
      assert(atom_bit s2 = O). inversion H;auto.
      Hsimpl.
      rewrite<- FP.fp_union_emp with (fp:=FP.emp).
      apply type_glob_step_exists in H as [].
      destruct x;subst;try(inversion H;fail).
      econstructor;eauto.
    Qed.
    Lemma npnsw_step_cons_npnsw_or_sw_stepN:
      forall pc l fp pc' i ltids fp' pc'',
        glob_npnsw_step pc l fp pc'->
        npnsw_or_sw_stepN i ltids pc' fp' pc''->
        npnsw_or_sw_stepN (S i) (cons (cur_tid pc) ltids)pc (FP.union fp fp') pc''.
    Proof. intros. econstructor 2;eauto. Qed.
    
      
    Lemma sw_star_cons_npnsw_or_sw_stepN:
      forall pc pc' i ltids fp pc'',
        sw_star glob_step pc pc'->
        npnsw_or_sw_stepN i ltids pc' fp pc''->
        npnsw_or_sw_stepN i ltids pc fp pc''.
    Proof.
      induction 1;intros. auto.
      apply IHsw_star in H1.
      rewrite <- FP.emp_union_fp with (fp:=fp).
      econstructor 3;eauto.
      inversion H;subst;econstructor;eauto.
    Qed.
    Lemma npnsw_or_sw_stepN_cons1:
      forall l1 l2 pc fp pc' i fp' pc'',
        npnsw_or_sw_stepN 1 l1 pc fp pc'->
        npnsw_or_sw_stepN i l2 pc' fp' pc''->
        npnsw_or_sw_stepN (S i)(app l1 l2) pc (FP.union fp fp') pc''.
    Proof.
      remember 1.
      induction 1;subst;intros. inversion Heqn.
      inversion Heqn;subst.
    
      apply npnsw_or_sw_stepN_0 in H0;Hsimpl;subst.
      eapply sw_star_cons_npnsw_or_sw_stepN in H3;eauto.
      eapply npnsw_step_cons_npnsw_or_sw_stepN in H;eauto.
      rewrite FP.fp_union_emp;auto.
    
      apply IHnpnsw_or_sw_stepN in H1;auto.
      inversion H;subst.
      rewrite<- FP.fp_union_assoc.
      econstructor 3;eauto.
    Qed.
    Lemma npnsw_or_sw_stepN_SN_split:
      forall i ltids pc fp pc',
        npnsw_or_sw_stepN (S i) ltids pc fp pc'->
        exists l1 l2 fp1 fp2 pc1,npnsw_or_sw_stepN 1 l1 pc fp1 pc1 /\ npnsw_or_sw_stepN i l2 pc1 fp2 pc' /\ FP.union fp1 fp2 =fp /\ app l1 l2 = ltids.
    Proof.
      intros. remember (S i).
      induction H. inversion Heqn.
      exists (cons (cur_tid pc) nil),l',fp,fp',pc'. inversion Heqn;subst;split;[|split];auto.
      rewrite <- FP.fp_union_emp with(fp:=fp).
      econstructor;eauto. constructor.
      apply npnsw_or_sw_stepN_bitO in H0 as [];auto.
    
      Hsimpl.
      assert(l=sw). inversion H;auto. subst.
      eapply npnsworsw_conssw in H;eauto.
      Esimpl;eauto.
      rewrite FP.fp_union_assoc;auto.
    Qed.
    Lemma npnsw_or_sw_stepN_cons:
      forall i l1 l2 pc fp pc' j fp' pc'',
        npnsw_or_sw_stepN i l1 pc fp pc'->
        npnsw_or_sw_stepN j l2 pc' fp' pc''->
        npnsw_or_sw_stepN (i+j)(app l1 l2) pc (FP.union fp fp') pc''.
    Proof.
      induction i;intros.
      {
        apply npnsw_or_sw_stepN_0 in H;Hsimpl;subst. 
        rewrite FP.emp_union_fp;auto.
        eapply sw_star_cons_npnsw_or_sw_stepN;eauto.
      }
      {
        apply npnsw_or_sw_stepN_SN_split in H;Hsimpl.
        eapply IHi in H0;eauto.
        eapply npnsw_or_sw_stepN_cons1 in H0;eauto.
        rewrite <- H2. rewrite<- FP.fp_union_assoc. rewrite <- H3.
        simpl. rewrite List.app_assoc in H0. auto.
      }
    Qed.
    
    Lemma mem_eq_npnsw_or_sw_stepN:
      forall pc pc1,
        mem_eq_pc GE pc pc1->
        forall i l fp pc',
          npnsw_or_sw_stepN i l pc fp pc'->
          exists pc1',npnsw_or_sw_stepN i l pc1 fp pc1' /\ mem_eq_pc GE pc' pc1'.
    Proof.
      intros. revert pc1 H.
      induction H0;intros.
      eexists;split;[constructor|auto]. inversion H0 as (?&?&?&?);congruence.
    
      apply npnswstep_l1 in H;Hsimpl.
      eapply mem_eq_globstep in H1 as ?;eauto;Hsimpl.
      apply npnswstep_l3 in H3;auto.
      eapply IHnpnsw_or_sw_stepN in H4 as ?;Hsimpl.
      eapply npnsw_step_cons_npnsw_or_sw_stepN in H5 as ?;eauto.
      inversion H1 as (_&?&?&_).
      Esimpl;eauto;congruence.
    
      eapply mem_eq_globstep in H as ?;eauto;Hsimpl.
      eapply IHnpnsw_or_sw_stepN in H3 as ?;Hsimpl.
      eapply npnsworsw_conssw in H2 as ?;eauto.
    Qed.
    
    Lemma npnsw_or_sw_stepN_1_inv:
      forall l pc fp pc',
        npnsw_or_sw_stepN 1 l pc fp pc'->
        exists pc1,sw_star glob_step pc pc1 /\
              exists pc2,glob_npnsw_step pc1 tau fp pc2 /\
                    sw_star glob_step pc2 pc' /\ l = cons (cur_tid pc1) nil.
    Proof.
      remember 1.
      induction 1;intros. inversion Heqn.
      inversion Heqn;subst.
      apply npnsw_or_sw_stepN_0 in H0 as [?[]];subst.
      rewrite FP.fp_union_emp.
      exists pc;split;econstructor;split;eauto.
      apply npnswstep_taustep in H as ?;congruence.
    
      destruct IHnpnsw_or_sw_stepN as (?&?&?&?&?);auto.
      assert(l=sw/\fp=FP.emp). inversion H;auto. destruct H4;subst.
      apply type_glob_step_elim in H.
      eapply sw_star_cons in H1;eauto.
      rewrite FP.emp_union_fp.
      Hsimpl;Esimpl;eauto.
    Qed.
    Lemma sw_star_cons:
      forall pc pc1 pc2,
        sw_star glob_step pc pc1 ->
        sw_star glob_step pc1 pc2->
        sw_star (@glob_step GE) pc pc2.
    Proof.
      induction 1;intros;auto.
      econstructor;eauto.
    Qed.
    
    Lemma npnsw_or_sw_stepN_inv1:
      forall i ltids pc fp pc',
        i>0->
        npnsw_or_sw_stepN i ltids pc fp pc'->
        exists pc1,
          sw_star glob_step pc pc1 /\
          exists pc2 fp1,glob_npnsw_step pc1 tau fp1 pc2 /\
                    exists l2 fp2,npnsw_or_sw_stepN (i-1) l2 pc2 fp2 pc' /\ FP.union fp1 fp2 = fp /\ cons (cur_tid pc1) l2 = ltids.
    Proof.
      induction i;intros. inversion H.
      destruct i.
      {
        apply npnsw_or_sw_stepN_1_inv in H0 as L;Hsimpl.
        apply npnsw_or_sw_stepN_bitO in H0 as L;Hsimpl.
        apply glob_sw_star_bit_preservation in H3 as ?.
        assert(npnsw_or_sw_stepN 0 nil pc' FP.emp pc').
        constructor. congruence.
        eapply sw_star_cons_npnsw_or_sw_stepN in H8;eauto.
        Esimpl;eauto.
        rewrite FP.fp_union_emp;eauto.    
      }
      {
        apply npnsw_or_sw_stepN_SN_split in H0;Hsimpl.
        apply IHi in H1;Hsimpl.
        apply npnsw_or_sw_stepN_1_inv in H0;Hsimpl.
        eapply sw_star_cons in H1;eauto.
        eapply npnsw_step_cons_npnsw_or_sw_stepN in H4;eauto.
        eapply sw_star_cons_npnsw_or_sw_stepN in H4;eauto.
        assert(S (S i-1) = S (S i) -1). Omega.omega. rewrite <- H11;eauto.
        Esimpl;eauto.
        rewrite H6;auto.
        rewrite H7;auto. rewrite <- H3. rewrite H10;auto.
        Omega.omega.
      }
    Qed.


    Corollary cur_valid_id_case1 :
      forall pc fp pc' v pc'',
        invpc pc->
        tau_star glob_npnsw_step pc fp pc'->
        glob_step pc' (evt v) FP.emp pc''->
        @cur_valid_id GE pc.
    Proof.
      inversion 2;subst;intro.
      inversion H1;subst. split. eapply gettop_valid_tid;eauto. intro;solv_thread.
      apply npnswstep_cur_valid_tid in H1;auto.
    Qed.
    
   
    Lemma npnsw_or_sw_stepN_pc_valid_tid_backwards_preservation:
      forall i l pc fp pc' t,
        npnsw_or_sw_stepN i l pc fp pc'->
        pc_valid_tid pc' t->
        pc_valid_tid pc t.
    Proof.
      induction i;intros. apply npnsw_or_sw_stepN_0 in H.
      Hsimpl. apply swstar_l1 in H2. rewrite H2 in H0;auto.
      apply npnsw_or_sw_stepN_inv1 in H;Hsimpl.
      assert(S i - 1 = i). Omega.omega.
      rewrite H5 in H2 ;clear H5.
      eapply IHi in H2;eauto.
      apply swstar_l1 in H. rewrite H in *;simpl in *.
      eapply npnswstep_pc_valid_tid_backwards_preservation in H1;eauto.
      Omega.omega.
    Qed.

    Lemma npnsw_or_sw_stepN_thdpinv:
      forall i l pc fp pc' ,
        npnsw_or_sw_stepN i l pc fp pc'->
        invpc pc->
        invpc pc'.
    Proof.
      induction i;intros. apply npnsw_or_sw_stepN_0 in H. Hsimpl;subst.
      apply swstar_l1 in H2. rewrite H2;auto.
      apply npnsw_or_sw_stepN_inv1 in H. Hsimpl.
      assert(S i - 1 = i). Omega.omega.
      rewrite H5 in H2 ;clear H5.
      eapply IHi in H2;eauto.
      apply npnsw_step_thdpinv in H1;auto.
      apply swstar_l1 in H;auto. rewrite H;auto.
      Omega.omega.
    Qed.
    Lemma npnsw_or_sw_stepN_evt_ex:
      forall i ltids pc fp pc',
        invpc pc->
        npnsw_or_sw_stepN i ltids pc fp pc'->
        forall v fp' pc'' pc''',
          tau_star glob_npnsw_step pc' fp' pc''->
          glob_step pc'' (evt v) FP.emp pc'''->
          (exists ix lx pc' fpx,npnsw_or_sw_stepN ix lx pc fpx pc' /\ (race glob_predict_star_alter pc' \/ predicted_abort1 pc')) \/
          sw_star glob_step pc ({-|pc,cur_tid pc'})/\
          exists pc1 pc2 fp1 fp2 pc3 j l',
            tau_star glob_npnsw_step ({-|pc,cur_tid pc'}) fp1 pc1 /\
            glob_step pc1 (evt v) FP.emp pc2 /\
            npnsw_or_sw_stepN j l' pc2 fp2 pc3 /\ mem_eq_pc GE pc''' ({-|pc3,cur_tid pc'}) /\ j <= i /\ FP.union fp1 fp2 = FP.union fp fp'.
    Proof.
      pose wdge;pose modwdge.
      induction i;intros.
      {
        apply npnsw_or_sw_stepN_bitO in H0 as ?.
        apply npnsw_or_sw_stepN_0 in H0.
        Hsimpl;subst.
        apply swstar_l1 in H6 as ?;Hsimpl.
        right. rewrite <- H0.
        Esimpl;eauto. constructor.
        inversion H2;auto.
        apply npnsw_taustar_tid_preservation in H1.
        rewrite H1. inversion H2;subst. apply mem_eq_pc_refl.
        rewrite FP.union_comm_eq;auto.
      }
      {
        apply npnsw_or_sw_stepN_bitO in H0 as ?.
        apply npnsw_or_sw_stepN_inv1 in H0;[|Omega.omega].
        Hsimpl;subst.
        assert(S i - 1 = i). Omega.omega.
        rewrite H7 in *;clear H7.
        apply sw_star_invpc_preservation in H0 as ?;auto.
        assert(invpc x0).
        apply npnswstep_l1 in H5;Hsimpl.
        apply type_glob_step_elim in H5.
        eapply GE_mod_wd_tp_inv;eauto.
        
        eapply IHi in H6 as?;eauto.
        destruct H9;Hsimpl.
        {
          eapply npnsw_step_cons_npnsw_or_sw_stepN in H9;eauto.
          eapply sw_star_cons_npnsw_or_sw_stepN in H9;eauto.
          left. Esimpl;eauto. 
        }
        {
          assert(cur_tid x0 = cur_tid pc' \/ cur_tid x0 <> cur_tid pc').
          apply classic. destruct H16.
          {
            rewrite <- H16,pc_cur_tid in H10.
            eapply tau_star_cons in H10;eauto.
            apply swstar_l1 in H0 as ?.
            rewrite H17 in H10.
            apply npnsw_step_tid_preservation in H5 as ?.
            rewrite H18,H16 in H10,H17. rewrite H17 in H0.
            right.
            
            Esimpl;eauto.
            rewrite <- FP.fp_union_assoc.
            rewrite H15.
            rewrite FP.fp_union_assoc.
            auto.
          }
          {
            apply npnsw_step_tid_preservation in H5 as ?.
            assert(cur_tid x <> cur_tid pc'). intro;contradict H15;congruence.
            assert(atom_bit x = O). apply swstar_l1 in H0. rewrite H0. auto.
            eapply glob_npnsw_step_star_evt_ex in H5 as ?;eauto.
            destruct H20 as [|[]].
            {
              apply swstar_l1 in H0 as ?.
              remember (cur_tid x) as t1.
              rewrite H21 in *;clear x H21 Heqt1;simpl in *.
              apply npnsw_step_thdpinv in H5 as ?;auto.
              apply npnsw_or_sw_stepN_thdpinv in H6 as ?;auto.
              eapply cur_valid_id_case1 in H1;eauto.
              eapply npnsw_or_sw_stepN_pc_valid_tid_backwards_preservation in H6;eauto.
              eapply npnswstep_pc_valid_tid_backwards_preservation in H5 as ?;eauto.
              assert(sw_star glob_step pc ({-|pc,cur_tid pc'})).
              econstructor 2;[|constructor].
              destruct pc,H23;simpl in *;subst;econstructor;eauto.
              
              apply swstar_npnsw_or_sw_stepN in H24 as ?;auto.
              left. Esimpl;eauto. right.
              econstructor 2; eauto. instantiate(1:=pc).
              destruct pc,H23;simpl in *;subst;econstructor;eauto.
            }
            {
              apply swstar_npnsw_or_sw_stepN in H0;auto.
              left;Esimpl;eauto.
            }
            {
              Hsimpl.
              eapply mem_eq_npnsw_or_sw_stepN in H24 as ?;eauto.
              Hsimpl.
    
              eapply cur_valid_id_case1 in H21 as ?;eauto.
              apply swstar_l1 in H0 as ?.
              rewrite H28 in *. simpl in *.
              assert(glob_step pc sw FP.emp ({-|pc,cur_tid pc'})).
              destruct pc,H27;simpl in *;subst;econstructor;eauto.
              assert(sw_star glob_step pc ({-|pc,cur_tid pc'})).
              econstructor;eauto. constructor.
              right.
    
              assert(invpc x4). apply npnsw_step_thdpinv in H5;auto. apply npnsw_taustar_thdpinv in H10;auto.
              assert(invpc x5). eapply GE_mod_wd_tp_inv;eauto.
              assert(cur_valid_id x5).
              revert H32 H11;clear;intros.
              inversion H11;subst;split. eapply gettop_valid_tid;auto. solv_thread.
              intro;solv_thread.
    
              assert(pc_valid_tid x13 (cur_tid x5)). destruct H33,H24 as (?&?&?&?).
              simpl in *;subst;split;try congruence.
              assert(sw_star glob_step x13 ({-|x13,cur_tid x5})).
              assert(glob_step x13 sw FP.emp ({-|x13,cur_tid x5})).
              apply npnsw_or_sw_stepN_bitO in H25 as [].
              destruct x13,H34;simpl in *;subst;econstructor;eauto.
              econstructor;eauto. constructor.
    
              eapply sw_star_cons_npnsw_or_sw_stepN in H25;eauto.
              eapply npnsw_step_cons_npnsw_or_sw_stepN in H25;eauto.
    
              apply npnsw_taustar_thdpinv in H21 as ?;auto.
              eapply GE_mod_wd_tp_inv in H36;eauto.
              apply npnswstep_cur_valid_tid in H23 as ?;auto.
              assert(type_glob_step glob_sw x12 sw FP.emp ({-|x12,cur_tid x})).
              inversion H22;subst. destruct H37. econstructor;eauto.
              eapply  npnsworsw_conssw in H25;eauto.
              
              Esimpl;eauto.
              eapply mem_eq_pc_trans;eauto.
              eapply mem_eq_pc_change;eauto.
              Omega.omega.
              rewrite FP.emp_union_fp.
              rewrite <- FP.fp_union_assoc.
              rewrite <- H15.
              rewrite FP.fp_union_assoc.
              rewrite FP.union_comm_eq with (fp1:=x6).
              rewrite FP.fp_union_assoc.
              auto.
            }
          }
        }
      }
    Qed.

 
    Lemma predicted_abort1_O:
      forall pc ,
        predicted_abort1 pc ->
        @atom_bit GE pc = O.
    Proof.
      inversion 1;subst. unfold halfatomblock_abort,halfatomblockstep in H1.
      Hsimpl. apply npnswstar_bit in H0. inversion H3;subst;simpl in *;auto.
      inversion H0;auto.
    Qed.
    Lemma npnsw_or_sw_stepN_race:
      forall i l pc fp pc',
        invpc pc->
        npnsw_or_sw_stepN i l pc fp pc'->
        race glob_predict_star_alter pc' \/ (exists t, predicted_abort1 ({-|pc',t}))->
        race glob_predict_star_alter pc \/ (exists t,predicted_abort1 ({-|pc,t})).
    Proof.
      induction 2;intros;auto.
      eapply npnsw_step_thdpinv in H0 as ?;eauto.
      Hsimpl. clear H2.
      apply npnswstep_taustep in H0 as?;subst.

      destruct IHnpnsw_or_sw_stepN.

      eapply npnsw_step_race_glob_predict_star_alter_cons_2 in H0 as ?;eauto.
      destruct H4;auto. 
      Hsimpl;eauto.
      Hsimpl.
      assert(cur_tid pc' = x \/ cur_tid pc' <> x).
      apply classic.
      destruct H4. apply npnsw_step_tid_preservation in H0 as ?.
      rewrite <- H4,pc_cur_tid in H2.
      eapply npnswstep_predicted_abort in H2;try apply H0;eauto.
      right. exists x;auto. rewrite <- H4, <-H5, pc_cur_tid;auto.
      apply predicted_abort1_O in H2;auto. apply npnswstep_l2 in H0;auto. congruence.
      
      eapply npnswstep_sw_predicted_abort1 in H0;eauto;simpl;try congruence.
      destruct H0;auto. Hsimpl;eauto.
      apply predicted_abort1_O in H2 as ?.
      apply predicted_abort1_sw in H2;auto.
      destruct pc',H2;simpl in *;subst;econstructor;eauto.
    
      assert(invpc pc'). inversion H0;subst;auto.
      Hsimpl. clear H2.
      destruct IHnpnsw_or_sw_stepN.
      eapply swstep_race_glob_predict_star_alter_cons in H2;eauto.
      inversion H0;subst;auto.
      Hsimpl.
      assert(pc' = ({-|pc,cur_tid pc'})). inversion H0;auto.
      rewrite H4 in *;simpl in *.
      right. Esimpl;eauto.
    Qed.

    Lemma noevt_stepN_evtstep_inv:
      forall i pc fp pc',
        noevt_stepN glob_step i pc fp pc'->atom_bit pc = O -> atom_bit pc' = O->invpc pc->
        forall v pc'',
          evtstep pc' (evt v) FP.emp pc''->
          exists pc1,sw_star glob_step pc pc1 /\
                (
                  (exists j l fp' pc2,atomblockstarN j l pc1 fp' pc2 /\ (race glob_predict_star_alter pc2 \/ predicted_abort1 pc2) )\/
                  (exists j l fp' pc2,atomblockstarN j l pc1 fp' pc2 /\
                   exists fp1 pc3,tau_star glob_npnsw_step pc2 fp1 pc3 /\
                   exists pc4,glob_step pc3 (evt v) FP.emp pc4 /\ cur_tid pc3 = cur_tid pc' /\
                   exists fp'' pc5, npnsw_or_sw_star pc4 fp'' pc5 /\
                               mem_eq_pc GE pc'' ({-|pc5,cur_tid pc''})/\
                               FP.union fp' (FP.union fp1 fp'') = fp)).
    Proof.
      intros.
      destruct i.
      {
        apply noevt_stepN_0 in H;Hsimpl;subst.
        Esimpl;eauto.
        right. Esimpl;eauto;try(econstructor;eauto;fail);eauto.
        eapply type_glob_step_elim;eauto.
        econstructor. constructor.
        rewrite pc_cur_tid. apply mem_eq_pc_refl.
        repeat rewrite FP.fp_union_emp;auto.
      }
      {
        assert(L:invpc pc').
        apply noevt_stepN_sound in H. apply non_evt_star_star in H as [].
        eapply GE_mod_wd_star_tp_inv2;eauto.
        assert(L2:cur_tid pc' = cur_tid pc''). inversion H3;auto.
        apply noevt_stepN_Si_to_atomblockstarN in H;auto;[|Omega.omega].
        
        Hsimpl.
        destruct H4 as [|[|[]]].
        {
          Hsimpl. Esimpl;eauto.
          left. Esimpl;eauto.
        }
        {
          Esimpl;eauto.
          left. Esimpl;eauto. constructor.
          inversion H4. inversion H6;subst;auto.
        }
        {
          Hsimpl.
          Esimpl;eauto.
          left. Esimpl;eauto.
        }
        {
          assert(L3:cur_valid_id pc').
          inversion H3;subst;split;[eapply gettop_valid_tid|intro;solv_thread];eauto.
          Hsimpl.
          apply atomblockstarN_atomO in H4 as ?;Hsimpl.
          apply npnsw_or_sw_stepN_exists in H5;auto;Hsimpl.
          eapply mem_eq_globstep in H3;eauto;Hsimpl.
          
          assert(invpc x). apply swstar_l1 in H. rewrite H. auto.
          apply atomblockstarN_invpc_preservation in H4 as ?;auto.
          assert(invpc x5). inversion H6 as (?&?&?&?);simpl in *;subst. unfold invpc in *;congruence.
          assert(sw_star glob_step x5 ({-|x5,cur_tid pc'})).
          assert(pc_valid_tid x5 (cur_tid pc')).
          revert H13 H3;clear;inversion 2;subst;split;[eapply gettop_valid_tid|intro];solv_thread.
          assert(atom_bit x5 = O). inversion H3;auto.
          
          econstructor;[|constructor].
          destruct x5,H14;simpl in *;subst;econstructor;eauto.
          
          eapply swstar_npnsw_or_sw_stepN in H14;eauto.
          eapply npnsw_or_sw_stepN_cons in H14;eauto.
          rewrite<- List.app_nil_end in H14.
          rewrite FP.fp_union_emp in H14.
          assert(x6+0=x6);auto. rewrite H15 in H14;clear H15.
          
          
          eapply npnsw_or_sw_stepN_evt_ex in H14 as ?;eauto;[|constructor|eapply type_glob_step_elim;eauto].
    
          destruct H15;Hsimpl.
          {
            eapply npnsw_or_sw_stepN_race in H15;eauto.
            destruct H15.
            {
              Esimpl;eauto. left. Esimpl;eauto.
            }
            {
              Hsimpl.
              apply predicted_abort1_O in H15 as ?.
              apply predicted_abort1_sw in H15 as ?;auto.
              assert(glob_step x3 sw FP.emp ({-|x3,x13})).
              destruct x3,H18;simpl in *;subst;econstructor;eauto.
              destruct x0.
              {
                inversion H4;subst;clear H4.
                enough(sw_star glob_step pc ({-|x3,x13})).
                Esimpl;eauto. left. Esimpl;[constructor| ];auto.
                apply swstar_l1 in H. rewrite H in *;simpl in *.
                econstructor 2;[|constructor];eauto.
                destruct pc,H18;simpl in *;subst;econstructor;eauto.
              }
              eapply atomblockstarN_cons_sw in H4;eauto.
              Esimpl;eauto. left;Esimpl;eauto.
            }
            destruct H16;auto.
            right. eexists;erewrite pc_cur_tid;eauto.
          }
          {
            destruct x0.
            {
              inversion H4;subst.
              simpl in *.
              eapply sw_star_cons in H15 as ?;eauto.
              Esimpl;eauto.
              right;Esimpl;eauto. constructor;auto.
              eapply npnsw_taustar_tid_preservation in H16;eauto.
              eapply npnsw_or_sw_stepN_sound;eauto.
              eapply mem_eq_pc_trans;eauto.
              congruence.
              rewrite H21.
              rewrite FP.emp_union_fp.
              rewrite FP.union_comm_eq;auto.
            }
           
            eapply mem_eq_pc_trans in H19 as ?;eauto.
            assert(cur_tid pc' = cur_tid pc'').
            destruct H22 as (?&?&?&?);try congruence.
            simpl in *;subst. try congruence.
            rewrite <- H23 in *;clear H23.
            simpl in *.
            eapply cur_valid_id_case1 in H16 as ?;eauto.
            assert(sw_star glob_step x3 ({-|x3,cur_tid pc'})).
            econstructor;[|constructor].
            destruct x3,H7;simpl in *;subst;econstructor;eauto.
    
            eapply atomblockstarN_cons_swstar in H4;eauto.
            Esimpl;eauto.
            right;Esimpl;eauto.
            eapply npnsw_taustar_tid_preservation in H16;eauto.
            eapply npnsw_or_sw_stepN_sound;eauto.
            rewrite H21.
            rewrite FP.fp_union_emp;auto.
          }
          inversion H3;auto.
        }
      }
    Qed.
    
    Lemma npnsw_or_sw_star_non_evt_star:
      forall pc fp pc',
        npnsw_or_sw_star pc fp pc'->non_evt_star glob_step pc fp pc'.
    Proof.
      destruct 1;induction H. constructor. econstructor;eauto.
      destruct H;auto. apply npnswstep_taustep in H as ?;subst.
      apply npnswstep_l1 in H. Hsimpl. apply type_glob_step_elim in H. auto.
      assert(e=sw). inversion H;auto. subst.
      apply type_glob_step_elim in H;auto.
    Qed.  
    Inductive Evt_gstar :nat ->@ProgConfig GE->list glabel->FP.t->@ProgConfig GE->Prop:=
    | starbase_nonevt:
        forall i pc fp pc',
          atom_bit pc = O -> atom_bit pc' = O -> noevt_stepN glob_step i pc fp pc'->
          Evt_gstar 0 pc nil fp pc'
    | cons_evtstep:
        forall i pc fp pc' v pc'' k l fp' pce,
          atom_bit pc = O->
          atom_bit pc' = O->
          noevt_stepN glob_step i pc fp pc'->
          glob_step pc' (evt v) FP.emp pc'' ->
          Evt_gstar k pc'' l fp' pce ->
          Evt_gstar (S k) pc (cons (evt v) l) (FP.union fp fp') pce.
    Inductive Evt_gstar_alter :nat ->@ProgConfig GE->list glabel->FP.t->@ProgConfig GE->Prop:=
    | starbase_nonevt_alter:
        forall i pc fp pc',
          atom_bit pc = O -> atom_bit pc' = O -> noevt_stepN glob_step i pc fp pc'->
          Evt_gstar_alter 0 pc nil fp pc'
    | cons_evtstep_alter:
        forall i l pc fp pc' v pc'' pc''' k l' fp' fp'' pc'''' pce,
          atomblockstarN i l pc fp pc'->
          tau_star glob_npnsw_step pc' fp' pc''->
          glob_step pc'' (evt v) FP.emp pc''' ->
          sw_star glob_step pc''' pc''''->
          Evt_gstar_alter k pc'''' l' fp'' pce ->
          Evt_gstar_alter (S k) pc (cons (evt v) l') (FP.union (FP.union fp fp') fp'') pce.
    Lemma mem_eq_evt_gstar:
      forall i pc l fp pc' pc1,
        mem_eq_pc GE pc pc1->
        Evt_gstar i pc l fp pc'->
        exists pc2,Evt_gstar i pc1 l fp pc2/\mem_eq_pc GE pc' pc2.
    Proof.
      pose wdge;pose modwdge.
      induction i;inversion 2;subst.
      eapply mem_eq_noevt_stepN in H3;eauto;Hsimpl.
      Esimpl;eauto. econstructor;eauto. inversion H as (?&?&?&?);congruence.
      inversion H4 as (?&?&?&?);congruence.
    
      apply type_glob_step_exists in H5 as [x ?];destruct x;subst;try(inversion H1;fail).
      eapply mem_eq_noevt_stepN in H4 as ?;eauto;Hsimpl.
      eapply mem_eq_globstep in H7 as ?;eauto;Hsimpl.
      apply type_glob_step_elim in H8.
      eapply IHi in H6;eauto;Hsimpl.
      Esimpl;eauto.
      eapply cons_evtstep in H5;eauto.
      inversion H as (?&?&?&?);congruence.
      inversion H7 as (?&?&?&?);congruence.
    Qed.
      
    Lemma mem_eq_evt_gstar_alter:
      forall i pc l fp pc' pc1,
        mem_eq_pc GE pc pc1->
        Evt_gstar_alter i pc l fp pc'->
        exists pc2,Evt_gstar_alter i pc1 l fp pc2/\mem_eq_pc GE pc' pc2.
    Proof.
      pose wdge.  pose modwdge.
      intros. revert pc1 H. induction H0;intros.
      eapply mem_eq_noevt_stepN in H2 as ?;eauto;Hsimpl.
      Esimpl. econstructor. inversion H2 as (?&?&?&?);congruence.
      inversion H4 as (?&?&?&?). rewrite H0 in H6;symmetry in H6;eapply H6.
      eauto.
      auto.
    
      eapply mem_eq_atomblockstarN in H4 as ?;eauto;Hsimpl.
      eapply mem_eq_npnsw_step_star in H6 as ?;eauto;Hsimpl.
      
    
      apply type_glob_step_exists in H1 as[].
      eapply mem_eq_globstep in H8 as ?;eauto;Hsimpl.
      apply type_glob_step_elim in H9.
      eapply mem_eq_swstar in H10 as ?;eauto;Hsimpl.
    
      apply IHEvt_gstar_alter in H12 as ?;Hsimpl.
      Esimpl;eauto.
      econstructor;eauto.
    Qed.
             

    Lemma non_evt_star_cons:
      forall (step:Step) s s' s'' fp fp',
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
    
    Lemma tau_star_non_evt_star:
      forall (step:Step) pc fp pc',
        tau_star step pc fp pc'->
        non_evt_star step pc fp pc'.
    Proof.
      induction 1;intros.
      constructor.
      econstructor;eauto.
    Qed.
    Lemma non_evt_star_cons_Evt_gstar:
      forall pc fp pc',
        atom_bit pc = O ->
        non_evt_star glob_step pc fp pc'->
        forall j l' fp1 pc2,
          Evt_gstar j pc' l' fp1 pc2->
          Evt_gstar j pc l' (FP.union fp fp1) pc2.
    Proof.
      intros.
      inversion H1;subst.
      apply noevt_stepN_sound in H4.
      eapply non_evt_star_cons in H4;eauto.
      apply noevt_stepN_exists in H4 as [].
      econstructor;eauto.
    
      apply noevt_stepN_sound in H4. eapply non_evt_star_cons in H4;eauto.
      apply noevt_stepN_exists in H4 as [].
      rewrite FP.fp_union_assoc.
      econstructor;eauto.
    Qed.  
    

    
    Lemma Evt_gstar_sound:
      forall i pc l fp pc',
        Evt_gstar i pc l fp pc'->
        exists l',star glob_step pc l' fp pc'.
    Proof.
      induction 1;intros.
      apply noevt_stepN_sound in H1.
      apply non_evt_star_star in H1 as [];eauto.
    
      apply noevt_stepN_sound in H1.
      apply non_evt_star_star in H1 as [].
      eapply star_cons_step in H2;eauto.
      Hsimpl.
    
      eapply cons_star_star in H4;eauto.
      rewrite FP.fp_union_emp in H2;eauto.
    Qed.
    
    Lemma stepN_IO:
      forall i pc l fp pc',
        stepN GE glob_step i pc l fp pc'->
        atom_bit pc = I ->
        atom_bit pc' = O->
        exists j l1 fp1 pc1,stepN GE (type_glob_step core) j pc l1 fp1 pc1 /\
                       exists pc2,type_glob_step extat pc1 tau FP.emp pc2 /\
                             exists l2 fp2,stepN GE glob_step (i-j-1) pc2 l2 fp2 pc' /\
                                      FP.union fp1 fp2 = fp.
    Proof.
      remember (glob_step).
      induction 1;intros.
      rewrite H in H0;inversion H0.
    
      Hsimpl;subst.
      destruct (atom_bit pc') eqn:?.
      {
        apply type_glob_step_exists in H0 as [].
        destruct x;subst;try(inversion H0;subst;simpl in *;subst;try inversion H1;try inversion H2;fail).
        assert(l=tau /\ fp=FP.emp). inversion H0;auto. Hsimpl;subst.
        Esimpl;eauto. econstructor.
        assert(S i - 0 - 1 = i). Omega.omega.
        rewrite H3;eauto.
      }
      {
        assert(I=I). auto.
        Hsimpl.
        apply type_glob_step_exists in H0 as [].
        destruct x6;subst;try(inversion H0;subst;simpl in *;subst;try inversion H1;try inversion Heqb;fail).
        eapply stepN_cons in H0;eauto.
        Esimpl;eauto.
        rewrite FP.fp_union_assoc;auto.
      }
    Qed.
    Lemma corestepN_nonevtstar:
      forall i pc l fp pc',
        stepN GE (type_glob_step core) i pc l fp pc'->
        non_evt_star glob_step pc fp pc'.
    Proof.
      remember (type_glob_step core).
      induction 1;intros. constructor.
      Hsimpl;subst.
      assert(l=tau). inversion H0;auto. subst.
      econstructor;eauto. left;eauto. apply type_glob_step_elim in H0;auto.
    Qed.
    Lemma Evt_gstar_exists:
      forall pc l fp pc',
        atom_bit pc = O -> atom_bit pc' = O ->
        star glob_step pc l fp pc'->
        exists i l',Evt_gstar i pc l' fp pc'.
    Proof.
      intros.
      apply star_stepN in H1 as [].
      revert pc l fp pc' H H0 H1;induction x using(well_founded_induction lt_wf);intros.
    
      inversion H2;subst.
      Esimpl. econstructor;eauto. constructor.
      destruct (atom_bit pc'0) eqn:?.
      {
        eapply H in H3 as ?;eauto.
        Hsimpl.
    
        destruct l0.
        assert(non_evt_star glob_step pc (FP.union fp0 FP.emp) pc'0).
        econstructor;eauto. constructor.
        eapply non_evt_star_cons_Evt_gstar in H6 as ?;eauto.
        rewrite FP.fp_union_emp in H7. eauto.
    
        assert(non_evt_star glob_step pc (FP.union fp0 FP.emp) pc'0).
        econstructor;eauto. constructor.
        eapply non_evt_star_cons_Evt_gstar in H6 as ?;eauto.
        rewrite FP.fp_union_emp in H7. eauto.
    
        assert(noevt_stepN glob_step 0 pc FP.emp pc). constructor.
        assert(fp0=FP.emp). inversion H4;auto. subst.
        exists (S x),(cons (evt v) x0).
        econstructor;try apply H6;eauto.
      }
      {
        eapply stepN_IO in H3;eauto.
        Hsimpl.
        assert(l0=tau /\ fp0=FP.emp).
        inversion H4;subst;simpl in *;subst;try inversion Heqb;try inversion H0;auto.
        Hsimpl;subst.
        assert(non_evt_star glob_step pc x1 x3).
        apply corestepN_nonevtstar in H3.
        apply type_glob_step_elim in H5.
        assert(non_evt_star glob_step pc (FP.union FP.emp x1) x2).
        econstructor;eauto.
        assert(non_evt_star glob_step x2 (FP.union FP.emp FP.emp) x3).
        econstructor;eauto. constructor.
        eapply non_evt_star_cons in H8;eauto.
        rewrite FP.emp_union_fp in H8.
        repeat rewrite FP.fp_union_emp in H8.
        auto.
    
        eapply H in H6 as ?;eauto. Hsimpl.
        eapply non_evt_star_cons_Evt_gstar in H7;eauto.
        rewrite FP.emp_union_fp;eauto.
        Omega.omega.
        inversion H5;auto.
      }
    Qed.
    
    
    
    Lemma Evt_gstar_to_alter:
      forall i pc l fp pc',
        invpc pc->
        Evt_gstar i pc l fp pc'->
        exists pc0,sw_star glob_step pc pc0 /\
        ((exists j l1 fp1 pc1,Evt_gstar_alter j pc0 l1 fp1 pc1 /\
                        exists k l2 fp2 pc2, atomblockstarN k l2 pc1 fp2 pc2 /\
                                        (race glob_predict_star_alter pc2 \/ predicted_abort1 pc2)) \/ 
        exists pc'',Evt_gstar_alter i pc0 l fp pc'' /\ mem_eq_pc GE pc' pc'').
    Proof.
      pose wdge;pose modwdge.
      induction i;intros.
      {
        inversion H0;clear H0;subst.
        apply starbase_nonevt_alter in H3;auto.
        Esimpl;eauto. constructor.
        right. Esimpl;eauto. apply mem_eq_pc_refl.
      }
      {
        inversion H0;clear H0;subst.
        apply type_glob_step_exists in H5 as [x];destruct x;subst;try(inversion H0;fail).
        eapply noevt_stepN_evtstep_inv in H4 as ?;eauto.
        Hsimpl. destruct H5;Hsimpl.
        {
          Esimpl;eauto.
          left;Esimpl;eauto.
          apply atomblockstarN_atomO in H5 as [].
          econstructor;auto. constructor.
        }
        {
          rename H9 into Q1.
          rename H10 into H9,H11 into H10,H12 into H11.
          eapply mem_eq_evt_gstar in H10 as ?;eauto;Hsimpl.
          assert(glob_step x8 sw FP.emp ({-|x8,cur_tid pc''})).
          {
            apply noevt_stepN_sound in H4.
            apply non_evt_star_star in H4 as [].
            apply GE_mod_wd_star_tp_inv2 in H4;auto.
            apply type_glob_step_elim in H0.
            eapply GE_mod_wd_tp_inv in H4;eauto.
            assert(cur_valid_id pc'').
            inversion H0;subst. split. eapply gettop_valid_tid;auto. solv_thread.
            intro;solv_thread.
            inversion H10 as (?&?&?&?);simpl in *.
            destruct H14. rewrite H15 in *.
            assert(atom_bit pc'' = O). inversion H0;auto.
            rewrite H20 in H16.
            destruct x8;simpl in *;subst. econstructor;eauto.
          }
          apply npnsw_or_sw_star_non_evt_star in H9.
          assert(non_evt_star glob_step x8 (FP.union FP.emp FP.emp) ({-|x8,cur_tid pc''})).
          econstructor 2;eauto. constructor.
          assert(L:atom_bit x8 = O). inversion H14;auto.
          assert(L2:atom_bit x6 = O). inversion H8;auto.
          eapply non_evt_star_cons_Evt_gstar in H15;eauto.
          eapply non_evt_star_cons_Evt_gstar in H9;eauto.
          repeat rewrite FP.emp_union_fp in H9.
    
          clear x8 L H10 H12 H14 H15.
          eapply IHi in H9 as ?;eauto.
          Hsimpl.
    
          destruct H12;Hsimpl.
          {
            Esimpl;eauto.
            left.
            Esimpl;eauto.
            econstructor 2;eauto.
          }
          {
            Esimpl;eauto.
            right.
            rewrite <- H11.
            eapply cons_evtstep_alter in H12;try apply H5;eauto.
            
            rewrite FP.fp_union_assoc.
            rewrite <- FP.fp_union_assoc.
            Esimpl;eauto.
            eapply mem_eq_pc_trans;eauto.
          }
          assert(invpc x). apply swstar_l1 in H1. rewrite H1;auto.
          apply atomblockstarN_invpc_preservation in H5;auto.
          apply npnsw_taustar_thdpinv in H7;auto.
          eapply GE_mod_wd_tp_inv in H8;eauto.
        }
      }
    Qed.
    Lemma atomblockstep_np:
      forall pc l0 fp pc',
        invpc pc ->
        atomblockstep pc l0 fp pc'->
        exists pc1,non_evt_star np_step pc fp pc1/\
                np_step pc1 sw FP.emp pc'.
    Proof.
      inversion 2;subst.
      apply atomblockstep_invpc_preserve in H0 as R;auto.
      clear H0.
      destruct H2.
      destruct H0;Hsimpl.
    
      apply tauN_taustar in H1.
      eapply star_core_step_equiv in H1.
      assert(tau_star np_step x0 fp x1). revert H1;clear;induction 1;intros;econstructor;eauto. apply type_step_elim in H;auto.
      apply tau_star_non_evt_star in H3.
      apply entat_step_equiv in H0.
      apply type_step_elim in H0.
      eapply ne_star_step in H3;eauto.
      
      assert(glob_step pc' sw FP.emp pc').
      inversion H2;subst. econstructor;eauto.
      eapply gettop_valid_tid;eauto. solv_thread.
      intro;solv_thread.
    
      assert(type_np_step extat x1 sw FP.emp pc').
      inversion H2;subst;inversion H4;subst;econstructor;eauto.
      apply type_step_elim in H5.
      rewrite FP.emp_union_fp in H3.
      Esimpl;eauto.
    Qed.
    Lemma npsw_swstar:
      forall pc pc' pc'',
        @np_step GE pc sw FP.emp pc'->
        sw_star glob_step pc' pc''->
        np_step pc sw FP.emp pc''.
    Proof.
      induction 2;intros. auto.
      apply IHsw_star.
      inversion H;subst;inversion H0;subst;econstructor;eauto.
    Qed.

    Lemma npevt_swstar:
      forall pc pc' pc'' v,
        @np_step GE pc (evt v) FP.emp pc'->
        sw_star glob_step pc' pc''->
        np_step pc (evt v) FP.emp pc''.
    Proof.
      induction 2;intros. auto.
      apply IHsw_star.
      inversion H;subst;inversion H0;subst;econstructor;eauto.
    Qed.

    Lemma haltstep_np:
      forall pc l fp pc',
        haltstep pc l fp pc'->
        (exists t,np_step pc sw FP.emp ({-|pc',t})) \/ type_np_step allhalt pc tau FP.emp pc'.
    Proof.
      intros.
      assert((exists pc'',glob_step pc' sw FP.emp pc'') \/ ~(exists pc'',glob_step pc' sw FP.emp pc'')).
      apply classic.
      destruct H0;auto.
      {
        left.
        destruct H0. exists (cur_tid x).
        inversion H;subst;inversion H0;subst.
        econstructor;eauto.
      }
      right.
      inversion H;subst.
      econstructor;eauto.
      intros.
      apply NNPP;intro.
      contradict H0.
      eexists. econstructor;eauto.
    Qed.
    Lemma allhalt_swstar:
      forall pc pc' pc'',
        @type_np_step GE allhalt pc tau FP.emp pc'->
        sw_star glob_step pc' pc''->
        pc' = pc''.
    Proof.
      inversion 2;subst. auto.
      inversion H;subst.
      inversion H1;subst.
      apply H_all_thread_halted in H_thread_valid.
      contradiction.
    Qed.
      

    Lemma atomblockstar1_np:
      forall l pc fp pc',
        invpc pc ->
        atomblockstarN 1 l pc fp pc'->
        exists pc1,non_evt_star np_step pc fp pc1/\
                     ((exists t,np_step pc1 sw FP.emp ({-|pc',t}) ) \/ type_np_step allhalt pc1 tau FP.emp pc').
    Proof.
      pose wdge;pose modwdge.
      intros.
      apply atomblockstarN_invpc_preservation in H0 as ?;auto.
      inversion H0;subst.
      destruct H4.
      {
        apply npnsw_taustar_thdpinv in H3 as ?;auto.
        apply atomblockstep_np in H2;auto.
        Hsimpl.
        apply glob_npnsw_star_to_np_taustar in H3.
        apply tau_star_non_evt_star in H3.
        eapply non_evt_star_cons in H2;eauto.
        eapply npsw_swstar in H7;eauto.
        inversion H6;subst.
        rewrite FP.fp_union_emp.
        Esimpl;eauto.
        left;Esimpl;eauto. rewrite pc_cur_tid;eauto.
      }
      {
        assert(fp2=FP.emp). inversion H2;auto. subst.
        apply haltstep_np in H2.
        apply glob_npnsw_star_to_np_taustar in H3.
        apply tau_star_non_evt_star in H3.
        inversion H6;subst.
        do 2 rewrite FP.fp_union_emp. 
        destruct H2;Hsimpl;Esimpl;eauto.
      
        apply swstar_l1 in H5.
        rewrite H5.
        left. Esimpl;eauto.
        
        eapply allhalt_swstar in H5;eauto. subst.
        right;eauto.
      }
    Qed.
    
    Lemma atomblockstarN_np:
      forall i l pc fp pc',
        i > 0 ->
        invpc pc ->
        atomblockstarN i l pc fp pc'->
        exists pc1,non_evt_star np_step pc fp pc1/\
                     ((exists t,np_step pc1 sw FP.emp ({-|pc',t})) \/ type_np_step allhalt pc1 tau FP.emp pc').
    Proof.
      pose wdge;pose modwdge.
      induction i;intros.
      inversion H.
    
      destruct i.
      eapply atomblockstar1_np ;eauto.
    
      apply atomblockstarN_SN_N1_split in H1.
      Hsimpl.
    
      apply atomblockstarN_invpc_preservation in H1 as ?;auto.
      eapply IHi in H1;eauto;[|Omega.omega].
      Hsimpl.
      
      destruct H6.
      {
        Hsimpl;subst.
        apply atomblockstarN_cur_valid_tid in H2 as ?;auto.
        assert(np_step x4 sw FP.emp x1).
        inversion H6;subst;destruct x1,H3;simpl in *;subst;try econstructor;eauto.
        
        apply atomblockstar1_np in H2;auto.
        Hsimpl.
        eapply ne_star_step in H2;[|right;eauto].
        eapply non_evt_star_cons in H2;eauto.
      }
      {
        apply atomblockstarN_cur_valid_tid in H2 as [];auto.
        contradict H7.
        inversion H6;subst;eauto.
      }
    Qed.
    Lemma evtstep_np:
      forall pc v pc',
        invpc pc->
        @glob_step GE pc (evt v)FP.emp pc'->
        np_step pc (evt v) FP.emp pc'.
    Proof.
      pose wdge.
      intros. apply GE_mod_wd_tp_inv in H0 as ?;auto.
      inversion H0;subst.
      econstructor;eauto. eapply gettop_valid_tid;solv_thread.
      intro;solv_thread.
    Qed.
    Lemma noevt_stepN_np:
      forall i pc fp pc',
        noevt_stepN glob_step i pc fp pc'->
        i>0->
        atom_bit pc = O ->
        atom_bit pc' = O->
        invpc pc->
        exists pc1,sw_star glob_step pc pc1 /\
              ((exists pc2,npnsw_or_sw_star pc1 fp pc2 /\ mem_eq_pc GE pc' ({-|pc2,cur_tid pc'})) \/
              (exists j l fp' pc2,atomblockstarN j l pc1 fp' pc2 /\ (race glob_predict_star_alter pc2 \/ predicted_abort1 pc2))\/
              (exists l1 fp' pc2,star np_step pc1 l1 fp' pc2 /\
                            exists pc3,((exists t,np_step pc2 sw FP.emp ({-|pc3,t})) \/ type_np_step allhalt pc2 tau FP.emp pc3)/\
                             exists fp'' pc4,npnsw_or_sw_star pc3 fp'' pc4 /\
                                        mem_eq_pc GE pc' ({-|pc4,cur_tid pc'}) /\
                                        FP.union fp' fp'' = fp)).
    Proof.
      intros.
      eapply noevt_stepN_Si_to_atomblockstarN in H;eauto.
      Hsimpl.
      destruct H4 as [|[|[]]].
      Hsimpl. Esimpl;eauto.
      right;left. Esimpl;eauto.
      
      Esimpl;eauto.
      right;left. Esimpl;eauto. constructor;auto. inversion H4. inversion H6;auto.

      Hsimpl.
      Esimpl;eauto. right;left;Esimpl;eauto.
    
      Hsimpl.
      destruct x0.
      inversion H4;subst.
      Esimpl;eauto. left. Esimpl;eauto. rewrite FP.emp_union_fp;auto.
    
    
      apply atomblockstarN_np in H4;auto.
      Hsimpl.
      destruct H8.
      {
        Hsimpl.
        Esimpl;eauto. right. right.
        apply non_evt_star_star in H4 as [].
        Esimpl;eauto.
      }
      {
        Esimpl;eauto. right;right.
        apply non_evt_star_star in H4 as [].
        Esimpl;eauto.
      }
      Omega.omega.
      erewrite swstar_l1;eauto.
    Qed.
    
    Lemma predict_tid:
      forall pc,
        invpc pc ->
        forall t fp,
          glob_predict_star_alter pc t O fp->
          fp<>FP.emp->
          @pc_valid_tid GE pc t.
    Proof.
      inversion 2;subst;intros.
      eapply npnsw_star_fpnotemp_cur_valid_id in H1;eauto.
    Qed.
    Lemma race_tid_exists:
      forall pc,
        invpc pc->
        race glob_predict_star_alter pc->
        exists t,
          @pc_valid_tid GE pc t.
    Proof.
      intros.
      inversion H0;subst.
      assert(b1 = O \/ b2 = O). destruct b1,b2;auto.
      destruct H4;contradiction.
      
      destruct H6;subst;eexists;eapply predict_tid;eauto;intro;subst;apply FP.emp_never_conflict in H5 as [];contradiction.
    Qed.
    Lemma noevt_stepN_evt_np:
      forall i pc fp pc' v pc'',
        noevt_stepN glob_step i pc fp pc'->
        evtstep pc' (evt v) FP.emp pc'' ->
        atom_bit pc = O ->
        atom_bit pc' = O->
        invpc pc->
        exists pc1,sw_star glob_step pc pc1 /\
              ((exists j l fp' pc2,atomblockstarN j l pc1 fp' pc2 /\ (race glob_predict_star_alter pc2 \/ predicted_abort1 pc2))\/
              (exists l1 fp' pc2,star np_step pc1 l1 fp' pc2 /\
                            exists pc3 ,np_step pc2 (evt v) FP.emp pc3/\
                             exists fp'' pc4,npnsw_or_sw_star pc3 fp'' pc4 /\
                                        mem_eq_pc GE pc'' ({-|pc4,cur_tid pc''}) /\
                                        FP.union fp' fp'' = fp)).
    Proof.
      pose wdge ;pose modwdge.
      intros.
      eapply noevt_stepN_evtstep_inv in H as ?;eauto.
    
      Hsimpl.
      destruct H5;Hsimpl.
      Esimpl;eauto;left;Esimpl;eauto.
    
      destruct x0.
      {
        inversion H5;subst.
        apply glob_npnsw_star_to_np_taustar in H6.
        apply tau_star_to_star in H6 as [].
        apply evtstep_np in H7.
        Esimpl;eauto. right;Esimpl;eauto.
        eapply thdp_inv_npstar;eauto.
        apply swstar_l1 in H4.
        rewrite H4;auto.
      }
      {
        rename H8 into Q1,H9 into H8,H10 into H9,H11 into H10.
        eapply atomblockstarN_np in H5;[|Omega.omega|erewrite swstar_l1;eauto].
        Hsimpl.
        apply non_evt_star_star in H5 as [].
        assert(L1:invpc x3).
        assert(invpc x). apply swstar_l1 in H4. rewrite H4;auto.
        apply thdp_inv_npstar in H5;auto.
        assert(invpc x3).
        destruct H11;Hsimpl.
        assert(invpc ({-|x3,x11})).
        eapply thdp_inv_npstar in H5;eauto. eapply star_step;[|constructor];eauto.
        auto.
        eapply thdp_inv_npstar in H5;eauto. eapply star_step;[eapply type_step_elim|constructor];eauto. auto.
        
        assert(L2:invpc x5).
        eapply npnsw_taustar_thdpinv;eauto.
        assert(L3:cur_valid_id x3).
        eapply cur_valid_id_case1;eauto.
        destruct H11.
        {
          Hsimpl.
          
          assert(np_step x9 sw FP.emp x3).
          inversion H11;subst;destruct x3,L3;simpl in *;subst; try econstructor;eauto.     
          apply glob_npnsw_star_to_np_taustar in H6.
          apply tau_star_to_star in H6 as [].
          apply evtstep_np in H7.
          eapply star_step in H6 as ?;eauto.
          eapply cons_star_star in H13;eauto.
          Esimpl;eauto. right;Esimpl;eauto.
          rewrite FP.emp_union_fp.
          rewrite <-FP.fp_union_assoc.
          auto.
          auto.
        }
        {
          revert H11 L3;clear;intros.
          destruct L3.
          contradict H0.
          inversion H11;subst;eauto.
        }
      }
    Qed.
    

    Lemma allhalt_not_step:
      forall pc pc',
        @type_np_step GE allhalt pc tau FP.emp pc'->
        forall l fp pc'',
          np_step pc' l fp pc''->
          False.
    Proof.  
      intros. apply npstep_nothalted in H0.
      inversion H;subst. eauto.
    Qed.
    Lemma allhalt_not_abort:
      forall pc pc',
        @type_np_step GE allhalt pc tau FP.emp pc'->
        predicted_abort1 pc'->
        False.
    Proof.
      intros.
      inversion H0;subst.
      inversion H1;subst. unfold halfatomblock_abort,halfatomblockstep in H2.
      Hsimpl. eapply type_glob_step_elim in H4. apply globstep_nothalted in H4.
      inversion H;subst;auto.
      intro R;inversion R.

      apply npnswstep_l1 in H3;Hsimpl;apply type_glob_step_elim in H3;apply globstep_nothalted in H3;inversion H;subst;auto.
      intro R;inversion R.

      unfold npnsw_star_abort in H2.
      Hsimpl. inversion H2;subst.
      destruct H3. inversion H;subst;auto.
      apply npnswstep_l1 in H4;Hsimpl;apply type_glob_step_elim in H4;apply globstep_nothalted in H4;inversion H;subst;auto.
      intro R;inversion R.
    Qed.
    Lemma allhalt_not_abort2:
      forall pc pc' t
        (v1:invpc pc),
        @type_np_step GE allhalt pc tau FP.emp pc'->
        predicted_abort1 ({-|pc',t})->
        False.
    Proof.
      intros.
      apply predicted_abort1_sw in H0 as v2;auto. destruct v2 as [t1 t2].
      inversion H0;subst.
      inversion H1;subst. unfold halfatomblock_abort,halfatomblockstep in H2.
      Hsimpl. eapply type_glob_step_elim in H4. apply globstep_nothalted in H4.
      inversion H;subst;auto. 
      intro R;inversion R.

      apply npnswstep_l1 in H3;Hsimpl;apply type_glob_step_elim in H3;apply globstep_nothalted in H3;inversion H;subst;auto. 

      unfold npnsw_star_abort in H2.
      Hsimpl. inversion H2;subst.
      destruct H3. inversion H;subst;auto.
      apply npnswstep_l1 in H4;Hsimpl;apply type_glob_step_elim in H4;apply globstep_nothalted in H4;inversion H;subst;auto.

      inversion H;subst;eapply ThreadPool.pop_inv;eauto.
    Qed.

    Lemma npsw_predicted_abort:
      forall pc fp pc' t,
        invpc pc->
        np_step pc sw fp pc'->
        @predicted_abort1 GE ({-|pc',t})->
        np_step pc sw fp ({-|pc',t}).
    Proof.
      intros. assert(fp=FP.emp). inversion H0;auto. subst.
      eapply npsw_swstar;eauto.
      econstructor 2;eauto;[|constructor].
      apply predicted_abort1_O in H1 as ?.
      apply predicted_abort1_sw in H1;auto.
      destruct pc',H1;simpl in *;subst;econstructor;eauto.
      assert(star np_step pc (cons sw nil) (FP.union FP.emp FP.emp) pc').
      econstructor ;eauto. constructor.
      eapply thdp_inv_npstar in H3;eauto.
    Qed.
    Lemma npevt_predicted_abort:
      forall pc fp pc' t v,
        invpc pc->
        np_step pc (evt v) fp pc'->
        @predicted_abort1 GE ({-|pc',t})->
        np_step pc (evt v) fp ({-|pc',t}).
    Proof.
      intros. assert(fp=FP.emp). inversion H0;auto. subst.
      eapply npevt_swstar;eauto.
      econstructor 2;eauto;[|constructor].
      apply predicted_abort1_O in H1 as ?.
      apply predicted_abort1_sw in H1;auto.
      destruct pc',H1;simpl in *;subst;econstructor;eauto.
      assert(star np_step pc (cons (evt v) nil) (FP.union FP.emp FP.emp) pc').
      econstructor ;eauto. constructor.
      eapply thdp_inv_npstar in H3;eauto.
    Qed.
    Lemma Evt_gstar_nprace:
      forall i pc l fp pc',
        invpc pc->
        Evt_gstar i pc l fp pc'->
        (race glob_predict_star_alter pc' \/ (exists t,predicted_abort1 ({-|pc',t})))->
        (race glob_predict_star_alter pc \/ (exists t,predicted_abort1 ({-|pc,t}))) \/
        exists pc1,
          sw_star glob_step pc pc1/\
          exists l1 fp1 pc2,star np_step pc1 l1 fp1 pc2 /\
                       exists l2 pc3,np_step pc2 l2 FP.emp pc3 /\ l2 <> tau /\
                                (race glob_predict_star_alter pc3 \/ predicted_abort1 pc3).
    Proof.
      pose wdge.
      induction i;intros.
      {
        inversion H0;subst.
        destruct i.
        {
          apply noevt_stepN_0 in H4 as ?. Hsimpl. subst.
          apply swstar_l1 in H6.
          rewrite H6 in H1.
          destruct H1.
          eapply race_changetid in H1;simpl in H1;erewrite pc_cur_tid in H1.
          auto.
          Hsimpl. simpl in H1. left. eauto.
        }
        {
          apply noevt_stepN_np in H4;auto;[|Omega.omega].
          Hsimpl.
          
          destruct H5 as [|[|]];Hsimpl.
          {
            erewrite swstar_l1 with(pc':=x) in H5;eauto.
            destruct H1.
            eapply mem_eq_race in H6;eauto.
            eapply race_changetid in H6;simpl in H6;erewrite pc_cur_tid in H6.
            eapply npnsw_or_sw_stepN_exists in H5;auto;Hsimpl.
            eapply npnsw_or_sw_stepN_race in H5;eauto.
            destruct H5.
            eapply race_changetid in H5;simpl in H5;erewrite pc_cur_tid in H5;eauto.
            Hsimpl. eauto.

            Hsimpl.
            apply mem_eq_pc_change with(t:= x1) in H6.
            apply mem_eq_predicted_abort1 in H6;eauto. simpl in H6.
            eapply npnsw_or_sw_stepN_exists in H5;auto;Hsimpl.
            eapply npnsw_or_sw_stepN_race in H5;eauto.
            destruct H5.
            eapply race_changetid in H5;simpl in H5;erewrite pc_cur_tid in H5;eauto.
            Hsimpl. eauto.
          }
          {
            destruct x0.
            {
              inversion H5;subst.
              destruct H6;try erewrite swstar_l1 in H6;eauto.
              eapply race_changetid in H6;simpl in H6;erewrite pc_cur_tid in H6;eauto.
            }
            {
              apply atomblockstarN_np in H5;[|Omega.omega|erewrite swstar_l1;eauto].
              Hsimpl.
              destruct H7.
              {
                Hsimpl.
                right.
                apply non_evt_star_star in H5 as [].
                destruct H6.
                Esimpl;eauto.
                intro contra;inversion contra. left; eapply race_changetid;eauto.
                apply predicted_abort1_sw in H6 as ?;auto.
                assert(sw_star glob_step ({-|x3,x5}) x3).
                econstructor 2;[|constructor]. apply predicted_abort1_O in H6.
                destruct x3,H8;simpl in *;subst;econstructor;eauto.
                eapply npsw_swstar in H7;eauto.
                Esimpl;eauto. intro R;inversion R.
                apply swstar_l1 in H4. rewrite H4 in *;subst.
                eapply star_cons_step in H7 as [];eauto.
                eapply thdp_inv_npstar in H7;eauto.
              }
              {
                destruct H6.
                apply race_tid_exists in H6 as [?[]].
                contradict H8;inversion H7;subst;eauto.
                apply swstar_l1 in H4.
                rewrite H4 in *.
                apply non_evt_star_star in H5 as [].
                apply thdp_inv_npstar in H5;auto.
                apply type_step_elim in H7.
                eapply thdp_inv_npstar;eauto.
                eapply star_step;[|constructor];eauto.
                
                eapply allhalt_not_abort in H7;eauto.
                contradiction.
              }
            }
          }
          {
            destruct H1.
            eapply mem_eq_race in H8 as ?;eauto.
            eapply  race_changetid in H10;simpl in H10;erewrite pc_cur_tid in H10.
            assert(atom_bit x3 = O).
            destruct H6;Hsimpl.
            destruct x6;try contradiction;inversion H6;auto.
            inversion H6;auto.
            eapply npnsw_or_sw_stepN_exists in H7;auto;Hsimpl.
            assert(L:invpc x3).
            apply swstar_l1 in H4. rewrite H4 in *.
            pose wdge.
            apply thdp_inv_npstar in H5;auto.
            destruct H6;Hsimpl.
            assert(invpc ({-|x3,x8})).
            eapply thdp_inv_npstar;eauto.
            eapply star_step;[|constructor];eauto. auto.
            eapply thdp_inv_npstar;eauto.
            eapply star_step;[eapply type_step_elim|constructor];eauto.  
            
            Hsimpl.
            eapply npnsw_or_sw_stepN_race in H7;eauto.
            destruct H6,H7.
            {
              Hsimpl.
              apply race_changetid with(t:=x8) in H7.
              right;Esimpl;eauto.
              intro contra;inversion contra.
            }
            {
              Hsimpl.
              assert(sw_star glob_step ({-|x3,x9}) ({-|x3,x8})).
              econstructor 2;[|constructor].
              apply predicted_abort1_O in H7 as ?;auto.
              apply predicted_abort1_sw in H7;auto.
              destruct x3,H7;simpl in *;subst;econstructor;eauto.
              eapply npsw_swstar in H6;eauto.
              right. Esimpl;eauto.
              intro R;inversion R.
            }
            {
              apply race_tid_exists in H7 as [?[]];auto.
              contradict H12;inversion H6;subst;eauto.
            }
            {
              Hsimpl.
              assert(sw_star glob_step x3 ({-|x3,x8})).
              econstructor 2;[|constructor].
              apply predicted_abort1_O in H7 as ?;auto.
              apply predicted_abort1_sw in H7;auto.
              destruct x3,H7;simpl in *;subst;econstructor;eauto.
              eapply npsw_swstar in H12;eauto.
              right. Esimpl;eauto.
              intro R;inversion R.

              eapply allhalt_not_abort2 in H6;eauto.
              contradiction.
              apply swstar_l1 in H4.
              rewrite H4 in H5.
              eapply GE_mod_wd_npstar_tp_inv;eauto.
            }


            Hsimpl.
            apply mem_eq_pc_change with(t:= x6) in H8 as?.
            eapply mem_eq_predicted_abort1 in H10;eauto.
            simpl in *.
            assert(atom_bit x3 = O).
            destruct H6;Hsimpl.
            destruct x6;try contradiction;inversion H6;auto.
            inversion H6;auto.
            eapply npnsw_or_sw_stepN_exists in H7;auto;Hsimpl.
            assert(L:invpc x3).
            apply swstar_l1 in H4. rewrite H4 in *.
            apply thdp_inv_npstar in H5;auto.
            destruct H6;Hsimpl. assert(invpc ({-|x3,x9})).
            eapply thdp_inv_npstar;eauto.
            eapply star_step;[|constructor];eauto. auto.
            eapply thdp_inv_npstar;eauto.
            eapply star_step;[eapply type_step_elim|constructor];eauto.
            
            
            Hsimpl.
            eapply npnsw_or_sw_stepN_race in H7;eauto.
            destruct H6,H7.
            {
              Hsimpl.
              apply race_changetid with(t:=x9) in H7.
              right;Esimpl;eauto.
              intro contra;inversion contra.
            }
            {
              Hsimpl.
              assert(sw_star glob_step ({-|x3,x10}) ({-|x3,x9})).
              econstructor 2;[|constructor].
              apply predicted_abort1_O in H7 as ?;auto.
              apply predicted_abort1_sw in H7;auto.
              destruct x3,H7;simpl in *;subst;econstructor;eauto.
              eapply npsw_swstar in H6;eauto.
              right. Esimpl;eauto.
              intro R;inversion R.
            }
            {
              apply race_tid_exists in H7 as [?[]];auto.
              contradict H12;inversion H6;subst;eauto.
            }
            {
              Hsimpl.
              assert(sw_star glob_step x3 ({-|x3,x9})).
              econstructor 2;[|constructor].
              apply predicted_abort1_O in H7 as ?;auto.
              apply predicted_abort1_sw in H7;auto.
              destruct x3,H7;simpl in *;subst;econstructor;eauto.
              eapply npsw_swstar in H12;eauto.
              right. Esimpl;eauto.
              intro R;inversion R.

              eapply allhalt_not_abort2 in H6;eauto.
              contradiction.
              apply swstar_l1 in H4.
              rewrite H4 in H5.
              eapply GE_mod_wd_npstar_tp_inv;eauto.
            }
          }
        }
      }
      {
        inversion H0;subst.
        eapply type_glob_step_exists in H6 as [].
        destruct x;subst;try(inversion H2;fail).
        eapply noevt_stepN_evt_np in H5 as ?;eauto.
    
        Hsimpl.
        destruct H8.
        {
          Hsimpl.
          destruct x0.
          {
            inversion H8;subst.
            apply swstar_l1 in H6. rewrite H6 in H9.
            destruct H9. eapply race_changetid with(t:=cur_tid pc) in H9;eauto.
            left. left. rewrite <- pc_cur_tid with(pc:=pc). auto.
            left;right;eauto.
          }
          {
            erewrite swstar_l1 with(pc':=x) in H8;eauto.
            apply atomblockstarN_np in H8;auto;[|Omega.omega].
            Hsimpl.
            destruct H10.
            {
              Hsimpl.
              destruct H9.
              apply race_changetid with(t:=x5) in H9.
              apply non_evt_star_star in H8 as [].
              right. Esimpl;eauto. erewrite <- swstar_l1 in H8;eauto.
              intro R;inversion R.
              rewrite <- pc_cur_tid in H9.
              eapply npsw_predicted_abort in H10;eauto.
              simpl in *.
              apply non_evt_star_star in H8 as [].
              right;Esimpl;eauto. erewrite <- swstar_l1 in H8;eauto.
              intro R;inversion R.
              apply non_evt_star_star in H8 as [].
              eapply thdp_inv_npstar in H8;eauto.
            }
            {
              destruct H9.
              apply race_tid_exists in H9 as [?[]].
              contradict H11. inversion H10;subst;eauto.
              apply non_evt_star_star in H8 as [].
              apply thdp_inv_npstar in H8;auto.
              apply type_step_elim in H10.
              eapply thdp_inv_npstar;eauto. eapply star_step;eauto. constructor.

              eapply allhalt_not_abort in H10;eauto.
              contradiction.
            }
          }
        }
        {
          assert(P1:cur_valid_id pc'').
          assert(invpc pc'').
          apply noevt_stepN_sound in H5.
          apply non_evt_star_star in H5 as [].
          apply GE_mod_wd_star_tp_inv2 in H5;auto.
          apply type_glob_step_elim in H2.
          eapply GE_mod_wd_tp_inv;eauto.
          revert H2 H9;clear;intros.
          inversion H2;subst. split;[eapply gettop_valid_tid|intro];solv_thread.
          Hsimpl.
          eapply mem_eq_evt_gstar in H11 as ?;eauto.
          Hsimpl.
          assert(race glob_predict_star_alter x6 \/ exists t,predicted_abort1 ({-|x6,t})).
          destruct H1.
          eapply mem_eq_race in H14 as ?;eauto.
          Hsimpl. apply mem_eq_pc_change with(t:=x7) in H14; eapply mem_eq_predicted_abort1 in H14;eauto. 
          assert(invpc x5).
          eapply npnsw_or_sw_star_non_evt_star in H10.
          apply non_evt_star_star in H10 as [].
          eapply GE_mod_wd_star_tp_inv2 in H10;eauto.
          eapply star_cons_step in H9 as [];eauto.
          eapply thdp_inv_npstar;eauto.
          apply swstar_l1 in H6;rewrite H6;auto.
          assert(pc_valid_tid x5 (cur_tid pc'')).
          inversion H11 as (?&?&?&?);destruct P1;simpl in *;subst;split;try congruence.
          assert(atom_bit x5=O).  inversion H2;subst. inversion H11 as (?&?&?&?);simpl in *;subst. auto.
          assert(glob_step x5 sw FP.emp ({-|x5,cur_tid pc''})).
          
          destruct x5,H17;simpl in *;subst;econstructor;eauto.
    
          apply npnsw_or_sw_star_non_evt_star in H10 as ?.
          assert(non_evt_star glob_step x5 FP.emp ({-|x5,cur_tid pc''})).
          rewrite <- FP.fp_union_emp with(fp:=FP.emp).
          econstructor. right;eauto. constructor.
          eapply non_evt_star_cons_Evt_gstar in H21;eauto.
          assert(atom_bit x3 = O). inversion H9;auto.
          eapply non_evt_star_cons_Evt_gstar in H20;eauto.
    
          eapply IHi in H20 as ?;eauto.
          destruct H23;Hsimpl.
          {
            destruct H23.
            right;Esimpl;eauto.
            intro R;inversion R.
            Hsimpl.
            eapply npevt_predicted_abort in H9;eauto.
            right;Esimpl;eauto.
            intro R;inversion R.
            apply swstar_l1 in H6;rewrite H6 in H8;eapply thdp_inv_npstar in H8;eauto.
          }
          {
            assert(invpc x2). eapply thdp_inv_npstar in H8;eauto.
            apply swstar_l1 in H6;rewrite H6;auto.
            assert(np_step x2 (evt v) FP.emp x7).
            revert H23 H28 H9;clear.
            intro;revert x2;induction H23;intros;auto.
            apply IHsw_star. eauto.
            inversion H9;subst;inversion H;subst.
            econstructor;eauto.
    
            eapply star_step in H24;eauto.
            eapply cons_star_star in H24;eauto.
            right;Esimpl;eauto.
          }
          eapply star_cons_step in H9 as [];eauto.
          eapply thdp_inv_npstar ;eauto.
          apply swstar_l1 in H6;rewrite H6;auto.
        }
      }
    Qed.
    
    Lemma globrace_equiv2:
      forall pc,
        @race GE glob_predict_star_alter pc ->
        invpc pc->
        star_race glob_predict pc.
    Proof.
      intros.
      assert(atom_bit pc = O). inversion H;subst;auto. inversion H2;auto.
      eapply nppredictrace_globpredictstaraltrace_equiv in H.
      apply nprace_equiv in H.
      apply np_race_config_np_race_config_base_equiv in H;auto.
      eapply np_race_config_base_star_race;eauto.
    Qed.

    Lemma abort_eq:
      forall ge pc,
        @abort ge pc ->
        ThreadPool.valid_tid pc.(thread_pool) pc.(cur_tid) ->
        np_abort pc.
    Proof.
      unfold abort,np_abort.
      intros.
      Hsimpl;split;auto.
      intro.
      inversion H2;subst. contradict H;eauto.
      
      intros. intro.
      apply type_step_exists in H2 as [].
      destruct x;try(inversion H2;fail);destruct gl;try (inversion H2;fail).
      apply core_step_equiv in H2;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
      apply call_step_equiv in H2;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
      apply ret_step_equiv in H2;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
      apply entat_step_equiv in H2;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
      assert(fp=FP.emp). inversion H2;auto. subst.
      apply extat_step_equiv in H2;Hsimpl;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
      assert(fp=FP.emp). inversion H2;auto. subst.
      apply thrdhalt_step_equiv in H2;Hsimpl;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
      assert(fp=FP.emp). inversion H2;auto. subst.
      apply allhalt_step_equiv in H2;Hsimpl;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
      assert(fp=FP.emp). inversion H2;auto. subst.
      apply efprint_step_equiv in H2;Hsimpl;apply type_glob_step_elim in H2;eapply H1 in H2;inversion H2.
    Qed.
    
    

    (*Stop*)

    Lemma np_corestar_npstar:
      forall pc fp pc',
        tau_star (@type_np_step GE core) pc fp pc'->
        tau_star np_step pc fp pc'.
    Proof.
      induction 1;intros;econstructor.
      eapply type_step_elim. eauto.
      auto.
    Qed.
    Lemma globcorestar_npnswstar:
      forall pc fp pc',
        tau_star (@type_glob_step GE core) pc fp pc'->
        tau_star glob_npnsw_step pc fp pc'.
    Proof.
      induction 1;intros;econstructor.
      left;eauto. auto.
    Qed.
    Lemma predicted_abort1_not_npsafe:
      forall pc,
        invpc pc->
        @predicted_abort1 GE pc ->
        ~ safe_state np_step np_abort pc.
    Proof.
      intros. intro.
      inversion H0;subst. 
      apply glob_npnsw_star_to_np_taustar in H2.
      unfold halfatomblock_abort,halfatomblockstep in H3.
      Hsimpl.
      enough(cur_valid_id x0).
      apply entat_step_equiv in H5.
      apply star_core_step_equiv in H6.
      apply np_corestar_npstar in H6.
      apply tau_star_to_star in H6 as [].
      unfold safe_state in H1.
      apply tau_star_to_star in H2 as [].
      apply type_step_elim in H5.
      eapply star_step in H5;eauto.
      eapply cons_star_star in H5;eauto.
      eapply H1 in H5 as ?;eauto.
      eapply abort_eq in H4;eauto.
      destruct H7;auto.
      apply tau_star_to_star in H2 as [].
      eapply thdp_inv_npstar in H2 as ?;auto.
      apply type_glob_step_cur_valid_id in H5 as ?;auto.
      apply globcorestar_npnswstar in H6.
      assert(cur_tid pc' = cur_tid x1). inversion H5;auto.
      apply type_glob_step_elim in H5 as ?.
      apply GE_mod_wd_tp_inv in H10;auto.
      assert(pc_valid_tid x1 (cur_tid x1)).
      inversion H5;subst. split;auto. eapply gettop_valid_tid;eauto. solv_thread. 
      intro. solv_thread.
      eapply npnsw_taustar_pc_valid_tid_preservation in H6;eauto.
      apply npnsw_taustar_tid_preservation in H6.
      rewrite <- H6. auto.
      intro R;inversion R.

      unfold npnsw_star_abort in H3;Hsimpl.
      apply abort_eq in H4;auto.
      apply  glob_npnsw_star_to_np_taustar in H3.
      apply tau_star_to_star in H3.
      Hsimpl.
      eapply H1 in H3;eauto.

      eapply npnsw_taustar_pc_valid_tid_preservation;eauto.
      apply npnsw_taustar_tid_preservation in H3.
      rewrite <- H3.
      inversion H2;subst;split;auto.
    Qed.
    Definition npdrfpc {ge}(pc:@ProgConfig ge):Prop:=
      ~ np_race_config pc /\ ~ np_star_race_config pc.
    Lemma p_star_abort_np_star_abort:
      forall pc
        (Hv:cur_valid_id pc)
        (HDrf: npdrfpc pc /\ forall t, pc_valid_tid pc t->npdrfpc ({-|pc,t})),
        @invpc GE pc-> atom_bit pc = O->
        forall l fp pc',
          star glob_step pc l fp pc'->
          predicted_abort1 pc'->
          exists t l' fp' pc'',
            star np_step ({-|pc,t}) l' fp' pc'' /\ pc_valid_tid pc t /\
            np_abort pc''.
    Proof.
      intros. apply predicted_abort1_O in H2 as ?.
      apply Evt_gstar_exists in H1;auto.
      Hsimpl.

      eapply Evt_gstar_nprace in H1 as R;eauto;[|right;eexists;erewrite pc_cur_tid;eauto].
      destruct R. destruct H6.
      apply nppredictrace_globpredictstaraltrace_equiv in H6.
      apply nprace_equiv in H6.

      destruct H4. contradiction.
      Hsimpl.
      apply predicted_abort1_sw in H6 as ?;auto.

      apply predicted_abort1_not_npsafe in H6;auto.
      unfold safe_state in H6.
      do 3 apply not_all_ex_not in H6 as [].
      apply imply_to_and in H6 as [].
      apply NNPP in H8.
      Esimpl;eauto.

      Hsimpl.
      destruct H10.
      {
        apply nppredictrace_globpredictstaraltrace_equiv in H10.
        apply nprace_equiv in H10.
        assert(pc_valid_tid pc (cur_tid x1)).
        apply swstar_l in H6 as [];subst;auto.
        destruct H6. inversion H6;subst;split;auto.
        remember (cur_tid x1) as t.
        apply swstar_l1 in H6. rewrite <- Heqt in *. rewrite H6 in *. clear x1 Heqt H6.
        apply H5 in H11.
        destruct H11.
        contradict H11.

        eapply np_star_race_config_np_race_config_1_equiv;eauto.
        Esimpl;eauto. econstructor;eauto. split;auto.
        eapply np_race_config_np_race_config_base_equiv;eauto.
        eapply cons_star_step in H8;eauto.
        eapply thdp_inv_npstar;eauto.
      }
      {
        assert(invpc x6).
        eapply cons_star_step in H8;eauto.
        eapply thdp_inv_npstar;eauto.
        apply swstar_l1 in H6. rewrite H6;auto.
        eapply predicted_abort1_not_npsafe in H10;eauto.
        
        unfold safe_state in H10.
        do 3 apply not_all_ex_not in H10 as [].
        apply imply_to_and in H10 as [].
        apply NNPP in H12.

        eapply star_step in H10;eauto.
        eapply cons_star_star in H10;eauto.
        assert(pc_valid_tid pc (cur_tid x1)).
        apply swstar_l in H6 as [];subst;auto.
        destruct H6. inversion H6;subst;split;auto.
        remember (cur_tid x1) as t.
        apply swstar_l1 in H6. rewrite <- Heqt in *. rewrite H6 in *. clear x1 Heqt H6.
        Esimpl;eauto.
      }
    Qed.      

      
      
      
    Lemma p_star_race_np_star_race:
      forall pc (HSafe:safe_state np_step np_abort pc /\ forall t,pc_valid_tid pc t ->safe_state np_step np_abort ({-|pc,t})),
        invpc pc->
        atom_bit pc = O->
        @star_race_config GE pc->
        np_race_config pc \/ 
        exists pc',
          sw_star glob_step pc pc'/\
          np_star_race_config pc'.
    Proof.
      intros pc [HSafe0 HSafe] inv1 H H0.
      unfold star_race_config in H0.
      Hsimpl.
      apply race_equiv in H1.
      pose proof predict_equiv.
      eapply predict_equiv_race_equiv in H2;eauto.
      apply H2 in H1.
      apply predict_race_to_star in H1.
      apply predict_star_race_to_alter in H1.
    
      clear H2.
      assert(atom_bit x1 = O). inversion H1. inversion H3;auto.
      apply Evt_gstar_exists in H0;auto.
      Hsimpl.
    
      eapply Evt_gstar_nprace in H0;eauto.
      destruct H0. destruct H0.
      apply nppredictrace_globpredictstaraltrace_equiv in H0.
      apply nprace_equiv in H0.
      auto.

      Hsimpl.
      apply predicted_abort1_sw in H0 as ?;auto.
      eapply predicted_abort1_not_npsafe in H0 as ?;eauto. contradict H0. eauto.
      
      Hsimpl.
      right.
      Esimpl;eauto.
      eapply np_star_race_config_np_race_config_1_equiv;eauto.
    
      apply swstar_l1 in H0;rewrite H0;auto.
    
      Esimpl;eauto.
      econstructor;eauto.
      Esimpl;eauto.
      destruct H6.
      eapply nppredictrace_globpredictstaraltrace_equiv in H6.
      apply nprace_equiv in H6.
      eapply np_race_config_np_race_config_base_equiv;eauto.
    
      apply swstar_l1 in H0.
      rewrite H0 in H3.
      eapply star_cons_step in H4 as [];eauto.
      eapply thdp_inv_npstar in H4;eauto.

      apply swstar_l in H0. destruct H0.
      subst. eapply cons_star_step in H4;eauto.
      Hsimpl.
      eapply safe_succeed in H4 as ?;eauto.
      eapply predicted_abort1_not_npsafe in H6;eauto.
      contradiction.
      eapply thdp_inv_npstar ;eauto.

      destruct H0.
      assert(pc_valid_tid pc (cur_tid x4)).
      inversion H0;split;auto.
      apply HSafe in H8.
      
      eapply cons_star_step in H4;eauto.
      Hsimpl. assert(({-|pc,cur_tid x4}) = x4). inversion H0;auto.
      rewrite H9 in *.
      eapply safe_succeed in H4 as ?;eauto.
      eapply predicted_abort1_not_npsafe in H6;eauto. contradiction.
      eapply thdp_inv_npstar ;eauto.
      rewrite <- H9;auto.
    Qed.


      
End Complex_reorder.

  

Section PRace_Proof.


  Lemma Safe_eq:
    forall ge pc,
      safe_state np_step np_abort pc <->
      @np_safe_config ge pc.
  Proof.
    split.
    intro.
    {
      revert pc H. cofix.
      intros.
      econstructor. eapply H. constructor.
      intros. eapply Safe_eq.
      eapply safe_succeed;eauto. econstructor 2;eauto. constructor.
    }
    {
      intros.
      unfold safe_state.
      intros.
      induction H0.
      inversion H;subst;auto.
      inversion H;subst. eauto.
    }
  Qed.
  Lemma PRace_NPRace:
    forall NL L p,
      forall (HSafe:np_safe_prog p),
      @wd_langs NL L (fst p)->
      race_prog p ->
      np_race_prog p.
  Proof.
    intros.
    unfold race_prog in H0.
    Hsimpl.
    assert(invpc x0 x1).
    inversion H0;subst. eapply ThreadPool.init_inv;eauto.
    assert(atom_bit x1 = O).
    inversion H0;subst. auto.
    apply init_config_GE_wd in H0 as ?.
    specialize (@lang_wd_mod_wd _ _ _ _ _ _ _ H H0) as ?.
    

    apply p_star_race_np_star_race in H1;auto.
    destruct H1.
    econstructor;eauto.
    Hsimpl.
    assert(x1 = x3 \/ pc_valid_tid x1 (cur_tid x3)).
    revert H1 H2 H3 H4 H5;clear;intros.
    induction H1;auto.
    apply GE_mod_wd_tp_inv in H as ?;auto.
    assert(atom_bit s2 = O).
    inversion H;auto.
    Hsimpl.
    destruct IHsw_star;subst.
    right. inversion H;split;auto.
    right. inversion H;subst. destruct H7. simpl in *;subst.
    split;auto.

    destruct H7. subst. econstructor 2;eauto.
    assert(x2 = cur_tid x1). inversion H0;auto. subst.
    eapply init_free in H7;eauto.
    econstructor 2;eauto. erewrite <- swstar_l1;eauto.

    inversion HSafe;subst.
    eapply H6 in H0 as ?;eauto. split.
    apply Safe_eq. auto.
    intros.
    assert(x2 = cur_tid x1). inversion H0;auto. subst.
    eapply init_free in H0;eauto.
    eapply H6 in H0;eauto.
    apply Safe_eq;auto.
  Qed.
  
Definition drfpc {ge}(pc:@ProgConfig ge):Prop:=
  ~ star_race_config pc.


Lemma drf_drfpc:
  forall NL L p gm ge pc t,
    @init_config NL L p gm ge pc t->
    drf p ->
    drfpc pc.
Proof.
  unfold drf,drfpc;intros.
  intro. contradict H0.
  unfold race_prog.
  eexists;eauto.
Qed.

Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).
Lemma NPDRF_config:
  forall NL L p gm ge pc t,
    npdrf p->
    @init_config NL L p gm ge pc t->
    (
      forall t,
        GSimDefs.pc_valid_tid pc t->
        npdrfpc ({-|pc,t})).
Proof.    
  intros.
  assert(t=cur_tid pc). inversion H0;auto. subst.
  eapply init_free in H0;eauto.
  unfold npdrf in H. unfold npdrfpc.
  apply not_or_and.
  intro.
  contradict H. destruct H2.
  econstructor;eauto.
  econstructor 2;eauto.
Qed.

Lemma NPSAFE_config:
  forall NL L p gm ge pc t,
    np_safe_prog p->
    @init_config NL L p gm ge pc t->
    (
      forall t,
        GSimDefs.pc_valid_tid pc t->
        np_safe_config ({-|pc,t})).
Proof.
  intros.
  assert(t=cur_tid pc). inversion H0;subst;auto.
  subst.
  eapply init_free in H1;eauto.
  eapply H in H1;eauto.
Qed.
Lemma NPDRF_DRF_Config:
  forall NL L p gm ge pc t,
    @wd_langs NL L (fst p) ->
    init_config p gm ge pc t->
    (forall t, GSimDefs.pc_valid_tid pc t->np_safe_config ({-|pc,t}))->
    (forall t, GSimDefs.pc_valid_tid pc t ->npdrfpc ({-|pc,t}))->
    drfpc pc.
Proof.
  intros. assert(t=cur_tid pc). inversion H0;auto. subst.
  apply init_property_1_alt in H0 as ?.
  specialize (H1 (cur_tid pc) H3) as ?.
  unfold npdrfpc in H2. unfold drfpc.
  intro. 
  assert(invpc ge pc).
  inversion H0;subst. eapply ThreadPool.init_inv;eauto.
  assert(atom_bit pc = O).
  inversion H0;subst. auto.
  apply init_config_GE_wd in H0 as ?.
  specialize (@lang_wd_mod_wd _ _ _ _ _ _ _ H H0) as ?.
  
  apply p_star_race_np_star_race in H5;auto.
  destruct H5.
  eapply H2 in H3;eauto. destruct H3;auto.  rewrite pc_cur_tid in H3;auto.
  Hsimpl. apply swstar_l in H5.
  destruct H5. subst. eapply H2 in H3 as [];eauto. rewrite pc_cur_tid in H5;auto.
  destruct H5. assert(Init.pc_valid_tid pc (cur_tid x)). inversion H5;subst;split;auto.
  apply H2 in H12 as []. assert(({-|pc,cur_tid x}) = x). inversion H5;auto.
  rewrite H14 in H13;auto.
  split;auto. apply Safe_eq;auto. rewrite pc_cur_tid in H4;auto.
  intros.
  apply H1 in H10.
  eapply Safe_eq;eauto.
Qed.
   
Lemma DRF_NPDRF_Config:
  forall NL L p gm ge pc t,
    @wd_langs NL L (fst p) ->
    init_config p gm ge pc t ->
    drfpc pc ->
    npdrfpc pc.
Proof.
  unfold drfpc,npdrfpc.
  pose proof NPRace_Race_Config.
  intros.
  apply not_or_and.
  eauto.
Qed.

Lemma stepN_SN_split:
  forall i ge l pc fp pc',
    stepN ge glob_step (S i) pc l fp pc'->
    exists l1 fp1 pc1 l2 fp2,
      stepN ge glob_step i pc l1 fp1 pc1/\
      glob_step pc1 l2 fp2 pc' /\ FP.union fp1 fp2 = fp.
Proof.
  induction i;intros.
  inversion H;subst. inversion H1;subst.
  Esimpl;eauto. constructor. rewrite FP.union_comm_eq;auto.
  inversion H;subst.
  eapply IHi in H1;eauto.
  Hsimpl.
  eapply stepN_cons in H3;eauto.
  Esimpl;eauto. rewrite <- H2. rewrite FP.fp_union_assoc;auto.
Qed.
Lemma globstar_OI_split:
  forall ge l pc fp pc',
    star glob_step pc l fp pc'->
    atom_bit pc = O->
    atom_bit pc' = I->
    exists l1 fp1 pc1 pc2 fp2,
      star glob_step pc l1 fp1 pc1 /\
      atom_bit pc1 = O /\
      type_glob_step entat pc1 tau FP.emp pc2 /\
      tau_star (@type_glob_step ge core) pc2 fp2 pc' /\
      FP.union fp1 fp2 = fp.
Proof.
  intros.
  apply star_stepN in H as [].
  revert ge l pc fp pc' H H0 H1.
  induction x;intros.
  inversion H;subst. rewrite H0 in H1;inversion H1.

  apply stepN_SN_split in H. Hsimpl.
  destruct (atom_bit x2) eqn:?.
  {
    apply type_glob_step_exists in H2 as [].
    destruct x5;try(inversion H2;subst;simpl in *;try rewrite H1 in Heqb;inversion Heqb;inversion H1;fail).
    assert(x3 = tau /\ x4 = FP.emp). inversion H2;subst;auto. destruct H4;subst.
    Esimpl;eauto. eapply stepN_star;eauto. constructor.
  }
  {
    eapply IHx in H;eauto.
    Hsimpl.
    apply type_glob_step_exists in H2 as [].
    apply corestar_tid_bit_preserve in H6 as ?.
    destruct H8.
    rewrite Heqb in H9.
    destruct x10;try(inversion H2;subst;inversion Heqb;inversion H9;fail).
    assert(x3 = tau). inversion H2;subst;auto. subst.
    eapply tau_plus_1 with(step:=type_glob_step core) in H2.
    eapply tau_star_plus in H2;eauto. apply tau_plus2star in H2.
    Esimpl;eauto.  rewrite FP.fp_union_assoc;auto.
    inversion H2;subst. simpl in *;subst. inversion H1.
  }
Qed.
Lemma star_abort_predicted_abort1:
  forall ge pc l fp pc',
    star glob_step pc l fp pc'-> cur_valid_id ge pc' ->
    atom_bit pc = O->
    abort pc'->
    exists l' fp' pc'',
      star glob_step pc l' fp' pc''/\ predicted_abort1 ge pc''.
Proof.
  intros.
  destruct (atom_bit pc') eqn:?.
  {
    Esimpl;eauto. econstructor 2. instantiate(1:=pc'). destruct pc',H0;simpl in *;subst;econstructor;eauto.
    econstructor. Esimpl;eauto. constructor.
  }
  {
    apply globstar_OI_split in H;auto.
    Hsimpl.
    Esimpl;eauto. econstructor;eauto. constructor.
    unfold halfatomblock_abort,halfatomblockstep.
    Esimpl;eauto.
  }
Qed.
Lemma step_validid:
  forall ge pc l fp pc',
    GlobEnv.wd ge->
    glob_step pc l fp pc'->
    invpc ge pc-> ThreadPool.valid_tid pc.(thread_pool) pc.(cur_tid) ->
    ThreadPool.valid_tid pc'.(thread_pool) pc'.(cur_tid).
Proof.
  unfold invpc. 
  intros. apply GE_mod_wd_tp_inv in H0 as ?;auto.
  inversion H0;subst;solv_thread;solv_thread.
Qed.

Lemma star_validid:
  forall ge pc l fp pc',
    GlobEnv.wd ge->
    star glob_step pc l fp pc'->
    invpc ge pc-> ThreadPool.valid_tid pc.(thread_pool) pc.(cur_tid) ->
    ThreadPool.valid_tid pc'.(thread_pool) pc'.(cur_tid).
Proof.
  induction 2;intros.
  auto.
  eapply step_validid in H0 as ?;eauto.
  eapply GE_mod_wd_tp_inv in H0 as ?;eauto.
Qed.
Lemma NPSafe_Safe':
  forall NL L cus e,
    @wd_langs NL L cus ->
    np_safe_prog (cus, e) ->
    npdrf (cus, e) ->
    safe_prog (cus, e).
Proof.
  intros.
  econstructor. intros.
  unfold npdrf in H1.
  pose proof (NPDRF_config NL L (cus,e) gm GE pc t H1 H2).

  apply NNPP;intro. unfold safe_state in H4.
  do 3 apply not_all_ex_not in H4 as [].
  apply imply_to_and in H4 as [].
  contradict H5. intro.

  apply init_property_1 in H2 as ?.
  assert(t=cur_tid pc). inversion H2;auto. subst.
  assert(invpc GE pc). inversion H2;subst. eapply ThreadPool.init_inv;eauto.
  assert(GlobEnv.wd GE). inversion H2;subst. inversion H8;subst;auto.
  eapply star_validid in H4 as ?;eauto.
  assert(GSimDefs.pc_valid_tid x1 x1.(cur_tid)).
  split;auto. destruct H5;auto.
  assert(atom_bit pc = O). inversion H2;auto.
  eapply star_abort_predicted_abort1 in H4 as ?;eauto.
  Hsimpl.
  eapply p_star_abort_np_star_abort in H12;eauto.
  Hsimpl.

  eapply init_free in H14;eauto.
  apply H0 in H14.
  apply Safe_eq in H14.
  apply H14 in H12. auto.
  intros.
  specialize (@lang_wd_mod_wd ) as ?.
  eapply H14;eauto. simpl;auto.
  apply init_property_1_alt in H2;eauto.
  split.
  apply init_property_1_alt in H2.
  apply H3 in H2. rewrite pc_cur_tid in H2. auto.
  auto.
Qed.

Lemma NPSafe_Safe_Config:
  forall NL L cus e gm ge pc t,
    @wd_langs NL L cus ->
    init_config (cus,e) gm ge pc t->
    (forall t, pc_valid_tid pc t-> np_safe_config ({-|pc,t}))->
    (forall t, pc_valid_tid pc t-> npdrfpc ({-|pc,t}))->
    safe_state glob_step abort pc.
Proof.
  intros.
  apply NNPP;unfold safe_state. intro.
  do 3 apply not_all_ex_not in H3 as [].
  apply imply_to_and in H3 as []. apply NNPP in H4.
  apply init_property_1 in H0 as ?.
  assert(t=cur_tid pc). inversion H0;auto. subst.
  assert(invpc ge pc). inversion H0;subst. eapply ThreadPool.init_inv;eauto.
  assert(GlobEnv.wd ge). inversion H0;subst. inversion H7;subst;auto.
  eapply star_validid in H3 as ?;eauto.
  assert(GSimDefs.pc_valid_tid x1 x1.(cur_tid)).
  split;auto. destruct H4;auto.
  assert(atom_bit pc = O). inversion H0;auto.
  eapply star_abort_predicted_abort1 in H4 as ?;eauto.
  Hsimpl.
  eapply p_star_abort_np_star_abort in H11;eauto.
  Hsimpl.
  eapply H1 in H13 as ?;eauto.
  apply Safe_eq in H15.
  eapply H15 in H11. contradiction.
  eapply lang_wd_mod_wd;eauto.
  simpl;auto.

  eapply init_property_1_alt in H0;auto.
  split;auto.
  rewrite <- pc_cur_tid;apply H2.
  eapply init_property_1_alt;eauto.
Qed.  
End PRace_Proof.