Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics GlobSemantics_Lemmas NPSemantics TypedSemantics .

Require Import DRF USimDRF NPDRF.

Require Import Classical Wf Arith ListDom.

Require Import FPLemmas PRaceLemmas Init SmileReorder ConflictReorder Init DRFLemmas SimEtr.
Local Notation "'<<' i ',' c ',' sg ',' F '>>'" := {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|} (at level 60, right associativity).
Local Definition pc_valid_tid {ge}:= @GSimDefs.pc_valid_tid ge.
Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:= D|}(at level 70,right associativity).  Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).

(** This file consists of proofs and results on np-semantics and p-semantics:
    - [NP(S) refine P(S)]
    - [DRF(S)/\Safe(S)/\WD_langs(S) -> P(S) refine NP(S)]
  *)
Section Refinement.
  Hypothesis init_free:
    forall NL (L:@langs NL)(p:prog L) gm ge pc t,
      init_config p gm ge pc pc.(cur_tid) ->
      pc_valid_tid pc t->
      init_config p gm ge ({-|pc,t}) t.
  Definition p_np_config_refine {ge:GlobEnv.t}(s:@ProgConfig ge):Prop:=
    forall B,Etr np_step np_abort final_state s B->
        Etr glob_step abort final_state s B.

  Definition p_np_prog_refine {NL:nat}{L:@langs NL}(P:@prog NL L):Prop:=
    forall gm ge pc,
      init_config P gm ge pc pc.(cur_tid) ->
      p_np_config_refine pc.
  (*Definition np_p_config_refine {ge:GlobEnv.t}(s:@ProgConfig ge):Prop:=
    forall B, Etr glob_step abort final_state s B-> Etr np_step np_abort final_state s B.*)
  Definition np_p_config_refine_weak {ge:GlobEnv.t}(s:@ProgConfig ge):Prop:=
    forall B, Etr glob_step abort final_state s B->
         exists t,Etr np_step np_abort final_state ({-|s,t}) B /\ pc_valid_tid s t.
  
  (*Definition np_p_prog_refine {NL:nat}{L:@langs NL}(P:@prog NL L):Prop:=
    forall gm ge pc,
      init_config P gm ge pc pc.(cur_tid) ->
      np_p_config_refine pc.*)
  Definition np_p_prog_refine_weak {NL:nat}{L:@langs NL}(P:@prog NL L):Prop:=
    forall gm ge pc,
      init_config P gm ge pc pc.(cur_tid)->
      np_p_config_refine_weak pc.
  Lemma threadpool_spawn_domadd:
    forall ge t mid c sg ,
      let t' :=  @ThreadPool.spawn ge t mid c sg in
      ThreadPool.next_tid t' = BinPos.Pos.succ (ThreadPool.next_tid t).
  Proof.
    intros.
    unfold ThreadPool.spawn in t'.
    simpl.
    auto.
  Qed.
  Lemma threadpool_init_domeq:
    forall e ge1 ge2 t1 t2,
      @ThreadPool.init ge1 e t1->
      @ThreadPool.init ge2 e t2->
      t1.(ThreadPool.next_tid) = t2.(ThreadPool.next_tid).
  Proof.
    induction e;intros.
    Coqlib.inv H;Coqlib.inv H0.
    split;auto.

    Coqlib.inv H;Coqlib.inv H0.

    rewrite threadpool_spawn_domadd.
    rewrite threadpool_spawn_domadd.
    f_equal.
    auto.
  Qed.
  Lemma threadpool_init_domeq':
    forall e ge1 ge2 t1 t2,
      @ThreadPool.init ge1 e t1->
      @ThreadPool.init ge2 e t2->
      (forall t,ThreadPool.valid_tid t1 t<->ThreadPool.valid_tid t2 t).
  Proof.
    intros.
    eapply threadpool_init_domeq in H;eauto.
    unfold ThreadPool.valid_tid.
    rewrite H.
    split;auto.
  Qed.
  Lemma switchable_glob_config_refine:
    forall ge pc t,
      @pc_valid_tid ge pc pc.(cur_tid)->
      atom_bit pc = O ->
      forall B,
        Etr glob_step abort final_state pc B->
        Etr glob_step abort final_state ({-|pc,t}) B.
  Proof.
    intros.
    assert(glob_step ({-|pc,t}) sw FP.emp pc).
    destruct pc. simpl in *;subst.
    destruct H.
    econstructor;eauto.
    destruct B.
    {
      Coqlib.inv H1.
      assert(non_evt_star glob_step ({-|pc,t}) fp state').
      rewrite <-FP.emp_union_fp with (fp:=fp).
      econstructor;eauto.
      econstructor;eauto.
    }
    {
      Coqlib.inv H1.
      assert(non_evt_star glob_step ({-|pc,t}) fp state').
      rewrite <-FP.emp_union_fp with (fp:=fp).
      econstructor;eauto.
      econstructor;eauto.      
    }
    {
      Coqlib.inv H1.
      assert(silent_diverge glob_step ({-|pc,t})).
      destruct H3.
      assert(sw_star glob_step ({-|s,t}) s').
      econstructor;eauto.
      econstructor;eauto.
      econstructor;eauto.
    }
    {
      Coqlib.inv H1.
      assert(non_evt_star glob_step ({-|pc,t}) fp state').
      rewrite <-FP.emp_union_fp with (fp:=fp).
      econstructor;eauto.
      econstructor;eauto.   
    }
  Qed.

    
  Lemma Etr_cons_globsw:
    forall ge pc pc',
      @glob_step ge pc sw FP.emp pc'->
      forall B,
        Etr glob_step abort final_state pc' B->
        Etr glob_step abort final_state pc B.
  Proof.
    intros.
    assert(non_evt_star glob_step pc (FP.union FP.emp FP.emp) pc').
    econstructor;eauto. constructor.
    inversion H0;subst.

    eapply non_evt_star_cons in H2;eauto.
    econstructor;eauto.

    eapply non_evt_star_cons in H2;eauto.
    econstructor;eauto.

    inversion H2;subst.
    eapply ETrace.sw_star_cons in H;eauto.
    econstructor. econstructor;eauto.

    eapply non_evt_star_cons in H2;eauto.
    econstructor;eauto.
  Qed.
    
    
    
  Lemma init_pair_valid_tid:
    forall NL L sc tc e sgm sge spc tgm tge tpc i i',
      @init_config NL L (sc,e) sgm sge spc i->
      @init_config NL L (tc,e) tgm tge tpc i'->
      forall j,
        pc_valid_tid spc j-> pc_valid_tid tpc j.
  Proof.
    intros.
    destruct H1.
    assert(ThreadPool.valid_tid tpc.(thread_pool) j).
    inversion H;inversion H0;subst.
    eapply threadpool_init_domeq' in H1;eauto.
    split;auto.
    eapply config_thdp_init_property1 ;eauto.
  Qed.
  Lemma P_NP_Refine_adjusted:
    forall NL L scus tcus e,
      @np_prog_refine NL L (scus,e)(tcus,e)->
      np_p_prog_refine_weak (tcus,e)->
      p_np_prog_refine (scus,e)->
      prog_refine (scus,e)(tcus,e).
  Proof.
    unfold np_p_prog_refine_weak;unfold np_p_config_refine_weak;
      unfold p_np_prog_refine;unfold p_np_config_refine;intros NL L scus tcus e H refine1 refine2.
    inversion H;clear H;subst.
    constructor;intros.
    unfold config_refine;intros.
    assert(tt=cur_tid tpc). inversion H2;subst;auto. subst.
    assert(ts=cur_tid spc). inversion H1;subst;auto. subst.
    specialize (refine1 _ _ _ H2 _ H3) as [t[]];auto.
    eapply init_free in H5 as initt2;eauto.
    eapply init_pair_valid_tid with(sc:=tcus)(tc:=scus) in H5 as ?;eauto.
    eapply init_free in H6 as inits2;eauto.

    specialize (H0 _ _ _ _ _ _ _ _ H inits2 initt2).
    unfold np_config_refine in H0.
    specialize (H0 _ H4).
    specialize (refine2 _ _ _ inits2 _ H0).

    assert(glob_step spc sw FP.emp ({-|spc,t})).
    destruct H6.
    assert(atom_bit spc = O).
    inversion H1;auto.
    destruct spc;simpl in *;subst. econstructor;eauto.

    eapply  Etr_cons_globsw;eauto.
  Qed.
    
    
  (*
  Lemma P_NP_Refine:
  forall NL L  scus tcus e,
    @np_prog_refine NL L (scus, e) (tcus, e) ->
    np_p_prog_refine (tcus,e)->
    p_np_prog_refine (scus,e)->
    prog_refine (scus, e) (tcus, e).
  Proof.
    unfold np_p_prog_refine. unfold p_np_prog_refine.
    unfold np_p_config_refine. unfold p_np_config_refine.
    intros.
    Coqlib.inv H.
    econstructor.
    intros.
    assert(forall t,ThreadPool.valid_tid spc.(thread_pool) t<->ThreadPool.valid_tid tpc.(thread_pool) t).
    
    Coqlib.inv H3;Coqlib.inv H4.
    eapply threadpool_init_domeq';eauto.
    apply init_property_1_alt in H3 as L1.
    assert(ThreadPool.valid_tid spc.(thread_pool) ts).
    Coqlib.inv H3;auto.
    eapply H5 in H6.
    assert(~ThreadPool.halted tpc.(thread_pool) ts).
    eapply config_thdp_init_property1;eauto.
    assert(pc_valid_tid tpc ts).
    split;auto.
    assert(cur_tid tpc = tt).
    Coqlib.inv H4;auto.
    rewrite <- H9 in H4.
    eapply init_free in H8 as L2;eauto.

    eapply H2 in L2 as r1;eauto.
    unfold np_config_refine in r1.
    assert(ts = cur_tid spc).
    Coqlib.inv H3;auto.
    rewrite H10 in H3.
    specialize (H1 sgm sge spc H3) as r2.

    specialize (H0 tgm tge _ L2) as r3.
    unfold config_refine.
    intros.
    apply r2.
    apply r1.
    apply r3.

    eapply switchable_glob_config_refine;eauto.
    eapply init_property_1_alt;eauto.
    Coqlib.inv H4;auto.
  Qed.
*)
  Lemma tau_np_p:
    forall ge pc fp pc',
      @np_step ge pc tau fp pc'->
      glob_step pc tau fp pc'.
  Proof.
    intros.
    inversion H;subst.
    econstructor;eauto.
    econstructor 2;eauto.
    econstructor 3;eauto.
    econstructor 4;eauto.
    econstructor 5;eauto.
  Qed.
  Lemma sw_np_p:
    forall ge pc fp pc',
      @np_step ge pc sw fp pc'->
          exists pc'',
            glob_step pc tau fp pc'' /\ glob_step pc'' sw FP.emp pc'.
  Proof.
    intros.
    inversion H;subst.
    exists ({thdp',t,gm,O}).
    split.
    econstructor 4;eauto.
    econstructor;eauto.
    exists ({thdp',t,gm,O}).
    split.
    econstructor 6;eauto.
    econstructor;eauto.
  Qed.
  Lemma non_evt_star_equiv:
    forall ge pc fp state',
      non_evt_star (@np_step ge) pc fp state'->
      non_evt_star glob_step pc fp state'.
  Proof.
    induction 1;intros.
    econstructor.
    destruct H.
    apply tau_np_p in H.
    econstructor;eauto.
    apply sw_np_p in H as (?&?&?).
    econstructor;eauto.
    rewrite <- FP.emp_union_fp with(fp:=fp2).
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

  Lemma mem_eq_non_evt_starN:
    forall ge pc pc',
      (forall ix,mod_wd (GlobEnv.modules ge ix))->
      mem_eq_pc ge pc pc'->
      forall i fp pc2,
        non_evt_starN glob_step i pc fp pc2->
        exists pc'',non_evt_starN glob_step i pc' fp pc'' /\ mem_eq_pc ge pc2 pc''.
  Proof.
    intros ge pc pc' wd;intros. revert ge pc pc' pc2 fp wd H H0.
    induction i;intros;inversion H0;subst.
    eexists;split;eauto. constructor.
    assert(exists l,glob_step pc l fp1 s2 /\ (l = tau \/ l = sw)).
    destruct H2;eauto.
    destruct H1 as (?&?&?).
    apply type_glob_step_exists in H1 as [].
    eapply mem_eq_globstep in H1 as (?&?&?);eauto.
    eapply IHi in H4 as (?&?&?);eauto.
    eexists;split;eauto. econstructor;eauto.
    destruct H3;subst;eapply type_glob_step_elim in H1;eauto.
  Qed.
  Lemma non_evt_star_Sn_split{State:Type}:
    forall step n s fp s',
      @non_evt_starN State step (S n) s fp s'->
      exists fp1 fp2 s1,
        non_evt_starN step n s fp1 s1 /\
        (step s1 tau fp2 s' \/ step s1 sw fp2 s') /\
        FP.union fp1 fp2 = fp.
  Proof.
    induction n;intros.
    exists FP.emp ,fp,s.
    split. constructor.
    split. inversion H;subst. inversion H3;subst. rewrite FP.fp_union_emp. auto.
    rewrite (FP.emp_union_fp fp);auto.

    inversion H;clear H;subst.
    apply IHn in H3.
    destruct H3 as (?&?&?&?&?&?).
    exists (FP.union fp1 x),x0,x1.
    split. econstructor;eauto.
    split. assumption.
    rewrite <- H2.
    rewrite FP.fp_union_assoc.
    reflexivity.
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

  Lemma no_npstep_no_globstep:
    forall ge pc,
      ThreadPool.inv pc.(thread_pool)->
      (forall l fp pc',~ @np_step ge pc l fp pc')->
      (forall l' fp' pc'',glob_step pc l' fp' pc''->l'=sw).
  Proof.
    intros ge pc invthdp ? ? ? ? ?.
    assert(~ exists l fp pc',np_step pc l fp pc').
    repeat (apply all_not_not_ex;intro);eauto.
    destruct l';auto;contradict H1.
    
    eapply type_glob_step_exists in H0 as [];eauto.
    destruct x eqn:?;try (inversion H0;subst;fail);try (exists tau,fp',pc'';eapply type_step_elim with(t:=x);inversion H0;subst;econstructor;eauto).
    exists sw,fp',pc''.
    inversion H0;subst.
    econstructor;eauto.
    eapply gettop_valid_tid in H_tp_core;eauto.
    eapply valid_tid_preserve;eauto.
    intro. solv_thread.
    
    inversion H0;subst.
    assert((forall t',ThreadPool.valid_tid thdp' t'->ThreadPool.halted thdp' t') \/ ~ (forall t',ThreadPool.valid_tid thdp' t'->ThreadPool.halted thdp' t')).
    apply classic.
    destruct H1.
    exists tau,FP.emp,({thdp',t,gm,O}).
    econstructor 5;eauto.
    apply not_all_ex_not in H1 as [].
    apply not_imply_elim2 in H1 as L1.
    apply not_imply_elim in H1.
    exists sw,FP.emp,({thdp',x,gm,O}). econstructor;eauto.

    exists (evt v),fp',pc''.
    inversion H0;subst;econstructor;eauto.
    
    eapply gettop_valid_tid in H_tp_core;eauto.
    eapply valid_tid_preserve;eauto.
    intro;solv_thread.
  Qed.

  
                                 
  Lemma init_abort_np_p:
    forall NL L P gm ge pc t,
      @init_config NL L P gm ge pc t->
      np_abort pc->
      abort pc.
  Proof.
    unfold np_abort.
    unfold abort.
    intros.
    destruct H0.
    assert(ThreadPool.inv pc.(thread_pool)).
    inversion H;subst. eapply ThreadPool.init_inv;eauto.
    split;[|apply no_npstep_no_globstep];auto.
    intro.
    assert(ThreadPool.init (snd P)(thread_pool pc)).
    inversion H;subst;auto.
    assert(ThreadPool.valid_tid pc.(thread_pool) pc.(cur_tid)).
    inversion H;subst;auto.
    clear H H1 H2.
    contradict H0.
    induction H4;subst.
    
    solv_thread.
    inversion H5.
    unfold BinPos.Pos.compare in H1.
    unfold BinPos.Pos.compare_cont in H1.
    destruct cur_tid;inversion H1.

    solv_thread.
    unfold Coqlib.Plt in H5.
    apply Coqlib.Plt_succ_inv in H5.
    destruct H5;try contradiction.
    eapply IHinit;eauto.
    econstructor;eauto.
    constructor.
  Qed.
    
    
  Definition np_accepted {ge}(pc:@ProgConfig ge):Prop:=
    exists NL L P gm pc0,
      @init_config NL L P gm ge pc0 pc0.(cur_tid) /\
      exists l fp,
        star np_step pc0 l fp pc.
  Lemma np_accepted_inv_thdp:
    forall ge pc,
      @np_accepted ge pc->
      ThreadPool.inv pc.(thread_pool).
  Proof.
    intros.
    unfold np_accepted in H.
    destruct H as (?&?&?&?&?&?&?&?&?).
    assert(ThreadPool.inv x3.(thread_pool)).
    inversion H;subst;eapply ThreadPool.init_inv;eauto.
    eapply GE_mod_wd_npstar_tp_inv;eauto.
    inversion H;subst.
    inversion H2;auto.
  Qed.
  Fixpoint add(l:list glabel)(l':glabel):list glabel:=
    match l with
    | nil => cons l' nil
    | cons x y => cons x (add y l')
    end.
  Lemma star_npstep_inv:
    forall ge pc l fp pc',
      star (@np_step ge) pc l fp pc'->
      (pc = pc' /\ l = nil /\ fp=FP.emp) \/
      (exists pc'' l' fp' l'' fp'',star np_step pc l' fp' pc'' /\ np_step pc'' l'' fp'' pc' /\ l = add l' l'' /\ fp = FP.union fp' fp'').
  Proof.
    induction 1.
    left;auto.
    destruct IHstar.
    destruct H1 as (?&?&?);subst.
    right.
    do 6 eexists. constructor. split;eauto. rewrite FP.union_comm_eq;auto.
    destruct H1 as (?&?&?&?&?&?&?&?&?).
    right.
    do 6 eexists. econstructor 2;eauto. split;eauto. split.
    rewrite H3;auto.
    rewrite <-FP.fp_union_assoc.
    rewrite H4;auto.
  Qed.
  Lemma star_abort_np_p:
    forall ge pc,
      @np_accepted ge pc->
      np_abort pc->
      abort pc.
  Proof.
    intros.
    apply np_accepted_inv_thdp in H as inv1.
    pose proof H as L1.
    destruct H as (NL&L&P&gm&pc0&init&l&fp&star1).
    apply star_npstep_inv in star1.
    destruct star1.
    destruct H as (?&?&?);subst.
    eapply init_abort_np_p;eauto.

    destruct H as (pc''&l'&fp'&l''&fp''&star1&step1&_).
    split.
    intro.
    apply type_step_exists in step1 as [x step1].
    destruct x;try(inversion step1;subst;simpl in *;try contradiction;solv_thread;solv_thread;fail).
    destruct H0;contradict H0.
    econstructor;eauto;intros.
    inversion step1;subst;auto.
    eapply no_npstep_no_globstep;eauto.
    destruct H0;auto.
  Qed.
  Lemma sw_diverge:
    forall State step s s',
      @silent_diverge State step s'->
      step s sw FP.emp s'->
      silent_diverge step s.
  Proof.
    intros.
    inversion H;subst.
    econstructor;eauto.
    econstructor;eauto.
  Qed.

  Inductive lstep{ge}:@Step ge->@Step ge:=
  | build:
      forall step s0 s1 fp s2,
        sw_star step s0 s1->
        step s1 tau fp s2 ->
        lstep step s0 tau fp s2.

  Lemma sw_star_lstep_lemma{ge}: forall (step:@Step ge) s s',sw_star (lstep step) s s'-> s=s'.
  Proof. induction 1;auto. inversion H. Qed.
  Inductive tau_plus'{ge}:@Step ge->@Step ge:=
  | plus'_1:
      forall (step:Step ge) s fp s',
        step s tau fp s'->
        tau_plus' step s tau fp s'
  | plus'_cons:
      forall (step:Step ge) s fp s' fp' s'',
        step s tau fp s'->
        tau_plus' step s' tau fp' s''->
        tau_plus' step s tau (FP.union fp fp') s''.
  Lemma sw_star_tau_plus'_lemma{ge}: forall (step:@Step ge) s s',sw_star (tau_plus' step) s s'-> s=s'.
  Proof. induction 1;auto. inversion H. Qed.
  Lemma silent_diverge_lstep_equiv{ge}:
    forall (step:@Step ge) s,
      silent_diverge step s<->silent_diverge (lstep step) s.
  Proof.
    split;revert step s;cofix;intros.
    inversion H;subst.
    econstructor;eauto. constructor. econstructor;eauto.
    inversion H;subst.
    apply sw_star_lstep_lemma in H0;subst.
    inversion H1;subst.
    econstructor;eauto.
  Qed.
  Lemma sw_lstep_cons{ge}:
    forall (step:@Step ge) s s' fp s'',
      step s sw FP.emp s'->
      lstep step s' tau fp s''->
      lstep step s tau fp s''.
  Proof.
    intros.
    inversion H0;subst.
    econstructor. econstructor 2. eauto. eauto. eauto.
  Qed.
  Lemma lnpstep_taupluslglobstep{ge}:
    forall s fp s',
      lstep (@np_step ge) s tau fp s'->
      tau_plus' (lstep glob_step) s tau fp s'.
  Proof.
    inversion 1;subst.
    clear H.
    induction H0.
    apply tau_np_p in H1. econstructor. econstructor. constructor. eauto.
    specialize (IHsw_star H1).
    apply sw_np_p in H as (?&?&?).
    assert(lstep glob_step s1 tau FP.emp x).
    econstructor;[constructor|eauto].
    inversion IHsw_star;subst;eapply sw_lstep_cons in H4;eauto.
    rewrite<- FP.emp_union_fp with(fp:=fp).
    econstructor 2;eauto. constructor;auto.

    rewrite <- FP.emp_union_fp with (fp:=(FP.union fp0 fp')).
    econstructor 2. eauto.
    econstructor 2;eauto.
  Qed.
    
  Lemma silent_diverge_lstep_npstep_tauplus_lstep_pstep{ge}:
    forall s,
      silent_diverge (lstep (@np_step ge)) s->silent_diverge (tau_plus'(lstep glob_step)) s.

  Proof.
    cofix.
    intros.
    inversion H;subst.
    apply sw_star_lstep_lemma in H0;subst.
    apply lnpstep_taupluslglobstep in H1.
    econstructor;eauto. constructor.
  Qed.

  Lemma tauplus'_diverge_inv{ge}:
  forall (step:@Step ge) s,
    silent_diverge (tau_plus' step) s ->
    exists s' fp, step s tau fp s' /\ silent_diverge (tau_plus' step) s'.
  Proof.
    inversion 1;subst.
    apply sw_star_tau_plus'_lemma in H0;subst.
    inversion H1;subst. eauto.
    exists s'0,fp. split;auto.
    econstructor;eauto. constructor.
  Qed.
  
  Lemma tau_plus'_diverge_lemma{ge}:
    forall (step:@Step ge) s,
      silent_diverge (tau_plus' step) s->silent_diverge step s.
  Proof.
    cofix.
    intros.
    apply tauplus'_diverge_inv in H.
    destruct H as (?&?&?&?).
    econstructor. constructor. eauto. auto.
  Qed.
  Lemma silent_diverge_np_p{ge}:
    forall pc,
      silent_diverge (@np_step ge) pc -> silent_diverge glob_step pc.
  Proof.
    intros.
    apply silent_diverge_lstep_equiv.
    apply silent_diverge_lstep_equiv in H.
    apply silent_diverge_lstep_npstep_tauplus_lstep_pstep in H.
    apply tau_plus'_diverge_lemma;auto.
  Qed.

  Lemma Etr_p_sw{ge}:
    forall pc B t,
      Etr (@glob_step ge) abort final_state pc B->
      glob_step ({-|pc,t}) sw FP.emp pc ->
      Etr glob_step abort final_state ({-|pc,t}) B.
  Proof.
    intros.
    case B eqn:?.
    {
      inversion H.
      econstructor;eauto.
      instantiate (1:=(FP.union FP.emp fp)).
      econstructor;eauto.
    }
    {
      inversion H.
      econstructor;eauto.
      instantiate (1:=(FP.union FP.emp fp)).
      econstructor;eauto.
    }
    {
      inversion H.
      econstructor;eauto.
      inversion H1;subst.
      econstructor;eauto.
      econstructor;eauto.
    }
    {
      inversion H;subst.
      econstructor 4 with(fp:=(FP.union FP.emp fp)).
      econstructor;eauto.
      
      eauto.
      eauto.
    }
  Qed.


  Lemma np_evtstep_inv:
    forall ge pc v pc',
      @np_step ge pc (evt v) FP.emp pc'->
      glob_step pc (evt v) FP.emp ({-|pc',cur_tid pc}) /\
      glob_step ({-|pc',cur_tid pc}) sw FP.emp pc'.
  Proof. inversion 1;subst;split;econstructor;eauto. Qed.
  Lemma np_accepted_add_step:
    forall ge pc l fp pc',
      @np_accepted ge pc->
      np_step pc l fp pc'->
      np_accepted pc'.
  Proof.
    intros.
    destruct H as (?&?&?&?&?&?&?&?&?).
    do 6 eexists;eauto.
    eapply cons_star_step in H0;eauto.
  Qed.
  Lemma np_accepted_add_star:
    forall ge pc l fp pc',
      @np_accepted ge pc->
      star np_step pc l fp pc'->
      np_accepted pc'.
  Proof. induction 2;intros;auto;eapply np_accepted_add_step in H0;eauto. Qed.
  Lemma Etr_np_p_done:
    forall ge pc,
      Etr (@np_step ge) np_abort final_state pc Behav_done->
      Etr glob_step abort final_state pc Behav_done.
  Proof. inversion 1;subst;econstructor;eauto;eapply non_evt_star_equiv;eauto. Qed.
  Lemma Etr_np_p_diverge:
    forall ge pc,
      Etr (@np_step ge) np_abort final_state pc Behav_diverge->
      Etr glob_step abort final_state pc Behav_diverge.
  Proof. inversion 1;subst;constructor;eapply silent_diverge_np_p;eauto. Qed.
  Lemma Etr_np_p_abort:
    forall ge pc,
      @np_accepted ge pc->
      Etr (@np_step ge) np_abort final_state pc Behav_abort->
      Etr glob_step abort final_state pc Behav_abort.
  Proof. inversion 2;subst;econstructor;eauto;eapply non_evt_star_star in H1 as L1;destruct L1;try eapply non_evt_star_equiv;try eapply star_abort_np_p;eauto;eapply np_accepted_add_star;eauto. Qed.
  Lemma Etr_np_cons_inv:
    forall ge pc v b,
      np_accepted pc->
      Etr (@np_step ge) np_abort final_state pc (Behav_cons v b)->
      exists fp pc' pc'',non_evt_star np_step pc fp pc'/\np_step pc' (evt v) FP.emp pc'' /\ Etr np_step np_abort final_state pc'' b /\ np_accepted pc''.
  Proof.
    intros.
    inversion H0;subst.
    do 4 eexists;eauto.
    split;eauto.
    split;eauto.
    apply non_evt_star_star in H3 as [].
    eapply star_cons_step in H4 as [];eauto.
    eapply np_accepted_add_star;eauto.
  Qed.
  Inductive limited_etr {ge}:nat->@Step ge->(@ProgConfig ge->Prop)->(@ProgConfig ge->Prop)-> @ProgConfig ge->behav->Prop:=
  | done_0: forall step abort final pc,
      Etr step abort final pc Behav_done->
      limited_etr 0 step abort final pc Behav_done
  | abort_0: forall step abort final pc,
      Etr step abort final pc Behav_abort->
      limited_etr 0 step abort final pc Behav_abort
  | diverge_0: forall step abort final pc,
      Etr step abort final pc Behav_diverge->
      limited_etr 0 step abort final pc Behav_diverge
  | cons': forall step abort final pc fp pc' pc'' v i b,
      limited_etr i step abort final pc'' b->
      non_evt_star step pc fp pc'->
      step pc' (evt v) FP.emp pc'' ->
      limited_etr (S i) step abort final pc (Behav_cons v b).
                   
  Lemma limited_etr_npetr:
    forall ge i pc b,
      @limited_etr ge i np_step np_abort final_state pc b->
      Etr np_step np_abort final_state pc b.
  Proof.
    induction i;intros.
    inversion H;subst;auto.

    inversion H;subst.
    econstructor;eauto.
  Qed.

  Lemma Etr_np_p_limited:
    forall ge i pc b,
      @np_accepted ge pc->
      limited_etr i np_step np_abort final_state pc b->
      Etr glob_step abort final_state pc b.
  Proof.
    induction i;intros.
    inversion H0;subst;auto.
    eapply Etr_np_p_done;eauto.
    eapply Etr_np_p_abort;eauto.
    eapply Etr_np_p_diverge;eauto.

    inversion H0;subst.
    apply non_evt_star_equiv in H3 as L1.
    apply np_evtstep_inv in H4 as L2.
    destruct L2.
    econstructor;eauto.
    eapply Etr_p_sw;eauto.
    eapply IHi;eauto.
    apply non_evt_star_star in H3 as [].
    eapply star_cons_step in H4 as [];eauto.
    eapply np_accepted_add_star;eauto.
  Qed.

  CoInductive inf_etr {ge}(step:@Step ge)(abort final:@ProgConfig ge->Prop):@ProgConfig ge->behav->Prop:=
  | build_infetr:
      forall pc fp pc' v pc'' b,
        inf_etr step abort final pc'' b->
        non_evt_star step pc fp pc'->
        step pc' (evt v) FP.emp pc'' ->
        inf_etr step abort final pc (Behav_cons v b).
  Definition inf_etr_alt {ge}(step:@Step ge)(abort final:@ProgConfig ge->Prop)(pc:@ProgConfig ge)(b:behav):Prop:=
    Etr step abort final pc b /\ ~ exists i,limited_etr i step abort final pc b.

  Lemma inf_etr_alt_inv:
    forall ge step abort final pc b,
      @inf_etr_alt ge step abort final pc b->
      exists fp pc' pc'' v b',
        b = Behav_cons v b' /\
        non_evt_star step pc fp pc' /\
        step pc' (evt v) FP.emp pc'' /\
        inf_etr_alt step abort final pc'' b'.
  Proof.
    destruct 1.
    inversion H;subst;try (contradict H0;exists 0;econstructor;eauto;fail).
    exists fp,state',state'',v,B'.
    unfold inf_etr_alt.
    repeat try match goal with H:_|-_/\_=> split end;auto.
    intro L;contradict H0;destruct L;eexists;econstructor;eauto.
  Qed.

  Lemma inf_etr_alt_sound:
    forall ge step abort final pc b,
      @inf_etr_alt ge step abort final pc b->
      inf_etr step abort final pc b.
  Proof.
    cofix.
    intros.
    apply inf_etr_alt_inv in H as (fp&pc'&pc''&v&b'&eq&nstar1&step1&inf').
    subst.
    econstructor;eauto.
  Qed.
    
  CoInductive inf_etr_alt2 {ge}(step:@Step ge)(abort final:@ProgConfig ge->Prop):@ProgConfig ge->behav->Prop:=
  | build_infetr':
      forall pc fp pc' v pc'' pc''' b,
        inf_etr_alt2 step abort final pc''' b->
        non_evt_star step pc fp pc'->
        step pc' (evt v) FP.emp pc'' ->
        step pc'' sw FP.emp pc''' ->
        inf_etr_alt2 step abort final pc (Behav_cons v b).
  
  Lemma sw_step_non_evt_star:
    forall ge (step:@Step ge) s s',
      step s sw FP.emp s'->
      non_evt_star step s FP.emp s'.
  Proof.
    intros.
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    econstructor;eauto.
    constructor.
  Qed.
  Lemma non_evt_star_cons_inf_etr_alt2:
    forall ge (step:@Step ge) s fp s' b abort final,
      non_evt_star step s fp s'->
      inf_etr_alt2 step abort final s' b->
      inf_etr_alt2 step abort final s b.
  Proof.
    inversion 2;subst.
    eapply non_evt_star_cons in H2;eauto.
    econstructor;eauto.
  Qed.

  Lemma inf_etr_alt2_p:
    forall ge a f pc b,
      GlobEnv.wd ge->
      invpc ge pc->
      inf_etr glob_step a f pc b->
      @inf_etr_alt2 ge glob_step a f pc b.
  Proof.
    cofix;inversion 3;subst.
    apply non_evt_star_star in H3 as ?;destruct H5.
    apply GE_mod_wd_star_tp_inv2 in H5;try assumption.
    eapply GE_mod_wd_tp_inv in H5 as ?;try eassumption.
    assert(glob_step pc'' sw FP.emp pc'').
    inversion H4;subst;econstructor;eauto.
    eapply gettop_valid_tid;eauto. solv_thread.
    intro;solv_thread.

    econstructor;try eapply inf_etr_alt2_p;eauto.
  Qed.
    
    
  Lemma inf_etr_alt2_sound:
    forall ge step abort final pc b,
      @inf_etr_alt2 ge step abort final pc b->
      inf_etr step abort final pc b.
  Proof.
    cofix.
    intros.
    inversion H;subst.
    apply sw_step_non_evt_star in H3.
    eapply non_evt_star_cons_inf_etr_alt2 in H3;[|eauto].
    econstructor;eauto.
  Qed.

  Lemma np_inf_etr_glob_inf_etr_alt2:
    forall ge pc b,
      @inf_etr ge np_step np_abort final_state pc b->
      inf_etr_alt2 glob_step abort final_state pc b.
  Proof.
    cofix.
    intros.
    inversion H;subst.
    apply non_evt_star_equiv in H1.
    apply np_evtstep_inv in H2 as [].
    apply sw_step_non_evt_star in H3 as H4.
    econstructor;eauto.
  Qed.

  Lemma inf_etr_np_p:
    forall ge pc b,
      @inf_etr ge np_step np_abort final_state pc b->
      inf_etr glob_step abort final_state pc b.
  Proof.
    intros.
    apply np_inf_etr_glob_inf_etr_alt2 in H.
    apply inf_etr_alt2_sound;auto.
  Qed.

  Lemma inf_etr_etr:
    forall ge step abort final pc b,
      @inf_etr ge step abort final pc b->
      Etr step abort final pc b.
  Proof.    
    cofix.
    intros.
    inversion H;subst.
    econstructor;eauto.
  Qed.

  
  Lemma Etr_np_p:
    forall ge pc b,
      @np_accepted ge pc-> 
      Etr np_step np_abort final_state pc b->
      Etr glob_step abort final_state pc b.
  Proof.
    intros.
    assert((exists i,limited_etr i np_step np_abort final_state pc b) \/ (~ exists i,limited_etr i np_step np_abort final_state pc b)).
    apply classic.
    destruct H1.
    destruct H1.
    eapply Etr_np_p_limited;eauto.
    
    assert(inf_etr_alt np_step np_abort final_state pc b).
    split;auto.
    clear H0 H1.
    
    apply inf_etr_alt_sound in H2.
    apply inf_etr_np_p in H2.
    apply inf_etr_etr;auto.
  Qed.

  Lemma p_np_refine{NL}{L}:
    forall P,@p_np_prog_refine NL L P.
  Proof.
    unfold p_np_prog_refine in *;unfold p_np_config_refine in *.
    intros.
    apply Etr_np_p;auto.
    unfold np_accepted.
    do 6 eexists;eauto.
    do 2 eexists;constructor.
  Qed.

  Definition drf_pc{ge:GlobEnv.t} (pc:@ProgConfig ge):=
    exists NL L p gm, drfpc pc /\ @init_config NL L p gm ge pc pc.(cur_tid) /\ wd_langs (fst p) /\ safe_state glob_step abort pc.

  Definition drf_pc_glob {ge}(pc:@ProgConfig ge):=
    atom_bit pc = O /\
    exists pc0 l fp,drf_pc pc0 /\ star glob_step pc0 l fp pc.
  Lemma drf_pc_glob_cons:
    forall ge pc l fp pc',
      @drf_pc_glob ge pc->
      star glob_step pc l fp pc'->
      atom_bit pc' = O ->
      drf_pc_glob pc'.
  Proof.
    unfold drf_pc_glob;intros.
    destruct H as (?&?&?&?&?&?);split;auto.
    do 4 eexists;eauto.
    eapply cons_star_star;eauto.
  Qed.


  Lemma drf_pc_glob_l1:
    forall ge pc,
      @drf_pc_glob ge pc->
      ThreadPool.inv pc.(thread_pool)/\
      GlobEnv.wd ge.
  Proof.
    unfold drf_pc_glob;intros.
    destruct H as (?&?&?&?&?&?).
    destruct H0 as (?&?&?&?&?&?&?).
    assert(ThreadPool.inv x.(thread_pool)).
    inversion H2;subst.
    eapply ThreadPool.init_inv;eauto.
    assert(GlobEnv.wd ge).
    eapply init_config_GE_wd;eauto.
    eauto.
    split. eapply GE_mod_wd_star_tp_inv2 in H1;eauto.
    auto.
  Qed.
  Lemma drf_pc_glob_l2:
    forall ge pc,
      @drf_pc_glob ge pc->
      (forall ix,
        mod_wd (GlobEnv.modules ge ix)).
  Proof.
    unfold drf_pc_glob;intros.
    destruct H as (?&?&?&?&?&?).
    destruct H0 as (?&?&?&?&?&?&?).
    eapply lang_wd_mod_wd;eauto. Hsimpl;eauto.
  Qed.

  Lemma stepN_SN_split_weak:
    forall i ge pc l fp pc',
      stepN ge glob_step (S i) pc l fp pc'->
      exists l1 fp1 pc1,stepN ge glob_step i pc l1 fp1 pc1 /\
                   exists l2 fp2,glob_step pc1 l2 fp2 pc'.
  Proof.
    induction i;intros.
    exists nil,FP.emp,pc. split. constructor.
    inversion H;subst. inversion H1;subst. eauto.

    inversion H;subst.
    eapply IHi in H1 as (?&?&?&?&?&?&?).
    eapply stepN_cons in H3;eauto.
    repeat eexists;eauto.
  Qed.

  Lemma valid_tid_preserve':
    forall ge pc l fp pc',
      GlobEnv.wd ge->
      ThreadPool.inv pc.(thread_pool)->
      @glob_step ge pc l fp pc'->
      ThreadPool.valid_tid pc'.(thread_pool) pc'.(cur_tid) \/ ThreadPool.halted pc'.(thread_pool) pc'.(cur_tid).
  Proof.
    intros.
    eapply GE_mod_wd_tp_inv in H0 as ?;eauto.
    inversion H1;subst;simpl;try(left;auto;eapply gettop_valid_tid;solv_thread;solv_thread;fail);try (right;auto;fail).
  Qed.

  Lemma pc_glob_l3:
    forall NL L p gm ge pc0 pc l fp,
      @init_config NL L p gm ge pc0 pc0.(cur_tid)->
      star glob_step pc0 l fp pc->
      ThreadPool.valid_tid pc.(thread_pool) pc.(cur_tid)\/
      ThreadPool.halted pc.(thread_pool) pc.(cur_tid).
  Proof.
    intros until fp;intro init;intros.
    apply star_stepN in H as [].
    destruct x.
    inversion H;subst.
    apply init_property_1 in init.  auto.

    apply stepN_SN_split_weak in H.
    Hsimpl.
    apply stepN_star in H.
    apply init_config_GE_wd in init as ?.
    assert(invpc ge pc0). inversion init;eapply ThreadPool.init_inv;eauto.
    eapply GE_mod_wd_star_tp_inv2 in H;eauto.
    eapply valid_tid_preserve' in H0;eauto.
  Qed.

  Definition non_evt_thrd_globstar (ge:GlobEnv.t)(pc:@ProgConfig ge)(fp:FP.t)(pc':@ProgConfig ge):Prop:=
    exists i l fp1 pc1,
      atomblockstarN ge i l pc fp1 pc1 /\
      exists fp2,
        tau_star glob_npnsw_step pc1 fp2 pc' /\
        FP.union fp1 fp2 = fp.

   Lemma atomblockstep_star:
    forall ge pc fp pc' l0,
      atomblockstep ge pc l0 fp pc'->
      exists l,star glob_step pc l fp pc'.
  Proof.
    inversion 1;subst.
    Hsimpl.
    destruct H0.
    Hsimpl.
    apply coretauN_globtauN in H1.
    apply tauN_taustar in H1.
    apply tau_star_to_star in H1 as [].
    apply type_glob_step_elim in H0.
    apply type_glob_step_elim in H2.
    eapply star_cons_step in H2 as [];eauto.
    eapply star_step in H2;eauto.
    rewrite FP.emp_union_fp in H2.
    rewrite FP.fp_union_emp in H2.
    eauto.
  Qed.
  Lemma swstar_star:
    forall ge pc pc',
      sw_star (@glob_step ge) pc pc'->
      exists l,star glob_step pc l FP.emp pc'.
  Proof.
    induction 1;intros.
    eexists;econstructor.
    destruct IHsw_star.
    eapply star_step in H1;eauto.
    rewrite FP.fp_union_emp in H1.
    eauto.
  Qed.
  Lemma atomblockstarN_star:
    forall ge i l pc fp pc',
      atomblockstarN ge i l pc fp pc'->
      exists l',star glob_step pc l' fp pc'.
  Proof.
    induction 1;intros.
    Esimpl. constructor.
    destruct IHatomblockstarN.
    apply tau_star_to_star in H as [].
    apply npnsw_star_glob_star in H.
    assert(exists l,star glob_step pc1 l fp2 pc2).
    destruct H0.
    eapply atomblockstep_star;eauto.
    apply type_glob_step_elim in H0.
    exists (cons tau nil).
    rewrite <- FP.fp_union_emp with(fp:=fp2).
    econstructor;eauto. constructor.
    destruct H4.
    apply swstar_star in H1 as [].
    eapply cons_star_star in H1;eauto.
    eapply cons_star_star in H1;eauto.
    rewrite FP.fp_union_emp in H1.

    eapply cons_star_star in H3;eauto.
  Qed.
  Lemma non_evt_thrd_globstar_star:
    forall ge pc fp pc',
      @non_evt_thrd_globstar ge pc fp pc'->
      exists l,star glob_step pc l fp pc'.
  Proof.
    unfold non_evt_thrd_globstar;intros;Hsimpl.
    eapply atomblockstarN_star in H as [].
    apply tau_star_to_star in H0 as [].
    apply npnsw_star_glob_star in H0.
    eapply cons_star_star in H0 ;eauto.
    rewrite <- H1. eauto.
  Qed.

    
  Lemma pc_valid_tid_nonevtstar_cons_evtstep:
    forall ge pc fp pc' v pc'',
      drf_pc_glob pc->
      non_evt_star (@glob_step ge) pc fp pc'->
      glob_step pc' (evt v) FP.emp pc''->
      pc_valid_tid pc (cur_tid pc'').
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as [].
    assert(ThreadPool.inv pc'.(thread_pool)).
    apply non_evt_star_star in H0 as [].
    eapply GE_mod_wd_star_tp_inv2;eauto.
    
    apply pc_valid_tid_back in H1;auto.
    apply non_evt_star_star in H0 as [].
    
    eapply pc_valid_tid_back_star in H1;eauto.
  Qed.

  Definition drf_pc_glob_weak (ge:GlobEnv.t)(pc:@ProgConfig ge):=
    exists p l fp,drf_pc p /\ star glob_step p l fp pc.
  Lemma drf_pc_glob_weaken:
    forall ge pc,
      drf_pc_glob pc->
      drf_pc_glob_weak ge pc.
  Proof. destruct 1;auto. Qed.
  Lemma drf_pc_glob_strengthen:
    forall ge pc,
      drf_pc_glob_weak ge pc ->
      atom_bit pc = O->
      drf_pc_glob pc.
  Proof. destruct 1 as (?&?&?&?&?);intro;split;eauto. Qed.

  Lemma non_evt_star_IO:
    forall ge pc fp pc',
      non_evt_star (@glob_step ge) pc fp pc'->
      atom_bit pc = I->
      atom_bit pc' = O->
      exists fp1 pc1,tau_star (type_glob_step core) pc fp1 pc1 /\
                exists pc2,type_glob_step extat pc1 tau FP.emp pc2 /\
                      exists fp2,non_evt_star glob_step pc2 fp2 pc' /\
                             FP.union fp1 fp2 = fp.
  Proof.
    induction 1;intros.
    rewrite H in H0;inversion H0.

    destruct H.
    destruct (atom_bit s2) eqn:?.

    apply type_glob_step_exists in H as [].
    destruct x;try(inversion H;simpl in *;subst;simpl in *;subst;inversion H1;inversion Heqb;fail);auto.
    assert(fp1=FP.emp). inversion H;auto. subst.
    exists FP.emp,s1. split. constructor.
    exists s2. split;auto.
    exists fp2. split;auto.

    assert(I=I). auto.
    specialize (IHnon_evt_star H3 H2) as (?&?&?&?&?&?&?&?).

    exists (FP.union fp1 x),x0. split. econstructor;eauto.
    inversion H;subst;simpl in *;subst;inversion H1;try inversion Heqb;econstructor;eauto.

    eexists;split;eauto.
    eexists;split;eauto.
    rewrite <- H7. rewrite FP.fp_union_assoc;auto.

    inversion H;subst. inversion H1.
  Qed.
  Lemma non_evt_starN_IO:
    forall ge i pc fp pc',
      non_evt_starN (@glob_step ge) i pc fp pc'->
      atom_bit pc = I->
      atom_bit pc' = O->
      exists j fp1 pc1,tau_N (type_glob_step core) j pc fp1 pc1 /\ j <= i /\ 
                exists pc2,type_glob_step extat pc1 tau FP.emp pc2 /\
                      exists fp2,non_evt_starN glob_step (i-j-1) pc2 fp2 pc' /\
                             FP.union fp1 fp2 = fp.
  Proof.
    induction i;intros;inversion H;subst.
    rewrite H0 in H1. inversion H1.

    destruct H3.
    destruct (atom_bit s2) eqn:?.

    apply type_glob_step_exists in H2 as [].
    destruct x;try(inversion H2;simpl in *;subst;simpl in *;subst;inversion H0;inversion Heqb;fail);auto.
    inversion H2;subst. simpl in *;subst. inversion Heqb.
    assert(fp1=FP.emp). inversion H2;auto. subst.
    exists 0,FP.emp,pc. split. constructor. split. Lia.lia.
    exists s2. split;auto.
    exists fp2. split;auto.
    simpl. assert(i-0=i). Lia.lia.
    rewrite H3;auto.
    
    specialize (IHi _ _ _ H5 Heqb H1) as (?&?&?&?&?&?&?&?&?&?).
    exists (S x),(FP.union fp1 x0),x1. split. econstructor;eauto. inversion H2;subst;inversion H0;inversion Heqb. econstructor;eauto.
    split. Lia.lia.

    eexists;split;eauto.
    eexists;split;eauto.
    rewrite <- H8. rewrite FP.fp_union_assoc;auto.

    inversion H2;subst. inversion H0.
  Qed.
  Lemma tau_star_IO:
    forall ge pc fp pc',
      tau_star (@glob_step ge) pc fp pc'->
      atom_bit pc = I->atom_bit pc' = O->
      exists fp1 pc1,tau_star (type_glob_step core) pc fp1 pc1/\
                exists pc2,type_glob_step extat pc1 tau FP.emp pc2/\
                      exists fp2,tau_star glob_step pc2 fp2 pc'/\
                            FP.union fp1 fp2= fp.
  Proof.
    induction 1;intros.
    rewrite H in H0;inversion H0.

    destruct (atom_bit s') eqn:?.

    apply type_glob_step_exists in H as [].
    destruct x;try(inversion H;simpl in *;subst;simpl in *;subst;inversion H1;inversion Heqb;fail);auto.
    assert(fp=FP.emp). inversion H;auto. subst.
    exists FP.emp,s. split. constructor.
    exists s'. split;auto.
    exists fp'. split;auto.

    assert(I=I). auto.
    specialize (IHtau_star H3 H2) as (?&?&?&?&?&?&?&?).

    exists (FP.union fp x),x0. split. econstructor;eauto.
    apply type_glob_step_exists in H as [].
    destruct x3;inversion H;subst;inversion Heqb;inversion H1;auto.

    eexists;split;eauto.
    eexists;split;eauto.
    rewrite <- H7. rewrite FP.fp_union_assoc;auto.
  Qed.

  Lemma tau_N_IO:
    forall i ge pc fp pc',
      tau_N (@glob_step ge) i pc fp pc'->
      atom_bit pc = I->atom_bit pc' = O->
      exists j fp1 pc1,tau_N (type_glob_step core) j pc fp1 pc1/\ j < i /\
                exists pc2,type_glob_step extat pc1 tau FP.emp pc2/\
                      exists fp2,tau_N glob_step (i-j-1) pc2 fp2 pc'/\
                            FP.union fp1 fp2= fp.
  Proof.
    induction i;intros.
    inversion H;subst.
    rewrite H0 in H1. inversion H1.

    inversion H;subst.
    destruct (atom_bit s') eqn:?.

    apply type_glob_step_exists in H3 as [].
    destruct x;try(inversion H2;simpl in *;subst;simpl in *;subst;inversion H0;inversion Heqb;fail);auto.
    inversion H2;subst;simpl in *;subst. inversion Heqb.
    
    assert(fp0=FP.emp). inversion H2;auto. subst.
    exists 0,FP.emp,pc. split. constructor. split. Lia.lia.
    exists s'. split;auto.
    exists fp'. split;auto.
    assert(S i - 0 - 1 = i). Lia.lia.
    rewrite H3;auto.

    specialize (IHi _ _ _ _ H4 Heqb H1) as (?&?&?&?&?&?&?&?&?&?).
    apply type_glob_step_exists in H3 as [].
    destruct x4;try(inversion H3;simpl in *;subst;simpl in *;subst;inversion H0;inversion Heqb;fail);auto.
    exists (S x),(FP.union fp0 x0),x1. split. econstructor;eauto.
    split. Lia.lia.
    eexists;split;eauto.
    eexists;split;eauto.
    rewrite <- H8. rewrite FP.fp_union_assoc;auto.
  Qed.

  Lemma drf_pc_glob_stepfpsmile:
    forall ge pc fp pc' t fp' pc'',
      @drf_pc_glob ge pc->
      glob_step pc tau fp pc'->
      t <> cur_tid pc->
      glob_step ({-|pc',t}) tau fp' pc''->
      FP.smile fp fp'.
  Proof.
    intros.
    apply FP.smile_conflict_compat.
    intro.
    apply FP.emp_never_conflict in H3 as L1.
    destruct L1.
    apply type_glob_step_exists in H0 as [].
    apply type_glob_step_exists in H2 as [].
    destruct x;try (inversion H0;subst;contradiction;fail).
    destruct x0;try (inversion H2;subst;contradiction;fail).
    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    assert(v1:forall ix, mod_wd (GlobEnv.modules ge ix)).
    eapply drf_pc_glob_l2 ;eauto.
    eapply drf_pc_glob_l1 in H as ?;auto. destruct H6 as [v2 v3].
    
    eapply corestep_conflict in H3;Hsimpl;eauto.
    destruct H3.
    unfold drf_pc_glob,drf_pc in H;Hsimpl.
    apply type_glob_step_elim in H0 as?. apply GE_mod_wd_tp_inv in H11;auto.
    apply type_glob_step_cur_valid_id in H2;auto.
    apply npnswstep_l3 in H0;auto.
    eapply npnswstep_pc_valid_tid_backwards_preservation in H0;eauto.
    assert(glob_step pc sw FP.emp ({-|pc,t})).
    destruct pc,H0;simpl in *;subst;econstructor;eauto.
    eapply star_cons_step in H12;eauto. Hsimpl.
    apply H10 in H12;auto.
    intro R;inversion R.

    Hsimpl.
    destruct H as (?&?&?&?&?&?).
    destruct H7 as (?&?&?&?&?&?&?).
    unfold drfpc in H7.
    contradict H7.
    unfold star_race_config.
    exists x2,x3,pc.
    split;auto.
    econstructor.
    apply H1.
    instantiate(2:=O).
    instantiate(1:=x).
    destruct pc.
    simpl in *;subst.
    inversion H3;subst.
    econstructor;eauto.
    instantiate(2:=O).
    instantiate(1:=fp).
    destruct pc.
    simpl in *;subst.
    inversion H0;subst.
    econstructor;eauto.
    left;intro contra;inversion contra.
    apply FP.conflict_sym;auto.
   
  Qed.

  Lemma type_glob_step_atomOpreserve:
    forall ge i pc l fp pce,
      @type_glob_step ge i pc l fp pce->
      atom_bit pce = atom_bit pc->
      forall GE pc' l' fp' pc'',
        @type_glob_step GE i pc' l' fp' pc''->
        atom_bit pc'' = atom_bit pc'.
  Proof. intros;destruct i;inversion H;simpl in *;subst;inversion H0;inversion H1;subst;auto. Qed.

  Lemma tid_change_bit_eq:forall ge (pc:@ProgConfig ge) t, atom_bit ({-|pc,t}) = atom_bit pc.
  Proof. destruct pc;auto. Qed.

  Lemma drf_pc_glob_taustep_ex:
    forall ge pc fp pc' t fp' pc'',
      drf_pc_glob pc->
      glob_step pc tau fp pc'->
      t <> cur_tid pc->
      glob_step ({-|pc',t}) tau fp' pc''->
      atom_bit pc' = O ->
      atom_bit pc'' = O->
      exists pc1,glob_step ({-|pc,t}) tau fp' pc1/\ atom_bit pc1 = O /\
            exists pc2,glob_step ({-|pc1,cur_tid pc}) tau fp pc2 /\
                  mem_eq_pc ge pc'' ({-|pc2,t}) /\
                  drf_pc_glob pc2.
  Proof.
    intros.
    assert(O1:atom_bit pc = O). inversion H;auto.
    eapply drf_pc_glob_stepfpsmile in H as L;eauto.
    apply type_glob_step_exists in H0 as [].
    apply type_glob_step_exists in H2 as [].
    assert(tau<>sw). intro R;inversion R.
    apply drf_pc_glob_l1 in H as R;destruct R.
    specialize (drf_pc_glob_l2 ge pc H) as wdge.
    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    
    eapply globstep_reorder_rule in L as (?&?&?&?&?);eauto;try congruence.
    exists x1.
    split. eapply type_glob_step_elim;eauto.
    split. pose proof type_glob_step_atomOpreserve.
    rewrite <- H3 in H4. rewrite <- tid_change_bit_eq with(pc:=pc')(t:=t) in H4.
    specialize (type_glob_step_atomOpreserve _ _ _ _ _ _ H2 H4 _ _ _ _ _ H8) as L1.
    rewrite tid_change_bit_eq in L1. congruence.
    eexists;split;[eapply type_glob_step_elim|split];eauto.
    assert(cur_tid pc'' = t). inversion H2;auto.
    rewrite <- H11;auto.

    apply type_glob_step_elim in H8 as L1.
    apply type_glob_step_elim in H9 as L2.
    assert(glob_step pc sw FP.emp ({-|pc,t})).
    apply drf_pc_glob_l1 in H as [].
    eapply globstep_pc_valid_curtid in L1 as [];eauto.
    destruct pc;simpl in*;subst;econstructor;eauto.

    assert(drf_pc_glob x1).
    eapply drf_pc_glob_cons;eauto.
    do 2 (eapply star_step;eauto). constructor.
    assert(atom_bit ({-|pc',t}) = atom_bit pc'').
    destruct pc';simpl in *;subst. congruence.
    pose proof type_glob_step_atomOpreserve.
    symmetry in H12.
    specialize (H13 _ _ _ _ _ _ H2 H12  _ _ _ _ _ H8).
    rewrite H13.
    destruct pc;simpl in *;auto.

    assert(glob_step x1 sw FP.emp ({-|x1,cur_tid pc})).
    eapply drf_pc_glob_l1 in H12 as L';destruct L'.
    eapply globstep_pc_valid_curtid in L2 as [];eauto.
    destruct H12.
    destruct x1;simpl in *;subst;econstructor;eauto.

    eapply drf_pc_glob_cons;eauto.
    do 2 (eapply star_step;eauto). constructor.
    assert(atom_bit pc' = atom_bit pc). congruence.
    pose proof type_glob_step_atomOpreserve.
    specialize (H15 _ _ _ _ _ _ H0 H14 _ _ _ _ _ H9).
    inversion H12. destruct x1;subst;simpl in *;subst;auto.
  Qed.


  Lemma drf_pc_glob_taustep_halfatomblock_fpsmile:
    forall ge pc fp pc' t pc1 fp2 pc2,
      @drf_pc_glob ge pc->
      glob_step pc tau fp pc'->
      t <> cur_tid pc->
      type_glob_step entat ({-|pc',t}) tau FP.emp pc1 ->
      tau_star (type_glob_step core) pc1 fp2 pc2->
      FP.smile fp fp2.
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as L1;destruct L1 as [R1 R2].
    specialize (drf_pc_glob_l2 ge pc H) as modwd.
    apply FP.smile_conflict_compat.
    intro.
    apply FP.emp_never_conflict in H4 as L;destruct L.
    apply type_glob_step_exists in H0 as [].
    destruct x;try(inversion H0;subst;contradiction).
    rewrite<- pc_cur_tid with(pc:=pc) in H0.
    eapply atomblock_open_reorderstep1 in H0 as L1;eauto.
    destruct L1 as (?&?&?&?&?&?).
    assert(mem_eq_pc ge pc1 (changepc ge x0 t I)).
    unfold mem_eq_pc. split;auto. split. inversion H2;auto.
    split;auto. inversion H2;auto. rewrite <-H10. simpl. apply GMem.eq'_refl.
    eapply mem_eq_corestar in H11 as (?&?&?);eauto.

    apply FP.conflict_sym in H4.
    eapply taustar_fpconflict_split in H11;eauto.
    destruct H11 as (?&?&?&?&?&?&?&?&?&?).
    eapply atomblock_open_reorder_corestar in H11 as L;eauto.
    destruct L as (?&?&?&?&?&?).

    assert(mem_eq_pc ge x4 (changepc ge x7 t I)).
    unfold mem_eq_pc. split;auto. apply corestar_tid_bit_preserve in H11 as []. split;auto. split;auto. simpl. apply GMem.eq'_sym;auto.

    eapply mem_eq_corestep in H22 as L;eauto.
    destruct L as (?&?&?).
    eapply corestep_changebit with(x:=I) in H19.
    simpl in H19. rewrite changepc_again in H19.
    assert(changepc ge x6 (cur_tid pc) I = ({-|(changepc ge x6 t I),cur_tid pc})).
    auto.
    rewrite H25 in H19.
    assert(changepc ge x7 t I = ({-|(changepc ge x7 (cur_tid pc) I),t}));auto.
    rewrite H26 in H23.
    
    eapply corestep_conflict in H15 as L;eauto.
    destruct L.

    assert(x6 = ({-|changepc ge x6 t I, t})). simpl.
    apply corestar_tid_bit_preserve in H18 as [].
    destruct x6;simpl in *;subst. auto.
    rewrite <- H28 in H27. clear H28.
    contradict H27.
    apply corestar_globstar in H18.
    apply tau_star_to_star in H18 as [].
    assert(x = changepc ge x t I). inversion H7;subst;auto.
    rewrite <- H27 in *.
    apply type_glob_step_cur_valid_id in H7 as ?.
    assert(glob_step pc sw FP.emp ({-|pc,t})).
    destruct pc,H28;simpl in *;subst.
    destruct H. simpl in H;subst.
    econstructor;eauto.
    eapply type_glob_step_elim in H7.
    eapply star_step in H7;eauto.
    eapply star_step in H29;eauto.
    unfold drf_pc_glob,drf_pc in H;Hsimpl.
    eapply cons_star_star in H29;eauto.

    auto.
    intro R;inversion R.
    
    destruct H27 as (?&?&?&?).
    rewrite changepc_curtid in H27.
    assert(changepc ge x6 t I = x6).
    destruct x6;simpl in *;subst. unfold changepc.
    apply corestar_tid_bit_preserve in H18 as [].
    simpl in *;subst;auto.
    rewrite H29 in *.

    assert(changepc ge x t I =x).
    inversion H7;subst;auto.
    rewrite H30 in *.
    
    inversion H.
    destruct H32 as (?&?&?&?&?).
    destruct H32 as (?&?&?&?&?&?&?).
    unfold drfpc in H32. contradict H32.
    unfold star_race_config.
    do 4 eexists;eauto.

    eapply race_equiv.
    pose proof  predict_equiv.
    eapply predict_equiv_race_equiv in H32;eauto.
    eapply H32.
    destruct pc as [thdp tid tgm tbit];simpl in *;subst.
    econstructor.
    eapply H1.
    instantiate(2:=I).
    instantiate(1:=FP.union x2 x9).
    econstructor;eauto.
    eapply tau_star_star;eauto.
    rewrite <- FP.fp_union_emp with(fp:=x9).
    eapply tau_star_cons;eauto. constructor.

    instantiate(2:=O).
    instantiate(1:=fp).
    econstructor;eauto.
    right. intro contra;inversion contra.
    rewrite FP.union_comm_eq.
    apply conflict_union.
    apply FP.conflict_sym;auto.

    simpl. assert(ThreadPool.inv x.(thread_pool)).
    apply type_glob_step_elim in H7.
    eapply GE_mod_wd_tp_inv in H7;eauto.
    apply core_tau_star_star in H18 as [].    
    eapply GE_mod_wd_star_tp_inv2 in H18;eauto.

    inversion H8;auto.
    intro contra;inversion contra.
    apply type_glob_step_elim in H7.
    eapply GE_mod_wd_tp_inv in H7;eauto.
    inversion H0;auto.
    intro contra;inversion contra.
  Qed.


  Lemma drf_pc_glob_taustep_atomblock_ex:
    forall ge pc fp pc' t pc1 i fp2 pc2 pc3,
      @drf_pc_glob ge pc->
      glob_step pc tau fp pc'->
      atom_bit pc' = O->
      t <> cur_tid pc->
      type_glob_step entat ({-|pc',t}) tau FP.emp pc1->
      tau_N (type_glob_step core) i pc1 fp2 pc2->
      type_glob_step extat pc2 tau FP.emp pc3->
      exists pc1',
        type_glob_step entat ({-|pc,t}) tau FP.emp pc1'/\
        exists pc2',
          tau_N (type_glob_step core) i pc1' fp2 pc2'/\
          exists pc3',
            type_glob_step extat pc2' tau FP.emp pc3'/\
            exists pc4',
              glob_step ({-|pc3',cur_tid pc}) tau fp pc4' /\
              mem_eq_pc ge pc3 ({-|pc4',cur_tid pc3}) /\
              drf_pc_glob pc3'.
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as L;destruct L as [R1 R2].
    specialize (drf_pc_glob_l2 ge pc H) as modwd.
    assert(atomblockN ge i ({-|pc',t}) fp2 pc3).
    unfold atomblockN.
    repeat (eexists;eauto).
    eapply drf_pc_glob_taustep_halfatomblock_fpsmile in H0 as ?;eauto.
    apply type_glob_step_exists in H0 as [].
    assert(atom_bit pc = atom_bit pc'). inversion H;congruence.
    rewrite <- pc_cur_tid with (pc:=pc) in H0.
    assert(L:tau<>sw). intro L;inversion L.
    eapply atomblock_reorder in H6 as (?&?&?&?&?);eauto.
    inversion H6 as (?&?&?&?&?).
    do 8 (eexists;eauto). eapply type_glob_step_elim;eauto.
    split;auto.

    inversion H6 as (?&?&?&?&?).

    assert(glob_step pc sw FP.emp ({-|pc,t})).
    eapply type_glob_step_elim in H14.
    apply globstep_pc_valid_curtid in H14;auto.
    destruct H,pc,H14;simpl in *;subst;econstructor;eauto.

    assert(drf_pc_glob x0).
    apply tauN_taustar in H15.
    eapply core_tau_star_star in H15 as [];eauto.
    eapply drf_pc_glob_cons;eauto.
    eapply star_step;eauto.
    eapply star_step;eauto. eapply type_glob_step_elim;eauto.
    eapply cons_star_star;eauto.
    eapply star_step. eapply type_glob_step_elim;eauto. constructor.
    inversion H16;auto.

    auto.
    eapply tauN_taustar;eauto.
  Qed.


  Lemma drf_pc_glob_taustep_taustar_ex:
    forall x ge pc fp pc' t fp2 pc'',
      @drf_pc_glob ge pc->
      glob_step pc tau fp pc'->
      atom_bit pc' = O ->
      tau_N glob_step x ({-|pc',t}) fp2 pc''->
      atom_bit pc'' = O->
      t <> cur_tid pc->
      exists pc1,
        tau_N glob_step x ({-|pc,t}) fp2 pc1 /\
        atom_bit pc1 = O /\
        exists pc2,
          glob_step ({-|pc1,cur_tid pc}) tau fp pc2 /\
          atom_bit pc2 = O /\
          mem_eq_pc ge pc'' ({-|pc2,t})/\
          drf_pc_glob pc2.
  Proof.
    induction x using (well_founded_induction lt_wf);intros.
    specialize (drf_pc_glob_l2 _ _ H0) as modwdge.
    apply drf_pc_glob_l1 in H0 as L1.
    destruct L1 as [invpc wdge].
    inversion H3;subst.
    {
      exists ({-|pc,t}). split. constructor.
      split. inversion H0. destruct pc;simpl in*;auto.
      exists pc'. simpl. rewrite pc_cur_tid. split;auto.
      split;auto.
      split;[apply mem_eq_pc_refl|].
      eapply drf_pc_glob_cons;eauto. eapply star_step;eauto. constructor.
    }
    {
      destruct (atom_bit s') eqn:?.
      {
        eapply drf_pc_glob_taustep_ex in H1 as L1;eauto.
        destruct L1 as (?&?&?&?&?&?&?).
        eapply mem_eq_glob_tauN in H11 as L1;eauto.
        destruct L1 as (?&?&?).

        assert(n<S n). auto.
        assert(R1:drf_pc_glob x).
        assert(glob_step pc sw FP.emp ({-|pc,t})).
        apply globstep_pc_valid_curtid in H8;auto.
        destruct H0,pc,H8;simpl in *;subst;econstructor;eauto.
        intro contra;inversion contra.
        eapply drf_pc_glob_cons in H0;eauto.
        do 2 (eapply star_step;eauto). constructor.
        inversion H12 as (?&_).
        assert(atom_bit x1 = O). destruct H14 as (?&?&?&?). congruence.

        assert(R2:drf_pc_glob ({-|x,cur_tid pc})).
        assert(glob_step x sw FP.emp ({-|x,cur_tid pc})).
        apply globstep_pc_valid_curtid in H10;auto.
        destruct x,H10;simpl in *;subst;econstructor;eauto.
        apply drf_pc_glob_l1 in R1 as [];auto.
        intro contra;inversion contra.
        eapply drf_pc_glob_cons;eauto.
        eapply star_step;eauto. constructor.
        specialize (H n H15 _ _ _ _ _ _ _ R2 H10 H16 H13 H17 H5).

        destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?).
        simpl in *.
        assert(cur_tid x = t). inversion H8;auto. subst.
        rewrite pc_cur_tid in H.
        exists x2. split;econstructor;eauto.
        eexists;split;eauto.
        split;auto.
        split;auto.
        eapply mem_eq_pc_trans;eauto.

        apply tauN_taustar in H.
        apply tau_star_to_star in H as [].
        eapply drf_pc_glob_cons in H;eauto.
        apply drf_pc_glob_l1 in H as L. destruct L.
        apply globstep_pc_valid_curtid in H19 as L1;auto.
        assert(glob_step x2 sw FP.emp ({-|x2,cur_tid pc})).
        destruct x2,L1;simpl in *;subst;econstructor;eauto.
        eapply drf_pc_glob_cons in H;eauto.
        eapply star_step. eauto.
        eapply star_step;eauto. constructor.
        intro contra;inversion contra.
      }
      {
        apply type_glob_step_exists in H6 as [].
        destruct x;try(inversion H6;subst;simpl in *;subst;inversion H2;inversion Heqb;fail).
        inversion H6;subst. simpl in *. rewrite H2 in Heqb;inversion Heqb.
        
        eapply tau_N_IO in H7 ;eauto.
        destruct H7 as (?&fp1&pc1&star1&?&pc2&extstep&fp2&star2&fpunion).
        assert(tau_star (type_glob_step core) s' fp1 pc1).
        eapply tau_star_tau_N_equiv;eauto.
        assert(fp0=FP.emp). inversion H6;auto. rewrite H9 in *;clear H9. 
        eapply drf_pc_glob_taustep_atomblock_ex in H1 as L;eauto.

        destruct L as (pc1'&ent1'&pc2'&star1'&pc3'&ext1'&pc4'&step'&eq'&drf').

        assert(n-x-1<S n). Lia.lia.
        assert(drf_pc_glob ({-|pc3',cur_tid pc})).
        assert(glob_step pc3' sw FP.emp ({-|pc3',cur_tid pc})).
        apply globstep_pc_valid_curtid in step' as [].
        destruct drf',pc3';simpl in *;subst;econstructor;eauto.
        apply drf_pc_glob_l1 in drf' as [];auto.
        intro contra;inversion contra.
        eapply drf_pc_glob_cons;eauto. eapply star_step;eauto. constructor.
        inversion drf';auto.
        
        inversion eq' as (_&?&_&_).
        assert(atom_bit pc2 = O).
        inversion extstep;auto.
        rewrite H12 in H11;symmetry in H11;simpl in H11.
        
        eapply mem_eq_glob_tauN in eq' as L2;eauto.
        destruct L2 as (?&?&?).
        assert(cur_tid pc2 =t ).
        assert(cur_tid s' = t). inversion H6;auto.
        assert(cur_tid pc1=t).
        revert star1 H15;clear;intros.
        induction star1;auto.
        apply IHstar1. rewrite <-H15. inversion H;auto.
        inversion extstep;subst;auto.

        rewrite H15 in *;clear H15.

        eapply H in H13 as L;eauto.
        destruct L as (?&?&?&?&?&?&?&?).
        simpl in *.

        exists x1;split.
        {
          apply type_glob_step_elim in ent1'.
          eapply tau_N_S;eauto.
          apply type_glob_step_elim in ext1'.
          assert(cur_tid pc3' = t).
          assert(cur_tid pc1' = t). inversion ent1';auto.
          assert(cur_tid pc2' = t).
          revert star1' H21;clear;intros.
          induction star1';auto. eapply IHstar1'. inversion H;subst;auto.
          inversion ext1';subst;auto.

          rewrite <- H21 in H15. rewrite pc_cur_tid in H15.          
          eapply tau_N_S in H15;eauto.
          assert(S(n-x-1) = n-x). Lia.lia.
          rewrite H22 in H15.
          assert(n=x+(n-x)). Lia.lia. rewrite H23.
          rewrite<- fpunion.
          apply coretauN_globtauN in star1'.
          rewrite FP.emp_union_fp in H15.
          eapply tau_N_cons;eauto.
        }
        split;auto.
        esplit;split;eauto.
        split;auto.
        split;auto.
        eapply mem_eq_pc_trans;eauto.
        inversion H14 as (?&?&?&?).
        congruence.
      }
    }
  Qed.

  Lemma globstep_conflict_corestep:
    forall ge pc l fp pc' fp'',
      @glob_step ge pc l fp pc'->
      FP.conflict fp fp''->
      type_glob_step core pc tau fp pc'.
  Proof. intros. apply FP.emp_never_conflict in H0 as [].  inversion H;subst;try contradiction. econstructor;eauto. Qed.
      
  Lemma drf_pc_l4:
    forall ge pc,
      @drf_pc_glob ge pc->
      forall l fp pc',
        star glob_step pc l fp pc'->
        race glob_predict_star_alter pc'->
        False.
  Proof.
    intros.
    inversion H as (?&?).
    Hsimpl. destruct H3. Hsimpl.
    apply drf_pc_glob_l1 in H as ?;Hsimpl.
    apply GE_mod_wd_star_tp_inv2 in H0 as ?;eauto.
    unfold drfpc in H3.
    contradict H3.
    eapply globrace_equiv in H1;eauto.
    destruct H1;Hsimpl.
    pose predict_equiv.
    eapply predict_equiv_race_equiv in i.
    eapply i in H3.
    apply race_equiv in H3.
    unfold star_race_config.
    eapply cons_star_star in H1;try eassumption.
    eapply cons_star_star in H1;try eassumption.
    Esimpl;eauto.
    eapply drf_pc_glob_l2;eauto.
  Qed.



  Lemma predicted_abort1_star_abort:
    forall ge pc,
      predicted_abort1 ge pc ->
      exists l fp pc',
        star glob_step pc l fp pc'/\
        abort pc'.
  Proof.
    intros.
    inversion H;subst.
    {
      unfold halfatomblock_abort,halfatomblockstep in H1. Hsimpl.
      apply corestar_globstar in H4.
      apply type_glob_step_elim in H3.
      eapply tau_star_cons in H3;eauto.
      apply npnsw_taustar_to_taustar in H0.
      eapply tau_star_star in H3;eauto.
      apply tau_star_to_star in H3 as [].
      eauto.
    }
    {
      destruct H1;Hsimpl.
      eapply npnsw_taustar_to_taustar in H1.
      apply tau_star_to_star in H1 as [].
      eapply star_step in H0;eauto.
    }
  Qed.
  Lemma swstar_globstar:
    forall ge pc pc',
      sw_star (@glob_step ge) pc pc'->
      exists l fp, star glob_step pc l fp pc'.
  Proof.
    induction 1;intros. Esimpl;auto. constructor.
    Hsimpl. Esimpl;eauto. econstructor 2;eauto.
  Qed.
  Lemma drf_pc_non_evt_star_evt_step_inv:
    forall ge pc fp pc' pc'' v,
      drf_pc_glob pc ->
      non_evt_star glob_step pc fp pc'->
      glob_step pc' (evt v) FP.emp pc'' -> 
      exists t,
        pc_valid_tid pc t /\
        exists fp1 pc1,non_evt_thrd_globstar ge ({-|pc,t}) fp1 pc1 /\ cur_tid pc1 = cur_tid pc' /\ 
                exists pc2, glob_step pc1 (evt v) FP.emp pc2 /\
                       exists fp2 pc3, non_evt_star glob_step pc2 fp2 pc3 /\
                                  mem_eq_pc ge pc'' pc3.
  
  Proof.
    intros.
    apply noevt_stepN_exists in H0 as [].
    apply type_glob_step_exists in H1 as [].
    destruct x0;subst;try(inversion H1;fail).
    apply drf_pc_glob_l1 in H as ?;destruct H2 as [Q1 Q2].
    specialize (drf_pc_glob_l2 _ _ H) as modwdge.
    inversion H as [Q3 _].
    assert(Q4:atom_bit pc' = O). inversion H1;auto.
    pose proof H0 as R.
    eapply noevt_stepN_evtstep_inv in H0;eauto.
    Hsimpl.
    destruct H2;Hsimpl.
    {
      apply atomblockstarN_star in H2 as [].
      destruct H3.
      apply swstar_star in H0 as [].
      eapply cons_star_star in H2;eauto.
      eapply drf_pc_l4 in H;eauto.
      contradiction.

      eapply predicted_abort1_star_abort in H3.
      Hsimpl.
      eapply cons_star_star in H3;eauto.
      unfold drf_pc_glob,drf_pc in H;Hsimpl.
      eapply swstar_globstar in H0;Hsimpl.
      eapply cons_star_star in H3;eauto.
      eapply cons_star_star in H3;eauto.
      eapply H9 in H3;eauto. contradiction.
    }
    {
      unfold non_evt_thrd_globstar.
      pose proof H0 as R1.
      apply swstar_l1 in H0.
      rewrite H0 in *.
      apply atomblockstarN_invpc_preservation in H2 as ?;auto.
      apply npnsw_taustar_thdpinv in H3 as ?;auto.
      eapply GE_mod_wd_tp_inv in H4 as?;eauto.
      
      Esimpl;eauto.
      {
        destruct x1.
        inversion H2;subst. eapply cur_valid_id_case1 in H3;eauto.
        eapply atomblockstarN_cur_valid_tid in H2;eauto.
        Lia.lia.
      }
      apply npnsw_or_sw_star_non_evt_star in H6.
      instantiate(1:=FP.union x8 (FP.union FP.emp FP.emp)).
      eapply non_evt_star_cons;eauto.
      econstructor;[|constructor]; right.

      apply noevt_stepN_sound in R.
      apply non_evt_star_star in R as [? R].
      eapply GE_mod_wd_star_tp_inv2 in  R;eauto.
      apply type_glob_step_elim in H1.
      eapply GE_mod_wd_tp_inv in R;eauto.
      assert(cur_valid_id ge pc'').
      revert H1 R. clear;intros.
      inversion H1;subst. split;[eapply gettop_valid_tid|intro];solv_thread.
      assert(atom_bit pc'' = O).
      inversion H1;auto.
      destruct x9,pc''. inversion H7 as (?&?&?&?);simpl in *;subst.
      destruct H12. econstructor;eauto.
    }
  Qed.
  Lemma non_evt_thrd_globstar_np_nonevt_star:
    forall ge pc fp pc',
      (forall ix,mod_wd (GlobEnv.modules ge ix))->
      non_evt_thrd_globstar ge pc fp pc'->
      pc_valid_tid pc' (cur_tid pc')->
      ThreadPool.inv pc.(thread_pool)->
      GlobEnv.wd ge->
      non_evt_star np_step pc fp pc'.
  Proof.
    destruct 2;intros;Hsimpl.
    destruct x.
    {
      inversion H0;subst;auto.
      apply glob_npnsw_star_to_np_taustar in H4.
      rewrite FP.emp_union_fp.
      revert H4;clear;intros.
      induction H4.
      constructor.
      econstructor;eauto.
    }
    {
      apply atomblockstarN_np in H0 as ?;auto;[|Lia.lia].
      Hsimpl.
      apply glob_npnsw_star_to_np_taustar in H4 as ?.
      apply tau_star_non_evt_star in H8.
      rewrite <-H5.
      destruct H7 as [[]|].
      Focus 2.
      eapply non_evt_star_cons;eauto.
      apply type_step_elim in H7;eauto.
      rewrite <- FP.emp_union_fp with(fp:=x3).
      econstructor 2;eauto.

      assert(np_step x4 sw FP.emp x2).
      assert(pc_valid_tid x2 (cur_tid x2)).
      assert(invpc ge x2). eapply atomblockstarN_invpc_preservation;eauto.
      revert H4 H9 H1 H3;clear;intros.
      induction H4. auto.
      apply npnsw_step_thdpinv in H as ?;auto.
      eapply npnswstep_cur_valid_tid;eauto.

      inversion H7;subst;destruct x2,H9;simpl in *;subst; econstructor;eauto.

      eapply non_evt_star_cons. eauto.
      rewrite <- FP.emp_union_fp with(fp:=x3).
      econstructor;eauto.
    }
  Qed.    
  

  Lemma final_state_step:
    forall ge x pc l fp pc',
      invpc ge pc' ->
      @type_glob_step ge x pc l fp pc'->
      final_state pc'->
      x = glob_halt.
  Proof.
    inversion 3;subst.
    assert( x= glob_halt \/ x <> glob_halt). destruct x eqn:?;auto;right;intro R;inversion R.
    destruct H2;subst;auto.
    assert(~ThreadPool.halted pc'.(thread_pool) pc'.(cur_tid)).
    clear H3.
    destruct x;subst;inversion H0;subst;intro;solv_thread;solv_thread.
    contradict H_not_halted.
    econstructor;eauto. unfold CallStack.is_emp. auto.

    contradict H4;apply H3.
    destruct x;subst;try contradiction;inversion H0;subst;auto;
    eapply gettop_valid_tid;auto;solv_thread;solv_thread.
  Qed.

  Lemma final_state_npnsw_or_sw_star:
    forall ge pc fp pc',
      invpc ge pc->GlobEnv.wd ge->
      npnsw_or_sw_star ge pc fp pc'->
      final_state pc'->
      pc = pc' /\ fp = FP.emp.
  Proof.
    intros ge pc fp pc' H wdge [] ?.
    induction H0;intros;auto.
    destruct H0.
    {
      apply npnsw_step_thdpinv in H0 as ?;auto.
      apply npnswstep_l1 in H0 as (?&?&?).
      Hsimpl;subst.
      eapply final_state_step in H1;eauto.
      destruct H4 as [|[]];subst;inversion H1.
    }
    {
      apply type_glob_step_elim in H0 as ?.
      eapply GE_mod_wd_tp_inv in H3;eauto.
      Hsimpl.
      subst.
      eapply final_state_step in H1;eauto.
      inversion H1.
    }
  Qed.

  Lemma final_state_atom:
    forall ge pc l fp pc',
      GlobEnv.wd ge ->@invpc ge pc-> atom_bit pc = O->
      star glob_step pc l fp pc'->
      @final_state ge pc'->
      atom_bit pc' = O.
  Proof.
    intros.
    apply star_stepN in H2 as [].
    destruct x.
    inversion H2;subst;auto.

    apply stepN_SN_split_weak in H2.
    Hsimpl.
    apply stepN_star in H2.
    eapply GE_mod_wd_star_tp_inv2 in H2;eauto.
    eapply GE_mod_wd_tp_inv in H2;eauto.
    apply type_glob_step_exists in H4 as [].
    eapply final_state_step in H3;eauto.
    subst. inversion H4;auto.
  Qed.

  Lemma non_evt_star_done_inv:
    forall ge pc,
      @drf_pc_glob ge pc->
      forall fp pc',
        non_evt_star glob_step pc fp pc'->
        final_state pc'->
        final_state pc \/
        (exists pc1,
            sw_star glob_step pc pc1 /\
            exists i l fp1 pc2,
              atomblockstarN ge i l pc1 fp1 pc2 /\ mem_eq_pc ge pc' ({-|pc2,cur_tid pc'})).
  Proof.
    intros.
    apply noevt_stepN_exists in H0 as [].
    destruct x.
    {
      apply noevt_stepN_0 in H0 as [].
      apply swstar_npnsw_or_sw_stepN in H2;auto;[|inversion H];auto.
      apply npnsw_or_sw_stepN_sound in H2.
      apply drf_pc_glob_l1 in H as [].
      eapply final_state_npnsw_or_sw_star in H2;eauto.
      destruct H2;subst;auto.
    }
    {
      apply drf_pc_glob_l1 in H as ?;destruct H2 as [invpc1 wdge].
      specialize (drf_pc_glob_l2 _ _ H) as modwdge.
      inversion H as (?&_).
      assert(atom_bit pc' = O).
      apply noevt_stepN_sound in H0.
      apply non_evt_star_star in H0 as [].
      eapply final_state_atom ;eauto.
      apply noevt_stepN_Si_to_atomblockstarN in H0;auto;[|Lia.lia].
      Hsimpl.
      destruct H4 as [|[|[|]]].
      {
        Hsimpl.
        apply atomblockstarN_star in H4 as [].
        apply swstar_globstar in H0;Hsimpl.
        eapply cons_star_star in H4;eauto.
        unfold drf_pc_glob,drf_pc in H;Hsimpl.
        apply predicted_abort1_star_abort in H5.
        Hsimpl.
        eapply cons_star_star in H5;eauto.
        eapply cons_star_star in H5;eauto.
        apply H10 in H5. contradiction.
      }
      {
        apply swstar_star in H0 as [].
        eapply drf_pc_l4 in H;eauto.
        contradiction.
      }
      {
        apply swstar_star in H0 as [].
        Hsimpl.
        apply atomblockstarN_star in H4 as [].
        eapply cons_star_star in H4;eauto.
        eapply drf_pc_l4 in H5;eauto.
        contradiction.
      }
      {
        Hsimpl.
        right.
        Esimpl;eauto.

        apply final_state_npnsw_or_sw_star in H5 as [];auto. congruence.
        eapply atomblockstarN_invpc_preservation in H4;eauto.
        apply swstar_l1 in H0;rewrite H0;auto.

        inversion H1;subst.
        inversion H6 as (?&?&?&?).
        econstructor;eauto.
        intros.
        rewrite H7 in *;eauto.
      }
    }
  Qed.
  
  Lemma Etr_p_np_done:
    forall ge pc,
      drf_pc_glob pc ->
      Etr (@glob_step ge) abort final_state pc Behav_done->
      Etr np_step np_abort final_state pc Behav_done \/
      exists t,Etr np_step np_abort final_state ({-|pc,t}) Behav_done /\ pc_valid_tid pc t .
  Proof.
    intros.
    inversion H0;clear H0;subst.
    apply non_evt_star_done_inv in H1;auto.
    destruct H1.
    {
      left. econstructor. constructor. auto.
    }
    {
      Hsimpl.
      destruct x0.
      inversion H1;subst.
      apply swstar_l1 in H0 as ?.
      rewrite H5 in H3. simpl in H3.
      left. econstructor. constructor.
      inversion H3;subst. inversion H2;subst.
      econstructor;eauto.
      intros;eauto. rewrite H6 in *;eauto.

      apply drf_pc_glob_l1 in H as ?.
      destruct H4.
      specialize (drf_pc_glob_l2 _ _ H) as ?.
      pose proof H0 as R1.
      apply swstar_l1 in H0. rewrite H0 in *.
      apply atomblockstarN_np in H1;auto;[|Lia.lia].

      Hsimpl.
      destruct H7.
      {
        destruct H7.
        apply type_step_exists in H7 as [].
        destruct x6;try(inversion H7;fail).
        apply extat_step_equiv in H7.
        Hsimpl. simpl in *.
        assert(final_state ({-|x3,x5})).
        inversion H2;subst.
        inversion H3.
        rewrite H9 in *. econstructor;eauto.
        eapply final_state_step in H8;eauto.
        inversion H8.
        eapply non_evt_star_thdp_inv in H1;eauto.
        apply type_glob_step_elim in H7.
        eapply GE_mod_wd_tp_inv in H7;eauto.

        apply thrdhalt_step_equiv in H7.
        Hsimpl. simpl in *.
        assert(final_state ({-|x3,x5})).
        inversion H2;subst.
        inversion H3.
        rewrite H9 in *. econstructor;eauto.
        eapply final_state_step in H8;eauto.
        inversion H8.
        eapply non_evt_star_thdp_inv in H1;eauto.
        apply type_glob_step_elim in H7.
        eapply GE_mod_wd_tp_inv in H7;eauto.
      }
      {
        assert(final_state x3).
        inversion H7;subst.
        econstructor;eauto.

        right.
        inversion H1;subst.
        exists (cur_tid x).
        apply type_step_elim in H7 as R.
        assert(non_evt_star np_step ({-|pc,cur_tid x}) (FP.union FP.emp FP.emp) x3). econstructor;eauto. constructor.
        eapply non_evt_star_cons in H9;eauto.
        split. econstructor;eauto.
        inversion H7;subst.
        split. eapply gettop_valid_tid;eauto. intro;solv_thread.

        exists (cur_tid x).
        apply type_step_elim in H7 as R.
        assert(non_evt_star np_step x4 (FP.union FP.emp FP.emp) x3). econstructor;eauto. constructor.
        eapply non_evt_star_cons in H11;try apply H1;eauto.
        split. econstructor;eauto.
        destruct H9;inversion H9;subst;split;try (eapply gettop_valid_tid;eauto);try intro ;solv_thread.
      }
    }
  Qed.
    
  Lemma np_p_abort_equiv:
    forall NL L p gm ge pc0 l fp pc,
      @init_config NL L p gm ge pc0 pc0.(cur_tid) /\ star glob_step pc0 l fp pc ->
      @abort ge pc->
      np_abort pc.
  Proof.
    unfold abort.
    unfold np_abort.
    intros.
    destruct H0.
    split.
    Focus 2.
    intros. intro.
    apply type_step_exists in H2 as [].
    destruct x,gl ;try(inversion H2;fail).
    apply core_step_equiv in H2;apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    apply call_step_equiv in H2;apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    apply ret_step_equiv in H2;apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    apply entat_step_equiv in H2;apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    assert(fp0=FP.emp). inversion H2;auto. subst. 
    apply extat_step_equiv in H2 as [];apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    assert(fp0=FP.emp). inversion H2;auto. subst.
    apply thrdhalt_step_equiv in H2 as [].
    apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    assert(fp0=FP.emp). inversion H2;subst;auto. subst.
    apply allhalt_step_equiv in H2 as [];apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    assert(fp0=FP.emp). inversion H2;auto. subst.
    apply efprint_step_equiv in H2 as [];apply type_glob_step_elim in H2;apply H1 in H2;inversion H2.
    intro.
    inversion H2;subst.
    destruct H.
    eapply pc_glob_l3 in H as [];eauto.
  Qed.

  Lemma npnsw_abort_preserve:
    forall ge pc l fp pc',
      @drf_pc_glob ge pc ->
      forall t,
        t <> cur_tid pc->
        glob_npnsw_step ({-|pc,t}) l fp pc'->
        abort ({-|pc',cur_tid pc})->
        abort pc.
  Proof.
    intros.
    apply npnswstep_l1 in H1;Hsimpl.
    inversion H2;subst.
    simpl in *.
    split;auto. intro.
    destruct H3 as [|[]];subst;inversion H1;subst;contradict H4;econstructor;solv_thread;solv_thread;auto.

    intros.
    apply type_glob_step_exists in H6 as [].

    assert(gl = sw \/ gl <> sw).
    destruct gl;auto;right;intro R;inversion R.
    destruct H7;auto.
    assert(FP.conflict fp fp0 \/ ~FP.conflict fp fp0).
    apply classic.
    destruct H8.
    inversion H as (?&_).
    apply FP.emp_never_conflict in H8 as R;destruct R.
    destruct x;subst;try(inversion H1;subst;contradiction).
    destruct x0;subst;try(inversion H6;subst;contradiction).
    assert(l=tau). inversion H1;auto. subst.
    assert(gl=tau). inversion H6;auto. subst.
    assert(race glob_predict pc).
    econstructor 1 with(b1:=O)(b2:=O);eauto.
    econstructor;eauto.
    econstructor;eauto. rewrite pc_cur_tid;eauto.
    left;intro R;inversion R.
    apply predict_race_to_star in H12.
    apply predict_star_race_to_alter in H12.
    eapply drf_pc_l4 in H12;eauto.
    contradiction.
    constructor.
    apply FP.smile_conflict_compat in H8.

    enough(exists pc'',type_glob_step x0 ({-|pc',cur_tid pc}) gl fp0 pc'').
    destruct H9.
    apply type_glob_step_elim in H9.
    eauto.
    specialize (drf_pc_glob_l2 _ _ H) as ?.
    inversion H as (?&_).
    apply drf_pc_glob_l1 in H as [].
    rewrite <- pc_cur_tid with(pc:=pc) in H6.
    eapply  predict_step_ex with(t2:=cur_tid pc) in H1;eauto.
  Qed.    



 
  Lemma drf_pc_glob_cons_npnsw:
    forall ge pc l fp pc' t,
      @drf_pc_glob ge pc ->
      glob_npnsw_step ({-|pc,t}) l fp pc'->
      drf_pc_glob ({-|pc,t}) /\ drf_pc_glob pc'.
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as ?.
    Hsimpl.
    apply npnswstep_cur_valid_tid in H0 as ?;auto.
    assert(glob_step pc sw FP.emp ({-|pc,t})).
    inversion H.
    destruct pc,H3;simpl in *;subst;econstructor;eauto.
    assert(drf_pc_glob ({-|pc,t})).
    inversion H.
    eapply drf_pc_glob_cons;eauto.
    eapply star_step;eauto. constructor.
    assert(atom_bit pc' = O). apply npnswstep_l2 in H0. inversion H;auto. simpl in H0. try congruence.
    apply npnswstep_l1 in H0.
    Hsimpl.
    apply type_glob_step_elim in H0.
    split;auto.
    eapply drf_pc_glob_cons;eauto.
    eapply star_step;eauto. constructor.
  Qed.
  Lemma drf_pc_glob_cons_validid:
    forall ge pc t,
      @drf_pc_glob ge pc->
      pc_valid_tid pc t->
      drf_pc_glob ({-|pc,t}).
  Proof.
    intros. inversion H.
    assert(glob_step pc sw FP.emp ({-|pc,t})).
    destruct pc,H0;simpl in * ;subst;econstructor;eauto.
    eapply drf_pc_glob_cons;eauto. eapply star_step;[eauto|constructor].
  Qed.


  Lemma npnsw_step_taustar_ex:
    forall ge pc l fp pc',
      @drf_pc_glob ge pc ->
      forall t,
        t<>cur_tid pc->
        glob_npnsw_step ({-|pc,t}) l fp pc'->
        forall fp' pc'',
          tau_star glob_step ({-|pc',cur_tid pc}) fp' pc''->
          exists pc1 pc2,
            tau_star glob_step pc fp' pc1 /\
            glob_npnsw_step (changepc ge pc1 t O) l fp pc2 /\
            mem_eq_pc ge pc'' (changepc ge pc2 (cur_tid pc'') (atom_bit pc'')).
  Proof.
    intros.
    apply tau_star_tau_N_equiv in H2 as [].
    revert pc l fp pc' t fp' pc'' H H0 H1 H2.
    induction x using (well_founded_induction lt_wf);intros.
    destruct x.
    inversion H3;clear H3;subst.
    Esimpl;eauto. constructor. eapply npnswstep_changebitO in H2. simpl in H2. eauto.
    unfold changepc;simpl. apply mem_eq_pc_refl.

    apply drf_pc_glob_l1 in H0 as ?;destruct H4 as  [inv1 wdge].
    specialize (drf_pc_glob_l2 _ _ H0) as modwdge.

    assert(atom_bit pc' = O). inversion H0. apply npnsw_step_O_preservation in H2;auto.
    inversion H3;clear H3;subst.
    destruct (atom_bit s') eqn:?.
    {
      apply type_glob_step_exists in H6 as [].
      apply npnswstep_l1 in H2;Hsimpl.
      eapply globstep_reorder_rule_alter in H3 as ?;eauto.
      destruct H6 as [|[]];Hsimpl.
      {
        rewrite pc_cur_tid in H6.
        destruct H0. Hsimpl. destruct H8;Hsimpl.
        contradict H6.
        eapply H12;eauto. 
      }
      {
        apply FP.emp_never_conflict in H8 as L;destruct L.
        destruct H5 as [|[]];subst;try(inversion H2;subst;contradiction).
        assert(l=tau). inversion H2;auto. subst.
        assert(race glob_predict pc).
        econstructor 1 with(b1:=O)(b2:=O);eauto.
        econstructor;eauto. inversion H0;auto.
        econstructor;eauto. inversion H0;auto.
        left;intro L;inversion L.
        apply predict_race_to_star in H5. apply predict_star_race_to_alter in H5.
        eapply drf_pc_l4 in H5;eauto. contradiction.
        constructor.
      }
      {
        eapply mem_eq_glob_tauN in H10 ;eauto.
        Hsimpl.
        rewrite pc_cur_tid in H8.
        assert(atom_bit x2 = O).
        inversion H0 as (?&_).
        assert(atom_bit ({-|pc',cur_tid pc}) = atom_bit s'). simpl;congruence.
        eapply type_glob_step_atomOpreserve in H8;try apply H3;eauto.
        congruence.
        apply npnswstep_l3 in H9;auto.
        assert(T1:drf_pc_glob x2).
        eapply drf_pc_glob_cons;eauto. apply type_glob_step_elim in H8.
        eapply star_step;eauto. constructor.

        assert(cur_tid pc = cur_tid x2). inversion H8;auto.
        assert(cur_tid s' = cur_tid pc). inversion H3;auto.
        rewrite H14,H13 in H10. rewrite H13 in *.
        eapply H in H9 as ?;eauto.
        Hsimpl.
        Esimpl;eauto. econstructor;eauto. eapply type_glob_step_elim;eauto.
        eapply mem_eq_pc_trans;eauto.
        inversion H11 as (?&?&?&?);congruence.
      }
      apply npnswstep_l3 in H2;auto.
      apply npnswstep_l2 in H2;auto.
      congruence.
      intro R. subst.
      destruct H5 as [|[]];subst;inversion H2.
      intro R;inversion R.
    }
    {
      apply type_glob_step_exists in H6 as [].
      destruct x0;try(inversion H3;subst;simpl in *;subst;try inversion Heqb;try inversion H4;fail).
      inversion H3;subst;simpl in *;subst. rewrite Heqb in H4;inversion H4.
      apply npnswstep_l2 in H2 as ?. simpl in H5.
      apply npnswstep_taustep in H2 as?;subst.
      apply npnswstep_l1 in H2;Hsimpl.
      assert(fp0=FP.emp). inversion H3;auto. subst.
      eapply atomblock_open_reorderstep1 in H2 as ?;eauto;[|intro R;inversion R].
      Hsimpl.
      assert(mem_eq_pc ge s' (changepc ge x2 (cur_tid s') I)).
      split;auto. split;auto. split;auto. simpl. rewrite H11;apply GMem.eq'_refl.
      eapply mem_eq_glob_tauN in H12 as ?;eauto.
      Hsimpl.

      destruct x.
      {
        inversion H13;subst.
        Esimpl;eauto. econstructor 2. eapply type_glob_step_elim in H8. rewrite pc_cur_tid in H8;eauto.
        constructor.
        eapply npnswstep_l3 in H9;eauto.
        eapply mem_eq_pc_change in H14;erewrite pc_cur_tid in H14. simpl in H14.
        unfold changepc. inversion H14 as (?&?&?&?). simpl in *;subst;auto. rewrite H16;auto.
      }
      {
        apply tauN_I_split in H13;auto.
        destruct H13.
        {
          apply tauN_taustar in H13.
          eapply atomblock_open_reorder_corestar in H13 as ?;try apply H9;eauto.

          Hsimpl.
          assert(mem_eq_pc ge x3 (changepc ge x5 (cur_tid x3)(atom_bit x3))).
          split;auto. Esimpl;auto. simpl.
          apply GMem.eq'_sym;auto.

          apply npnswstep_l3 in H16;auto.
          apply core_tau_star_tau_star in H15.
          assert((changepc ge x1 (cur_tid s') I) = x1).
          inversion H8;subst. unfold changepc;simpl.
          inversion H3;subst. simpl. auto.
          rewrite H20 in H15. apply type_glob_step_elim in H8.
          rewrite pc_cur_tid in H8.
          eapply tau_star_cons in H15;eauto.
          Esimpl;eauto.
          eapply mem_eq_pc_trans;eauto.

          inversion H14 as (?&?&?&?). congruence.

          apply npnswstep_l3 in H9;auto. apply npnswstep_l2 in H9. auto.
          intro R;inversion R.
          inversion H3;auto.

          apply NNPP. intro. apply smile_conflict in H15.
          apply FP.conflict_sym in H15.
          eapply taustar_fpconflict_split in H13;eauto.
          Hsimpl.
          
          eapply atomblock_open_reorder_corestar in H13 as ?;try apply H9;eauto.
          Hsimpl.
          apply corestar_tid_bit_preserve in H13 as T2.
          destruct T2;simpl in *.
          assert(mem_eq_pc ge x6 (changepc ge x9 (cur_tid s')I)).
          split;auto. Esimpl;auto. simpl. apply GMem.eq'_sym;auto.
          eapply mem_eq_corestep in H27 ;eauto;Hsimpl.

          apply FP.emp_never_conflict in H18 as ?. destruct H29.
          destruct x0;try(inversion H22;subst;contradiction).

          assert(type_glob_step core (changepc ge x8 t  I) tau fp (changepc ge x9 t I)).
          inversion H22;subst;econstructor;eauto.
          rewrite <-pc_cur_tid with(pc:=(changepc ge x8 t I)) in H31.
          assert(changepc ge x9 (cur_tid s') I = ({-|changepc ge x9 t I,cur_tid s'})).
          auto.
          rewrite H32 in H27.
          eapply corestep_conflict in H18 as ?;eauto.
          destruct H33 as [|].
          {
            simpl in H33.
            assert(x8 =  ({thread_pool x8, cur_tid s', gm x8, I})).
            apply corestar_tid_bit_preserve in H21 as [].
            simpl in *. destruct x8;simpl in *;subst;congruence.
            rewrite <- H34 in H33;clear H34.
            assert(cur_tid s' =cur_tid pc). inversion H3;auto.
            assert((changepc ge x1 (cur_tid s') I) = x1).
            rewrite H34. inversion H8;subst. auto.
            rewrite H35 in H21. rewrite pc_cur_tid in H8.
            apply type_glob_step_elim in H8 as ?.
            apply corestar_globstar in H21.
            apply tau_star_to_star in H21 as [].
            eapply star_step in H36;eauto.
            unfold drf_pc_glob,drf_pc in H0;Hsimpl.
            eapply cons_star_star in H36;eauto.
            eapply H41 in H36;eauto.
          }
          Hsimpl.

          apply corestar_tid_bit_preserve in H21 as ?.
          destruct H35.
          simpl in H35,H36,H33.
          assert(x8 = ({thread_pool x8,cur_tid s',gm x8,I})).
          destruct x8;simpl in *;subst;auto.
          rewrite <- H37 in H33.
          assert(changepc ge x1 (cur_tid s') I = x1).
          assert(cur_tid s' = cur_tid pc). inversion H3;auto.
          rewrite H38 in *.
          destruct x1;unfold changepc;simpl;f_equal.
          inversion H8;auto. inversion H8;auto.
          rewrite H38 in *.
          apply tau_plus_1 in H33.
          apply tau_plus2star in H33.
          eapply tau_star_star in H33;eauto.
          assert(FP.conflict fp (FP.union x4 x0)).
          eapply conflict_union_ano in H34;eauto.
          rewrite FP.union_comm_eq;eauto.
          assert(race glob_predict pc).
          econstructor 1;try apply H39. eauto.
          econstructor 1;eauto. inversion H0;auto.
          econstructor 2;eauto. left;intro T;inversion T.
          apply predict_race_to_star in H40;apply predict_star_race_to_alter in H40.
          eapply drf_pc_l4;eauto. constructor.
          simpl. inversion H3;auto.
          simpl. apply type_glob_step_elim in H8. apply GE_mod_wd_tp_inv in H8;auto.
          apply core_tau_star_tau_star in H21.
          apply tau_star_to_star in H21 as [].
          eapply GE_mod_wd_star_tp_inv2 in H21;eauto.
          apply npnswstep_l3 in H9;auto. apply npnswstep_l2 in H9;auto.
          intro R;inversion R.
          inversion H3;subst. intro. simpl in *;subst. contradiction.
          apply type_glob_step_elim in H8. apply GE_mod_wd_tp_inv in H8;auto.
          apply type_glob_step_elim in H8. apply GE_mod_wd_tp_inv in H8;auto.
        }
        {
          Hsimpl.
          assert(FP.smile fp x6 \/ ~ FP.smile fp x6).
          apply classic.
          destruct H19.
          {
            
            eapply atomblock_open_reorder_core_tauN in H13 as ?;eauto.
            Hsimpl.
            assert(mem_eq_pc ge x4 (changepc ge x11 (cur_tid pc) I)).
            split;auto. split;auto. inversion H15;auto.
            split;auto. simpl. apply tauN_taustar in H13. apply corestar_tid_bit_preserve in H13 as []. simpl in *. inversion H3;subst. simpl in *;subst. congruence.
            simpl. apply GMem.eq'_sym;auto.
            eapply mem_eq_globstep in H24 as ?;eauto.
            Hsimpl.
            
            eapply atomblock_open_reorderstep2 in H25 as ?;eauto.
            Hsimpl.
            assert(mem_eq_pc ge x12 ({-|x14, (cur_tid pc)})).
            split;auto. split;auto. simpl. apply npnswstep_l3 in H28;auto. apply npnswstep_l2 in H28. rewrite <- H28;simpl. inversion H25;auto.
            split;auto. inversion H25;auto. rewrite <-H30. simpl. apply GMem.eq'_refl.
            apply mem_eq_pc_trans with(p1:=x7) in H31 as ?;auto.
            eapply mem_eq_glob_tauN in H32 as ?;eauto.
            Hsimpl.

            apply npnswstep_l3 in H28 as ?;auto.
            assert(cur_tid x13 = cur_tid pc). inversion H27;auto.
            assert(atom_bit x13 = O). inversion H27;auto.
            assert(changepc ge x13 t O = ({-|x13,t})).
            unfold changepc. f_equal. auto.
            rewrite H38 in *.
            rewrite <- H36 in H33.
            eapply H in H33 as ?;eauto.
            Hsimpl.

            Esimpl;eauto.
            assert(changepc ge x1 (cur_tid s') I = x1).
            unfold changepc. inversion H3;subst;simpl in *;subst.
            inversion H8;subst;simpl in *;subst. auto.
            rewrite H42 in *.
            apply tauN_taustar in H20.
            apply corestar_tid_bit_preserve in H20 as R;destruct R.
            assert(changepc ge x10 (cur_tid pc) I = x10).
            destruct x1;simpl in *;subst.
            inversion H42;subst.
            destruct x10;simpl in *;subst;auto. unfold changepc. simpl. f_equal.
            inversion H3;auto.
            rewrite H45 in *.
            apply type_glob_step_elim in H8.
            apply core_tau_star_tau_star in H20 as H20.
            eapply tau_star_cons in H8;eauto.
            rewrite pc_cur_tid in H8.
            eapply type_glob_step_elim in H27.
            eapply tau_star_cons in H39;try apply H27;eauto.
            eapply tau_star_star in H39;eauto.
            repeat rewrite FP.emp_union_fp in H39.
            rewrite FP.emp_union_fp. congruence.
            eapply mem_eq_pc_trans;eauto.
            eapply mem_eq_pc_trans;eauto.
            eapply mem_eq_pc_trans with(p1:=pc'') in H34;eauto.
            inversion H34 as (?&?&?&?). congruence.
            Lia.lia.

            assert(changepc ge x1 (cur_tid s') I = x1).
            unfold changepc. inversion H3;subst;simpl in *;subst.
            inversion H8;subst;simpl in *;subst. auto.
            rewrite H39 in *.
            apply tauN_taustar in H20.
            apply corestar_tid_bit_preserve in H20 as R;destruct R.
            assert(changepc ge x10 (cur_tid pc) I = x10).
            destruct x1;simpl in *;subst.
            inversion H39;subst.
            destruct x10;simpl in *;subst;auto. unfold changepc. simpl. f_equal.
            inversion H3;auto.
            rewrite H42 in *.
            apply type_glob_step_elim in H8.
            apply core_tau_star_tau_star in H20 as H20.
            eapply tau_star_cons in H8;eauto.
            rewrite pc_cur_tid in H8.
            eapply type_glob_step_elim in H27.
            apply tau_star_to_star in H8 as [].
            eapply star_cons_step in H27 as [];eauto.
            eapply drf_pc_glob_cons;eauto.
            rewrite H36;auto.
            apply npnswstep_l3 in H21;auto. apply npnswstep_l2 in H21;auto.
            intro R;inversion R.
            apply npnswstep_l3 in H9;auto. apply npnswstep_l2 in H9;auto.
            intro R;inversion R.
            inversion H3;subst;auto.
            apply type_glob_step_elim in H8;eapply GE_mod_wd_tp_inv in H8;eauto.
          }
          {
            apply smile_conflict in H19.
            clear H15 H16 H17 H18 x3 H14 x8 x9.
            apply tauN_taustar in H13.
            apply FP.emp_never_conflict in H19 as ?.
            destruct H14 as [? _].
            destruct x0;try(inversion H9;subst;contradiction).
            apply FP.conflict_sym in H19.
            eapply taustar_fpconflict_split in H19;eauto.
            clear x4 H13.
            Hsimpl.

            eapply atomblock_open_reorder_corestar in H13 as ?;eauto.
            Hsimpl.
            assert(changepc ge x1 (cur_tid s') I = x1).
            inversion H8;subst. unfold changepc. f_equal.
            inversion H3;auto.
            rewrite H24 in *.
            assert(mem_eq_pc ge x4 (changepc ge x10 (cur_tid s') I)).
            split;auto. apply corestar_tid_bit_preserve in H13 as[];subst. split;auto. split;auto. apply GMem.eq'_sym;auto.

            eapply mem_eq_globstep in H25 as ?;eauto.
            Hsimpl.

            assert(type_glob_step core (changepc ge x9 t I)tau fp (changepc ge x10 t I)).
            inversion H21;subst;econstructor;eauto.
            assert(changepc ge x10 (cur_tid s') I = ({-|changepc ge x10 t I,cur_tid s'})). auto.
            rewrite H29 in H26;clear H29.
            rewrite <- pc_cur_tid with(pc:=(changepc ge x9 t I)) in H28.
            eapply corestep_conflict in H26 as ?;eauto;simpl;auto.

            destruct H29.
            {
              simpl in *.
              assert(cur_tid s' = cur_tid pc). inversion H3;auto.
              rewrite H30 in *.
              assert(cur_tid x1 = cur_tid pc). destruct x1;simpl in H24. inversion H24;auto.
              apply corestar_tid_bit_preserve in H20 as ?. Hsimpl.
              rewrite <- H31,H32 in H29.
              assert(atom_bit x1 = I). inversion H24;auto.
              rewrite <- H34,H33 in H29. rewrite pc_cur_tid in H29.
              rewrite pc_cur_tid in H8.
              apply type_glob_step_elim in H8 as ?.
              apply corestar_globstar in H20 as ?. 
              eapply tau_star_to_star in H36 as [].
              eapply star_step in H35;eauto.
              unfold drf_pc_glob,drf_pc in H0;Hsimpl.
              contradict H29;eapply cons_star_star in H35;eauto.
            }
            Hsimpl.
            simpl in H29.
            assert(cur_tid s' = cur_tid pc). inversion H3;auto.
            apply corestar_tid_bit_preserve in H20 as ?.
            rewrite <-H24 in H32. simpl in H32.
            assert(({thread_pool x9, cur_tid s', gm x9, I}) = x9).
            destruct x9,H32;simpl in *;subst;auto. f_equal;try congruence.
            rewrite H33 in *.
            apply tau_plus_1 in H29.
            apply tau_plus2star in H29.
            eapply tau_star_star in H29;eauto.
            
            assert(race glob_predict pc).
            econstructor. eauto.
            econstructor. eauto. inversion H0;auto.
            econstructor 2. eauto. eapply H29.
            left. intro R;inversion R.
            rewrite FP.union_comm_eq. eapply conflict_union_ano;auto.
            apply predict_race_to_star in H34.
            apply predict_star_race_to_alter in H34.
            eapply drf_pc_l4 in H34;eauto.
            contradiction.
            constructor.
            inversion H3;auto.
            apply type_glob_step_elim in H8. apply GE_mod_wd_tp_inv in H8;auto.
            apply core_tau_star_star in H20 as [].
            apply GE_mod_wd_star_tp_inv2 in H20;auto.
            inversion H9;auto.
            intro R;inversion R.
            inversion H3;auto.
            apply type_glob_step_elim in H8. apply GE_mod_wd_tp_inv in H8;auto.
          }
        }
      }
    }
  Qed.
  Lemma tau_N_OI:
    forall i ge pc fp pc',
      tau_N (@glob_step ge) i pc fp pc'->
      atom_bit pc = O->
      atom_bit pc' = I->
      exists j fp1 pc1,tau_N glob_step j pc fp1 pc1 /\ j<i /\
                exists pc2,type_glob_step entat pc1 tau FP.emp pc2 /\
                      exists k fp2,tau_N (type_glob_step core)k pc2 fp2 pc'/\
                            FP.union fp1 fp2 = fp /\ j+k+1=i.
  Proof.
    induction i;intros.
    inversion H;subst.
    rewrite H0 in H1;inversion H1.
    assert(S i = i + 1). Lia.lia.
    rewrite H2 in H. clear H2.
    apply tau_N_split in H.
    Hsimpl.
    inversion H2;subst;clear H2.
    inversion H6;subst;clear H6.

    destruct (atom_bit x) eqn:?.
    apply type_glob_step_exists in H5 as [].
    destruct x1;try(inversion H2;subst;simpl in *;subst;inversion Heqb;inversion H1;fail).
    assert(fp0=FP.emp). inversion H2;auto. subst.
    Esimpl;eauto.  rewrite FP.emp_union_fp. constructor.
    Lia.lia.

    eapply IHi in H;eauto.
    Hsimpl.
    apply type_glob_step_exists in H5 as [].
    destruct x7;try(inversion H5;subst;simpl in *;subst;inversion Heqb;inversion H1;fail).

    pose proof @tau_N_O _ (type_glob_step core) pc'.
    eapply tau_N_S in H5;eauto.
    eapply tau_N_cons in H5;eauto.
    Esimpl;eauto.
    rewrite FP.fp_union_emp.
    rewrite <- H6,FP.fp_union_assoc.
    auto.
    rewrite <- H7.
    Lia.lia.
  Qed.
 
    
  Lemma npnsw_or_sw_stepN_validid:
    forall ge i l pc fp pc',
      invpc ge pc-> GlobEnv.wd ge->
      @npnsw_or_sw_stepN ge i l pc fp pc'->
      (pc = pc' \/ pc_valid_tid pc pc'.(cur_tid )).
  Proof.
    induction i;intros l pc fp pc' invpc1 wdge;intros.
    remember 0.
    induction H;subst. auto.
    inversion Heqn.
    assert(0=0). auto.
    assert(inv2:invpc ge pc'). apply type_glob_step_elim in H;eapply GE_mod_wd_tp_inv;eauto.
    Hsimpl.
    destruct IHnpnsw_or_sw_stepN.
    subst. inversion H;subst;right;split;auto.
    inversion H;subst. inversion H2;subst.
    simpl in *. right;split;auto.

    apply npnsw_or_sw_stepN_inv1 in H;[|Lia.lia].
    Hsimpl.
    assert(S i - 1 = i). Lia.lia.
    rewrite H4 in H1;clear H4.
    assert(inv3:invpc ge x0). apply npnsw_step_thdpinv in H0;auto. apply swstar_l1 in H;rewrite H;auto.
    apply IHi in H1;auto.
    destruct H1.
    {
      subst. apply swstar_l1 in H. rewrite H in *.
      apply npnsw_step_tid_preservation in H0 as ?.
      simpl in H1. rewrite H1 in *. clear x H H1.
      apply npnswstep_cur_valid_tid in H0;auto.
    }
    {
      subst.
      eapply npnswstep_pc_valid_tid_backwards_preservation in H0;eauto.
      apply swstar_l1 in H ;rewrite H in H0.
      auto.
    }
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


  Lemma npnswstep_halfatomblock_abort:
    forall ge pc l fp pc' t fp' pc'',
      drf_pc_glob pc->
      glob_npnsw_step pc l fp pc'->
      t <> cur_tid pc ->
      halfatomblockstep ge ({-|pc',t}) tau fp' pc''->
      abort pc''->
      exists pc1,halfatomblockstep ge({-|pc,t}) tau fp' pc1/\ abort pc1.
  Proof.
    unfold halfatomblockstep;intros.
    apply drf_pc_glob_l1 in H as L;destruct L as [R1 R2].
    specialize (drf_pc_glob_l2 _ _ H)as R3.
    Hsimpl.
    apply npnswstep_taustep in H0 as ?;subst.
    apply npnswstep_l2 in H0 as R4.
    apply npnswstep_l1 in H0 ;Hsimpl.
    assert(FP.smile fp fp'). 
    eapply drf_pc_glob_taustep_halfatomblock_fpsmile in H as ?;eauto.
    eapply type_glob_step_elim;eauto.

    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    eapply atomblock_open_reorderstep1 in H0 as ?;eauto;[|intro R;inversion R].
    Hsimpl.
    assert(mem_eq_pc ge x (changepc ge x2 t I)).
    split;auto. inversion H4;subst. Esimpl;eauto. simpl. rewrite H11. apply GMem.eq'_refl.
    eapply mem_eq_corestar in H12 as ?;eauto.
    Hsimpl.
    assert(atom_bit x2 = O).
    apply npnswstep_l3 in H9;auto. apply npnswstep_l2 in H9;auto.

    assert(ThreadPool.inv x1.(thread_pool)). eapply type_glob_step_elim in H8;eapply GE_mod_wd_tp_inv in H8;eauto.
    eapply atomblock_open_reorder_corestar in H13 as ?;eauto;[|intro R;inversion R].
    Hsimpl.

    assert(mem_eq_pc ge (changepc ge x5 t I) x3).
    split;auto. apply corestar_tid_bit_preserve in H13 as []. split;auto.

    assert(mem_eq_pc ge (changepc ge x5 t I ) pc''). eapply mem_eq_pc_trans;eauto. apply mem_eq_pc_sym;eauto.
    apply mem_eq_abort in H22;auto.
    assert(x1 = changepc ge x1 t I). inversion H8;auto. rewrite <- H23 in *.
    Esimpl. auto. eauto.  eauto.
    destruct H22.
    split.
    {
      simpl in H22.
      intro. contradict H22.
      assert(cur_tid x4 = t). apply corestar_tid_bit_preserve in H17 as [].
      rewrite H23 in H17;auto. rewrite H22 in H25.
      destruct H6 as [|[]];subst;inversion H18;subst;simpl in *;subst.
      eapply halted_preserve;eauto.
      revert H25 H_tp_push H1;clear;intros.
      inversion H25;subst. econstructor;solv_thread.
      rewrite <- H3. simpl. rewrite Maps.PMap.gso;auto.
      eapply halted_preserve with(thdp2:=thdp') in H25;eauto.
      eapply halted_preserve;eauto.
    }
    {
      intros.
      apply corestar_tid_bit_preserve in H17 as ?.
      rewrite H23 in H26;simpl in H26. destruct H26.
      apply type_glob_step_exists in H25 as [].
      destruct x6;try(inversion H25;subst;inversion H27;fail).
      {
        assert(FP.conflict fp0 fp \/ ~ FP.conflict fp0 fp).
        apply classic. destruct H28.
        {

          assert(gl = tau). inversion H25;auto. subst. eapply tau_plus_1 in H25.
          eapply tau_plus2star in H25.
          eapply tau_star_cons' in H25;eauto.
          apply FP.emp_never_conflict in H28 as ?.
          destruct H26.
          destruct H6 as [|[]];subst;try(inversion H0;subst;contradiction).
          assert(race glob_predict pc).
          econstructor. eauto.
          econstructor 2;eauto. econstructor;eauto.
          inversion H;auto.
          right;intro R;inversion R.
          rewrite FP.union_comm_eq.
          apply conflict_union. auto.
          apply predict_race_to_star in H6.
          apply predict_star_race_to_alter in H6.
          eapply drf_pc_l4 in H6;eauto. contradiction. constructor.
        }
        {
          apply FP.smile_conflict_compat in H28.
          remember (changepc ge x4 t O) as pce.
          assert(type_glob_step core ({-|pce,t}) gl fp0 (changepc ge pc'0 t O)).
          inversion H25;simpl in *;subst;simpl in *;subst.
          econstructor;eauto.
          assert(changepc ge x4 (cur_tid pc) O = ({-|pce,cur_tid pc})).
          rewrite Heqpce. auto.
          rewrite H30 in H18.
          assert(ThreadPool.inv pce.(thread_pool)).
          rewrite Heqpce;simpl.
          eapply core_tau_star_star in H17 as [].
          eapply GE_mod_wd_star_tp_inv2;eauto.
          apply fpsmile_sym in H28.
          assert(gl <> sw). assert(gl = tau). inversion H29;auto. subst;intro R;inversion R.
          
          specialize (predict_step_ex ge x0 core pce (cur_tid pc) t tau fp x5 gl fp0 (changepc ge pc'0 t O) R2 H31 R3 H18 H29 H28 H6 H32 H1) as ?.
          Hsimpl.

          assert(type_glob_step core (changepc ge x5 t I) gl fp0 (changepc ge x6 t I)).
          unfold changepc. inversion H33;subst. simpl. econstructor;eauto.
          apply type_glob_step_elim in H34.
          eauto.
        }
      }
      {
        assert(ThreadPool.inv x4.(thread_pool)).
        apply core_tau_star_star in H17 as []. eapply GE_mod_wd_star_tp_inv2;eauto.
        apply npnswstep_l3 in H18;auto.
        revert H24 H25 H18 H28 R2 R3 H1 H26 H27.
        clear;intros.
        eapply npnsw_step_diff_thread_sim in H18 as sim1;eauto.
        simpl in sim1.
        assert(thread_sim ge x4 (changepc ge x5 t I)).
        unfold thread_sim,changepc,getcurcs in *.  simpl in *. 
        Hsimpl;Esimpl;try congruence.

        apply npnsw_step_eff in H18 as eff1;auto.
        assert(fp0 = FP.emp). inversion H25;auto. subst.
        assert(FP.smile fp FP.emp). apply FP.smile_conflict_compat. intro.
        apply FP.emp_never_conflict in H0 as [];contradiction.
        simpl in *.
        eapply GEffect_fpsmile_disj_GPre_Rule in eff1;eauto.
        apply GPre_comm in eff1.
        eapply extatstep_Glocality in H25;eauto.
        Hsimpl.
        apply type_glob_step_elim in H2;eauto.
        }
    }
  Qed.
    
    

  (*
   Lemma npnsw_or_sw_stepN_taustar_abort:
     forall ge i l pc fp pc' fp' pc'' fp'' pc''',
       drf_pc_glob pc->
       npnsw_or_sw_stepN ge i l pc fp pc'->
       tau_star glob_npnsw_step pc' fp' pc'' ->
       halfatomblockstep ge pc'' tau fp'' pc'''->
       abort pc'''->
       exists fp1 pc1 pc2,
         sw_star glob_step pc ({-|pc,cur_tid pc'}) /\ 
         tau_star glob_npnsw_step ({-|pc,cur_tid pc'}) fp1 pc1/\
         halfatomblockstep ge pc1 tau fp'' pc2 /\
         abort pc2.
   Proof.
     induction i;intros.
     {
       apply npnsw_or_sw_stepN_0 in H0.
       Hsimpl;subst. apply swstar_l1 in H5 as ?.
       rewrite <- H0. Esimpl;eauto.
     }
     {
       apply npnsw_or_sw_stepN_inv1 in H0;[|Lia.lia].
       Hsimpl;subst. assert(S i-1=i). Lia.lia. rewrite H6 in *;clear H6.
       assert(drf_pc_glob x0).
       apply swstar_l1 in H0. rewrite H0 in H4.
       eapply drf_pc_glob_cons_npnsw;eauto.
       eapply IHi in H6 as ?;eauto.
       assert(R0:invpc ge pc').
       apply drf_pc_glob_l1 in H6 as [].
       apply npnsw_or_sw_stepN_sound in H5.
       apply npnsw_or_sw_star_non_evt_star in H5.
       apply non_evt_star_star in H5 as [].
       eapply GE_mod_wd_star_tp_inv2 in H5;eauto.
       assert(R1:cur_valid_id ge pc'').
       apply drf_pc_glob_l1 in H6 as [].
       unfold halfatomblockstep in H2;Hsimpl.
       apply tau_star_to_star in H1 as [].
       apply npnsw_star_glob_star in H1.
       eapply GE_mod_wd_star_tp_inv2 in H1;eauto.
       revert H9 H1 H8;clear;split. inversion H9;subst. eapply gettop_valid_tid;eauto. inversion H9;subst;intro;solv_thread.
       assert(pc_valid_tid pc (cur_tid pc'')).
       apply drf_pc_glob_l1 in H as [];auto.
       apply swstar_star in H0 as [].
       apply npnswstep_l1 in H4;Hsimpl.
       apply type_glob_step_elim in H4.
       apply npnsw_or_sw_stepN_sound in H5.
       apply npnsw_or_sw_star_non_evt_star in H5.
       apply non_evt_star_star in H5 as [].
       apply tau_star_to_star in H1 as [].
       apply npnsw_star_glob_star in H1.
       eapply cons_star_star in H1;eauto. eapply star_step in H1;eauto.
       eapply cons_star_star in H1;eauto.
       eapply pc_valid_tid_back_star;eauto.
       apply npnsw_taustar_tid_preservation in H1 as ?.
       rewrite<- H9 in H8.
       clear fp' pc'' pc''' x2 x3 H1 H2 H3 H5 IHi R0 R1 H9.
       rename H8 into R0.
       Hsimpl.

       assert(drf_pc_glob x).
       apply swstar_l3 in H0 as []. congruence.
       eapply drf_pc_glob_cons in H;eauto. eapply star_step;[eauto|constructor]. inversion H0;auto.

       assert(cur_tid x0 = cur_tid pc' \/ cur_tid x0 <> cur_tid pc').
       apply classic.
       destruct H8.
       rewrite <- H8,pc_cur_tid in *.
       eapply tau_star_cons in H2;eauto.
       apply npnsw_step_tid_preservation in H4.
       rewrite <- H4.
       apply swstar_l1 in H0 as ?. rewrite <- H9.
       Esimpl;eauto.

       apply drf_pc_glob_l1 in H7 as L;destruct L as [R1 R2].
       specialize (drf_pc_glob_l2 _ _ H7) as R3.

       apply npnsw_step_tid_preservation in H4 as R4.
       rewrite <- R4 in H8.
       eapply glob_npnsw_step_star_ex in H2 as ?;eauto.
       destruct H9 as [|[]];Hsimpl.
       {
         
       }
       {
         inversion H7 as [R5 _].
         inversion H6 as [R6 _].
         assert(race glob_predict_star_alter x).
         econstructor. eauto.
         econstructor. rewrite pc_cur_tid. econstructor 2;eauto. constructor. auto.
         auto.
         econstructor. eauto. auto. apply glob_npnsw_star_bitO_preserve in H10;auto.
         left;intro R;inversion R.
         rewrite FP.fp_union_emp;auto.
         eapply drf_pc_l4 in H12;eauto.
         contradiction. constructor.
       }
       {
         
         unfold halfatomblockstep in H3.
         Hsimpl.
         eapply mem_eq_globstep in H12 as ?;eauto;Hsimpl.
         eapply mem_eq_corestar in H16 as ?;eauto;Hsimpl.

         apply mem_eq_pc_sym in H18.
         eapply mem_eq_abort in H18 as ?;eauto.

         assert(halfatomblockstep ge ({-|x6,cur_tid x3}) tau fp'' x9).
         unfold halfatomblockstep. Esimpl;eauto.

         
         eapply npnswstep_halfatomblock_abort in H20;try apply H11;eauto.
         Hsimpl. simpl in *.
         apply npnsw_taustar_tid_preservation in H2 as ?.
         simpl in H22. rewrite <- H22 in*.
         apply npnsw_taustar_tid_preservation in H10 as ?.
         simpl in H23. rewrite H23 in H20. rewrite pc_cur_tid in H20.
         apply swstar_l1 in H0 as T1. rewrite T1 in *;simpl in *.
         Esimpl;eauto.

         revert H R0;clear. intros.
         inversion H.
         econstructor 2;[|constructor].
         destruct pc,R0;simpl in *;subst;econstructor;eauto.

         apply npnsw_taustar_thdpinv in H10 as ?;auto.
         assert(glob_step pc sw FP.emp ({-|pc,cur_tid pc'})).
         revert H R0;clear. intros.
         inversion H.
         destruct pc,R0;simpl in *;subst;econstructor;eauto.

         apply tau_star_to_star in H10 as [].
         apply npnsw_star_glob_star in H10.
         apply swstar_l1 in H0. rewrite H0 in *;simpl in *.
         eapply star_step in H22 as ?;eauto.
         assert(atom_bit x6 = O). inversion H15;auto.
         apply npnswstep_l2 in H11 as T. rewrite H24 in T;simpl in T.
         eapply drf_pc_glob_cons in H23;eauto.
         apply npnswstep_cur_valid_tid in H11;auto.
         assert(glob_step x5 sw FP.emp ({-|x5,cur_tid x})).
         destruct x5,H11;simpl in *;subst. econstructor;eauto.
         eapply drf_pc_glob_cons;eauto.
         eapply star_step;eauto. constructor.
         simpl.
         apply npnsw_taustar_tid_preservation in H2.
         rewrite<- H2. simpl. intro. rewrite H21 in H8. contradiction.
       }
     }
   Qed.
*)
  Lemma drf_pc_glob_l3:
    forall ge pc,
      drf_pc_glob pc->
      exists NL L p gm pc0 t l fp,
        @init_config NL L p gm ge pc0 t /\ drfpc pc0 /\ star glob_step pc0 l fp pc.
  Proof. unfold drf_pc_glob;unfold drf_pc;intros;Hsimpl;Esimpl;eauto. Qed.
  Lemma init_star_abort_validid:
    forall NL L p gm ge pc t l fp pc',
      @init_config NL L p gm ge pc t ->
      star glob_step pc l fp pc'->
      abort pc'->
      cur_valid_id ge pc'.
  Proof.
    intros.
    apply star_stepN in H0 as [].
    revert NL L p gm ge pc t l fp pc' H H0 H1.
    induction x;intros.
    inversion H0;subst.
    assert(t = cur_tid pc'). inversion H;auto. subst.
    eapply init_property_1_alt in H;eauto. 

    apply stepN_SN_split_weak in H0;Hsimpl.
    apply init_config_GE_wd in H as ?.
    assert(invpc ge pc). inversion H;subst;eapply ThreadPool.init_inv;eauto.
    apply stepN_star in H0.
    eapply GE_mod_wd_star_tp_inv2 in H0;eauto.
    eapply valid_tid_preserve' in H2;eauto.
    destruct H1,H2.
    split;auto.
    contradiction.
  Qed.
  Lemma drf_pc_glob_weak_abort_validid:
    forall ge pc,
      @drf_pc_glob_weak ge pc -> abort pc ->ThreadPool.valid_tid pc.(thread_pool) pc.(cur_tid).
  Proof.
    intros.
    unfold drf_pc_glob_weak in H. unfold abort in H0.
    unfold drf_pc in H. Hsimpl.
    eapply pc_glob_l3 in H3 as [];eauto.
    contradiction.
  Qed.
  (*
  Lemma npnsw_or_sw_stepN_abort:
    forall ge i l pc fp pc',
      drf_pc_glob pc->
      npnsw_or_sw_stepN ge i l pc fp pc'->
      abort pc'->
      exists j fp' pc'',
        pc_valid_tid pc (cur_tid pc') /\
        tau_N glob_npnsw_step j ({-|pc,cur_tid pc'}) fp' pc''/\
        abort pc''.
  Proof.
    intros ge i l pc fp pc' drf1 H H0;revert ge l pc fp pc' drf1 H H0.
    induction i;intros.
    {
      remember 0.
      induction H.
      rewrite pc_cur_tid.
      Esimpl;eauto;[|constructor].

      apply drf_pc_glob_weaken in drf1.
      eapply drf_pc_glob_weak_abort_validid in H0 as ?;eauto.
      destruct H0;split;auto.

      inversion Heqn.

      assert(drf_pc_glob pc').
      eapply drf_pc_glob_cons;eauto.
      eapply star_step;[eapply type_glob_step_elim|constructor];eauto.
      inversion H;auto.
      Hsimpl. subst.
      assert(pc' = ({-|pc,cur_tid pc'})). inversion H;auto.
      rewrite H6 in *;simpl in *.
      Esimpl;eauto.
    }
    {
      apply npnsw_or_sw_stepN_inv1 in H;[|Lia.lia].
      Hsimpl.
      assert(S i - 1 = i). Lia.lia.
      rewrite H5 in H2;clear H5.
      assert(L:drf_pc_glob x0).
      assert(atom_bit x0 = O). apply glob_npnsw_step_bitO_preserve in H1;auto.
      apply swstar_l1 in H;rewrite H. inversion drf1;auto.
      apply swstar_star in H as [].
      eapply npnswstep_l1 in H1.
      Hsimpl. apply type_glob_step_elim in H1.
      eapply star_cons_step in H1 as [];eauto.
      eapply drf_pc_glob_cons;eauto.
        
      eapply IHi in H2 as ?;eauto.
      destruct H5 as (?&?&?&pcvalid1&?&?).
      assert(cur_tid x = cur_tid pc' \/ cur_tid x <> cur_tid pc').
      apply classic.
      destruct H7.
      {
        apply npnsw_step_tid_preservation in H1 as ?.
        rewrite H8 in H7. rewrite <- H7 in H5.
        rewrite pc_cur_tid in H5.
        apply swstar_l1 in H.
        rewrite H in *;simpl in *.
        rewrite <- H8 in H7. rewrite H7 in H1.
        eapply tau_N_S in H5;eauto.
        Esimpl;eauto.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H1;eauto.
      }
      {
        apply drf_pc_glob_l1 in L as ?.
        destruct H8 as [invpc1 wdge].
        apply npnsw_or_sw_stepN_validid in H2 as ?;auto.
        destruct H8.
        subst.
        apply swstar_l1 in H. rewrite H in H1. apply npnsw_step_tid_preservation in H1 as?. simpl in H3. rewrite H3 in H1.
        exists 1,(FP.union x1 FP.emp),pc'. split;auto.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H1;eauto.
        split;auto.
        econstructor;eauto. constructor.
        eapply npnswstep_pc_valid_tid_backwards_preservation in H8;eauto.
        rename H8 into validid1.
        apply swstar_l1 in H as ?.
        rewrite H8 in validid1.
        rewrite H8 in H1.
        apply tauN_taustar in H5.
        pose proof drf1 as L0.
        apply drf_pc_glob_l1 in drf1 as [L1 _].
        specialize (drf_pc_glob_l2 _ _ L0) as modwdge.
        inversion L0 as (L4&_).
 
        
        eapply glob_npnsw_step_star_ex_alter in H1;eauto.
        destruct H1.
        eapply race_changetid in H1;simpl in H1;erewrite pc_cur_tid in H1.
        eapply drf_pc_l4 in H1;eauto.
        contradiction. constructor.

        Hsimpl. simpl in *. apply mem_eq_pc_sym in H11.
        apply mem_eq_abort in H11;auto.
        apply npnsw_taustar_tid_preservation in H5 as ?;auto.
        rewrite <-H12 in H11. simpl in H11.
        apply npnsw_taustar_tid_preservation in H9 as ?;auto.
        simpl in H13. rewrite H13 in *.
        assert(swstep1:glob_step pc sw FP.emp ({-|pc,cur_tid x7})).
        destruct pc,validid1;simpl in *;subst;econstructor;eauto.
        
        apply npnswstar_bit in H9 as ?. simpl in H14. 
        apply tau_star_to_star in H9 as ?;destruct H15.
        
        apply npnsw_star_glob_star in H15.
        eapply star_step in swstep1 as ?;eauto.
        eapply drf_pc_glob_cons in H16 as ?;eauto;[|congruence].
        
        eapply npnsw_abort_preserve in H10;eauto.
        apply tau_star_tau_N_equiv in H9 as [].
        
        Esimpl;eauto.
      }
    }
  Qed.


  Lemma noevt_stepN_taustarabort_ex:
    forall ge i pc fp pc',
      drf_pc_glob pc->
      GlobEnv.wd ge ->
      (forall ix, mod_wd (GlobEnv.modules ge ix)) ->
      invpc ge pc ->
      atom_bit pc = O->
      noevt_stepN ge glob_step i pc fp pc'->
      abort pc'->
        exists pc1,
          sw_star glob_step pc pc1 /\
          ((exists j l fp' pc2,atomblockstarN ge j l pc1 fp' pc2 /\ race glob_predict_star_alter pc2) \/
           (exists  j l fp' pc2 fp2 pc3,
             atomblockstarN ge j l pc1 fp' pc2 /\ tau_star glob_npnsw_step pc2 fp2 pc3 /\ abort pc3) \/
           (exists j l fp' pc2 fp2 pc3 fp3 pc4,
               atomblockstarN ge j l pc1 fp' pc2 /\ tau_star glob_npnsw_step pc2 fp2 pc3 /\ halfatomblockstep ge pc3 tau fp3 pc4 /\abort pc4)).            
  Proof.
    intros ge i pc fp pc' drf1;intros.
    destruct i.
    apply noevt_stepN_0 in H3 as [];subst.
    Esimpl;eauto. right;left. Esimpl;eauto. econstructor. apply swstar_l1 in H5;rewrite H5;auto. constructor.
    assert(T0:cur_valid_id ge pc').
    apply noevt_stepN_sound in H3.
    apply non_evt_star_star in H3 as [].
    eapply drf_pc_glob_weak_abort_validid in H4 as ?;eauto.
    destruct H4. split;auto.
    unfold drf_pc_glob,drf_pc_glob_weak,drf_pc in *.
    Hsimpl. eapply cons_star_star in H3;eauto.
    Esimpl;eauto.
     
    destruct (atom_bit pc') eqn:?.
    {
      eapply noevt_stepN_Si_to_atomblockstarN in H3;eauto;[|Lia.lia].
      Hsimpl.
      destruct H5;Hsimpl.
      Esimpl;eauto. left;Esimpl;eauto. constructor. inversion H5. inversion H7;auto.

      destruct H5;Hsimpl.
      Esimpl;eauto. left;Esimpl;eauto.

      
      apply npnsw_or_sw_stepN_exists in H6;Hsimpl;[|apply atomblockstarN_atomO in H5 as [];auto].
      eapply mem_eq_abort in H4;eauto;[|apply mem_eq_pc_sym;eauto].

      assert(T1:drf_pc_glob x3).
      apply swstar_star in H3 as [].
      apply atomblockstarN_star in H5 as ?.
      apply atomblockstarN_atomO in H5.
      Hsimpl. eapply cons_star_star in H9;eauto.
      eapply drf_pc_glob_cons;eauto.

      
      assert(T2:drf_pc_glob x5).
      apply npnsw_or_sw_stepN_bitO in H6 as ?.
      destruct H9.
      apply npnsw_or_sw_stepN_sound in H6. apply npnsw_or_sw_star_non_evt_star in H6.
      apply non_evt_star_star in H6 as [].
      eapply drf_pc_glob_cons;eauto.
      
      assert(T3:sw_star glob_step x5 ({-|x5,cur_tid pc'})).
      econstructor 2;[|constructor].
      destruct x5,pc',T2,T0,H7 as (?&?&?&?). simpl in *;subst. econstructor;eauto.
      eapply swstar_npnsw_or_sw_stepN in T3;[|inversion T2;auto].
      eapply npnsw_or_sw_stepN_cons in T3;eauto.
      rewrite appnil in T3. rewrite FP.fp_union_emp in T3.
      remember ({-|x5,cur_tid pc'}) as r.
      clear x5 Heqr H6 T2.
      rename T3 into H6,r into x5.

      
      eapply npnsw_or_sw_stepN_abort in H6;eauto.
      Hsimpl.
      assert(glob_step x3 sw FP.emp ({-|x3,cur_tid x5})).
      apply atomblockstarN_atomO in H5 as [];destruct x3,H6;simpl in *;subst;econstructor;eauto.

      destruct x0.
      {
        inversion H5;subst.
        assert(sw_star glob_step pc ({-|x3,cur_tid x5})).
        apply swstar_l1 in H3.
        rewrite H3 in *;subst.
        simpl in *.
        assert(glob_step pc sw FP.emp ({-|pc,cur_tid x5})).
        destruct pc;inversion H11;subst. econstructor;eauto.
        econstructor 2;[eauto|constructor].
        Esimpl;eauto.
        clear H4.
        right;left. Esimpl;eauto. constructor. apply atomblockstarN_atomO in H5;auto.
        eapply tauN_taustar;eauto.
      }
      {
        eapply atomblockstarN_cons_sw in H5;eauto.
        Esimpl;eauto. right;left.
        clear H4.
        apply tauN_taustar in H9.
        Esimpl;eauto.
      }
    }
    
    {
      apply noevt_stepN_Si_to_atomblockstarN2 in H3;auto;[|Lia.lia].
      Hsimpl. 
      destruct H5;Hsimpl.
      Esimpl;eauto;left;Esimpl;eauto.

      apply npnsw_or_sw_stepN_exists in H6;Hsimpl;[|apply atomblockstarN_atomO in H5 as [];auto].
      assert(tau_star glob_npnsw_step x5 FP.emp x5). constructor.
      assert(drf_pc_glob x3).
      apply atomblockstarN_atomO in H5 as ?.
      apply atomblockstarN_star in H5. apply swstar_star in H3.
      Hsimpl. eapply cons_star_star in H5;eauto. eapply drf_pc_glob_cons;eauto.

      eapply mem_eq_abort in H4;try apply mem_eq_pc_sym;eauto.
      
      eapply  npnsw_or_sw_stepN_taustar_abort in H7;try apply H6;eauto.
      Hsimpl.

      destruct x0.
      {
        inversion H5;subst.
        assert(sw_star glob_step pc ({-|x3,cur_tid x5})).
        apply swstar_l3 in H3 as [];subst;auto.
        econstructor;eauto.

        Esimpl;eauto. right;right;Esimpl;eauto. constructor. auto.
      }
      
      eapply atomblockstarN_cons_swstar in H5;eauto.
      Esimpl;eauto. right;right;Esimpl;eauto.
    }
  Qed.    
*)
  Lemma corestar_globstar:
    forall ge pc fp pc',
      tau_star (@type_glob_step ge core) pc  fp pc'->
      tau_star glob_step pc fp pc'.
  Proof.
    induction 1;intros;econstructor;eauto. eapply type_glob_step_elim;eauto. Qed.
  Lemma corestar_npstar:
    forall ge pc fp pc',
      tau_star (@type_glob_step ge core) pc  fp pc'->
      non_evt_star np_step pc fp pc'.
  Proof.
    induction 1;intros. constructor.
    eapply core_step_equiv in H. apply type_step_elim in H.
    econstructor;eauto.
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



    
  Lemma Etr_p_np_abort:
    forall ge pc,
      @drf_pc_glob ge pc->
      Etr glob_step abort final_state pc Behav_abort->
      Etr np_step np_abort final_state pc Behav_abort \/
      exists t,Etr np_step np_abort final_state ({-|pc,t}) Behav_abort /\ pc_valid_tid pc t .
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as ?;Hsimpl.
    specialize (drf_pc_glob_l2 _ _ H) as ?.
    inversion H as [? _].
    inversion H0;subst.
    apply non_evt_star_star in H5 as [].
    contradict H6.
    unfold drf_pc_glob,drf_pc in H.
    Hsimpl.
    eapply cons_star_star in H5;eauto.
  Qed.
  (*
    apply noevt_stepN_exists in H5 as [].
    apply noevt_stepN_taustarabort_ex in H5;auto.
    Hsimpl.
    destruct H7 as [|[]].
    {
      Hsimpl.
      assert(drf_pc_glob x4).
      apply swstar_star in H5.
      apply atomblockstarN_star in H7 as ?.
      apply atomblockstarN_atomO in H7.
      Hsimpl. eapply cons_star_star in H9;eauto.
      eapply drf_pc_glob_cons;eauto.

      eapply drf_pc_l4 in H9;eauto. contradiction. constructor.
    }
    {
      Hsimpl.
      assert(drf_pc_glob x6).
      apply swstar_star in H5.
      apply atomblockstarN_star in H7 as ?.
      apply atomblockstarN_atomO in H7.
      apply npnswstar_bit in H8 as ?.
      apply tau_star_to_star in H8.
      Hsimpl. eapply cons_star_star in H10;eauto.
      apply npnsw_star_glob_star in H8.
      eapply cons_star_star in H8;eauto.
      eapply drf_pc_glob_cons;eauto. congruence.
      apply drf_pc_glob_weak_abort_validid in H9 as ?;try apply drf_pc_glob_weaken;auto.
      destruct x1.
      {
        inversion H7;subst.
        apply swstar_l3 in H5 as [].
        subst.
        left.
        apply glob_npnsw_star_to_np_taustar in H8.
        apply tau_star_non_evt_star in H8.
        econstructor;eauto. apply abort_eq;auto.

        right. exists (cur_tid x4). assert(({-|pc,cur_tid x4})= x4). inversion H5;auto.
        split.  apply glob_npnsw_star_to_np_taustar in H8.
        apply tau_star_non_evt_star in H8. rewrite H13.
        econstructor;eauto. apply abort_eq;auto.
        inversion H5;split;auto.
      }

      assert(invpc ge x0). apply swstar_l1 in H5. rewrite H5;auto.
      assert(invpc ge x4). apply atomblockstarN_star in H7 as []. eapply GE_mod_wd_star_tp_inv2;eauto.
      apply atomblockstarN_np in H7 as ?;auto.
      Hsimpl.
      destruct H15.
      {
        Hsimpl.
        assert(cur_valid_id ge x6). destruct H9;split;auto.
        apply tau_star_to_star in H8 as ?.
        Hsimpl.
        apply npnsw_star_glob_star in H17.
        eapply pc_valid_tid_back_star in H17;eauto.
        apply npnsw_taustar_tid_preservation in H8 as ?.
        rewrite <- H18 in H17.
        assert(sw_star glob_step ({-|x4,x8}) x4).
        econstructor 2;[|constructor].
        apply atomblockstarN_atomO in H7 as [_].
        destruct x4,H17;simpl in *;subst;econstructor;eauto.
        eapply npsw_swstar in H15;eauto.

        apply glob_npnsw_star_to_np_taustar in H8.
        apply tau_star_non_evt_star in H8.
        assert(non_evt_star np_step x7 (FP.union FP.emp FP.emp) x4).
        econstructor 2;[right|constructor];eauto.
        eapply non_evt_star_cons in H8;eauto.
        eapply non_evt_star_cons in H8;eauto.

        apply abort_eq in H9;auto.
        apply swstar_l3 in H5 as [].
        subst.
        left. econstructor;eauto.
        right. assert(x0 = ({-|pc,cur_tid x0})). inversion H5;auto.
        exists (cur_tid x0). rewrite <- H21. constructor. econstructor;eauto.
        inversion H5;split;auto.
      }
      {
        apply tau_star_to_star in H8;Hsimpl.
        apply npnsw_star_glob_star in H8.
        assert(pc_valid_tid x6 (cur_tid x6)). destruct H9;split;auto.
        eapply pc_valid_tid_back_star in H8;eauto.
        destruct H8. contradict H17. inversion H15;subst;simpl;eauto.
      }
      Lia.lia.
    }
    
    {
      Hsimpl.
      assert(L0:drf_pc_glob x6).
      apply atomblockstarN_star in H7.
      apply tau_star_to_star in H8 as [].
      apply npnsw_star_glob_star in H8.
      apply swstar_star in H5.
      unfold halfatomblockstep in H9. Hsimpl.
      eapply cons_star_star in H8;eauto.
      eapply cons_star_star in H8;eauto.
      eapply drf_pc_glob_cons;eauto. inversion H11;auto.

      assert(L1:drf_pc_glob_weak ge x8).
      unfold halfatomblockstep,drf_pc_glob,drf_pc_glob_weak,drf_pc in *;Hsimpl.
      apply type_glob_step_elim in H13 as ?.
      eapply corestar_globstar in H18. apply tau_star_to_star in H18 as [].
      eapply star_step in H18;eauto. eapply cons_star_star in H18;eauto.
      Esimpl;eauto.

      apply abort_eq in H10 as R;auto;[|try apply drf_pc_glob_weak_abort_validid;auto].
      assert(L2:cur_valid_id ge x6).
      unfold halfatomblockstep in H9;Hsimpl.
      apply drf_pc_glob_l1 in L0 as [].
      inversion H11;subst. split. eapply gettop_valid_tid;eauto.
      intro;solv_thread.

      
      unfold halfatomblockstep in H9;Hsimpl.
      apply entat_step_equiv in H11 as ?. apply type_step_elim in H13.
      apply corestar_npstar in H12.
      assert(non_evt_star np_step x6 (FP.union FP.emp FP.emp ) x9).
      econstructor 2;eauto. constructor.
      eapply non_evt_star_cons in H12;eauto.

      apply glob_npnsw_star_to_np_taustar in H8 as ?.
      apply tau_star_non_evt_star in H15.
      eapply non_evt_star_cons in H12;eauto.

      
      
      destruct x1.
      {
        inversion H7;subst.
        apply swstar_l3 in H5 as [];subst.
        left. econstructor;eauto.

        right. exists (cur_tid x4). split. assert(({-|pc,cur_tid x4}) = x4). inversion H5;auto. rewrite H17;econstructor;eauto.
        inversion H5;split;auto.
      }
      {
        assert(invpc ge x0). erewrite swstar_l1;eauto.
        eapply atomblockstarN_np in H7;eauto;[|Lia.lia].
        Hsimpl. destruct H17.
        {
          Hsimpl.

          assert(sw_star glob_step ({-|x4,x11}) x4).
          econstructor 2;[|constructor].
          apply npnsw_taustar_tid_preservation in H8 as ?.
          apply tau_star_to_star in H8 as [].
          apply npnsw_star_glob_star in H8.
          eapply pc_valid_tid_back_star in H8;eauto.
          rewrite<- H18 in H8.
          assert(atom_bit x4 = O).
          inversion H17;subst;auto.
          destruct x4,H8;simpl in *;subst.
          econstructor;eauto.
          apply non_evt_star_star in H7 as [].
          apply swstar_l1 in H5. rewrite H5 in *;simpl in *.
          eapply GE_mod_wd_npstar_tp_inv in H7;eauto.
          assert(star np_step x10 (cons sw nil) (FP.union FP.emp FP.emp) ({-|x4,x11})).
          econstructor;eauto. constructor.
          eapply GE_mod_wd_npstar_tp_inv in H19;eauto.

          eapply npsw_swstar in H17;eauto.
          assert(non_evt_star np_step x10 (FP.union FP.emp FP.emp) x4).
          econstructor;eauto. constructor.
          eapply non_evt_star_cons in H12;eauto.
          eapply non_evt_star_cons in H12;eauto.

          apply swstar_l3 in H5 as [];subst.
          left. econstructor;eauto.
          right. inversion H5;subst.
          eexists;split;[|split;eauto];econstructor;eauto.
        }
        {
          apply tau_star_to_star in H8 as [].
          apply npnsw_star_glob_star in H8.
          eapply pc_valid_tid_back_star in H8;eauto.
          inversion H17;subst.
          destruct H8.
          eapply H_all_thread_halted in H8. contradiction.
          apply non_evt_star_star in H7 as [].
          apply swstar_l1 in H5;rewrite H5 in *;simpl in *.
          eapply GE_mod_wd_npstar_tp_inv in H7;eauto.
          apply type_step_elim in H17.
          eapply GE_mod_wd_npstar_tp_inv with(pc:=x10);eauto.
          eapply star_step;eauto. constructor.
        }
      }
    }
  Qed.    
   *)
  Lemma silent_diverge_cons_glob_non_evt_star:
    forall ge pc fp pc',
      non_evt_star (@glob_step ge) pc fp pc'->
      silent_diverge glob_step pc'->
      silent_diverge glob_step pc.
  Proof.
    induction 1;intros.
    auto.
    
    apply IHnon_evt_star in H1.
    destruct H.
    econstructor. constructor. eauto. eauto.
    inversion H1;subst.
    
    assert(fp1=FP.emp). inversion H;auto.
    subst.
    eapply sw_star_cons in H2;eauto.
    econstructor;eauto.
    econstructor;eauto. constructor.
  Qed.
  Section silent_diverge.
    Variable GE:GlobEnv.t.
    Hypothesis wdge: GlobEnv.wd GE.
    Hypothesis modwdge: forall ix, mod_wd (GlobEnv.modules GE ix).
    Local Arguments cur_valid_id [GE].
    Local Arguments changepc [GE].
    Local Arguments mem_eq_pc [GE].
    Local Arguments ProgConfig [GE].
    Local Arguments noevt_stepN [GE].
    Local Arguments Sdiverge [GE].
    Local Arguments Pdiverge [GE].
    
    Definition psilent_diverge := silent_diverge (@glob_step GE).
    Definition npsilent_diverge := silent_diverge (@np_step GE).
    
  Lemma noevt_stepN_cons:
    forall i pc fp pc' j fp' pc'',
      noevt_stepN (@glob_step GE) i pc fp pc'->
      noevt_stepN glob_step j pc' fp' pc''->
      noevt_stepN glob_step (i+j) pc (FP.union fp fp') pc''.
  Proof.
    induction i as [i IHi]using(well_founded_induction lt_wf);intros.
    destruct i.
    simpl. 
    apply noevt_stepN_0 in H.
    destruct H;subst.
    induction H1;subst. rewrite FP.emp_union_fp;auto.
    Hsimpl. econstructor 2;eauto. rewrite FP.emp_union_fp in IHsw_star;auto.

    eapply noevt_stepN_Si_inv in H. Hsimpl.
    eapply IHi in H0;try apply H2;auto.

    apply swstar_noevt_stepN in H.
    eapply cons_tau in H0;eauto.
    eapply IHi in H0;try apply H;eauto.
    assert(0+ S(i+j) = S i + j). Lia.lia.
    rewrite H4 in H0;clear H4.
    rewrite <- H3, <- FP.fp_union_assoc.
    rewrite FP.emp_union_fp in H0;auto.
    Lia.lia.
  Qed.
    
  Lemma psilent_diverge_inv:
    forall pc,
      psilent_diverge pc->
      exists i fp pc',
        noevt_stepN glob_step (S i) pc fp pc' /\ psilent_diverge pc'.
  Proof.
    inversion 1;subst.
    apply swstar_noevt_stepN in H0.
    eapply noevt_stepN_cons_taustep in H1;eauto.
  Qed.

  Lemma psilent_diverge_O_inv1:
    forall pc,
      psilent_diverge pc->
      (exists i fp pc',atom_bit pc' = O /\noevt_stepN glob_step (S i) pc fp pc' /\ psilent_diverge pc' )
      \/
      (~ ( exists i fp pc', atom_bit pc' = O /\noevt_stepN glob_step (S i) pc fp pc' /\ psilent_diverge pc')).
  Proof. intros;apply classic. Qed.

  Definition I_psilent_diverge :=
    fun pc =>
      @atom_bit GE pc = I /\ psilent_diverge pc /\
      ~ ( exists i fp pc', atom_bit pc' = O /\noevt_stepN glob_step (S i) pc fp pc' /\ psilent_diverge pc').     
                                    
  Lemma psilent_diverge_foreverI_inv1:
    forall pc,
      atom_bit pc = O->
      psilent_diverge pc ->
      (~ ( exists i fp pc', atom_bit pc' = O /\noevt_stepN glob_step (S i) pc fp pc' /\ psilent_diverge pc')) ->
       exists pc1 fp pc2,
         sw_star glob_step pc pc1 /\
         glob_step pc1 tau fp pc2 /\
         I_psilent_diverge pc2.
  Proof.
    unfold I_psilent_diverge. intros.
    inversion H0;subst.
    Esimpl;eauto.
    destruct (atom_bit s'') eqn:?;auto.
    contradict H1.
    apply swstar_noevt_stepN in H2.
    eapply noevt_stepN_cons_taustep in H3;eauto.
    Esimpl;eauto.

    intro.
    Hsimpl.
    apply swstar_noevt_stepN in H2.
    eapply noevt_stepN_cons_taustep in H3;eauto.
    eapply noevt_stepN_cons in H6;eauto.
    contradict H1.
    Esimpl;eauto.
  Qed.

  Lemma I_psilent_diverge_inv:
    forall pc,
      I_psilent_diverge pc ->
      exists fp pc',
        type_np_step core pc tau fp pc'/\
        I_psilent_diverge pc'.
  Proof.
    unfold I_psilent_diverge,psilent_diverge;intros.
    Hsimpl.
    inversion H0;subst.
    apply glob_sw_star_I in H2;auto.
    subst.
    destruct (atom_bit s'') eqn:?.
    contradict H1.
    Esimpl;eauto. econstructor 3;eauto. constructor.
    apply type_glob_step_exists in H3 as [].
    destruct x;try(inversion H2;subst;inversion H;inversion Heqb;fail).
    apply core_step_equiv in H2;auto.
    Esimpl;eauto.

    intro.
    Hsimpl.
    contradict H1.
    apply core_step_equiv in H2.
    apply type_glob_step_elim in H2.
    eapply cons_tau in H2;eauto.
    Esimpl;eauto.
  Qed.
  CoInductive core_Idiverge:@ProgConfig GE->Prop:=
    cons_core_Idiv:
      forall pc fp pc',
        atom_bit pc = I->
        type_np_step core pc tau fp pc'->
        core_Idiverge pc'->
        core_Idiverge pc.
  Lemma core_Idiverge_I_psilent_diverge_exists:
    forall pc,
      I_psilent_diverge pc->
      core_Idiverge pc.
  Proof.
    cofix.
    intros.
    apply I_psilent_diverge_inv in H as ?;Hsimpl.
    econstructor;eauto. inversion H;subst;auto.
  Qed.
  Lemma sw_step_I_psilent_diverge:
    forall pc pc',
      glob_step pc sw FP.emp pc'->
      core_Idiverge pc'->
      core_Idiverge ({-|pc,cur_tid pc'}).
  Proof. intros;inversion H;subst;auto. Qed.

  
  Lemma core_Idiverge_npsilent_diverge:
    forall pc,
      core_Idiverge pc ->
      npsilent_diverge pc.
  Proof.
    cofix.
    inversion 1;subst.
    apply type_step_elim in H1.
    econstructor;eauto. constructor.
    apply core_Idiverge_npsilent_diverge in H2.
    auto.
  Qed.

  Definition O_psilent_diverge:=
    fun pc =>
      atom_bit pc = O /\
      psilent_diverge pc /\ 
      ~ (exists i fp pc', noevt_stepN glob_step (S i) pc fp pc' /\ I_psilent_diverge pc').
  (*Note:case analysis:O-diverge or I-diverge*)
  Lemma psilent_diverge_inv2:
    forall pc,
      atom_bit pc = O ->
      psilent_diverge pc ->
      O_psilent_diverge pc \/ (exists i fp pc', noevt_stepN glob_step (S i) pc fp pc' /\ I_psilent_diverge pc').
  Proof.
    intros.
    assert(O_psilent_diverge pc \/ ~ O_psilent_diverge pc).
    apply classic. destruct H1;auto.
    right.
    unfold O_psilent_diverge in H1.
    apply not_and_or in H1 as [].
    contradiction.
    apply not_and_or in H1 as [].
    contradiction.
    apply NNPP in H1;auto.
  Qed.

  Ltac unfolds := unfold O_psilent_diverge,I_psilent_diverge,psilent_diverge,npsilent_diverge in *.

  Lemma O_psilent_diverge_inv:
    forall pc,
      O_psilent_diverge pc ->
      exists i fp pc',
        noevt_stepN glob_step (S i) pc fp pc'/\ O_psilent_diverge pc'.
  Proof.
    intros.
    destruct H;Hsimpl.
    pose proof H0 as R.
    apply psilent_diverge_O_inv1 in H0.
    destruct H0.
    Hsimpl.
    Esimpl;eauto.
    unfold O_psilent_diverge.
    Esimpl;eauto.
    intro. contradict H1.
    Hsimpl. eapply noevt_stepN_cons in H1;eauto.
    assert(S x + S x2 = S(x+x2+1)). Lia.lia.
    rewrite H5 in H1.
    eauto.

    apply psilent_diverge_foreverI_inv1 in R;auto.
    Hsimpl.
    contradict H1.
    apply swstar_noevt_stepN in H2.
    eapply noevt_stepN_cons_taustep in H2;eauto.
  Qed.

  Lemma O_globtaustep:
    forall pc fp pc',
      glob_step pc tau fp pc'-> atom_bit pc = atom_bit pc' ->
      glob_npnsw_step pc tau fp pc' \/ haltstep GE pc tau fp pc'.
  Proof.
    intros.
    apply type_glob_step_exists in H as [].
    destruct x;try(inversion H;subst;inversion H0;fail).
    left;left;auto.
    left;right;auto.
    left;right;auto.
    right;auto.
  Qed.
  Lemma atomblockstep_noevtstar:
    forall pc fp pc',
      atomblockstep GE pc tau fp pc'->
      non_evt_star glob_step pc fp pc'.
  Proof.
    unfold atomblockstep,atomblockN.
    intros;Hsimpl.
    apply tauN_taustar in H1.
    apply corestar_globstar in H1.
    apply tau_star_non_evt_star in H1.
    apply type_glob_step_elim in H0.
    apply type_glob_step_elim in H2.
    assert(non_evt_star glob_step x1 (FP.union FP.emp FP.emp) pc').
    econstructor 2;eauto. constructor.
    eapply non_evt_star_cons in H3;eauto.
    eapply ETrace.ne_star_step in H3;eauto.
    repeat rewrite FP.emp_union_fp in H3.
    rewrite FP.fp_union_emp in H3.
    auto.
  Qed.
  Lemma O_psilent_diverge_inv':
    forall pc,
      ThreadPool.inv pc.(thread_pool)->
      O_psilent_diverge pc ->
      exists pc' fp pc'',
        sw_star glob_step pc pc'/\
        (glob_npnsw_step pc' tau fp pc'' \/ haltstep GE pc' tau fp pc'' \/ atomblockstep GE pc' tau fp pc'') /\ O_psilent_diverge pc'' /\ ThreadPool.inv pc''.(thread_pool).
  Proof.
    intros.
    unfold O_psilent_diverge in H0.
    Hsimpl.

    inversion H1;subst.
    destruct (atom_bit s'') eqn:?.
    {
      apply O_globtaustep in H4 as ?.
      Esimpl. eauto. destruct H6;eauto.
      unfold O_psilent_diverge.
      Esimpl;eauto.
      intro.
      Hsimpl.

      eapply cons_tau in H4;eauto.
      contradict H2.
      apply swstar_noevt_stepN in H3.
      eapply noevt_stepN_cons in H4;eauto.
      Esimpl;eauto.

      destruct H6. apply npnsw_step_thdpinv in H6;eauto. apply swstar_l1 in H3. rewrite H3;auto.
      apply GE_mod_wd_tp_inv in H4;eauto. apply swstar_l1 in H3;rewrite H3;auto.
      apply swstar_l1 in H3;rewrite H3;simpl; congruence.
    }
    {
      assert(~ I_psilent_diverge s'').
      intro;contradict H2.
      apply swstar_noevt_stepN in H3.
      eapply noevt_stepN_cons_taustep in H4;eauto.
      unfold I_psilent_diverge in H6.
      apply not_and_or in H6 as []. contradiction.
      apply not_and_or in H6 as []. contradiction.
      apply NNPP in H6.
      Hsimpl.

      apply noevt_stepN_IO in H7;auto.
      Hsimpl. apply tau_star_tau_N_equiv in H7 as [].
      apply type_glob_step_exists in H4 as [].
      destruct x8;try(inversion H4;subst;inversion Heqb;inversion H6;fail).

      
      inversion H4;subst. simpl in *. subst. apply swstar_l1 in H3.
      destruct pc. simpl in *;subst. inversion H3.
      assert(R1:atomblockstep GE s' tau x3 x4).
      unfold atomblockstep,atomblockN. Esimpl;eauto.
      inversion H4;subst;auto.
      Esimpl. eauto.

      right;right. unfold atomblockstep,atomblockN.
      Esimpl;eauto. assert(fp'=FP.emp). inversion H4;auto. subst;auto.
      unfold O_psilent_diverge. Esimpl;eauto.
      inversion H9;auto.
      eapply silent_diverge_cons_glob_non_evt_star;eauto.
      eapply noevt_stepN_sound;eauto.

      intro. Hsimpl.
      contradict H2.
      assert(fp'=FP.emp). inversion H4;subst;auto. subst.
      apply atomblockstep_noevtstar in R1 as ?.
      apply noevt_stepN_exists in H2 as [].
      eapply noevt_stepN_cons in H13;eauto.
      apply swstar_noevt_stepN in H3.
      eapply noevt_stepN_cons in H13;eauto.
      assert(0+(x0+S x8) = S(x0+x8)). Lia.lia.
      rewrite H12 in H13;clear H12.
      Esimpl;eauto.

      apply swstar_l1 in H3 as ?.
      
      rewrite H13 in H4.
      apply atomblockstep_invpc_preserve in R1;auto.
      rewrite H13;auto.
    }
  Qed.

  CoInductive Odiverge:@ProgConfig GE->Prop:=
  | cons_Otau:
      forall  pc fp pc' pc'',
        ThreadPool.inv pc.(thread_pool)->
        glob_step pc sw FP.emp pc'->
        glob_npnsw_step pc' tau fp pc'' ->
        Odiverge pc''->
        Odiverge pc
  | cons_block:
      forall pc fp pc' pc'',
        ThreadPool.inv pc.(thread_pool)->
        glob_step pc sw FP.emp pc'->
        atomblockstarN GE 1 (cons (cur_tid pc') nil) pc' fp pc''->
        Odiverge pc''->
        Odiverge pc.

  Lemma Odiverge_O:  forall pc, Odiverge pc ->atom_bit pc = O /\ ThreadPool.inv pc.(thread_pool).
  Proof. split;inversion H;subst;auto;inversion H1;auto. Qed.
  Lemma non_evt_star_cons_Odiverge:
    forall pc fp pc',
      non_evt_star glob_step pc fp pc'->
      atom_bit pc = O ->
      ThreadPool.inv pc.(thread_pool)->
      Odiverge pc'->
      Odiverge pc.
  Proof.
    intros pc fp pc' H.
    apply noevt_stepN_exists in H as [].
    revert pc fp pc' H.
    induction x using(well_founded_induction lt_wf);intros.
    destruct x.
    {
      apply noevt_stepN_0 in H0 as [];subst.
      inversion H3;subst.
      apply swstar_l1 in H4.
      rewrite H4 in H5.
      econstructor;eauto. inversion H5;subst.
      destruct pc. simpl in *;subst; econstructor;eauto.

      apply swstar_l1 in H4. rewrite H4 in H5.
      econstructor 2;eauto. inversion H5;subst.
      destruct pc;simpl in *;subst. econstructor;eauto.
    }
    {
      edestruct Odiverge_O;eauto.
      apply noevt_stepN_Si_inv2 in H0;auto.
      Hsimpl.
      destruct H6;Hsimpl.
      {
        apply swstar_l1 in H0 as ?.
        rewrite H11 in H7;simpl in H7. rewrite H1 in H7.
        apply GE_mod_wd_tp_inv in H6 as ?;auto;[|rewrite H11;auto].
        eapply H in H8;eauto;[|Lia.lia].

        assert(invpc GE x0). rewrite H11;auto.
        apply O_globtaustep in H6.
        destruct H6.
        econstructor;eauto.
        apply npnsw_step_cur_valid_id in H6;auto. rewrite H11 in H6;destruct pc,H6;simpl in *;subst. rewrite H11. econstructor;eauto.

        assert(glob_step pc sw FP.emp x0).
        rewrite H11 in *.
        apply type_glob_step_cur_valid_id in H6;auto;try congruence.
        destruct pc,H6;simpl in *;subst; econstructor;eauto.
        econstructor 2. auto. eauto. econstructor. constructor. right;eauto.
        constructor. constructor. inversion H6;auto. auto.

        rewrite H11. simpl. congruence.
      }
      {
        apply swstar_l1 in H0 as ?.
        assert(glob_step pc sw FP.emp x0).
        unfold atomblockstep,atomblockN in H6. Hsimpl.
        apply type_glob_step_cur_valid_id in H12;auto;try congruence.
        rewrite H11 in H12;destruct pc,H12;simpl in *;subst. rewrite H11. econstructor;eauto. rewrite H11;auto.

        assert(atom_bit x2 = O). unfold atomblockstep,atomblockN in H6;Hsimpl.
        inversion H15;subst;auto.
        apply atomblockstep_invpc_preserve in H6 as ?;auto;[|rewrite H11;auto].
        
        eapply H in H8;eauto;[|Lia.lia].
        econstructor 2;try apply H8;eauto. econstructor 2;eauto.
        constructor. constructor. constructor. auto.
      }
    }
  Qed.    
  Lemma O_psilent_diverge_Odiverge:
    forall pc,
      ThreadPool.inv pc.(thread_pool)->
      O_psilent_diverge pc->
      Odiverge pc.
  Proof.
    cofix.
    intros.
    assert(L1:atom_bit pc = O). destruct H0;auto.
    apply O_psilent_diverge_inv' in H0;try apply H.
    Hsimpl.
    destruct H1 as [|[]].
    {
      apply swstar_l1 in H0.
      apply npnsw_step_cur_valid_id in H1 as ?;[|rewrite H0];auto.
      assert(glob_step pc sw FP.emp ({-|pc,cur_tid x})).
      rewrite H0 in H4. destruct pc,H4;simpl in *;subst. econstructor;eauto.
      econstructor;eauto.
      rewrite <- H0. eauto.
    }
    {
      apply swstar_l1 in H0.
      apply type_glob_step_cur_valid_id in H1 as ?;[|rewrite H0;auto|congruence].
      
      assert(atomblockstarN GE 1 (cons (cur_tid x) nil) x (FP.union (FP.union FP.emp x0) FP.emp) x1).
      econstructor 2;eauto. constructor. constructor. constructor.
      inversion H2;auto.
      rewrite FP.emp_union_fp in H5. rewrite FP.fp_union_emp in H5.
      econstructor 2;eauto.
      rewrite H0 in *. destruct pc,H4;simpl in *;subst;econstructor;eauto.
    }
    {
      apply swstar_l1 in H0.
      apply atomblockstep_cur_valid_id in H1 as ?;[|rewrite H0;auto].
      
      assert(atomblockstarN GE 1 (cons (cur_tid x) nil) x (FP.union (FP.union FP.emp x0) FP.emp) x1).
      econstructor 2;eauto. constructor. constructor. constructor.
      inversion H2;auto.
      rewrite FP.emp_union_fp in H5. rewrite FP.fp_union_emp in H5.
      econstructor 2;eauto.
      rewrite H0 in *. destruct pc,H4;simpl in *;subst;econstructor;eauto.
    }
  Qed.


  Definition neverIdiverge (pc:@ProgConfig GE):Prop:=
    Odiverge pc /\
    ~ (exists fp pc' fp' pc'', non_evt_star glob_step pc fp pc' /\ atomblockstarN GE 1 (cons(cur_tid pc') nil) pc' fp' pc''  /\ Odiverge pc'').

  Definition will_neverIdiverge (pc:@ProgConfig GE):Prop:=
    Odiverge pc /\
    exists fp pc', non_evt_star glob_step pc fp pc' /\ neverIdiverge pc'.

  CoInductive npnswdiverge:@ProgConfig GE->Prop:=
  | cons_npnsw_div:
      forall  pc fp pc' pc'',
        ThreadPool.inv pc.(thread_pool)->
        glob_step pc sw FP.emp pc'->
        glob_npnsw_step pc' tau fp pc'' ->
        npnswdiverge pc''->
        npnswdiverge pc.
  Lemma Odiverge_neverIdiverge_npnswdiverge:
    forall pc,
      neverIdiverge pc ->
      npnswdiverge pc.
  Proof.
    cofix.
    intros.
    destruct H.
    inversion H;subst.
    econstructor;eauto.
    apply Odiverge_neverIdiverge_npnswdiverge.
    split;auto.
    intro;contradict H0.
    Hsimpl.
    apply npnswstep_l1 in H3 as [?[]].
    apply type_glob_step_elim in H3.
    eapply ETrace.ne_star_step in H0;eauto.
    eapply ETrace.ne_star_step in H0;eauto.
    Esimpl;eauto.

    contradict H0.
    Esimpl;eauto.
    econstructor 2. eauto. constructor.
  Qed.
  Lemma npnsw_taustar_non_evt_star:
    forall pc fp pc',
      tau_star glob_npnsw_step pc fp pc'->
      non_evt_star (@glob_step GE) pc fp pc'.
  Proof.
    induction 1;intros;auto. constructor.
    econstructor;eauto. left.
    apply npnswstep_l1 in H;Hsimpl.
    eapply type_glob_step_elim in H;eauto.
  Qed.
  Lemma atomblockstarN_non_evt_star:
    forall i l pc fp pc',
      atomblockstarN GE i l pc fp pc'->
      non_evt_star glob_step pc fp pc'.
  Proof.
    induction i;intros. inversion H;subst;constructor.
    apply atomblockstarN_atomO in H as ?.
    destruct H0.
    inversion H;subst.
    apply swstar_noevt_stepN in H5.
    apply noevt_stepN_sound in H5.
    assert(non_evt_star glob_step pc1 fp2 pc2).
    destruct H4. eapply atomblockstep_noevtstar;eauto.
    rewrite<- FP.fp_union_emp with(fp:=fp2).
    econstructor 2. apply type_glob_step_elim in H2;eauto.
    constructor. apply npnsw_taustar_non_evt_star in H3.
    eapply non_evt_star_cons in H2;eauto.
    eapply non_evt_star_cons in H5;eauto.
    apply IHi in H6.
    eapply non_evt_star_cons in H6;eauto.
    rewrite FP.fp_union_emp in H5. auto.
  Qed.
  Lemma Odiverge_not_will_neverIdiverge_inv:
    forall pc,
      Odiverge pc ->
      ~ will_neverIdiverge pc ->
      exists fp pc' fp' pc'',
        npnsw_or_sw_star GE pc fp pc' /\
        atomblockstarN GE 1 (cons (cur_tid pc') nil) pc' fp' pc'' /\
        Odiverge pc'' /\
        ~ will_neverIdiverge pc''.
  Proof.
    intros.
    unfold will_neverIdiverge in H0.
    apply not_and_or in H0.
    destruct H0;[contradiction|].
    assert(~ neverIdiverge pc).
    intro;contradict H0.
    Esimpl;eauto. constructor.
    unfold neverIdiverge in H1.
    apply not_and_or in H1 as []. contradiction.
    apply NNPP in H1.
    Hsimpl.

    apply noevt_stepN_exists in H1 as [].
    revert pc x x0 x1 x2 H H0 H1 H2 H3.
    induction x3 as [x3 IHx3] using(well_founded_induction lt_wf);intros.
    destruct x3.
    {
      apply noevt_stepN_0 in H1 as [];subst.
      assert(atom_bit pc = O). inversion H;subst;auto. inversion H5;auto. inversion H5;auto.
      apply swstar_npnsw_or_sw_stepN in H4;auto.
      apply npnsw_or_sw_stepN_sound in H4.
      Esimpl;eauto. unfold will_neverIdiverge.
      intro. destruct H5.
      Hsimpl.
      contradict H0.
      apply atomblockstarN_non_evt_star in H2.
      apply npnsw_or_sw_star_non_evt_star in H4.
      eapply non_evt_star_cons in H2;try apply H4.
      eapply non_evt_star_cons in H6;eauto.
    }
    {
      assert(ThreadPool.inv pc.(thread_pool) /\ atom_bit pc = O /\ atom_bit x0 = O).
      Esimpl; try (inversion H;auto;fail).
      inversion H;subst;inversion H5;auto.
      apply atomblockstarN_atomO in H2 as [];auto.
      Hsimpl.
      apply noevt_stepN_Si_inv2 in H1;auto.
      Hsimpl.
      destruct H7;Hsimpl.
      {
        apply O_globtaustep in H7 as ?;auto.
        assert(Odiverge x6).
        apply noevt_stepN_sound in H9.
        apply atomblockstarN_non_evt_star in H2.
        eapply non_evt_star_cons in H2;eauto.
        eapply non_evt_star_cons_Odiverge;eauto.
        rewrite H8. rewrite (swstar_l1 _ _ _ H1). auto.
        rewrite (swstar_l1 _ _ _ H1) in H7.
        apply GE_mod_wd_tp_inv in H7;auto.
        destruct H12 as [R | R].
        {
          eapply IHx3 in H9;eauto;[|Lia.lia|].
          Hsimpl.
          eapply npnsw_step_cons_npnsw_or_sw_star in H9;eauto.
          eapply swstar_cons_npnsw_or_sw_star in H1 as ?;eauto.
          Esimpl;try apply H12;eauto.

          intro;Hsimpl.
          contradict H0.
          apply tau_plus_1 in R. apply tau_plus2star in R.
          apply npnsw_taustar_non_evt_star in R.
          apply swstar_noevt_stepN in H1. apply noevt_stepN_sound in H1.
          eapply non_evt_star_cons in R;eauto.
          eapply non_evt_star_cons in H12;eauto.
        }
        {
          eapply swstar_cons_npnsw_or_sw_star in H1;[|econstructor;constructor].
          Esimpl;try apply H1;try apply H13;eauto.

          econstructor 2.
          constructor. eauto. constructor. constructor.
          apply Odiverge_O in H13 as [];auto.

          unfold will_neverIdiverge.
          intro;Hsimpl.
          eapply ETrace.ne_star_step in H14;[|left;apply H7].
          apply npnsw_or_sw_star_non_evt_star in H1.
          eapply non_evt_star_cons in H14;eauto.
        }        
      }
      {
        assert(Odiverge x6).
        apply noevt_stepN_sound in H9.
        apply atomblockstarN_non_evt_star in H2.
        eapply non_evt_star_cons in H2;eauto.
        eapply non_evt_star_cons_Odiverge;eauto.
        unfold atomblockstep,atomblockN in H7;Hsimpl.
        inversion H14;auto.
        apply atomblockstep_invpc_preserve in H7;auto.
        rewrite (swstar_l1 _ _ _ H1);auto.

        eapply swstar_cons_npnsw_or_sw_star in H1;[|econstructor;constructor].
        Esimpl.  eauto. econstructor 2. constructor. left;eauto. constructor.
        constructor. apply Odiverge_O in H12 as [];auto.
        auto.
        unfold will_neverIdiverge;intro;Hsimpl.
        eapply atomblockstep_noevtstar in H7.
        eapply npnsw_or_sw_star_non_evt_star in H1.
        eapply non_evt_star_cons in H14;eauto.
        eapply non_evt_star_cons;eauto.
      }
    }
  Qed.


  CoInductive blockdiverge:@ProgConfig GE->Prop:=
    cons_npnsw_or_sw_star_block:
      forall pc fp pc' fp' pc'',
        atom_bit pc = O ->
        ThreadPool.inv pc.(thread_pool)->
        npnsw_or_sw_star GE pc fp pc'->
        atomblockstarN GE 1 (cons (cur_tid pc') nil) pc' fp' pc'' ->
        blockdiverge pc''->
        blockdiverge pc.
  Lemma Odiverge_not_will_neverIdiverge_atomblockdiverge:
    forall pc,
      Odiverge pc ->
      ~ will_neverIdiverge pc ->
      blockdiverge pc.
  Proof.
    cofix;intros.
    apply Odiverge_O in H as ?.
    apply Odiverge_not_will_neverIdiverge_inv in H;try apply H0.
    Hsimpl.
    econstructor;eauto.
  Qed.
  Lemma psilent_diverge_case:
    forall pc,
      atom_bit pc = O ->
      ThreadPool.inv pc.(thread_pool)->
      psilent_diverge pc ->
      (exists i fp pc', noevt_stepN glob_step (S i) pc fp pc' /\ core_Idiverge pc') \/
      (exists fp pc', non_evt_star glob_step pc fp pc' /\ npnswdiverge pc')\/
      blockdiverge pc.
  Proof.
    intros.
    apply psilent_diverge_inv2 in H1 as ?;auto.
    destruct H2.
    {
      assert(will_neverIdiverge pc \/ ~ will_neverIdiverge pc).
      apply classic.
      destruct H3.
      unfold will_neverIdiverge in H3. Hsimpl.
      right;left. apply Odiverge_neverIdiverge_npnswdiverge in H5.
      Esimpl;eauto.

      apply O_psilent_diverge_Odiverge in H2;auto.
      apply Odiverge_not_will_neverIdiverge_atomblockdiverge in H3;auto.
    }
    {
      Hsimpl.
      apply core_Idiverge_I_psilent_diverge_exists in H3.
      left;eauto.
    }
  Qed.
End silent_diverge.
Section diverge_proof.
  Lemma noevt_stepN_Si_Iinv_drfsafe:
    forall ge pc i fp pc',
      @drf_pc_glob ge pc ->
      noevt_stepN ge glob_step (S i) pc fp pc'->
      atom_bit pc' = I->
      exists i l fp1 fp2 pc0 pc1 pc2 pc3 t pc4 fp3,
        sw_star glob_step pc pc0 /\
        atomblockstarN ge i l pc0 fp1 pc1 /\
        npnsw_or_sw_star ge pc1 fp2 pc2 /\
        type_glob_step entat ({-|pc2,t}) tau FP.emp pc3 /\ tau_star (type_glob_step core) pc3 fp3 pc4 /\ mem_eq_pc ge pc' pc4.
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as ?. destruct H2 as [v1 wdge].
    specialize (drf_pc_glob_l2 _ _ H) as modwdge.
    inversion H as [O1 _].
    eapply noevt_stepN_OI in H0;eauto.
    Hsimpl.
    destruct x.
    {
      apply noevt_stepN_0 in H0 as [];subst.
      apply swstar_l1 in H6.
      apply tauN_taustar in H3.
      exists 0,nil,FP.emp,FP.emp,pc, pc,pc,x2,(cur_tid x1),pc',x4.
      rewrite<- H6. 
      Esimpl;eauto;try (constructor;auto;fail).
      econstructor;constructor.
      apply mem_eq_pc_refl.
    }
    {
      assert(L1:invpc ge x1).
      apply noevt_stepN_sound in H0.
      apply non_evt_star_star in H0 as [].
      eapply GE_mod_wd_star_tp_inv2 in H0;eauto.
      assert(atom_bit x1 = O). inversion H2;auto.
      apply noevt_stepN_Si_to_atomblockstarN in H0;auto;[|Lia.lia].
      Hsimpl.
      destruct H7 as [|[|[]]].
      {
        revert v1 wdge modwdge H H0 H7. clear. intros.
        unfold drf_pc_glob,drf_pc in H.
        Hsimpl.
        apply atomblockstarN_star in H2 as ?.
        Hsimpl.
        apply swstar_globstar in H0;Hsimpl.
        eapply cons_star_star in H8;eauto.
        eapply cons_star_star in H8;eauto.
        apply predicted_abort1_star_abort in H3;Hsimpl.
        eapply cons_star_star in H3;eauto.
        eapply H7 in H3;eauto.
        contradiction.
      }
      {
        unfold drf_pc_glob,drf_pc in H.
        Hsimpl.
        unfold drfpc in H8.
        contradict H8.
        rewrite (swstar_l1 _ _ _ H0) in H7.
        eapply race_changetid with(t:=cur_tid pc) in H7;simpl in H7;rewrite pc_cur_tid in H7.
        apply globrace_equiv in H7;auto.
        pose proof predict_equiv.
        eapply predict_equiv_to_star_race_equiv in H7;eauto.
        apply star_race_equiv in H7.
        unfold star_race_config in H7. Hsimpl.
        eapply cons_star_star in H7;try apply H9.
        unfold star_race_config;Esimpl;eauto.
      }
      {
        unfold drf_pc_glob,drf_pc,drfpc in H;Hsimpl.
        contradict H8.
        apply globrace_equiv in H9;auto.
        pose proof predict_equiv.
        eapply predict_equiv_to_star_race_equiv in H9;eauto.
        apply star_race_equiv in H9.
        unfold star_race_config in H9. Hsimpl.
        apply atomblockstarN_star in H7 as [].
        apply swstar_globstar in H0;Hsimpl.
        do 3 (eapply cons_star_star in H9;eauto).
        unfold star_race_config. Esimpl;eauto.
        apply atomblockstarN_invpc_preservation in H7;auto.
        rewrite (swstar_l1 _ _ _ H0);auto.
      }
      {
        Hsimpl.
        apply type_glob_step_cur_valid_id in H2 as ?;try congruence.
        eapply mem_eq_globstep in H9 as ?;eauto.
        Hsimpl.
        eapply mem_eq_coreN in H13 ;eauto;Hsimpl.
        apply tauN_taustar in H13.
        Esimpl;eauto.
      }
    }
  Qed.
  Lemma noevt_stepN_Si_Oinv_drfsafe:
    forall ge pc i fp pc',
      @drf_pc_glob ge pc ->
      noevt_stepN ge glob_step (S i) pc fp pc'->
      atom_bit pc' = O->
      exists i l fp1 fp2 pc0 pc1 pc2,
        sw_star glob_step pc pc0 /\
        atomblockstarN ge i l pc0 fp1 pc1 /\
        npnsw_or_sw_star ge pc1 fp2 pc2 /\
        mem_eq_pc ge pc' ({-|pc2,cur_tid pc'}).
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as ?. destruct H2 as [v1 wdge].
    specialize (drf_pc_glob_l2 _ _ H) as modwdge.
    inversion H as [O1 _].
    apply noevt_stepN_Si_to_atomblockstarN in H0;auto;[|Lia.lia].
    Hsimpl.
    destruct H2 as [|[|[]]].
    {
      revert v1 wdge modwdge H H0 H2. clear. intros.
      unfold drf_pc_glob,drf_pc in H.
      Hsimpl.
      apply atomblockstarN_star in H2 as ?.
      Hsimpl.
      apply swstar_globstar in H0;Hsimpl.
      eapply cons_star_star in H8;eauto.
      eapply cons_star_star in H8;eauto.
      apply predicted_abort1_star_abort in H3;Hsimpl.
      eapply cons_star_star in H3;eauto.
      eapply H7 in H3;eauto.
      contradiction.
    }
    {
      unfold drf_pc_glob,drf_pc,drfpc in H.
      Hsimpl.
      contradict H3.
      rewrite (swstar_l1 _ _ _ H0) in H2.
      eapply race_changetid with(t:=cur_tid pc) in H2;simpl in H2;rewrite pc_cur_tid in H2.
      apply globrace_equiv in H2;auto.
      pose proof predict_equiv.
      eapply predict_equiv_to_star_race_equiv in H2;eauto.
      apply star_race_equiv in H2.
      unfold star_race_config in H2. Hsimpl.
      eapply cons_star_star in H2;try apply H4.
      unfold star_race_config;Esimpl;eauto.
    }
    {
      unfold drf_pc_glob,drf_pc,drfpc in H;Hsimpl.
      contradict H3.
      apply globrace_equiv in H4;auto.
      pose proof predict_equiv.
      eapply predict_equiv_to_star_race_equiv in H4;eauto.
      apply star_race_equiv in H4.
      unfold star_race_config in H4. Hsimpl.
      apply atomblockstarN_star in H2 as [].
      apply swstar_globstar in H0;Hsimpl.
      do 3 (eapply cons_star_star in H4;eauto).
      unfold star_race_config. Esimpl;eauto.
      apply atomblockstarN_invpc_preservation in H2;auto.
      rewrite (swstar_l1 _ _ _ H0);auto.
    }
    {
      Hsimpl.
      Esimpl;eauto.
    }
  Qed.

  Lemma glob_npnsw_step_atomblockstarN_inv_ex_drfsafe:
    forall ge pc l fp pc',
      drf_pc_glob pc ->
      glob_npnsw_step pc l fp pc'->
      forall t fp1 pc1 ltids,
        t <> cur_tid pc->
        atomblockstarN ge 1 ltids ({-|pc',t}) fp1 pc1->
        FP.smile fp fp1 /\ exists pc',atomblockstarN ge 1 ltids ({-|pc,t}) fp1 pc'/\ exists pc'',glob_npnsw_step pc' l fp pc'' /\ mem_eq_pc ge pc1 ({-|pc'',cur_tid pc1}) /\ cur_tid pc'' = cur_tid pc.
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as ?.
    specialize (drf_pc_glob_l2 _ _ H) as ?.
    Hsimpl.
    apply npnsw_step_thdpinv in H0 as v1;eauto.
    apply atomblockstarN_cur_valid_tid in H2 as v2;auto.
    eapply npnswstep_pc_valid_tid_backwards_preservation in H0 as v3;eauto.
    eapply glob_npnsw_step_atomblockstarN_inv_ex_case in H0;eauto.

    assert(v4:glob_step pc sw FP.emp ({-|pc,t})).
    inversion H as [? _].
    destruct pc,v3;simpl in *;subst;econstructor;eauto.

    
    destruct H0 as [|[|]];Hsimpl.
    {
      simpl in *.
      apply predicted_abort1_star_abort in H0 as ?;Hsimpl.
      unfold drf_pc_glob,drf_pc,drfpc in H.
      Hsimpl.
      eapply star_step in v4;eauto.
      eapply cons_star_star in v4;eauto.
      eapply H12 in v4;eauto.
      congruence.
    }
    {
      unfold drf_pc_glob,drf_pc,drfpc in H.
      Hsimpl.
      contradict H6.
      apply globrace_equiv in H0;auto.
      pose proof predict_equiv.
      eapply predict_equiv_to_star_race_equiv in H0;eauto.
      apply star_race_equiv in H0.
      unfold star_race_config in H0. Hsimpl.
      eapply cons_star_star in H0;eauto.
      unfold star_race_config;Esimpl;eauto.
    }
    {
      simpl in *.
      Esimpl;eauto.
    }
  Qed.

  Lemma npnsw_or_sw_star_atomblockstarN_ex_drfsafe:
    forall i l ge pc fp pc' fp' pc'' ltids (drfsafe:drf_pc_glob pc),
      npnsw_or_sw_stepN ge i l pc fp pc'->
      atomblockstarN ge 1 ltids pc' fp' pc''->
      exists fp1 pc1,
        atomblockstarN ge 1 ltids ({-|pc,cur_tid pc'}) fp1 pc1 /\
        exists fp2 pc2,
          npnsw_or_sw_star ge pc1 fp2 pc2 /\ mem_eq_pc ge ({-|pc'',cur_tid pc2}) pc2.
  Proof.
    induction i;intros.
    apply npnsw_or_sw_stepN_0 in H; Hsimpl;subst.
    apply swstar_l1 in H2. rewrite <- H2.
    Esimpl;eauto. econstructor. constructor. rewrite pc_cur_tid;apply mem_eq_pc_refl.

    apply npnsw_or_sw_stepN_inv1 in H;[|Lia.lia].
    Hsimpl.
    assert(S i -1 = i). Lia.lia.
    rewrite H5 in H2;clear H5.
    eapply IHi in H2;eauto.
    Hsimpl.

    assert(cur_tid x0 = cur_tid pc' \/ cur_tid x0 <> cur_tid pc').
    apply classic.
    destruct H7.

    apply npnsw_step_tid_preservation in H1 as ?.
    rewrite <- H7,pc_cur_tid in H2.
    assert(ltids = cons (cur_tid x0) nil).
    inversion H2;subst;auto. inversion H13;subst;auto. subst.
    eapply npnswstep_cons_atomblockstarN in H1 as ?;eauto.
    rewrite (swstar_l1 _ _ _ H),<- H8 in H3;auto.
    rewrite <- H7,<- H8. Esimpl;eauto.

    eapply glob_npnsw_step_atomblockstarN_inv_ex_drfsafe in H1;eauto.
    Hsimpl.
    rewrite (swstar_l1 _ _ _ H) in H8;auto. simpl in H8.
    eapply mem_eq_npnsw_or_sw_star in H10;eauto. Hsimpl.

    do 3 eexists;eauto.
    {
      assert(cur_tid x10 = cur_tid x7). inversion H12 as (?&?&?&?);subst;auto.
      eapply mem_eq_pc_trans in H12;eauto.
      rewrite <- H13 in H12.
      assert(ThreadPool.inv x8.(thread_pool) /\ GlobEnv.wd ge /\ atom_bit x8 = O).
      apply drf_pc_glob_l1 in drfsafe as [].
      eapply atomblockstarN_invpc_preservation in H8 as ?;eauto.
      apply atomblockstarN_atomO in H8 as [];eauto.
      revert H9 H10 H12 H14. clear;intros.
      inversion H10;subst.
      inversion H;subst.
      {
        simpl in *.
        exists (FP.union x1 FP.emp),x9.
        split. econstructor. econstructor;eauto. left;eauto. constructor.
        eapply mem_eq_pc_change in H12;eauto.
      }
      {
        destruct H0.
        {
          Hsimpl.
          apply npnsw_step_thdpinv in H9 as ?;auto.
          apply npnsw_step_cur_valid_id in H0 as ?;auto.
          assert(atom_bit x9 = O). destruct H9 as [|[]];inversion H7;subst;auto.
          assert(type_glob_step glob_sw x9 sw FP.emp ({-|x9,cur_tid x5})).
          destruct x9,H6;simpl in *;subst; econstructor;eauto.
          eapply star_step in H;[|right;eauto].
          eapply star_step in H;[|left;eauto].
          Esimpl;eauto. econstructor;eauto.
        }
        {
          assert(type_glob_step glob_sw x9 e fp1 s2).
          destruct x9,s2;inversion H0;subst. econstructor;eauto.
          eapply star_step in H1;[|right;eauto].
          eapply star_step in H1;[|left;eauto].
          Esimpl;eauto. econstructor;eauto.
        }
      }
    }
    
    
    apply drf_pc_glob_l1 in drfsafe as [];auto.
    eapply drf_pc_glob_l2;eauto.
    apply swstar_globstar in H .
    Hsimpl.
    apply npnswstep_l1 in H1 as ?. Hsimpl.
    apply type_glob_step_elim in H8.
    eapply star_cons_step in H8 as [] ;eauto.
    eapply drf_pc_glob_cons;eauto.
    apply atomblockstarN_atomO in H2 as [];auto.
    destruct H1 as [|[]];inversion H1;subst;auto.
    apply npnsw_step_tid_preservation in H1. congruence.

    apply swstar_globstar in H as ?;Hsimpl.
    apply npnswstep_l1 in H1 as ?. Hsimpl.
    apply type_glob_step_elim in H6.
    eapply star_cons_step in H6 as [] ;eauto.
    eapply drf_pc_glob_cons;eauto.
    rewrite (swstar_l1 _ _ _ H) in H1;auto.
    inversion drfsafe.
    destruct H1 as [|[]];inversion H1;subst;auto.

  Qed.


  CoInductive blockdiverge_tid{ge:GlobEnv.t} :@ProgConfig ge->tid->Prop:=
  | cons_blockdiverge_tid:
      forall pc  fp pc' fp' pc'' t,
        atom_bit pc = O->
        ThreadPool.inv pc.(thread_pool)->
        npnsw_or_sw_star ge pc fp pc'->
        atomblockstarN ge 1 (cur_tid pc'::nil) pc' fp' pc''->
        blockdiverge_tid pc'' t->
        blockdiverge_tid pc (cur_tid pc').

  Lemma blockdiverge_tid_exists_lemma:
    forall ge pc fp pc' fp' pc'',
       atom_bit pc = O->
       ThreadPool.inv pc.(thread_pool)->
       npnsw_or_sw_star ge pc fp pc'->
       atomblockstarN ge 1 (cur_tid pc'::nil) pc' fp' pc''->
       blockdiverge ge pc'' ->
       blockdiverge_tid pc (cur_tid pc').
  Proof.
    cofix.
    intros.
    inversion H3;subst.
    econstructor;eauto.
  Qed.

  Lemma blockdiverge_tid_exists:
    forall ge pc,
      blockdiverge ge pc->
      exists t,blockdiverge_tid pc t.
  Proof. inversion 1;subst. eapply blockdiverge_tid_exists_lemma in H4;eauto. Qed.
  Lemma non_evt_star_cons_step:
    forall ge pc fp pc' fp' pc'',
      non_evt_star np_step pc fp pc'->
      non_evt_plus np_step pc' fp' pc''->
      non_evt_plus (@np_step ge) pc (FP.union fp fp') pc''.
  Proof.
    induction 1;intros.
    rewrite FP.emp_union_fp;auto.
    Hsimpl. rewrite<- FP.fp_union_assoc.
    destruct H.
    eapply SimEtr.ne_star_step. left;eauto. eauto. eauto.
    eapply SimEtr.ne_star_step. right;eauto. eauto. eauto.
  Qed.
  Lemma atomblockstarN_NP_drfsafe:
    forall ge l pc fp pc' t,
      drf_pc_glob pc ->
      atomblockstarN ge 1 l pc fp pc'->
      blockdiverge_tid  pc' t->
      exists pc1,non_evt_star np_step pc fp pc1/\
            ((exists t,np_step pc1 sw FP.emp ({-|pc',t}) )).
  Proof.
    intros.
    apply drf_pc_glob_l1 in H as ?. Hsimpl.
    specialize (drf_pc_glob_l2 _ _  H) as ?.
    apply atomblockstar1_np in H0;auto.
    Hsimpl.
    destruct H5;eauto.
    inversion H1;subst.
    inversion H8;subst.
    inversion H11;subst.
    {
      apply atomblockstarN_cur_valid_tid in H9;auto.
      inversion H5;subst.
      destruct H9 as [L R].
      eapply H_all_thread_halted in L;eauto.
      contradiction.
    }
    {
      destruct H12.
      apply npnsw_step_cur_valid_id in H12;auto.
      inversion H5;subst. destruct H12 as [L R].
      eapply H_all_thread_halted in L;eauto.
      contradiction.

      inversion H12;subst.
      inversion H5;subst.
      eapply H_all_thread_halted in H_thread_valid.
      contradiction.
    }
  Qed.
  Lemma npnsw_or_sw_star_cons_blockdiverge:
    forall ge pc fp pc' t,
      ThreadPool.inv pc.(thread_pool)-> atom_bit pc = O->
      npnsw_or_sw_star ge pc fp pc' ->
      blockdiverge_tid  pc' t->
      blockdiverge_tid  pc t.
  Proof.
    inversion 4;subst. unfold npnsw_or_sw_star in *. Hsimpl.
    eapply cons_star_star in H5;eauto.
    econstructor;eauto.  econstructor;eauto.
  Qed.
  Lemma mem_eq_blockdiverge_tid:
    forall ge pc pc' t (wdge:GlobEnv.wd ge)(modwdge:forall ix,mod_wd (GlobEnv.modules ge ix)),
      mem_eq_pc ge pc pc'->
      blockdiverge_tid pc t->
      blockdiverge_tid pc' t.
  Proof.
    cofix.
    inversion 4;subst.
    assert(o1:atom_bit pc' = O). destruct H;Hsimpl;congruence.
    assert(o2:ThreadPool.inv (thread_pool pc')). destruct H;Hsimpl;congruence.
    eapply mem_eq_npnsw_or_sw_star in H;try apply H3;try assumption.
    Hsimpl.
    eapply mem_eq_atomblockstarN in H6;try apply H4;try apply modwdge.
    Hsimpl.
    assert(cur_tid pc'0 = cur_tid x).
    inversion H6;subst;auto.
    rewrite H8 in *.
    econstructor;eauto.
  Qed.

  Lemma blockdiverge_changetid:
    forall ge pc t (wdge:GlobEnv.wd ge),
      blockdiverge_tid pc t->
      forall i,
        @blockdiverge_tid ge ({-|pc,i}) t.
  Proof.
    intros.
    inversion H;subst.
    inversion H2;subst.
    inversion H5;subst.
    {
      apply atomblockstarN_cur_valid_tid in H3 as ?;auto.
      assert(type_glob_step glob_sw ({-|pc',i}) sw FP.emp ({-|pc',cur_tid pc'})).
      destruct pc',H6;simpl in *;subst;econstructor;eauto.
      econstructor;eauto. econstructor. econstructor 2. right;eauto. rewrite pc_cur_tid. constructor.
    }
    {
      destruct H6.
      {
        apply npnsw_step_cur_valid_id in H6 as ?;auto.
        assert(type_glob_step glob_sw ({-|pc,i}) sw FP.emp pc).
        destruct pc,H8;simpl in *;subst;econstructor;eauto.
        eapply star_step in H7;[|left;eauto].
        eapply star_step in H7;[|right;eauto].
        econstructor;eauto. econstructor;eauto.
      }
      {
        assert(type_glob_step glob_sw ({-|pc,i}) sw FP.emp s2).
        inversion H6;subst;econstructor;eauto.
        eapply star_step in H7;[|right;eauto].
        econstructor;eauto. econstructor;eauto.
      }
    }
  Qed.
  Lemma blockdiverge_valid_tid:
    forall ge pc t,
      ThreadPool.inv pc.(thread_pool)->
      GlobEnv.wd ge->
      blockdiverge_tid pc t->
      @pc_valid_tid ge pc t.
  Proof.
    inversion 3;subst.
    apply npnsw_or_sw_star_non_evt_star in H4.
    apply non_evt_star_star in H4;Hsimpl.
    apply GE_mod_wd_star_tp_inv2 in H4 as ?;auto.
    apply atomblockstarN_cur_valid_tid in H5;auto;try congruence.
    eapply pc_valid_tid_back_star in H4;eauto.
  Qed.
    
  Lemma blockdiverge_tid_npdiverge:
    forall ge pc t,
      drf_pc_glob pc ->
      blockdiverge_tid pc t ->
      Pdiverge ge ({-|pc,t}).
  Proof.
    cofix.
    intros.
    inversion H0;subst.
    inversion H as [R1 _].
    apply npnsw_or_sw_stepN_exists in H3;Hsimpl;try assumption.
    eapply npnsw_or_sw_star_atomblockstarN_ex_drfsafe in H4 as ?;try apply H;try apply H3.
    Hsimpl.
    apply drf_pc_glob_l1 in H as ?. destruct H9 as [_ ?].
    apply atomblockstarN_atomO in H6 as ?. destruct H10 as [R2 R3].
    
    apply atomblockstarN_invpc_preservation in H6 as R;try assumption.

    apply atomblockstarN_cur_valid_tid in H6 as ?;try eassumption;[|Lia.lia].
    apply blockdiverge_changetid with(i:=cur_tid x4) in H5;try assumption.
    specialize (drf_pc_glob_l2 _ _ H) as ?.
    eapply mem_eq_blockdiverge_tid in H8;try apply H5;try assumption.
    eapply npnsw_or_sw_star_cons_blockdiverge in H7;try apply H8;try assumption.
    apply blockdiverge_valid_tid in H7 as ?;try assumption.
    assert(sw_star glob_step x2 ({-|x2,t0})).
    econstructor 2;[|constructor].
    destruct x2,H12;simpl in *;subst;econstructor;eauto.
    eapply atomblockstarN_cons_swstar in H13;try apply H6;try congruence.
    apply blockdiverge_changetid with(i:=t0) in H7;try assumption.
    assert(L:drf_pc_glob ({-|pc,cur_tid pc'})).
    assert(sw_star glob_step pc ({-|pc,cur_tid pc'})).
    econstructor 2;[|constructor].
    destruct pc,H10;simpl in *;subst;econstructor;eauto.
    apply swstar_globstar in H14;Hsimpl.
    eapply drf_pc_glob_cons;eauto.
    eapply atomblockstarN_NP_drfsafe in H13 as ?;try apply H7;try assumption.
    
    Hsimpl. simpl in *.
    assert(sw_star glob_step ({-|x2,x6}) ({-|x2,t0})).
    econstructor 2;[|constructor].
    apply atomblockstarN_atomO in H13 as [];auto.
    destruct x2,H12. simpl in *;subst.  econstructor;eauto.
    eapply npsw_swstar in H15;try apply H16.
    apply ne_plus1 in H15 as ?;[|right;auto].
    eapply non_evt_star_cons_step in H14;try apply H17.
    econstructor. eauto. eapply blockdiverge_tid_npdiverge in H7;eauto.
    eapply atomblockstarN_globstar in H13 as ?.
    Hsimpl.
    eapply drf_pc_glob_cons;eauto.
  Qed.

  Lemma blockdiverge_npsilent_diverge:
    forall ge pc,
      drf_pc_glob pc ->
      blockdiverge ge pc->
      exists t, npsilent_diverge ge ({-|pc,t}) /\ pc_valid_tid pc t.
  Proof.
    intros.
    apply blockdiverge_tid_exists in H0 as [].
    apply drf_pc_glob_l1 in H as ?;Hsimpl.
    apply blockdiverge_valid_tid in H0 as ?;auto.
    apply blockdiverge_tid_npdiverge in H0;auto.
    Esimpl;eauto. apply Pdiverge_sound in H0. apply Sdiverge_sound in H0;auto.
  Qed.

  


  Lemma npnsw_or_sw_stepN_last_valid:
    forall i l ge pc fp pc' (wdge:GlobEnv.wd ge),
      ThreadPool.inv pc.(thread_pool)->
      npnsw_or_sw_stepN ge (S i) l pc fp pc'->
      cur_valid_id ge pc'.
  Proof.
    induction i;intros.
    apply npnsw_or_sw_stepN_1_inv in H0;Hsimpl.
    apply swstar_l in H2 as [];Hsimpl;subst.
    apply npnsw_step_cur_valid_id in H1 as ?.
    eapply npnsw_step_pc_valid_tid_preservation in H1;eauto. apply npnsw_step_tid_preservation in H1. rewrite <- H1;auto.
    rewrite (swstar_l1 _ _ _ H0);auto.
    inversion H2;subst;split;auto.

    apply npnsw_or_sw_stepN_inv1 in H0;[|Lia.lia].
    Hsimpl.
    eapply IHi in H2;eauto.
    apply npnsw_step_thdpinv in H1;auto.
    rewrite (swstar_l1 _ _ _ H0);auto.
  Qed.

  Lemma npnsw_cons_npnsw_or_sw_stepN_sw:
    forall ge pc fp pc' t fp' pc'' i l,
      GlobEnv.wd ge->
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = O->
      @glob_npnsw_step ge pc tau fp pc'->
      npnsw_or_sw_stepN ge (S i) l ({-|pc',t}) fp' pc''->
      npnsw_or_sw_stepN ge (S (S i)) (cons (cur_tid pc) l) pc (FP.union fp fp') pc''.
  Proof.
    inversion 5;subst;apply npnsw_step_thdpinv in H2 as ?;auto.
    eapply npnsw_step_cur_valid_id in H5 as ?;eauto.
    assert(type_glob_step glob_sw pc' sw FP.emp ({-|pc',t})).
    apply npnsw_step_O_preservation in H2;auto.
    destruct pc',H7;simpl in *;subst;econstructor;eauto.
    
    eapply npnsworsw_conssw in H3;eauto.
    eapply npnsworsw_consnpnsw in H3;eauto.

    assert(type_glob_step glob_sw pc' l0 fp0 pc'0).
    destruct pc';inversion H4;subst. econstructor;eauto.
    eapply npnsworsw_conssw in H5;eauto.
    eapply npnsworsw_consnpnsw in H5;eauto.
  Qed.
  Lemma npnsw_or_sw_star_div:
    forall k lt ge pc fp pc' ,
      drf_pc_glob pc->
      npnsw_or_sw_stepN ge k lt pc fp pc' ->
      exists i l fp1 pc1 fp2 pc2,
        tau_star glob_npnsw_step ({-|pc,cur_tid pc'}) fp1 pc1 /\
        npnsw_or_sw_stepN ge i l pc1 fp2 pc2 /\ mem_eq_pc ge pc' pc2 /\ 
        ~ list_matched l (cur_tid pc').
  Proof.
    induction k;intros.
    
    apply npnsw_or_sw_stepN_0 in H0;Hsimpl;subst.
    Esimpl. constructor. constructor. inversion H;auto.
    rewrite (swstar_l1 _ _ _ H2);apply mem_eq_pc_refl.
    unfold list_matched;intro;Hsimpl.
    rewrite Coqlib.nth_error_nil in H0. inversion H0.
    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge1].
    pose proof drf_pc_glob_l2 _ _  H as modwdge.
    apply npnsw_or_sw_stepN_last_valid in H0 as L';auto.
    apply npnsw_or_sw_stepN_sound in H0 as L.
    apply npnsw_or_sw_star_non_evt_star in L.
    apply non_evt_star_star in L as [? L].
    eapply pc_valid_tid_back_star in L;eauto.
    clear x.
    apply npnsw_or_sw_stepN_inv1 in H0;[|Lia.lia].
    Hsimpl.
    enough(drf_pc_glob x0).
    assert(S k -1 = k). Lia.lia.
    rewrite H6 in H2. clear H6.
    eapply IHk in H2 as ?;eauto.
    Hsimpl.

    assert(cur_tid x0 = cur_tid pc' \/ cur_tid x0 <> cur_tid pc').
    apply classic.
    destruct H10.
    + rewrite <- H10,pc_cur_tid in H6.
      eapply tau_star_cons in H6;eauto.
      apply npnsw_step_tid_preservation in H1 as ?.
      rewrite (swstar_l1 _ _ _ H0),H11,H10 in H6.
      Esimpl;eauto.
    + enough(FP.smile x1 x6).
      pose proof H1 as L0.
      rewrite <- pc_cur_tid with(pc:=x) in H1 ;eapply npnswstep_star_reorder in H1;try apply H6;eauto.
      Hsimpl.
      eapply mem_eq_npnsw_or_sw_stepN in H13 as ?;eauto.
      Hsimpl.
      destruct x4.
      {
        apply npnsw_or_sw_stepN_0 in H14 as ?;Hsimpl;subst.
        apply npnsw_taustar_tid_preservation in H6 as ?. simpl in H3.
        rewrite <- H3 in *. apply npnsw_or_sw_stepN_sound in H2.
        apply swstar_l1 in H0.
        apply npnsw_step_tid_preservation in L0 as ?.
        apply npnsw_step_cur_valid_id in L0 as ?;[|rewrite H0];auto.
        eapply npnsw_step_pc_valid_tid_preservation in L0 as ?;eauto.
        apply drf_pc_glob_l1 in H5 as?. Hsimpl. rewrite H4 in H17.
        assert(pc_valid_tid x (cur_tid pc')).
        rewrite H0;auto.
        assert(atom_bit x11 = O).
        apply npnsw_taustar_O_preservation in H1.
        apply npnsw_step_O_preservation in H12;auto. rewrite H0;inversion H;auto.
        eapply npnsw_taustar_pc_valid_tid_preservation in H1 as ?;eauto.
        eapply npnsw_step_pc_valid_tid_preservation in H12 as ?;eauto.
        assert(type_glob_step glob_sw x11 sw FP.emp ({-|x11,cur_tid pc'})).
        destruct x11,H24;simpl in *;subst;econstructor;eauto.
        eapply npnsworsw_conssw in H14;eauto.
        eapply npnsworsw_consnpnsw in H14;eauto. simpl in *.

        eapply npnsw_taustar_pc_valid_tid_preservation in H1 as ?;try apply H16;eauto.
        assert(atom_bit x10 = O).
        apply npnsw_taustar_O_preservation in H1;auto. rewrite H0. inversion H;auto.
        assert(type_glob_step glob_sw x10 sw FP.emp ({-|x10,cur_tid x})).
        destruct x10,H26;simpl in *;subst;econstructor;eauto.
        eapply npnsworsw_conssw in H14;eauto.

        rewrite H0 in H1;simpl in H1.
        Esimpl;eauto. eapply mem_eq_pc_trans;eauto.
        unfold list_matched. intro;Hsimpl.
        destruct x4. simpl in H29. inversion H29. congruence.
        simpl in H29.
        rewrite Coqlib.nth_error_nil in H29. inversion H29.
      }
      
      enough (npnsw_or_sw_stepN ge (S (S x4))(cons (cur_tid x) x5) x10 (FP.union x1 x8) x12).
      rewrite (swstar_l1 _ _ _ H0) in H1;simpl in H1.
      Esimpl;try apply H16;eauto. eapply mem_eq_pc_trans;eauto.
      intro;contradict H9. unfold list_matched in *. Hsimpl.
      destruct x13. simpl in H9. inversion H9;subst. apply npnsw_step_tid_preservation in L0. congruence.
      simpl in H9. eauto.
      

      assert(atom_bit pc = O). inversion H;auto.
      rewrite (swstar_l1 _ _ _ H0) in H1.
      apply npnsw_taustar_O_preservation in H1 as ?;auto.
      apply npnsw_taustar_thdpinv in H1 as ?;auto.
      
      eapply npnsw_cons_npnsw_or_sw_stepN_sw in H14;try apply H12;eauto.
      simpl in H14.

      enough(type_glob_step glob_sw x10 sw FP.emp ({-|x10,cur_tid x})).
      eapply npnsworsw_conssw in H14;eauto.
      rewrite FP.emp_union_fp in H14;auto.

      apply npnsw_step_cur_valid_id in H12;auto.
      destruct x10,H12;simpl in *;subst. econstructor;eauto.

      intro;try congruence.
      apply npnsw_step_tid_preservation in H1;simpl in H1. congruence.

      rewrite (swstar_l1 _ _ _ H0);auto.

      apply NNPP;intro.
      apply smile_conflict in H11.

      rewrite <- pc_cur_tid with(pc:=x) in H1;eapply npnswstep_star_conflict in H1 as ?;eauto.
      destruct H12.

      unfold npnsw_star_abort in H12.
      Hsimpl. rewrite (swstar_l1 _ _ _ H0) in H12.
      simpl in H12.
      inversion H as [? _].
      assert(glob_step pc sw FP.emp ({-|pc,cur_tid pc'})).
      destruct pc,L. simpl in *;subst. econstructor;eauto.
      apply npnsw_taustar_to_taustar in H12.
      apply tau_star_to_star in H12 as [].
      eapply star_step in H15;eauto.
      unfold drf_pc_glob,drf_pc in H;Hsimpl.
      eapply cons_star_star in H15;eauto.
      eapply H20 in H15;eauto.

      Hsimpl.
      rewrite (swstar_l1 _ _ _ H0) in H12. simpl in H12.
      rewrite (swstar_l1 _ _ _ H0) in H1;simpl in H1.
      apply npnsw_step_tid_preservation in H1 as ?.
      assert(atom_bit pc = O). inversion H;subst;auto.
      assert(race glob_predict_star_alter pc).
      econstructor. eauto. econstructor. rewrite <- H14;simpl. econstructor 2;[|constructor];eauto. auto. apply npnsw_step_O_preservation in H1;auto.
      econstructor;eauto. apply npnsw_taustar_O_preservation in H12;auto.
      left;intro R;inversion R.
      rewrite FP.fp_union_emp;auto.

      apply globrace_equiv2 in H16;auto.
      unfold star_race in H16;Hsimpl.
      pose predict_equiv.
      eapply predict_equiv_race_equiv in H17;eauto.
      apply race_equiv in H17.
      unfold drf_pc_glob,drf_pc,drfpc in H. Hsimpl.
      
      contradict H18.
      unfold star_race_config.
      eapply cons_star_star in H16;eauto.

      apply npnsw_step_tid_preservation in H1;simpl in H1. congruence.
      rewrite (swstar_l1 _ _ _ H0);auto.

      apply swstar_globstar in H0 as ?;Hsimpl.
      apply npnswstep_l1 in H1 as ?. Hsimpl.
      apply type_glob_step_elim in H6.
      eapply star_cons_step in H6 as [];eauto.
      eapply drf_pc_glob_cons;eauto.
      apply npnsw_step_O_preservation in H1;auto.
      rewrite (swstar_l1 _ _ _ H0). inversion H;auto.
  Qed.


  Lemma npnsw_or_sw_stepN_last_valid_alt:
    forall i l ge pc fp pc' (wdge:GlobEnv.wd ge),
      ThreadPool.inv pc.(thread_pool)->
      npnsw_or_sw_stepN ge (S i) l pc fp pc'->
      pc_valid_tid  pc (cur_tid pc').
  Proof.
    intros.
    eapply npnsw_or_sw_stepN_last_valid in H0 as ?;eauto.
    apply npnsw_or_sw_stepN_sound in H0.
    apply npnsw_or_sw_star_non_evt_star in H0.
    apply non_evt_star_star in H0;Hsimpl.
    eapply pc_valid_tid_back_star ;eauto.
  Qed.
  Lemma thread_sim_refl:
    forall ge pc, thread_sim ge pc pc.
  Proof. unfold thread_sim;intros;Hsimpl;Esimpl;eauto. Qed.
  Lemma thread_sim_comm:
    forall ge pc pc',
      thread_sim ge pc pc'->
      thread_sim ge pc' pc.
  Proof.  unfold thread_sim;intros;Hsimpl;Esimpl;congruence. Qed.
  Lemma thread_sim_trans:
    forall ge pc pc1 pc2,
      thread_sim ge pc pc1->
      thread_sim ge pc1 pc2 ->
      thread_sim ge pc pc2.
  Proof.  unfold thread_sim;intros;Hsimpl;Esimpl;try congruence. Qed.
  Lemma thread_sim_preserve:
    forall ge x pc pc' t fp pc1,
      thread_sim ge ({-|pc,t}) pc'->
      cur_tid pc <> t->
      type_glob_step x pc tau fp pc1->
      x = core \/ x = call \/ x = ret ->
      thread_sim ge ({-|pc1,t}) pc'.
  Proof.
    unfold thread_sim,getcurcs;simpl;intros;Hsimpl.
    destruct H2 as [|[]];subst;inversion H1;subst;simpl in *;subst; Esimpl;eauto; solv_thread;solv_thread;auto.

    destruct Coqlib.peq;try contradiction;auto.
  Qed.
  Lemma thread_sim_preserve2:
    forall ge x pc pc' t fp pc1,
      thread_sim ge pc ({-|pc',t})->
      cur_tid pc' <> t->
      type_glob_step x pc' tau fp pc1->
      x = core \/ x = call \/ x = ret ->
      thread_sim ge pc ({-|pc1,t}).
  Proof.
    unfold thread_sim,getcurcs;simpl;intros;Hsimpl.
    destruct H2 as [|[]];subst;inversion H1;subst;simpl in *;subst; Esimpl;eauto; solv_thread;solv_thread;auto.

    destruct Coqlib.peq;try contradiction;auto.
  Qed.
  Lemma npnsw_or_sw_stepN_thread_sim:
    forall i l ge pc fp pc' t,
      GlobEnv.wd ge->
      (forall ix, mod_wd (GlobEnv.modules ge ix))->
      ThreadPool.inv pc.(thread_pool)->
      npnsw_or_sw_stepN ge i l pc fp pc'->
      ~ list_matched l t->
      thread_sim ge ({-|pc,t}) ({-|pc',t}).
  Proof.
    induction i;intros.
    apply npnsw_or_sw_stepN_0 in H2;Hsimpl;subst.
    rewrite (swstar_l1 _ _ _ H5);simpl. apply thread_sim_refl.
    apply npnsw_or_sw_stepN_inv1 in H2;[|Lia.lia].
    Hsimpl.
    assert(S i - 1 = i). Lia.lia.
    rewrite H8 in *;clear H8.

    assert(~ list_matched x2 t).
    intro;contradict H3;unfold list_matched in *;Hsimpl.
    exists (S x4). rewrite <- H7;auto.
    apply swstar_l1 in H2 as ?.
    rewrite H9 in H4. apply npnsw_step_thdpinv in H4 as ?;auto.
    eapply IHi in H5;eauto.
    eapply thread_sim_trans;eauto.

    eapply npnsw_step_diff_thread_sim in H4;eauto.
    simpl. intro.
    contradict H3. rewrite <- H7. exists 0. simpl. congruence.
  Qed.
    
    

  Lemma npnsw_or_sw_stepN_atomO:
    forall i l ge pc fp pc',
      npnsw_or_sw_stepN ge i l pc fp pc'->
      atom_bit pc = O /\ atom_bit pc' = O.
  Proof.
    induction 1;auto.
    destruct IHnpnsw_or_sw_stepN;split;auto.
    destruct H as [|[]];inversion H;subst;auto.
    Hsimpl;Esimpl;eauto. inversion H;auto.
  Qed.
  Lemma npnsw_or_sw_stepN_i_1_split:
    forall i l ge pc fp pc',
      npnsw_or_sw_stepN ge (S i) l pc fp pc'->
      exists l1 fp1 pc1 l2 fp2,
        npnsw_or_sw_stepN ge i l1 pc fp1 pc1 /\
        npnsw_or_sw_stepN ge 1 l2 pc1 fp2 pc' /\
        app l1 l2 = l /\ FP.union fp1 fp2 = fp.
  Proof.
    induction i;intros.
    Esimpl;eauto. constructor.
    apply npnsw_or_sw_stepN_atomO in H as [];auto.
    auto.
    rewrite FP.emp_union_fp;auto.
    apply npnsw_or_sw_stepN_SN_split in H;Hsimpl.
    eapply IHi in H0;eauto.
    Hsimpl.
    eapply npnsw_or_sw_stepN_cons in H0;eauto.
    assert(1 + i = S i). Lia.lia.
    rewrite H6 in H0;clear H6.
    Esimpl;eauto. rewrite <- H2,<- H4.
    rewrite List.app_assoc;auto.

    rewrite <- H1,<- H5. rewrite FP.fp_union_assoc;auto.
  Qed.

  Lemma drf_pc_glob_safe:
    forall ge pc ,
      @drf_pc_glob ge pc->
      safe_state glob_step abort pc.
  Proof.
    unfold drf_pc_glob,drf_pc. intros.
    Hsimpl. eapply safe_succeed;eauto.
  Qed.
  Lemma drf_pc_glob_drf:
    forall ge pc,
      @drf_pc_glob ge pc ->
      ~ race glob_predict_star_alter pc.
  Proof.
    intros.
    pose proof drf_pc_glob_l1 _ _ H as ?.
    pose proof drf_pc_glob_l2 _ _ H as ?.
    unfold drf_pc_glob,drf_pc,drfpc in H;Hsimpl.
    intro.
    apply globrace_equiv in H8;auto.
    pose predict_equiv.
    eapply predict_equiv_to_star_race_equiv in H8;eauto.
    apply star_race_equiv in H8.
    contradict H3. unfold star_race_config in *;Hsimpl.
    eapply cons_star_star in H3;eauto.
  Qed.

  Lemma npnsw_step_halfatomblockstep_ex:
    forall ge pc l fp pc' t fp2 pc2,
      drf_pc_glob pc->
      glob_npnsw_step pc l fp pc'-> invpc ge pc ->
      t <> cur_tid pc->
      halfatomblockstep ge ({-|pc',t}) tau fp2 pc2->
      FP.smile fp fp2 /\ exists pc1,halfatomblockstep ge ({-|pc,t}) tau fp2 pc1 .
  Proof.
    unfold halfatomblockstep.
    intros;Hsimpl.
    pose proof drf_pc_glob_l1 _ _  H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    inversion H as [o1 _].
    assert(R3:tau<>sw). intro T;inversion T.
    intros.
    apply npnswstep_taustep in H0 as ?;subst.
    apply npnswstep_l2 in H0 as ?.
    apply npnswstep_l1 in H0 as [?[]].
    rewrite <- pc_cur_tid with (pc:=pc) in H0.
    assert(FP.smile fp fp2 \/ ~ FP.smile fp fp2).
    apply classic. destruct H8.
    {
      apply npnswstep_l3 in H0;auto.
      apply npnsw_step_tid_preservation in H0 as ?. simpl in *.
      eapply npnswstep_half_I_smile in H0;eauto;try congruence.
      Hsimpl. Esimpl;eauto.
    }
    {
      apply smile_conflict in H8.
      destruct H7 as [|[]];subst;try(inversion H0;subst;apply FP.emp_never_conflict in H8 as [];contradiction).
      assert(cur_tid pc = cur_tid pc'). inversion H0;auto.
      pose proof H0 as T.
      eapply corestep_I_conflict in H0;eauto;try congruence.
      destruct H0.
      {
        apply drf_pc_glob_safe in H as ?.
        unfold halfatomblock_abort in H0;Hsimpl.
        apply halfatomblockstep_cur_valid_id in H0 as ?;auto.
        apply halfatomblockstep_star in H0 as[].
        assert(glob_step pc sw FP.emp ({-|pc,t})).
        destruct pc,H11;simpl in *;subst. rewrite o1. econstructor;eauto.
        eapply star_step in H12;eauto.
        eapply H9 in H12;eauto. congruence.
      }
      {
        Hsimpl.
        apply drf_pc_glob_drf in H.
        contradict H. apply FP.conflict_sym in H10.
        apply predict_star_race_to_alter.
        econstructor;eauto. econstructor 2;eauto. econstructor;eauto. apply npnswstep_l3 in T;auto. apply tau_plus2star. econstructor;eauto.
        right;intro R;inversion R.
      }
    }
  Qed.

  Lemma npnsw_star_halfatomblockstep_ex:
    forall ge pc fp pc' t fp2 pc2,
      drf_pc_glob pc->
      tau_star glob_npnsw_step pc fp pc'-> invpc ge pc ->
      t <> cur_tid pc->
      halfatomblockstep ge ({-|pc',t}) tau fp2 pc2->
      FP.smile fp fp2 /\ exists pc1,halfatomblockstep ge ({-|pc,t}) tau fp2 pc1.
  Proof.
    induction 2;intros. split. apply empsmile. Esimpl;eauto.
    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    apply npnsw_step_thdpinv in H0 as ?;auto.

    assert(drf_pc_glob s').
    apply npnsw_step_O_preservation in H0 as?;[|inversion H];auto.
    apply npnswstep_l1 in H0 as [?[]].
    apply type_glob_step_elim in H0.
    pose proof star_refl glob_step s'.
    eapply star_step in H0;eauto.
    eapply drf_pc_glob_cons;eauto.

    apply npnsw_step_tid_preservation in H0 as ?.
    rewrite H7 in H3.
    Hsimpl.

    eapply npnsw_step_halfatomblockstep_ex in H0;eauto;try congruence.
    Hsimpl.
    Esimpl;eauto. apply fpsmile_union;auto.
  Qed.

  Lemma drfsafe_npnsw_step_fpsmile:
    forall ge pc fp pc' t fp2 pc2,
      @drf_pc_glob ge pc->
      glob_npnsw_step pc tau fp pc'-> 
      t <> cur_tid pc->
      glob_npnsw_step ({-|pc',t}) tau fp2 pc2->
      FP.smile fp fp2 /\ exists pc1,glob_npnsw_step ({-|pc,t}) tau fp2 pc1 /\ exists pc2',
  glob_npnsw_step ({-|pc1,cur_tid pc}) tau fp pc2' /\ mem_eq_pc ge pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    rewrite <- pc_cur_tid with(pc:=pc) in H0.

    assert(FP.smile fp fp2 \/ ~ FP.smile fp fp2).
    apply classic. destruct H3.
    split;auto.
    eapply npnswstep_reorder in H3;eauto.
    apply smile_conflict in H3.
    eapply npnswstep_conflict in H3 as ?;eauto.
    apply npnsw_step_thdpinv in H0 as ?;auto.
    apply npnsw_step_cur_valid_id in H2 as ?;auto.
    eapply npnswstep_pc_valid_tid_backwards_preservation in H0 as ?;eauto.
    destruct H4.
    {
      assert(star glob_step pc (cons sw nil)(FP.union FP.emp FP.emp) ({-|pc,t})).
      econstructor 2;[|constructor].
      destruct pc,H,H7;simpl in *;subst;econstructor;eauto.
      eapply drf_pc_glob_safe in H. eapply H in H8;congruence.
    }
    {
      Hsimpl. inversion H as [o1 _].
      apply npnsw_step_O_preservation in H0 as o3;auto.
      apply npnsw_step_O_preservation in H4 as o2;auto.
      eapply drf_pc_glob_drf in H;contradict H.
      apply FP.conflict_sym in H8.
      econstructor;eauto. econstructor;auto. apply tau_plus2star;constructor;eauto.
      auto.
      econstructor;auto. apply tau_plus2star;constructor;eauto. auto.
      left;intro R;inversion R.
    }
  Qed.

  Lemma drfsafe_npnsw_or_sw_stepN_npnswstep_fpsmile:
    forall i l ge pc fp pc' fp' t pc'',
      drf_pc_glob pc ->
      npnsw_or_sw_stepN ge i l pc fp pc'->
      ~ list_matched l t->
      glob_npnsw_step ({-|pc',t}) tau fp' pc''->
      FP.smile fp fp' /\ exists pc1,glob_npnsw_step ({-|pc,t}) tau fp' pc1 /\
                               exists pc2, npnsw_or_sw_stepN ge i l pc1 fp pc2 /\
                                      mem_eq_pc ge pc'' pc2.
  Proof.
    induction 2;intros.
    split. apply empsmile. Esimpl;eauto.
    constructor. apply npnsw_step_O_preservation in H2;auto.  apply mem_eq_pc_refl.
    
    assert(drf_pc_glob pc').
    apply npnsw_step_O_preservation in H0 as o1;auto.
    apply npnswstep_l1 in H0;Hsimpl;apply type_glob_step_elim in H0 as R1;pose proof star_refl glob_step pc'.
    eapply star_step in H5;eauto.
    eapply drf_pc_glob_cons;eauto.
    inversion H;auto.
    Hsimpl.

    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    assert(~ list_matched l' t).
    intro;contradict H2.
    unfold list_matched in *. Hsimpl. exists (S x). auto.
    Hsimpl.
    assert(l=tau). destruct H0 as [|[]];inversion H0;auto. subst.
    eapply drfsafe_npnsw_step_fpsmile in H0;eauto.
    Hsimpl.
    eapply mem_eq_npnsw_or_sw_stepN in H12;eauto. Hsimpl.

   
    apply npnsw_step_tid_preservation in H3 as E0.
    simpl in E0.
    split. eapply fpsmile_union;eauto.
    do 2 eexists. eauto.
    destruct i.
    {
      apply npnsw_or_sw_stepN_0 in H12 as ?;Hsimpl;subst.
      apply npnsw_step_tid_preservation in H7 as E1.
      simpl in E1. rewrite <- E1 in *.
      rewrite (swstar_l1 _ _ _ H16) in H13.
      simpl in H13.
      eapply mem_eq_pc_trans in H13;eauto.
      assert(cur_tid x3 = cur_tid pc''). destruct H13;Hsimpl;auto.
      rewrite H14 in H13.
      apply npnsw_step_cur_valid_id in H10 as ?;auto.
      eapply npnsw_step_pc_valid_tid_preservation in H10 as ?;eauto.
      eapply npnsw_step_thdpinv in H10 as v3;eauto.
      eapply npnsw_step_pc_valid_tid_preservation in H11 as ?;eauto.
      apply npnsw_or_sw_stepN_atomO in H12 as [].
      assert(sw_star glob_step x2 ({-|x2,cur_tid pc''})).
      econstructor 2;[|constructor]. 
      destruct x2,H18;simpl in *;subst;econstructor;eauto.

      apply swstar_npnsw_or_sw_stepN in H20;auto.
      eapply npnsworsw_consnpnsw in H20;eauto.
      simpl in *;subst.

      assert(type_glob_step glob_sw x1 sw FP.emp ({-|x1,cur_tid pc})).
      apply npnsw_or_sw_stepN_atomO in H20 as [].
      apply npnsw_step_cur_valid_id in H11;auto.
      destruct x1,H11. simpl in *;subst. econstructor;eauto.
      eapply npnsworsw_conssw in H20;eauto.
      rewrite FP.emp_union_fp in H20.
      Esimpl;eauto.
    }
    {
      apply npnsw_step_cur_valid_id in H10 as ?;auto.
      eapply npnsw_step_pc_valid_tid_preservation in H10 as ?;eauto.
      eapply npnsw_step_thdpinv in H10 as v3;eauto.
      eapply npnsw_step_pc_valid_tid_preservation in H11 as ?;eauto.
      apply npnsw_step_O_preservation in H10;[|inversion H;auto].
      eapply npnsw_cons_npnsw_or_sw_stepN_sw in H12;try apply H11;eauto.
      simpl in *.
      assert(type_glob_step glob_sw x1 sw FP.emp ({-|x1,cur_tid pc})).
      apply npnsw_or_sw_stepN_atomO in H12 as [].
      apply npnsw_step_cur_valid_id in H11;auto.
      destruct x1,H11. simpl in *;subst. econstructor;eauto.
      eapply npnsworsw_conssw in H12;eauto.
      rewrite FP.emp_union_fp in H12.
      Esimpl;eauto.

      eapply mem_eq_pc_trans;eauto.
    }

    intro. contradict H2. exists 0;auto. simpl. congruence.

    assert(drf_pc_glob pc').
    apply type_glob_step_elim in H0 as ?.
    eapply drf_pc_glob_cons;eauto. econstructor;eauto. constructor.
    inversion H0;auto.
    Hsimpl.

    assert(fp=FP.emp). inversion H0;auto. subst.
    split. rewrite FP.emp_union_fp;auto.
    rewrite FP.emp_union_fp.
    assert(({-|pc',t}) = ({-|pc,t})). inversion H0;auto.
    rewrite H9 in *.
    Esimpl;eauto.
  Qed.
  Lemma drfsafe_npnsw_or_sw_stepN_halfatomblockstep_fpsmile:
    forall i l ge pc fp pc' fp' t pc'',
      drf_pc_glob pc ->
      npnsw_or_sw_stepN ge i l pc fp pc'->
      ~ list_matched l t->
      halfatomblockstep ge ({-|pc',t}) tau fp' pc''->
      FP.smile fp fp'.
  Proof.
    induction i;intros.
    apply npnsw_or_sw_stepN_0 in H0;Hsimpl;subst;apply empsmile.

    apply NNPP. intro.
    apply smile_conflict in H3.
    apply npnsw_or_sw_stepN_i_1_split in H0.
    Hsimpl.

    apply npnsw_or_sw_stepN_1_inv in H4 as ?;Hsimpl.
    assert(cur_tid x4 <> t).
    intro. contradict H1.
    rewrite <- H5,H10,H11.
    apply List.In_nth_error.
    apply List.in_or_app. right.
    left;auto.

    assert(drf_pc_glob x1).
    apply npnsw_or_sw_stepN_atomO in H0 as ?;Hsimpl.
    apply npnsw_or_sw_stepN_sound in H0;apply npnsw_or_sw_star_non_evt_star in H0;apply non_evt_star_star in H0 as [];eapply drf_pc_glob_cons;eauto.
    assert(drf_pc_glob x4).
    apply swstar_globstar in H7 as ?. Hsimpl.
    eapply drf_pc_glob_cons;eauto. rewrite (swstar_l1 _ _ _ H7);auto. inversion H12;auto.
    pose proof drf_pc_glob_l1 _ _ H13 as [v1 ?].
    apply swstar_l1 in H9. rewrite H9 in H2;simpl in H2.
    eapply  npnsw_step_halfatomblockstep_ex in H8;eauto.
    Hsimpl.
    inversion H12 as [? _].
    apply swstar_npnsw_or_sw_stepN in H7;auto.
    eapply npnsw_or_sw_stepN_cons in H7;eauto.
    assert(i + 0 = i). Lia.lia.
    rewrite H17 in H7.
    rewrite List.app_nil_r in H7.
    eapply IHi in H7;eauto.
    rewrite FP.fp_union_emp in H7.
    eapply fpsmile_union in H8;try apply H7;eauto.
    rewrite H6 in H8. apply smile_conflict in H3. contradiction.

    intro. unfold list_matched in H18.
    contradict H1.
    rewrite <-H5. Hsimpl.
    unfold list_matched. apply List.In_nth_error.
    apply List.in_or_app. left.
    apply Coqlib.nth_error_in in H1. auto.
  Qed.

  Lemma halfatomblockstep_cons:
    forall ge pc fp pc' fp' pc'',
      halfatomblockstep ge pc tau fp pc'->
      type_glob_step core pc' tau fp' pc''->
      halfatomblockstep ge pc tau (FP.union fp fp') pc''.
  Proof.
    unfold halfatomblockstep;intros;Hsimpl.
    eapply tau_plus_1 in H0;eauto. eapply tau_plus2star in H0;eapply tau_star_star in H0;eauto.
  Qed.

  Lemma drfsafe_npnsw_or_sw_stepN_thread_sim:
    forall i l ge pc fp pc' t ,
      drf_pc_glob pc ->
      npnsw_or_sw_stepN ge i l pc fp pc'->
      ~ list_matched l t->
      thread_sim ge ({-|pc,t}) ({-|pc',t}).
  Proof.
    induction 2;intros.
    apply thread_sim_refl.
    apply npnswstep_l1 in H0 as ?;Hsimpl.
    apply type_glob_step_elim in H3.
    pose proof star_refl glob_step pc'.
    eapply star_step in H5;eauto.
    inversion H as [? _].
    apply npnsw_step_O_preservation in H0 as ?;auto.
    eapply drf_pc_glob_cons in H5;eauto.
    assert(~list_matched l' t).
    intro;contradict H2. destruct H8. exists (S x0). auto.
    Hsimpl.

    assert(cur_tid pc <> t).
    intro. subst. contradict H2. exists 0. auto.
    eapply npnsw_step_diff_thread_sim in H0;eauto.
    eapply thread_sim_trans;eauto.

    apply type_glob_step_elim in H0 as ?.
    pose proof star_refl glob_step pc'.
    eapply star_step in H4;eauto.
    eapply drf_pc_glob_cons in H4;eauto;[|inversion H0;auto].
    Hsimpl.
    assert(({-|pc,t}) = ({-|pc',t})). inversion H0;subst;auto.
    congruence.
  Qed.

  Lemma GPre_trans:
    forall ge m1 m2 m3 fp t,
      GPre ge m1 m2 fp t->
      GPre ge m2 m3 fp t->
      GPre ge m1 m3 fp t.
  Proof.
    unfold GPre. intros.
    Hsimpl.
    split. eapply MemPre_trans;eauto.
    unfold GlobalFreelistEq in *;Hsimpl.
    intros. specialize (H1 _ _ H3).
    specialize (H2 _ _ H3). split;intro.
    apply H1;apply H2;auto.
    apply H2;apply H1;auto.
  Qed.
  Lemma GPre_refl:
    forall ge m fp t,GPre ge m m fp t.
  Proof. unfold GPre;intros. split. apply MemPre_refl. apply GlobalFreelistEq_refl. Qed.
  Lemma list_not_matched_split:
    forall A l a b,
      @list_matched A l b ->
      list_matched (cons a l) b.
  Proof.
    unfold list_matched;intros;Hsimpl.
    exists (S x);auto.
  Qed.
  Lemma drfsafe_npnsw_or_sw_stepN_fpsmile_GPre:
    forall i l ge pc fp pc' t fp0,
      drf_pc_glob pc ->
      npnsw_or_sw_stepN ge i l pc fp pc'->
      ~ list_matched l t->
      FP.smile fp fp0->
      GPre ge pc.(gm) pc'.(gm) fp0 t.
  Proof.
    induction 2;intros. apply GPre_refl.

    assert(~ list_matched l' t). intro;contradict H2. eapply list_not_matched_split;eauto.

    apply npnswstep_l1 in H0;Hsimpl.
    apply type_glob_step_elim in H0 as ?.
    pose proof star_refl glob_step pc'.
    eapply star_step in H7;eauto. eapply drf_pc_glob_cons in H7;eauto;[|inversion H;apply npnswstep_l3 in H0;auto;apply npnsw_step_O_preservation in H0;auto].

    assert(FP.smile fp' fp0).
    apply fpsmile_sym. apply fpsmile_sym in H3. eapply fpsmile_subset;eauto.
    rewrite FP.union_comm_eq;eapply FP.union_subset.
    Hsimpl.

    apply npnswstep_l3 in H0;auto.
    eapply GPre_trans;eauto.

    pose proof drf_pc_glob_l1 _ _ H as [].
    pose proof drf_pc_glob_l2 _ _ H as ?.
    apply npnsw_step_eff in H0;auto.
    apply GPre_comm.
    eapply GEffect_fpsmile_disj_GPre_Rule;eauto.
    intro. subst. contradict H2. exists 0;auto.
    apply fpsmile_sym in H3. apply fpsmile_sym. eapply fpsmile_subset;eauto.
    apply FP.union_subset.

    apply type_glob_step_elim in H0 as ?.
    pose proof star_refl glob_step pc'.
    eapply star_step in H5;eauto. eapply drf_pc_glob_cons in H5;eauto;[|inversion H0;auto].

    assert(FP.smile fp' fp0).
    apply fpsmile_sym. apply fpsmile_sym in H3. eapply fpsmile_subset;eauto.
    rewrite FP.union_comm_eq;eapply FP.union_subset.
    Hsimpl.
    assert(gm pc = gm pc'). inversion H0;auto.
    congruence.
  Qed.


  Lemma thread_sim_coreIdiverge:
    forall ge pc pc'  (inv1:ThreadPool.inv pc.(thread_pool))(inv2 :ThreadPool.inv pc'.(thread_pool)),
      GlobEnv.wd ge->
      (forall ix, mod_wd (GlobEnv.modules ge ix))->
      thread_sim ge pc pc'->
      (forall fp pc1,
          tau_star (type_glob_step core) pc fp pc1->
          GPre ge pc.(gm) pc'.(gm) fp pc.(cur_tid))->
      core_Idiverge ge pc->
      core_Idiverge ge pc'.
  Proof.
    cofix.
    intros.
    inversion H3;subst.
    specialize (H2 fp) as ?.
    apply core_step_equiv in H5. pose proof H5 as R.
    apply tau_plus_1 in H5. apply tau_plus2star in H5.
    specialize (H7 pc'0 H5).
    eapply corestep_Glocality in H7 as ?;try apply R;try assumption.
    Hsimpl.

    econstructor. unfold thread_sim in H1. Hsimpl;congruence.
    apply core_step_equiv;eauto.

    apply type_glob_step_elim in R as ?.
    eapply GE_mod_wd_tp_inv in H11 as ?;eauto.
    apply type_glob_step_elim in H8 as ?.
    eapply GE_mod_wd_tp_inv in H13 as ?;eauto.
    eapply thread_sim_coreIdiverge;try apply H10;eauto.

    intros.
    eapply globstep_eff in H11 as ?;eauto. eapply globstep_eff in H13 as ?;eauto.
    assert(cur_tid pc'0 = cur_tid pc). inversion R;auto.
    rewrite H18.
    assert(cur_tid pc' = cur_tid pc). destruct H1;Hsimpl;auto.
    rewrite H19 in H17.
    eapply GPre_GEffect_GPost_Rule;eauto.
    eapply H2;eauto. eapply tau_star_star;eauto.
  Qed.


 Lemma mem_eq_coreIdiverge:
    forall ge pc pc' (H_modwdge:forall ix, mod_wd (GlobEnv.modules ge ix)),
      mem_eq_pc ge pc pc'->
      core_Idiverge ge pc->
      core_Idiverge ge pc'.
  Proof.
    cofix.
    inversion 3;subst.
    
    apply core_step_equiv in H2. assert(atom_bit pc' = I). inversion H as (?&?&?&?);subst;auto. congruence.
    eapply mem_eq_globstep in H;eauto.
    Hsimpl.
    apply core_step_equiv in H.
    econstructor;eauto.
  Qed.
  Lemma silent_diverge_cons_np_non_evt_star:
    forall (ge : GlobEnv.t) (pc : @ProgConfig ge) (fp : FP.t) (pc' : ProgConfig),
      non_evt_star np_step pc fp pc' ->
      silent_diverge np_step pc' ->
      silent_diverge np_step pc.
  Proof.
    induction 1. auto.
    intros.
    destruct H.
    econstructor;eauto. constructor.
    Hsimpl.
    inversion IHnon_evt_star;subst.
    econstructor;try apply H3;eauto.
    econstructor 2;eauto. inversion H;subst;econstructor;eauto.
  Qed.    
  Lemma core_Idiverge_cons_corestar:
    forall ge pc fp pc',
      tau_star (type_glob_step core) pc fp pc'->
      core_Idiverge ge pc'->
      core_Idiverge ge pc.
  Proof.
    induction 1;intros. auto.
    Hsimpl.
    econstructor. inversion IHtau_star;subst. inversion H;subst;simpl in *;subst. auto.
    apply core_step_equiv;eauto.
    auto.
  Qed.
  Lemma case_coreIdiverge:
    forall ge pc i fp pc',
      drf_pc_glob pc->
      noevt_stepN ge glob_step (S i) pc fp pc' ->
      core_Idiverge ge pc' ->
      npsilent_diverge ge pc \/
      exists t,npsilent_diverge ge ({-|pc,t}) /\ pc_valid_tid pc t.
  Proof.
    intros.
    assert(atom_bit pc' = I).
    inversion H1;subst;auto.
    apply noevt_stepN_Si_Iinv_drfsafe in H0;auto.
    Hsimpl.

    apply atomblockstarN_atomO in H3 as R;destruct R.
    eapply npnsw_or_sw_stepN_exists in H4 as [?[]];auto.

    assert(drf_pc_glob x4).
    apply atomblockstarN_globstar in H3 as [].
    apply swstar_globstar in H0. Hsimpl.
    eapply cons_star_star in H3;eauto.
    eapply drf_pc_glob_cons;eauto.

    pose proof drf_pc_glob_l1 _ _ H10 as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H10 as modwdge.
    eapply npnsw_or_sw_stepN_thdpinv in H4 as ?;eauto.
    apply type_glob_step_cur_valid_id in H5 as ?;auto;try congruence.

    assert(npnsw_or_sw_stepN ge 0 nil x5 (FP.union FP.emp FP.emp) ({-|x5,x7})).
    assert(atom_bit x5 = O). inversion H5;auto.
    econstructor 3;eauto;[destruct x5,H12;simpl in *;subst|constructor;auto].
    econstructor;eauto.

    eapply npnsw_or_sw_stepN_cons in H13;eauto.
    rewrite FP.fp_union_emp in H13.

    eapply npnsw_or_sw_star_div in H13 as ?;auto.
    Hsimpl. simpl in *.

    pose proof H16 as R.
    eapply mem_eq_globstep in H16;eauto;Hsimpl.
    eapply mem_eq_corestar in H18;eauto;Hsimpl.
    eapply mem_eq_coreIdiverge in H7 as ?;eauto.
    eapply mem_eq_coreIdiverge in H20;eauto.

    destruct x12.
    {
      apply npnsw_or_sw_stepN_0 in H15.
      Hsimpl;subst.
      rewrite (swstar_l1 _ _ _ H22) in H16.
      assert(cur_tid x17 = x7). destruct R;Hsimpl. simpl in *;congruence.
      apply npnsw_taustar_tid_preservation in H14 as ?. simpl in H21.
      try rewrite H15,H21,pc_cur_tid in H16.

      apply npnsw_taustar_thdpinv in H14 as?;auto.
      apply type_glob_step_cur_valid_id in H16 as ?;auto;try congruence.
      eapply npnsw_taustar_pc_valid_tid_backwards_preservation in H14 as ?;eauto.
      assert(sw_star glob_step x4 ({-|x4,x7})).
      econstructor 2;[|constructor].
      destruct x4,H25. simpl in *;subst. econstructor;eauto.

      apply corestar_npstar in H18 as ?.
      apply entat_step_equiv in H16 as ?.
      apply type_step_elim in H28.

      eapply ETrace.ne_star_step in H27;eauto.
      apply glob_npnsw_star_to_np_taustar in H14.
      apply tau_star_non_evt_star in H14.
      eapply non_evt_star_cons in H27;eauto.
      apply core_Idiverge_npsilent_diverge in H20. 

      destruct x.
      {
        inversion H3;subst.
        right. exists (cur_tid x15).
        rewrite (swstar_l1 _ _ _ H0) in H25,H27;simpl in H25,H27.
        split;[|auto].
        eapply silent_diverge_cons_np_non_evt_star;eauto.
      }
      {
        apply atomblockstarN_cur_valid_tid in H3 as T1;auto;try congruence.
        eapply atomblockstarN_cons_swstar in H3;eauto.
        eapply atomblockstarN_np in H3;eauto.
        Hsimpl.
        destruct H29.
        Hsimpl.
        simpl in H29.
        assert(sw_star glob_step ({-|x4,x13})({-|x4,x7})).
        econstructor 2;[|constructor].
        destruct x4,H25,H10. simpl in *;subst. econstructor;eauto.
        eapply npsw_swstar in H29;eauto.

        assert(non_evt_star np_step x12 (FP.union FP.emp FP.emp) ({-|x4,x7})).
        econstructor 2;eauto. constructor.
        eapply non_evt_star_cons in H31;eauto.
        eapply non_evt_star_cons in H27;eauto.

        apply swstar_l1 in H0. rewrite H0 in *.
        right. exists (cur_tid x3). split;auto.
        eapply silent_diverge_cons_np_non_evt_star;eauto.

        inversion H29;subst.
        destruct H25. apply H_all_thread_halted in H21. contradiction.
        Lia.lia.

        rewrite (swstar_l1 _ _ _ H0). apply drf_pc_glob_l1 in H as [];auto.
        Lia.lia.
        rewrite (swstar_l1 _ _ _ H0). apply drf_pc_glob_l1 in H as [];auto.
      }
    }
    {
      assert(pc_valid_tid x4 x7).
      apply npnsw_or_sw_stepN_sound in H4;apply npnsw_or_sw_star_non_evt_star in H4;apply non_evt_star_star in H4 as[].
      eapply pc_valid_tid_back_star;eauto.
      apply npnsw_taustar_thdpinv in H14 as ?;auto.
      eapply npnsw_taustar_pc_valid_tid_preservation in H14 as ?;eauto.

      assert(drf_pc_glob x15).
      eapply npnsw_taustar_to_taustar in H14;auto.
      apply tau_star_to_star in H14 as [].
      assert(glob_step x4 sw FP.emp ({-|x4,x7})).
      destruct x4,H10,H21;simpl in *;subst. econstructor;eauto.
      eapply star_step in H24;eauto.
      eapply drf_pc_glob_cons;eauto.
      apply npnsw_or_sw_stepN_atomO in H15 as [];auto.

      eapply npnsw_or_sw_stepN_thread_sim in H15 as Sim1;eauto.
      assert(forall fp pc', halfatomblockstep ge x17 tau fp pc'->FP.smile fp x16).
      intros.
      assert(cur_tid x17 = x7). destruct R;Hsimpl;auto.
      rewrite <- pc_cur_tid with(pc:=x17),H26 in H25.
      eapply drfsafe_npnsw_or_sw_stepN_halfatomblockstep_fpsmile in H15 as ?;eauto.
      apply fpsmile_sym;auto.

      assert(halfatomblockstep ge x17 tau x9 x19).
      unfold halfatomblockstep;Esimpl;eauto.
      eapply H25 in H26 as ?;eauto.

      apply thread_sim_comm in Sim1.
      assert(cur_tid x17 = x7). inversion R;subst;Hsimpl;auto.
      rewrite <- H28,pc_cur_tid in Sim1.
      pose proof empsmile x16. apply fpsmile_sym in H29.
      eapply drfsafe_npnsw_or_sw_stepN_fpsmile_GPre in H29;try apply H15 ;eauto.
      apply GPre_comm in H29.
      assert(ThreadPool.inv x17.(thread_pool)).
      destruct R. Hsimpl. rewrite <- H30. auto. rewrite <- H28 in H29.
      eapply entatstep_Glocality in Sim1 as ?;eauto;simpl.
      Hsimpl.

      apply core_Idiverge_cons_corestar in H18;auto.      
      apply type_glob_step_elim in H31 as ?.
      apply GE_mod_wd_tp_inv in H34;auto.

      Coqlib.exploit  thread_sim_coreIdiverge;try apply H33;eauto.
      apply type_glob_step_elim in H16;apply GE_mod_wd_tp_inv in H16;auto.

      intros.
      assert(halfatomblockstep ge x17 tau fp0 pc1).
      unfold halfatomblockstep;Esimpl;eauto.

      apply H25 in H36.
      apply fpsmile_sym in H36.
      eapply drfsafe_npnsw_or_sw_stepN_fpsmile_GPre in H15;try apply H36;eauto.
      assert(gm x15 = gm x20). inversion H31;auto.
      assert(gm x18 = gm x17). inversion H16;auto.
      assert(cur_tid x18 = x7). inversion H16;subst. econstructor.
      rewrite <- H37, H38, H39. apply GPre_comm. auto.

      intro.
      apply core_Idiverge_npsilent_diverge in H35.
      apply entat_step_equiv in H31.
      apply type_step_elim in H31.
      apply npnsw_taustar_tid_preservation in H14 as ?;auto.
      simpl in H36. rewrite H28,H36,pc_cur_tid in H31.

      assert(non_evt_star np_step x20 FP.emp x20). constructor.
      eapply ETrace.ne_star_step in H37;eauto.

      destruct x.
      {
        inversion H3;subst. apply swstar_l1 in H0.
        rewrite H0 in *;simpl in *.
        right. exists (cur_tid x15). split;auto.
        apply glob_npnsw_star_to_np_taustar in H14.
        apply tau_star_non_evt_star in H14.
        eapply non_evt_star_cons in H37;eauto.
        eapply silent_diverge_cons_np_non_evt_star;eauto.
      }
      {
        apply atomblockstarN_np in H3;auto.
        Hsimpl.
        destruct H38.

        Hsimpl.
        assert(sw_star glob_step  ({-|x4, x22}) ({-|x4,x7})).
        econstructor 2;[|constructor].
        destruct x4,H21. simpl in *;subst. econstructor;eauto.
        eapply npsw_swstar in H39;eauto.

        apply glob_npnsw_star_to_np_taustar in H14;apply tau_star_non_evt_star in H14.
        eapply non_evt_star_cons in H37;eauto.
        eapply ETrace.ne_star_step in H37;eauto.
        eapply non_evt_star_cons in H37;eauto.
        eapply silent_diverge_cons_np_non_evt_star in H35;try apply H37.
        apply swstar_l in H0 as [];subst;Hsimpl;auto.
        right. exists (cur_tid x3). split;auto.
        inversion H0;subst;simpl;auto.
        inversion H0;subst;split;auto.

        inversion H38;subst. destruct H21.
        apply H_all_thread_halted in H21;contradiction.
        Lia.lia.

        rewrite (swstar_l1 _ _ _ H0).
        apply drf_pc_glob_l1 in H as [];auto.
      }
     }
  Qed.    
    

  CoInductive AO_psilent_diverge{ge}:tid->@ProgConfig ge->Prop:=
    AO_mk:
      forall pc fp pc1 fp1 pc2,
        npnsw_or_sw_star ge pc fp pc1 ->
        glob_npnsw_step pc1 tau fp1 pc2 ->
        AO_psilent_diverge (cur_tid pc1) pc2  ->
        AO_psilent_diverge (cur_tid pc1)pc.

  Lemma AO_psilent_diverge_valid_t:
    forall ge pc t,
      @drf_pc_glob ge pc ->
      AO_psilent_diverge t pc->
      pc_valid_tid pc t.
  Proof.
    inversion 2;subst.
    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    inversion H as [? _].
    apply npnsw_or_sw_stepN_exists in H1 as ?;auto.
    Hsimpl.
    apply npnsw_or_sw_stepN_atomO in H5 as [_].
    apply npnsw_or_sw_star_non_evt_star in H1 as ?.
    apply non_evt_star_star in H6;Hsimpl.
    eapply drf_pc_glob_cons in H6 as ?;eauto.

    pose proof drf_pc_glob_l1 _ _ H7 as [v2 _].
    eapply npnsw_step_cur_valid_id in H2;eauto.
    eapply pc_valid_tid_back_star in H6;eauto.
  Qed.

  Lemma npnsw_or_sw_stepN_pc_valid_tid_preserve:
    forall i l ge pc fp pc' t (wdge:GlobEnv.wd ge)(v1:invpc ge pc),
      @npnsw_or_sw_stepN ge i l pc fp pc'->
      pc_valid_tid pc t->
      pc_valid_tid pc' t.
  Proof.
    induction 3;intros.
    auto.
    eapply npnsw_step_thdpinv in H as ?;eauto.
    eapply npnsw_step_pc_valid_tid_preservation in H as ?;eauto.

    assert(pc' = ({-|pc,cur_tid pc'})). inversion H;auto.
    apply IHnpnsw_or_sw_stepN;rewrite H2;auto.
  Qed.
    
  Lemma npnsw_star_cons_npnsw_or_sw_star:
    forall (GE : GlobEnv.t) (pc : ProgConfig)
      (fp : FP.t) (pc' : ProgConfig),
      tau_star glob_npnsw_step pc fp pc' ->
      forall (fp2 : FP.t) (pc'' : ProgConfig),
        npnsw_or_sw_star GE pc' fp2 pc'' -> npnsw_or_sw_star GE pc (FP.union fp fp2) pc''.
  Proof.
    induction 1;intros.
    rewrite FP.emp_union_fp;auto.
    eapply IHtau_star in H1;eauto.
    eapply npnsw_step_cons_npnsw_or_sw_star in H;eauto.
    rewrite<- FP.fp_union_assoc;auto.
  Qed.
  Lemma mem_eq_AO_psilent_diverge:
    forall ge pc pc' t,
      GlobEnv.wd ge->
      (forall ix, mod_wd (GlobEnv.modules ge ix))->
      ThreadPool.inv pc.(thread_pool)->
      mem_eq_pc ge pc pc'->
      AO_psilent_diverge t pc ->
      AO_psilent_diverge t pc'.
  Proof.
    cofix;inversion 5;subst.
    eapply mem_eq_npnsw_or_sw_star in H2 as ? ;try apply H4;auto.
    Hsimpl.

    eapply npnswstep_l1 in H5;Hsimpl.
    assert(cur_tid pc1 = cur_tid x). destruct H8;Hsimpl;auto.
    rewrite H10.
    eapply mem_eq_globstep in H8;try apply H5;auto.
    Hsimpl. eapply npnswstep_l3 in H8;auto.

    
    apply npnsw_or_sw_star_non_evt_star in H4;apply non_evt_star_star in H4 as [].
    apply GE_mod_wd_star_tp_inv2 in H4;auto.
    apply type_glob_step_elim in H5. apply GE_mod_wd_tp_inv in H5;auto.
    econstructor;eauto.  eapply mem_eq_AO_psilent_diverge;eauto.
    rewrite<- H10. auto.
  Qed.
  Lemma AO_psilent_diverge_cons_npnsw_or_sw_star:
    forall ge pc fp pc' t,
      npnsw_or_sw_star ge pc fp pc'->
      AO_psilent_diverge t  pc'->
      AO_psilent_diverge t pc.
  Proof.
    destruct 1. induction H.
    auto.
    intros. Hsimpl.
    inversion IHstar;subst.
    destruct H2.
    eapply star_step in H;eauto.
    econstructor;eauto. eexists;eauto.
  Qed.
  Lemma drf_safe_AO_psilent_diverge_inv:
    forall ge pc t,
      @drf_pc_glob ge pc ->
      AO_psilent_diverge t pc ->
      (exists fp pc1 , drf_pc_glob pc1 /\ glob_npnsw_step ({-|pc,t}) tau fp pc1 /\ AO_psilent_diverge t pc1).
  Proof.
    intros.
    pose proof AO_psilent_diverge_valid_t _ _ _ H H0 as ?.
    inversion H0;clear H0;subst.
    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    inversion H as [? _].
    assert(v2:ThreadPool.inv pc1.(thread_pool)).
    apply npnsw_or_sw_star_non_evt_star in H2;apply non_evt_star_star in H2 as [];eapply GE_mod_wd_star_tp_inv2;eauto.
    eapply npnsw_step_thdpinv in H3 as v3;eauto.
    apply npnsw_or_sw_stepN_exists in H2;Hsimpl;auto.
    apply npnsw_or_sw_star_div in H2;auto;Hsimpl.

    
    assert(glob_step pc sw FP.emp ({-|pc,cur_tid pc1})).
    destruct pc,H1;simpl in *;subst;econstructor;eauto.
    assert(drf_pc_glob ({-|pc,cur_tid pc1})).
    eapply drf_pc_glob_cons;eauto. econstructor 2;eauto. constructor.

    inversion H2;subst.
    Focus 2.
    apply npnsw_or_sw_stepN_sound in H5.
    eapply npnsw_star_cons_npnsw_or_sw_star in H11;eauto.
    
    apply npnswstep_l1 in H3;Hsimpl.
    pose proof H6 as R1.
    eapply mem_eq_globstep in H6;eauto;Hsimpl.
    eapply mem_eq_AO_psilent_diverge in H13;eauto.
    apply npnswstep_l3 in H6;auto.
    assert(e1:cur_tid x6 = cur_tid pc1). inversion R1;Hsimpl;auto.
    rewrite <- e1 in H13.
    eapply AO_mk in H13;eauto. rewrite e1 in H13.
    Esimpl;try apply H13;eauto.
    assert(atom_bit s' = O). apply npnsw_step_O_preservation in H10;auto.
    apply npnswstep_l1 in H10;Hsimpl. apply type_glob_step_elim in H10 as ?.
    pose proof star_refl glob_step s'.
    eapply star_step in H17;eauto.
    eapply drf_pc_glob_cons;eauto.


    clear H2.
    apply npnswstep_l1 in H3;Hsimpl.
    pose proof H6 as R1.
    eapply mem_eq_globstep in H6;eauto;Hsimpl.
    eapply mem_eq_AO_psilent_diverge in H10;eauto.
    apply npnswstep_l3 in H6;auto.
    assert(cur_tid x6 = cur_tid pc1).
    destruct R1;Hsimpl;auto.
    eapply drfsafe_npnsw_or_sw_stepN_npnswstep_fpsmile in H9 as ?;eauto.
    
    Focus 2. rewrite <- H11,pc_cur_tid. eauto.
    Hsimpl.

    simpl in *.
    eapply mem_eq_AO_psilent_diverge in H15;eauto.
    apply npnsw_or_sw_stepN_sound in H14.
    eapply AO_psilent_diverge_cons_npnsw_or_sw_star in H15;eauto.

    apply npnsw_step_tid_preservation in H13 as ?. simpl in H16.
    assert(drf_pc_glob x7).
    eapply drf_pc_glob_cons_npnsw;eauto. 

    Esimpl;eauto.

    apply npnsw_step_thdpinv in H6;auto.
    eapply npnsw_or_sw_stepN_thdpinv in H5;eauto.
  Qed.    

  
Definition no_rep (l:list tid):Prop:=
    forall i j,
      i <> j ->
      i < length l ->
      j < length l ->
      List.nth_error l i <> List.nth_error l j.

  Definition pcvalid{ge}(pc:@ProgConfig ge)(l:list tid):Prop:=
    forall t, List.In t l ->pc_valid_tid pc t.
  Definition isdone {ge}(pc:@ProgConfig ge)(t:list tid):Prop:=
    forall fp pc' fp' pc'',
        npnsw_or_sw_star ge pc fp pc'->
        glob_npnsw_step pc' tau fp' pc'' ->
        npnswdiverge ge pc'' ->
        ~ List.In (cur_tid pc') t.

  Lemma notalldone:
    forall ge pc lt,
      drf_pc_glob pc->
      npnswdiverge ge pc ->
      isdone pc lt->
      (forall t,
          pc_valid_tid pc t-> 
          list_matched lt t)
      ->
      False.
  Proof.
    unfold isdone.
    inversion 2;subst;intros.
    assert(npnsw_or_sw_star ge pc (FP.union FP.emp FP.emp) pc').
    eexists. econstructor;[|constructor]. right.
    inversion H2;subst.  econstructor;eauto.
    assert(v1:ThreadPool.inv (thread_pool pc')).
    inversion H2;subst;auto.
    assert(npnsw_or_sw_star ge pc (FP.union FP.emp FP.emp) pc').
    eexists. econstructor 2;eauto;[|constructor].
    right;inversion H2;subst;econstructor;eauto.
    eapply H5 in H8;eauto.
    contradict H8.

    eapply npnsw_step_cur_valid_id in H3;eauto.
    assert(pc' = ({-|pc,cur_tid pc'})). inversion H2;auto.
    rewrite H8 in H3.
    eapply H6 in H3;eauto. simpl in H3.
    destruct H3.
    eapply Coqlib.nth_error_in;eauto.
  Qed.

  Lemma npnsw_or_sw_star_cons:
    forall ge pc fp pc' fp' pc'',
      npnsw_or_sw_star ge pc fp pc'->
      npnsw_or_sw_star ge pc' fp' pc''->
      npnsw_or_sw_star ge pc (FP.union fp fp') pc''.
  Proof. unfold npnsw_or_sw_star;intros;Hsimpl;eexists;eapply cons_star_star;eauto. Qed.

  Definition willdone := fun ge pc lt t=> (exists fp pc1, tau_star glob_npnsw_step ({-|pc,t}) fp pc1 /\ npnswdiverge ge ({-|pc1,cur_tid pc}) /\ isdone pc1 (cons t lt)).

  Lemma isdone_nil:  forall ge pc , @isdone ge pc nil.
  Proof. unfold isdone. intros. apply List.in_nil. Qed.
  Lemma isdone_app:
    forall ge pc t t',
      @isdone ge pc t->
      @isdone ge pc t'->
      @isdone ge pc (app t t').
  Proof.
    unfold isdone;intros.
    specialize (H _ _ _ _ H1 H2 H3).
    specialize (H0 _ _ _ _ H1 H2 H3).
    intro. apply List.in_app_iff in H4 as [];contradiction.
  Qed.
  Lemma mem_eq_npnswstep:
    forall ge pc pc' fp pc1 (modwdge:forall ix, mod_wd (GlobEnv.modules ge ix)),
      mem_eq_pc ge pc pc'->
      glob_npnsw_step pc tau fp pc1 ->
      exists pc2, mem_eq_pc ge pc1 pc2 /\
             glob_npnsw_step pc' tau fp pc2.
  Proof. destruct 3 as [|[]];eapply mem_eq_globstep in H;eauto;Hsimpl;eexists;split;try eapply npnswstep_l3;eauto. Qed.

  Lemma drf_pc_glob_cons_npnsw_star:
    forall (ge : GlobEnv.t) (pc : ProgConfig)(fp : FP.t) (pc' : ProgConfig) ,
      @drf_pc_glob ge pc ->
      tau_star glob_npnsw_step pc  fp pc' ->
      drf_pc_glob  pc'.
  Proof.
    intros;auto.
    induction H0. auto.
    rewrite <- pc_cur_tid with(pc:=s) in H0.
    eapply drf_pc_glob_cons_npnsw in H;eauto.
    Hsimpl. auto.
  Qed.
 
  Lemma mem_eq_npnswdiverge:
    forall ge pc pc' t (modwdge:forall ix ,mod_wd (GlobEnv.modules ge ix))(wdge:GlobEnv.wd ge),
      ThreadPool.inv pc.(thread_pool)->
      mem_eq_pc ge pc ({-|pc',t}) ->
      npnswdiverge ge pc ->
      npnswdiverge ge pc'.
  Proof.
    cofix.
    intros. inversion H1;subst.
    apply type_glob_step_exists in H3 as [].
    destruct x;try(inversion H3;fail).
    assert(v1:ThreadPool.inv pc'.(thread_pool)).
    destruct H0;Hsimpl. simpl in H0. congruence.
    eapply mem_eq_globstep in H0;eauto.
    Hsimpl.
    apply npnswstep_l1 in H4;Hsimpl.
    eapply mem_eq_globstep in H6;eauto.
    Hsimpl.
    apply npnswstep_l3 in H6;auto.
    apply type_glob_step_elim in H0.
    econstructor;eauto.
    destruct pc';inversion H0;subst. econstructor;eauto.
    rewrite <- pc_cur_tid in H8.
    eapply mem_eq_npnswdiverge in H8;auto.
    apply type_glob_step_elim in H3. apply type_glob_step_elim in H4.
    apply GE_mod_wd_tp_inv in H3;auto.
    apply GE_mod_wd_tp_inv in H4;auto.
  Qed.
  Lemma npnsw_or_sw_star_cons_npnsw_diverge:
    forall i l ge pc fp pc'(wdge:GlobEnv.wd ge),
      ThreadPool.inv pc.(thread_pool)-> atom_bit pc = O->
      npnsw_or_sw_stepN ge i l pc fp pc'->
      npnswdiverge ge pc'->
      npnswdiverge ge pc.
  Proof.
    induction 4;intros.
    auto. assert(l=tau). destruct H1 as [|[]];inversion H1;auto. subst.
    econstructor;eauto. apply npnsw_step_cur_valid_id in H1 as ?;auto.
    destruct pc,H4. simpl in *;subst;econstructor;eauto.
    apply npnsw_step_thdpinv in H1 as ?;auto.
    apply IHnpnsw_or_sw_stepN;auto. apply npnsw_step_O_preservation in H1;auto.

    apply type_glob_step_elim in H1 as ?.
    apply GE_mod_wd_tp_inv in H4;auto.
    assert(atom_bit pc' = O). inversion H1;auto.
    Hsimpl.

    inversion IHnpnsw_or_sw_stepN;subst.
    assert(glob_step pc sw FP.emp pc'0).
    inversion H7;subst. inversion H1;subst.
    econstructor;eauto.
    econstructor;eauto.
  Qed.
  Lemma npnswdiverge_notdone:
    forall ge pc pc' fp lt,
      drf_pc_glob pc->
      glob_npnsw_step pc tau fp pc'->
      npnswdiverge ge pc'->
      isdone pc lt ->
      ~ willdone ge pc lt (cur_tid pc)->
      exists fp1 pc1,
        tau_plus glob_npnsw_step pc' fp1 pc1/\
        npnswdiverge ge pc1/\
        isdone pc' lt /\
        ~ willdone ge pc' lt (cur_tid pc').
  Proof.
    intros.
    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    apply npnsw_step_tid_preservation in H0 as eq1.
    apply npnsw_step_thdpinv in H0 as v2;auto.
    apply npnsw_step_cur_valid_id in H0 as vpc1;auto.
    inversion H as [o1 _].
    unfold willdone in H3.
    assert(~ isdone pc' (cons (cur_tid pc')lt)).
    intro. contradict H3. Esimpl. econstructor 2. rewrite pc_cur_tid;eauto. constructor. 
    rewrite eq1,pc_cur_tid. eauto.
    rewrite eq1;auto.
    
    unfold isdone in H4.
    repeat apply not_all_ex_not in H4 as [].
    clear H4.

    rewrite <- pc_cur_tid with(pc:=pc) in H0.
    eapply drf_pc_glob_cons_npnsw in H as [];eauto.
    rewrite pc_cur_tid in *.

    eapply npnsw_step_cons_npnsw_or_sw_star in H0 as ?;eauto.
    eapply H2 in H5;eauto.
    specialize (H5 x4 x5).
    assert(cur_tid x0 = cur_tid pc').
    apply List.In_nth_error in x6 as [].
    destruct x6;simpl in H6. inversion H6;auto.
    contradict H5. eapply Coqlib.nth_error_in;eauto.

    rewrite H6 in *.
    pose proof drf_pc_glob_l1 _ _ H4 as [v' _].
    inversion H4 as [o2 _].
    apply npnsw_or_sw_stepN_exists in x3;auto;Hsimpl.
    apply npnsw_or_sw_stepN_atomO in H7 as o. destruct o as [o3 o4].
    eapply npnsw_or_sw_stepN_thdpinv in H7 as v3;eauto.
    apply npnsw_step_thdpinv in x4 as v4;auto.
    eapply npnsw_or_sw_star_div in H7;eauto;Hsimpl.
    rewrite H6 in *. rewrite pc_cur_tid in *.

    eapply mem_eq_npnswstep in H9 as ?;eauto;Hsimpl.
    eapply mem_eq_npnswdiverge in H11 as ?;eauto.

    assert(cur_tid x13 = cur_tid pc').
    rewrite <- H6; destruct H9;Hsimpl;auto.
    rewrite <- pc_cur_tid with(pc:=x13) , H14 in H12.
    assert(drf_pc_glob x11).
    eapply drf_pc_glob_cons_npnsw_star ;eauto.

    
    eapply drfsafe_npnsw_or_sw_stepN_npnswstep_fpsmile in H8 as ?;eauto.
    Hsimpl.
    eapply tau_plus_1 in H17.
    apply npnsw_taustar_tid_preservation in H7 as eq2. rewrite eq2,pc_cur_tid in H17.
    eapply tau_star_plus in H17;eauto.

    Esimpl;eauto.
    eapply mem_eq_npnswdiverge in H19;eauto.
    eapply npnsw_or_sw_star_cons_npnsw_diverge in H19;eauto.

    eapply tau_plus2star in H17. eapply npnsw_taustar_thdpinv;eauto.
    eapply npnsw_or_sw_stepN_atomO in H18 as [];auto.
    destruct H11;Hsimpl.
    congruence.

    unfold isdone.
    intros.
    eapply npnsw_step_cons_npnsw_or_sw_star in H20;eauto.

    intro.
    unfold willdone in H20.
    Hsimpl.
    contradict H3.

    rewrite pc_cur_tid in H20.
    eapply tau_star_cons in H20;eauto.
    rewrite eq1.
    Esimpl;eauto.
  Qed.

  Lemma npnswdiverge_notdone_tbc:
    forall ge pc pc' fp lt,
      drf_pc_glob pc->
      tau_plus glob_npnsw_step pc fp pc'->
      npnswdiverge ge pc'->
      isdone pc lt ->
      ~ willdone ge pc lt (cur_tid pc)->
      exists fp1 pc1,
        glob_npnsw_step pc tau fp1 pc1/\
        npnswdiverge ge pc1/\
        isdone pc lt /\
        ~ willdone ge pc lt (cur_tid pc).
  Proof.
    induction 2;intros. Esimpl;eauto.

    eapply drf_pc_glob_cons_npnsw in H as [];[|erewrite pc_cur_tid;eauto].
    assert(isdone s' lt).
    unfold isdone in *;intros.
    eapply npnsw_step_cons_npnsw_or_sw_star in H6;eauto.
    Hsimpl.
    apply npnsw_step_tid_preservation in H0 as ?.
    assert(~ willdone ge s' lt (cur_tid s')).
    rewrite<- H7.
    intro;contradict H4.
    unfold willdone in *;Hsimpl.
    rewrite <- pc_cur_tid,<- H7 in H0.
    eapply tau_star_cons in H4;eauto.
    rewrite pc_cur_tid. Esimpl;eauto.
    congruence.
    Hsimpl.
    Esimpl;eauto.
    pose proof drf_pc_glob_l1 _ _ H as [].
    eapply npnsw_step_thdpinv in H0 as ?;eauto.
    eapply npnsw_step_cur_valid_id in H9 as ?;eauto.
    econstructor;eauto.
    destruct H. apply npnsw_step_O_preservation in H0 as ?;auto.
    destruct s',H16;simpl in *;subst. econstructor;eauto.
  Qed.
    
  Lemma npnsw_tauplus_nonevtplus_np:
    forall ge pc fp pc',
      tau_plus glob_npnsw_step pc fp pc'->
      tau_plus (@np_step ge) pc fp pc'.
  Proof.
    induction 1;intros. apply glob_npnsw_step_to_np_step in H. econstructor;eauto.
    apply glob_npnsw_step_to_np_step in H.
    econstructor 2; eauto. 
  Qed.

  CoInductive npnsw_diverge'{ge}:@ProgConfig ge->Prop:=
    mk_npnsw_diverge':
      forall pc fp pc',
        atom_bit pc = O ->
        glob_npnsw_step pc tau fp pc'->
        npnsw_diverge' pc'->
        npnsw_diverge' pc.

  
  Lemma npnswdiverge_cur_tid_not_done_forever:
    forall ge pc pc' fp lt,
      drf_pc_glob pc->
      glob_npnsw_step pc tau fp pc'->
      npnswdiverge ge pc'->
      isdone pc lt ->
      ~ willdone ge pc lt (cur_tid pc)->
      npnsw_diverge' pc.
  Proof.
    cofix;intros.
    assert(drf_pc_glob pc'). rewrite <- pc_cur_tid with(pc:=pc) in H0; eapply drf_pc_glob_cons_npnsw in H as [];eauto.
    eapply npnswdiverge_notdone in H0 as ?;try eassumption.
    Hsimpl.
    
    eapply npnswdiverge_notdone_tbc in H5 as ?;try eassumption.
    Hsimpl.
    econstructor;eauto.
    inversion H;auto.
  Qed.

  Lemma cur_not_done:
    forall ge pc pc' fp lt,
      drf_pc_glob pc->
      glob_npnsw_step pc tau fp pc'->
      npnswdiverge ge pc'->
      isdone pc lt ->
      ~ List.In (cur_tid pc) lt.
  Proof.
    intros.
    eapply H2;eauto. econstructor. constructor.
  Qed.

  Lemma norep_split:
    forall l t,
      no_rep (cons t l)->
      no_rep l.
  Proof.
    unfold no_rep;intros.
    assert(S i < length(t::l)). simpl. Lia.lia.
    assert(S j < length(t::l)). simpl;Lia.lia.
    eapply H in H3;try apply H4;eauto.
  Qed.    
  Lemma norep_cons:
    forall l t,
      ~ List.In t l ->
      no_rep l->
      no_rep (cons t l).
  Proof.
    unfold no_rep;intros.

    destruct i,j;simpl in *.
    contradiction.

    intro. contradict H. eapply List.nth_error_In. eauto.
    intro. contradict H. eapply List.nth_error_In;eauto.

    eapply H0;eauto;Lia.lia.
  Qed.    
    
 


  Lemma if_will_cur_done:
    forall ge pc lt,
      drf_pc_glob pc-> cur_valid_id ge pc ->
      isdone pc lt ->
      pcvalid pc lt->
      no_rep lt ->
      ~ List.In (cur_tid pc) lt ->
      willdone ge pc lt (cur_tid pc)->
      exists fp pc',
        drf_pc_glob pc'/\ cur_valid_id ge pc' /\ cur_tid pc = cur_tid pc' /\
        tau_star glob_npnsw_step pc fp pc'/\ npnswdiverge ge pc' /\
        isdone pc' (cons (cur_tid pc) lt) /\
        pcvalid pc' (cons (cur_tid pc) lt) /\
        no_rep  (cons (cur_tid pc) lt).
  Proof.
    unfold willdone.
    intros.
    Hsimpl. rewrite pc_cur_tid in *.
    apply npnsw_taustar_tid_preservation in H5 as ?.
    rewrite H8,pc_cur_tid in H6.
    eapply drf_pc_glob_cons_npnsw_star in H;eauto.
    assert(cur_valid_id ge x0).
    eapply npnsw_taustar_pc_valid_tid_preservation in H5;eauto. rewrite<- H8.
    auto.
    Esimpl;eauto.
    
    unfold pcvalid. intros.
    eapply List.In_nth_error in H10 as [];eauto.
    destruct x1.
    simpl in H10. inversion H10;auto. rewrite H8;auto.

    simpl in H10. apply List.nth_error_In in H10.
    eapply H2 in H10. eapply npnsw_taustar_pc_valid_tid_preservation ;eauto.

    eapply norep_cons;eauto.
    
  Qed.

  Lemma if_will_cur_done_tbc:
    forall ge pc lt,
      drf_pc_glob pc ->
      npnswdiverge ge pc ->
      isdone pc (cons (cur_tid pc) lt) ->
      pcvalid pc (cons (cur_tid pc) lt) ->
      no_rep  (cons (cur_tid pc) lt)->
      exists fp pc1 pc2,
        glob_step pc sw FP.emp pc1 /\
        glob_npnsw_step pc1 tau fp pc2 /\
        ~ List.In (cur_tid pc2) (cons (cur_tid pc) lt) /\
        drf_pc_glob pc1 /\ cur_valid_id ge pc1/\
        npnswdiverge ge pc1/\npnswdiverge ge pc2/\
        isdone pc1 (cons (cur_tid pc) lt)/\
        pcvalid pc1 (cons (cur_tid pc) lt)/\
        no_rep (cons (cur_tid pc) lt).
  Proof.
    intros.
    inversion H0;subst.
    Esimpl;eauto. apply npnsw_step_tid_preservation in H6 as ?. rewrite <- H8.
    eapply H1;eauto. econstructor. econstructor 2;[|constructor]. right.
    inversion H5;subst;econstructor;eauto.
    
    eapply drf_pc_glob_cons;eauto. econstructor 2;[|constructor];eauto. inversion H5;auto.
    eapply npnsw_step_cur_valid_id in H6;eauto.
    inversion H5;subst;auto.
    econstructor;eauto. inversion H5;subst;auto.
    inversion H5;subst;econstructor;eauto.
    unfold isdone.
    intros.
    eapply swstar_cons_npnsw_or_sw_star in H8;eauto.
    econstructor 2;eauto. constructor.

    unfold pcvalid.
    intros. eapply H2 in H8.
    inversion H5;subst. destruct H8;split;auto.
  Qed.
    
  Lemma if_will_cur_done_tbc2:
    forall ge pc lt,
      drf_pc_glob pc-> cur_valid_id ge pc ->
      isdone pc lt ->
      pcvalid pc lt->
      no_rep lt ->
      ~ List.In (cur_tid pc) lt ->
      willdone ge pc lt (cur_tid pc)->
      exists fp fp2 pc' pc1 pc2,
        tau_star glob_npnsw_step pc fp pc'/\
        glob_step pc' sw FP.emp pc1 /\
        glob_npnsw_step pc1 tau fp2 pc2 /\
        ~ List.In (cur_tid pc2) (cons (cur_tid pc) lt) /\
        drf_pc_glob pc1 /\ cur_valid_id ge pc1/\
        npnswdiverge ge pc1/\npnswdiverge ge pc2/\
        isdone pc1 (cons (cur_tid pc) lt)/\
        pcvalid pc1 (cons (cur_tid pc) lt)/\
        no_rep (cons (cur_tid pc) lt).
  Proof.
    intros. eapply if_will_cur_done in H5;eauto. Hsimpl.
    rewrite H7 in *.
    eapply if_will_cur_done_tbc in H9 as ?;eauto.
    Hsimpl.
    Esimpl;eauto.
  Qed.

  Definition thread_nums {ge}(pc:@ProgConfig ge):nat:=
    BinPos.Pos.to_nat pc.(thread_pool).(ThreadPool.next_tid).

  Lemma thread_nums_preserve:
    forall ge pc l fp pc',
      star (@glob_step ge) pc l fp pc'->
      thread_nums pc' = thread_nums pc.
  Proof.
    induction 1;intros.
    auto. unfold thread_nums.
    inversion H;subst;auto;solv_thread.
  Qed.

  Lemma norep_nodup:
    forall l,
      no_rep l ->
      List.NoDup l.
  Proof.
    unfold no_rep.
    intros.
    apply List.NoDup_nth_error.
    intros.
    destruct (Nat.eq_dec i j);auto.
    apply H in n;auto. contradiction.
    apply List.nth_error_Some in H0.
    rewrite H1 in H0.
    apply List.nth_error_Some in H0. auto.
  Qed.
  Lemma maxi:
    forall ge pc lt, 
     @pcvalid ge pc lt->
     no_rep lt ->
     length lt < thread_nums pc.
  Proof.
    intros.
    apply norep_nodup in H0.
    unfold thread_nums.
    unfold pcvalid in H.
    eapply incl_length_lt;eauto.
    intros.
    eapply H in H1.
    
    destruct H1;auto.
  Qed.
       

  Lemma if_will_cur_done_tbc3:
    forall i ge pc lt fp pc',
      drf_pc_glob pc-> cur_valid_id ge pc ->
      glob_npnsw_step pc tau fp pc'->
      npnswdiverge ge pc'->
      isdone pc lt ->
      pcvalid pc lt->
      no_rep lt ->
      ~ List.In (cur_tid pc) lt ->
      i = thread_nums pc - length lt ->
      exists fp1 pc1 lt' fp2 pc2,
        drf_pc_glob pc1/\ npnswdiverge ge pc2 /\
        npnsw_or_sw_star ge pc fp1 pc1 /\
        glob_npnsw_step pc1 tau fp2 pc2 /\
        isdone pc1 lt'/\
        ~ willdone ge pc1 lt' (cur_tid pc1).
  Proof.
    induction i.
    intros.
    eapply maxi in H4;eauto.
    assert(thread_nums pc' = thread_nums pc).
    apply npnswstep_l1 in H1;Hsimpl. apply type_glob_step_elim in H1.
    eapply thread_nums_preserve.  econstructor 2;[|constructor];eauto.
    Lia.lia.

    intros.
    assert(willdone ge pc lt (cur_tid pc) \/ ~ willdone ge pc lt (cur_tid pc)).
    apply classic.
    destruct H8.
    
    Focus 2. Esimpl;eauto. econstructor. constructor.
    eapply if_will_cur_done_tbc2 in H as ?;eauto.
    Hsimpl.

    assert(length (cons (cur_tid pc) lt) = S (length lt)).
    simpl. auto.
    assert(i = thread_nums pc - length (cur_tid pc :: lt)).
    rewrite H20. Lia.lia.

    clear H20.
    apply npnsw_taustar_tid_preservation in H9 as ?;auto.
    rewrite H20 in *.
    
    assert(thread_nums x2 = thread_nums pc).
    apply npnsw_taustar_to_taustar in H9;apply tau_star_to_star in H9 as [].
    eapply star_cons_step in H10;eauto.
    Hsimpl. eapply thread_nums_preserve;eauto.
    rewrite<- H22 in H21. 

    eapply IHi in H21;eauto.
    Hsimpl.

    enough(npnsw_or_sw_star ge pc (FP.union x x4) x5).
    Esimpl;eauto.
    eapply swstar_cons_npnsw_or_sw_star in H24;[|econstructor 2;[|constructor]];eauto.
    eapply npnsw_star_cons_npnsw_or_sw_star;eauto.

    intro.
    apply npnsw_step_tid_preservation in H11 as ?.
    rewrite H24 in H23.
    contradiction.
  Qed.

  Lemma npnswdiverge_will_forever:
    forall ge pc fp pc',
      drf_pc_glob pc-> cur_valid_id ge pc ->
      glob_npnsw_step pc tau fp pc'->
      npnswdiverge ge pc'->
      exists fp1 pc1 ,
        drf_pc_glob pc1 /\
        npnsw_or_sw_star ge pc fp1 pc1 /\
        npnsw_diverge' pc1.
  Proof.
    intros.
    pose proof isdone_nil ge pc.
    assert(pcvalid pc nil). unfold pcvalid. intros. inversion H4.
    assert(no_rep nil). unfold no_rep. intros.
    inversion H6.
    assert( ~ List.In (cur_tid pc) nil).
    intro;inversion H6.

    eapply if_will_cur_done_tbc3 in H6;eauto.
    Hsimpl.
    eapply npnswdiverge_cur_tid_not_done_forever in H7;eauto.
  Qed.

  Lemma npnswdiverge_AO_psilent_diverge:
    forall ge pc fp1 pc1,
      drf_pc_glob pc1->
      npnsw_or_sw_star ge pc fp1 pc1 ->
      npnsw_diverge' pc1->
      AO_psilent_diverge (cur_tid pc1) pc.
  Proof.
    cofix.
    inversion 3;subst.
    econstructor;eauto.

    pose proof drf_pc_glob_l1 _ _ H as [].
    pose proof drf_pc_glob_l2 _ _ H as ?.
    inversion H as [? _].
    apply npnsw_step_tid_preservation in H3 as ?.
    rewrite H9.
    
    eapply npnswdiverge_AO_psilent_diverge;eauto;[|econstructor;constructor].
    rewrite <- pc_cur_tid with(pc:=pc1) in H3.
    eapply drf_pc_glob_cons_npnsw in H as [];eauto.
  Qed.    
End diverge_proof.

Lemma AO_psilent_diverge_exists:
  forall ge pc,
    drf_pc_glob pc->
    npnswdiverge ge pc->
    exists t,AO_psilent_diverge t pc.
Proof.
  inversion 2;subst.
  assert(drf_pc_glob pc').
  eapply drf_pc_glob_cons;eauto. econstructor 2;eauto. constructor.
  inversion H2;auto.

  pose proof drf_pc_glob_l1 _ _ H5 as [].
  assert(cur_valid_id ge pc'). inversion H2;subst;split;auto.
  eapply npnswdiverge_will_forever in H3;eauto.
  Hsimpl.
  destruct H9. 
  eapply npnswdiverge_AO_psilent_diverge in H10;eauto.
  econstructor. econstructor 2;eauto. right;eauto. inversion H2;subst;econstructor;eauto.
Qed.  
 Lemma npnswdiverge_npdiverge:
  forall ge pc,
    drf_pc_glob pc->
    npnswdiverge ge pc ->
    exists t, pc_valid_tid pc t /\ npsilent_diverge ge ({-|pc,t}).
Proof.
  intros.
  apply AO_psilent_diverge_exists in H0.
  destruct H0.
  exists x.
  split. apply AO_psilent_diverge_valid_t;auto.
  revert pc x H H0.
  cofix.
  intros.
  eapply drf_safe_AO_psilent_diverge_inv in H0;Hsimpl;try apply H.
  econstructor;eauto. constructor.
  apply glob_npnsw_step_to_np_step in H1 as ?. 
  Focus 2. eapply npnswdiverge_npdiverge;eauto.
  apply npnsw_step_tid_preservation in H1. simpl in H1. rewrite H1,pc_cur_tid.
  rewrite H1 in H3. eauto.
  auto.
Qed.
  
  Lemma Etr_p_np_diverge:
    forall ge pc,
      drf_pc_glob pc->
      Etr (@glob_step ge) abort final_state pc Behav_diverge->
      Etr np_step np_abort final_state pc Behav_diverge \/ exists t,Etr np_step np_abort final_state ({-|pc,t}) Behav_diverge /\ pc_valid_tid pc t .
  Proof.
    intros.
    inversion H0;subst;clear H0.
    enough(silent_diverge np_step pc \/ exists t, pc_valid_tid pc t /\ silent_diverge np_step ({-|pc,t})).
    destruct H0;Hsimpl.
    left. econstructor;eauto.
    right. Esimpl;eauto. econstructor;eauto.

    pose proof drf_pc_glob_l1 _ _ H as [v1 wdge].
    pose proof drf_pc_glob_l2 _ _ H as modwdge.
    inversion H as [? _].
    apply psilent_diverge_case in H1;auto.
    destruct H1 as [|[]];Hsimpl.
    eapply  case_coreIdiverge in H2;eauto.
    destruct H2;auto. Hsimpl. right;Esimpl;eauto.
    
    apply noevt_stepN_exists in H1 as [].
    destruct x1. apply noevt_stepN_0 in H1;Hsimpl;subst.
    assert(drf1:drf_pc_glob x0).

    apply swstar_globstar in H3 as ?. Hsimpl.
    eapply drf_pc_glob_cons;eauto.
    inversion H2;subst. inversion H5;auto.
    apply npnswdiverge_npdiverge in H2;auto.
    rewrite (swstar_l1 _ _ _ H3) in H2. simpl in H2. auto.

    assert(atom_bit x0 = O). inversion H2;subst. inversion H4;auto.
    
    eapply noevt_stepN_Si_Oinv_drfsafe in H1;auto;Hsimpl.
    assert(ThreadPool.inv x6.(thread_pool)).
    rewrite (swstar_l1 _ _ _ H1);auto.
    apply atomblockstarN_invpc_preservation in H4 as ?;auto.
    apply atomblockstarN_atomO in H4 as ?;Hsimpl.
    apply npnsw_or_sw_stepN_exists in H5 as [?[]];auto.
    apply npnsw_or_sw_stepN_thdpinv in H5 as ?;auto.
    assert(invpc ge x0). destruct H6;Hsimpl. unfold invpc in *.
    simpl in *. congruence.

    apply mem_eq_npnswdiverge in H6;auto.
    eapply npnsw_or_sw_star_cons_npnsw_diverge in H5;eauto.

    clear x0 x8 H11 H6 H2 H12 H3.
    destruct x2.
    {
      inversion H4;subst;clear H4.
      apply npnswdiverge_npdiverge in H5.
      Hsimpl.
      rewrite (swstar_l1 _ _ _ H1) in H3,H4.
      simpl in *. right. Esimpl;eauto.
      apply swstar_globstar in H1. Hsimpl.
      eapply drf_pc_glob_cons;eauto.
    }
    {
      apply npnswdiverge_npdiverge in H5;Hsimpl.
      assert(sw_star glob_step x7 ({-|x7,x0})).
      econstructor 2;[|constructor].
      destruct x7,H2;simpl in *;subst;econstructor;eauto.
      eapply atomblockstarN_cons_swstar in H4;eauto.
      apply atomblockstarN_np in H4;auto;[|Lia.lia].
      Hsimpl.
      destruct H6;Hsimpl.
      assert(sw_star glob_step ({-|x7,x11})({-|x7,x0})).
      econstructor 2;[|constructor].
      destruct x7,H2;simpl in *;subst;econstructor;eauto.
      eapply npsw_swstar in H6;eauto.
      assert(non_evt_star np_step x8 (FP.union FP.emp FP.emp) ({-|x7,x0})).
      econstructor 2;eauto. constructor.
      eapply non_evt_star_cons in H12;eauto.
      apply silent_diverge_cons_np_non_evt_star in H12;eauto.
      apply swstar_l3 in H1 as [].
      subst. auto.
      inversion H1;subst.
      right. Esimpl;eauto. split;auto.

      inversion H6;subst;destruct H2.
      apply H_all_thread_halted in H2. congruence.

      apply swstar_globstar in H1;Hsimpl.
      apply atomblockstarN_star in H4;Hsimpl.
      eapply cons_star_star in H2;eauto.
      eapply drf_pc_glob_cons;eauto.
    }
      
    eapply blockdiverge_npsilent_diverge in H1;eauto.
    right. Hsimpl. Esimpl;eauto.
  Qed.


  Lemma limited_etr_p_cons_non_evt_star:
     forall ge i pc b,
       limited_etr i (@glob_step ge) abort final_state pc b->
       forall pc0 fp,
         non_evt_star glob_step pc0 fp pc->
         limited_etr i glob_step abort final_state pc0 b.
  Proof.
    inversion 1;subst;intros;try (econstructor;inversion H0;subst;eapply non_evt_star_cons in H2;eauto;econstructor;eauto).
    inversion H0;subst.
    
    eapply silent_diverge_cons_glob_non_evt_star in H2;eauto.
    constructor;econstructor;eauto.
    
    eapply non_evt_star_cons in H1;eauto.
    econstructor;eauto.
  Qed.

  Lemma glob_evt_step_sw:
    forall ge pc v pc',
      @glob_step ge pc (evt v) FP.emp pc'->
      ThreadPool.inv pc.(thread_pool)->
      GlobEnv.wd ge->
      glob_step pc' sw FP.emp pc'.
  Proof.
    inversion 1;subst;intros.
    econstructor.
    eapply gettop_valid_tid;eauto.
    solv_thread.
    eapply GE_mod_wd_tp_inv in H;eauto.
    intro.
    solv_thread.
  Qed.
  Lemma glob_evt_step_np:
    forall ge pc v pc',
      @glob_step ge pc (evt v) FP.emp pc'->
      ThreadPool.inv pc.(thread_pool)->
      GlobEnv.wd ge->
      np_step pc (evt v) FP.emp pc'.
  Proof.
    intros.
    eapply glob_evt_step_sw in H as L1;eauto.
    inversion H;subst.
    inversion L1;subst.
    econstructor;eauto.
  Qed.
      


  
  Definition mod_wd_ge (ge:GlobEnv.t):Prop:=
    forall ix,
      mod_wd (GlobEnv.modules ge ix).
  Lemma mem_eq_pc_limited_etr_p:
    forall i ge pc pc' b,
      mod_wd_ge ge->
      mem_eq_pc ge pc pc'->
      limited_etr i glob_step abort final_state pc b->
      limited_etr i glob_step abort final_state pc' b.

  Proof.
    induction i;intros.
    inversion H1;subst.
    {
      inversion H2;subst.
      eapply mem_eq_non_evt_star in H3 as (?&?&?);eauto.
      eapply mem_eq_pc_finalstate in H5;eauto.
      econstructor;eauto.
      econstructor;eauto.
    }
    {
      inversion H2;subst.
      eapply mem_eq_non_evt_star in H3 as (?&?&?);eauto.
      eapply mem_eq_pc_abort in H5;eauto.
      econstructor;eauto.
      econstructor;eauto.
    }
    {
      inversion H2;subst.
      eapply mem_eq_pc_silent_diverge in H3;eauto.
      constructor. econstructor;eauto.
    }
    {
      inversion H1;subst.
      eapply mem_eq_non_evt_star in H4 as (?&?&?);eauto.
      apply type_glob_step_exists in H5 as [].
      destruct x0;try(inversion H5;fail).
      eapply mem_eq_globstep in H5 as (?&?&?);eauto.
      apply type_glob_step_elim in H5.
      eapply IHi in H3;eauto.
      econstructor;eauto.
    }
  Qed.

  Lemma limited_etr_p_np_base:
    forall ge pc B,
      drf_pc_glob pc->
      limited_etr 0 (@glob_step ge) abort final_state pc B->
      (limited_etr 0 np_step np_abort final_state pc B) \/ (exists t,limited_etr 0 np_step np_abort final_state ({-|pc,t}) B /\ pc_valid_tid pc t ) .
  Proof.
    inversion 2;subst.
    eapply Etr_p_np_done in H1;eauto.
    destruct H1. left.
    econstructor;eauto.
    right.
    destruct H1 as (?&?&?).
    exists x;split;auto. econstructor;eauto.
    eapply Etr_p_np_abort in H1;eauto.
    destruct H1. left.
    econstructor;eauto.
    right.
    destruct H1 as (?&?&?).
    exists x;split;auto. econstructor;eauto.
    eapply Etr_p_np_diverge in H1;eauto.
    destruct H1. left.
    econstructor;eauto.
    right.
    destruct H1 as (?&?&?).
    exists x;split;auto. econstructor;eauto.
  Qed.
  Lemma limited_etr_p_np_ind:
    forall i ge pc  B,
      drf_pc_glob pc->
      atom_bit pc = O->
      limited_etr (S i) (@glob_step ge) abort final_state pc B->
      exists t,limited_etr (S i) np_step np_abort final_state ({-|pc,t}) B /\ pc_valid_tid pc t.
  Proof.
    induction i;intros.
    {
      inversion H1;subst;clear H1.

      eapply drf_pc_non_evt_star_evt_step_inv in H4 as L1;eauto.
      destruct L1 as (t'&valid1&?&?&?&eq'&?&?&?&?&?&eq0).
      
      specialize (drf_pc_glob_l2 ge pc H) as modwd.
      eapply mem_eq_pc_limited_etr_p in H3;eauto.
      eapply limited_etr_p_cons_non_evt_star in H3;eauto.

      eapply pc_valid_tid_nonevtstar_cons_evtstep in H4 as ?;eauto.
      apply non_evt_thrd_globstar_star in H1 as L1.
      destruct L1 as [l L1].
      assert (pc_valid_tid pc (cur_tid pc')).
      inversion H5;subst;auto.

      assert(drf_pc_glob x0).
      eapply drf_pc_glob_cons;eauto.
      eapply star_step;eauto.
      instantiate(2:=sw).
      instantiate(1:=FP.emp).
      destruct pc;simpl in *;subst;destruct valid1;econstructor;eauto.
      inversion H2;auto.
      assert(drf_pc_glob x1).
      eapply drf_pc_glob_cons;eauto.
      eapply star_step;eauto. constructor.
      inversion H2;auto.
      apply drf_pc_glob_l1 in H9 as [].
      apply non_evt_thrd_globstar_np_nonevt_star in H1 as R1;auto.
      apply glob_evt_step_np in H2 as R2;auto.

      apply limited_etr_p_np_base in H3;auto.
      destruct H3.
      eexists;split;auto.
      econstructor;eauto.
      auto.

      destruct H3 as (?&?&?).
      eexists;split;auto.
      econstructor;eauto.
      inversion R2;subst. destruct H12.
      econstructor;eauto.
      auto.
      inversion H2;subst.
      split. eapply gettop_valid_tid;auto. solv_thread.
      intro. solv_thread.

      apply drf_pc_glob_l1 in H as [];auto.
    }
    {
      inversion H1;subst;clear H1.

      eapply drf_pc_non_evt_star_evt_step_inv in H4 as L1;eauto.
      destruct L1 as (t'&valid1&?&?&?&eq00&?&?&?&?&?&eq').
      specialize (drf_pc_glob_l2 _ _ H) as modwd.
      eapply mem_eq_pc_limited_etr_p in H3;eauto.
      eapply limited_etr_p_cons_non_evt_star in H3;eauto.

      eapply pc_valid_tid_nonevtstar_cons_evtstep in H4 as ?;eauto.
      apply non_evt_thrd_globstar_star in H1 as L1.
      destruct L1 as [l L1].
      assert (pc_valid_tid pc (cur_tid pc')).
      inversion H5;subst;auto.

      assert(drf_pc_glob x0).
      eapply drf_pc_glob_cons;eauto.
      eapply star_step;eauto.
      instantiate(1:=FP.emp).
      instantiate(1:=sw).
      destruct pc;simpl in *;subst;destruct valid1;econstructor;eauto.
      inversion H2;auto.
      assert(drf_pc_glob x1).
      eapply drf_pc_glob_cons;eauto.
      eapply star_step;eauto. constructor.
      inversion H2;auto.
      apply drf_pc_glob_l1 in H9 as [].
      apply non_evt_thrd_globstar_np_nonevt_star in H1 as R1;auto.
      apply glob_evt_step_np in H2 as R2;auto.

      eapply IHi in H3 as [?[]];eauto.
      eexists;split;auto.
      econstructor;eauto.
      destruct H12. inversion H2;subst. econstructor;eauto.
      inversion H2;auto.
      inversion H2;auto.

      inversion H2;subst. 
      split. eapply gettop_valid_tid;auto. solv_thread.
      intro. solv_thread.
      apply drf_pc_glob_l1 in H as [];auto.
    }    
  Qed.   

  Lemma limited_etr_p_np:
    forall i ge pc B,
      drf_pc_glob pc ->
      atom_bit pc = O->
      limited_etr i (@glob_step ge) abort final_state pc B->
      (limited_etr i np_step np_abort final_state pc B) \/
      (exists t,limited_etr i np_step np_abort final_state ({-|pc,t}) B /\ pc_valid_tid pc t).
  Proof.
    destruct i;intros.
    eapply limited_etr_p_np_base;eauto.
    right. eapply limited_etr_p_np_ind;eauto.
  Qed.


  CoInductive glob_inf_etr {ge}:@ProgConfig ge->behav->Prop:=
  | build_inf_etr_glob:
      forall pc  b,
        glob_inf_etr pc  b->
        forall pc0 pc01 fp0 pc1 v,
          glob_step pc0 sw FP.emp pc01 ->
          non_evt_thrd_globstar ge pc01 fp0 pc1 ->
          glob_step pc1 (evt v)FP.emp pc ->
          glob_inf_etr pc0 (Behav_cons v b).
  Lemma mem_eq_inf_etr:
    forall ge,
      (forall ix,mod_wd (GlobEnv.modules ge ix))->
      forall a f pc b,
      inf_etr_alt2 (@glob_step ge) a f pc b->
      forall pc',
        mem_eq_pc ge pc pc'->
        inf_etr_alt2 glob_step a f pc' b.
  Proof.
    intros ge modwdge.
    cofix.
    intros.
    inversion H;subst.
    eapply mem_eq_non_evt_star in H2;try apply H0;auto.
    Hsimpl.
    apply type_glob_step_exists in H3 as [].
    apply type_glob_step_exists in H4 as [].
    eapply mem_eq_globstep in H3;try apply H5;auto.
    Hsimpl.
    eapply mem_eq_globstep in H4;try apply H6;auto.
    Hsimpl.
    apply type_glob_step_elim in H3.
    apply type_glob_step_elim in H4.
    econstructor;try eapply mem_eq_inf_etr;eauto.
  Qed.
    
  Lemma inf_etr_glob_inf_etr:
    forall ge ab fn pc b,
      drf_pc_glob pc->
      inf_etr_alt2 (@glob_step ge) ab fn pc b->
      glob_inf_etr pc b.
  Proof.
    cofix.
    intros.
    specialize (drf_pc_glob_l2 _ _ H) as modwdge.
    inversion H0;subst.
    eapply drf_pc_non_evt_star_evt_step_inv in H2;try apply H3;auto.
    Hsimpl.
    apply type_glob_step_exists in H4 as ?;auto.
    Hsimpl.
    eapply mem_eq_globstep in H9 as ?;try apply H10;auto.
    Hsimpl.
    assert(non_evt_star glob_step x4 FP.emp x6).
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    econstructor;eauto. right;eapply type_glob_step_elim;eauto.
    constructor.

    eapply mem_eq_inf_etr in H12 as ?;try apply H1;auto.

    eapply non_evt_star_cons in H13;try apply H8;auto.
    eapply non_evt_star_cons_inf_etr_alt2  in H14;try apply H13;auto.

    enough(drf_pc_glob x2).
    econstructor;try eapply inf_etr_glob_inf_etr;eauto.
    inversion H as (?&_).
    destruct pc,H2;simpl in *;subst;econstructor;eauto.

    assert(glob_step pc sw FP.emp ({-|pc,x})).
    inversion H as (?&_).
    destruct pc,H2;simpl in *;subst;econstructor;eauto.
    destruct H5;Hsimpl.
    apply atomblockstarN_star in H5 as [].
    apply tau_star_to_star in H16 as [].
    apply npnsw_star_glob_star in H16.
    eapply cons_star_star in H16;eauto.
    eapply star_step in H16;eauto.
    eapply star_cons_step in H7 as ?;eauto.
    destruct H18.
    eapply drf_pc_glob_cons;eauto.
    inversion H7;auto.
  Qed.
    

  CoInductive glob_inf_etr_2 {ge}:@ProgConfig ge->behav->Prop:=
  | build_inf_etr_glob2:
      forall pc  b,
        glob_inf_etr_2 pc  b->
        forall pc0 fp0 pc1 v pc2,
          non_evt_thrd_globstar ge pc0 fp0 pc1 ->
          glob_step pc1 (evt v)FP.emp pc2 ->
          glob_step pc2 sw FP.emp pc ->
          glob_inf_etr_2 pc0 (Behav_cons v b).

  Lemma glob_inf_etr_l1:
    forall ge pc pc',
      @glob_step ge pc sw FP.emp pc'->
      forall b,
        glob_inf_etr_2 pc' b->
        glob_inf_etr pc b.
  Proof.
    cofix;intros.
    inversion H0;subst.
    econstructor;try eapply glob_inf_etr_l1;eauto.
  Qed.
  Lemma glob_inf_etr_l2:
    forall ge pc0 fp0 pc1 v pc2 b,
      non_evt_thrd_globstar ge pc0 fp0 pc1 ->
      glob_step pc1 (evt v)FP.emp pc2 ->
      glob_inf_etr pc2 b->
      glob_inf_etr_2 pc0 (Behav_cons v b).
  Proof.
    cofix.
    intros.
    inversion H1;subst.
    econstructor;try eapply glob_inf_etr_l2; eauto.
  Qed.    

  Lemma glob_inf_etr_l3:
    forall ge pc b,
      @glob_inf_etr ge pc b->
      exists pc',
        glob_step pc sw FP.emp pc' /\ glob_inf_etr_2 pc' b.
  Proof.
    inversion 1;subst.
    eapply glob_inf_etr_l2 in H0;eauto.
  Qed.

  


  Lemma non_evt_thrd_globstar_inv_preserve:
    forall ge pc fp pc',
      GlobEnv.wd ge->
      @non_evt_thrd_globstar ge pc fp pc'->
      invpc ge pc->
      invpc ge pc'.
  Proof.
    destruct 2;intros;Hsimpl.
    eapply atomblockstarN_invpc_preservation in H0;eauto.
    eapply npnsw_taustar_thdpinv;eauto.
  Qed.
  Lemma glob_inf_etr_np:
    forall ge pc pc' b,
      GlobEnv.wd ge ->
      (forall ix,mod_wd (GlobEnv.modules ge ix))->
      invpc ge pc->
      @glob_step ge pc sw FP.emp pc'->
      glob_inf_etr_2 pc' b->
      inf_etr np_step np_abort final_state pc' b.
  Proof.
    cofix;inversion 5;subst.
    apply GE_mod_wd_tp_inv in H2 as ?;auto.
    apply non_evt_thrd_globstar_inv_preserve in H5 as ?;auto.
    assert(cur_valid_id ge pc2).
    inversion H6;subst. split;[eapply gettop_valid_tid|intro];eauto. solv_thread.
    apply non_evt_thrd_globstar_np_nonevt_star in H5 as ?;auto.
    assert(np_step pc2 (evt v) FP.emp pc0).
    inversion H6;subst;inversion H7;subst;econstructor;eauto.

    assert(glob_step pc0 sw FP.emp pc0).
    inversion H7;subst;econstructor;eauto.
    econstructor;try eapply glob_inf_etr_np;try apply H12;try apply H13;eauto.

    eapply GE_mod_wd_tp_inv in H6;eauto.
    eapply GE_mod_wd_tp_inv;eauto.
  Qed.

  Lemma config_refine_alt:
    forall sge spc tge tpc t,
      @config_refine tge sge tpc spc->
      atom_bit tpc = O->
      pc_valid_tid tpc t->
      config_refine ({-|tpc,t}) spc.
  Proof.
    unfold config_refine. intros.
    apply H.
    eapply Etr_cons_globsw;eauto.
    destruct tpc,H1;simpl in *;subst;econstructor;eauto.
  Qed.    
  Lemma init_pair_config_refine:
    forall NL L sc tc e sgm sge spc tgm tge tpc i i',
      @init_config NL L (sc,e) sgm sge spc i->
      @init_config NL L (tc,e) tgm tge tpc i'->
      config_refine ({-|tpc,i}) spc->
      config_refine tpc spc.
  Proof.
    intros. apply init_property_1_alt in H0 as ?.
    assert(i'=cur_tid tpc). inversion H0;auto. subst.
    assert(tpc = ({-|tpc,cur_tid tpc})). destruct tpc;auto.
    rewrite H3.
    eapply config_refine_alt in H1;eauto;simpl.
    inversion H0;auto.
  Qed.
    
  Lemma np_p_config_refine_weak_proof{NL L}:
    forall P (H:True),
      wd_langs (fst P) ->
      forall (gm : gmem) (ge : GlobEnv.t) (pc : ProgConfig),
        @init_config NL L P gm ge pc (cur_tid pc) ->
        forall (B : behav) (HSafe:safe_state glob_step abort pc)(Hdrf:drfpc pc),
          Etr glob_step abort final_state pc B ->
          exists t : tid,
            Etr np_step np_abort final_state ({-|pc, t}) B /\ pc_valid_tid pc t.
  Proof.
    intros p H wdl;intros.
    assert((exists i,limited_etr i glob_step abort final_state pc B) \/ (~ exists i,limited_etr i glob_step abort final_state pc B)).
    apply classic.
    destruct H2.

    destruct H2.
    apply limited_etr_p_np in H2.
    destruct H2.
    apply limited_etr_npetr in H2;eauto.
    exists (cur_tid pc);rewrite pc_cur_tid;split;auto.
    eapply init_property_1_alt;eauto.

    destruct H2 as (?&?&?).
    apply limited_etr_npetr in H2.
    exists x0. split;auto.

    unfold drf_pc_glob;unfold drf_pc.
    split. inversion H0;auto.
    do 4 eexists;eauto.
    do 4 eexists;eauto. 
    constructor.
    inversion H0;auto.


    assert(drf_pc_glob pc).
    unfold drf_pc_glob. split. inversion H0;auto.
    unfold drf_pc. Esimpl;eauto. constructor.
    apply drf_pc_glob_l1 in H3 as ?;destruct H4.
    specialize (drf_pc_glob_l2 _ _ H3) as ?.
    assert(inf_etr_alt glob_step abort final_state pc B).
    split;auto.
    apply inf_etr_alt_sound in H7.
    eapply inf_etr_alt2_p in H7;eauto.
    apply inf_etr_glob_inf_etr in H7;auto.

    apply glob_inf_etr_l3 in H7.
    Hsimpl.

    eapply glob_inf_etr_np in H8;eauto.
    apply inf_etr_etr in H8.
    apply init_property_1_alt in H0 as ?.
    exists (cur_tid x). split;auto.
    inversion H7;subst;auto.

    eapply GE_mod_wd_tp_inv in H5;eauto.
    inversion H7;subst.   
    split;auto.
  Qed.

  Lemma np_p_refine_weak {NL}{L}:
    forall P,
      wd_langs (fst P)->
      safe_prog P->
      drf P->
      @np_p_prog_refine_weak NL L P.
  Proof.
    intros.
    unfold np_p_prog_refine_weak.
    unfold np_p_config_refine_weak.
    intros.
    eapply np_p_config_refine_weak_proof;eauto.
    eapply H0;eauto.
    eapply drf_drfpc;eauto.
  Qed.
  Lemma DRF_NP_Refine_Config_Proof:
    forall NL L mu su tu e sgm sge spc st tgm tge tpc tt,
      @wd_langs NL L su ->
      @wd_langs NL L tu ->
      (forall t : tid, DRFLemmas.pc_valid_tid tpc t -> np_safe_config ({-|tpc, t})) ->
      InitRel mu sge tge sgm tgm->
      init_config (su,e) sgm sge spc st->
      init_config (tu,e) tgm tge tpc tt->
      drf (su,e)->
      drfpc tpc->
      np_prog_refine (su,e)(tu,e)->
      config_refine tpc spc.
  Proof.
    intros. inversion H7;subst. clear H7. unfold np_config_refine in H8.
    unfold config_refine.
    intros.
    assert(tt = cur_tid tpc). inversion H4;auto. subst.
    assert(st =cur_tid spc). inversion H3;auto. subst.
    assert(atom_bit tpc = O). inversion H4;auto.
    apply init_property_1_alt in H4 as ?.

    eapply np_p_config_refine_weak_proof in H7;eauto;simpl;auto.
    Hsimpl.
    eapply init_free in H11 as ?;eauto.
    eapply init_pair_valid_tid in H11 as ?;try apply H3;eauto.
    eapply init_free in H13 as ?;eauto.
    eapply H8 in H14 as ?;eauto.
    eapply Etr_np_p in H15;eauto.
    rewrite <- pc_cur_tid with(pc:=spc).
    eapply switchable_glob_config_refine in H15;eauto.
    inversion H3;auto.
    unfold np_accepted. Esimpl;[|constructor]. eauto.
    eapply NPSafe_Safe_Config;eauto.
    intros.
    pose proof H11 as T.
    eapply init_free in H11;eauto.
    apply NNPP;intro. unfold npdrfpc in H12.
    apply not_and_or in H12.
    unfold drfpc in H6. contradict H6.

    assert(glob_step tpc sw FP.emp ({-|tpc,t})).
    destruct tpc,T;simpl in *;subst;econstructor;eauto.
    assert(star_race_config ({-|tpc,t})).
    eapply NPRace_Race_Config;try apply H11;eauto;auto.
    destruct H12;apply NNPP in H12;auto.
    unfold star_race_config in *;Hsimpl.
    eapply star_step in H6;eauto.
  Qed.

  (** [np_p_equiv] defines the equivalence of preemptive-semantics and non-preemptive smeantics.
      - [Etr] is the event trace of the configuration [pc], where [B] means the behavior of the configuration,
      - the configuration in non-preemptive should be able to start in any valid thread, otherwise it may not have the same behavior as in preemptive semantics.
 *)
  Definition np_p_equiv {NL}{L} (p: prog L):=
    forall m ge pc t,
      @init_config NL L p m ge pc t ->
      forall B,
        Etr glob_step abort final_state pc B <-> exists t, Etr np_step np_abort final_state ({-|pc,t}) B /\ pc_valid_tid pc t.
  (** Semantics Equivalence(Lemma 7):
 If the program is safe and data-race-free, and the languages of the program are well-defined, then we have the equivalence of P and NP. *)
  Lemma NP_P_Equiv{NL}{L}:
    forall P,
      wd_langs (fst P)->
      safe_prog P->
      drf P->
      @np_p_equiv NL L P.
  Proof.
    unfold np_p_equiv. split;intros.
    eapply np_p_refine_weak;eauto. inversion H2;subst;econstructor;eauto.
    destruct H3 as [?[]].
    eapply p_np_refine in H3 as ?;eauto.
    eapply switchable_glob_config_refine with(t:=cur_tid pc) in H5;eauto.
    simpl in H5. rewrite pc_cur_tid in H5. auto.
    inversion H2;subst;auto.

    inversion H2;subst;econstructor;eauto. simpl.
    destruct H4;auto.
  Qed.

End Refinement.



