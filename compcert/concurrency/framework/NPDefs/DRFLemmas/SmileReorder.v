Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics GlobSemantics_Lemmas NPSemantics TypedSemantics .

Require Import DRF USimDRF NPDRF FPLemmas PRaceLemmas.

Require Import Classical Wf Arith.
(** This file contains lemmas about reordering under the condition of data-race-free, used in the semantics equivalence of P and NP.*)
Local Notation "'<<' i ',' c ',' sg ',' F '>>'" := {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|} (at level 60, right associativity).
Local Definition pc_valid_tid {ge}:= @GSimDefs.pc_valid_tid ge.
Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:= D|}(at level 70,right associativity).  Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).
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
Ltac solv_thread_alt:=
  repeat
    match goal with
    | H:ThreadPool.update _ _ _ _ |- _ => Coqlib.inv H
    | H:CallStack.update _ _ _ |- _ => Coqlib.inv H
    | H:ThreadPool.halted _ _ |- _ => Coqlib.inv H
    end;
  unfold ThreadPool.get_top, ThreadPool.pop, ThreadPool.get_cs, ThreadPool.push,ThreadPool.valid_tid ,
  CallStack.pop, CallStack.top, CallStack.is_emp, CallStack.emp_cs in *; subst;
  repeat (rewrite Maps.PMap.gsspec in *;(destruct Coqlib.peq;subst;try contradiction; subst));
  repeat 
  match goal with
    H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try (inversion H; fail)
  | H: Some _ = Some _ |- _ => inversion H; clear H; subst
  | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
  | H:?P = ?Q |- context [ ?P ] => rewrite H 
  end.

Section Reorder.
  Variable GE:GlobEnv.t.
  Hypothesis wdge:forall ix,mod_wd (GlobEnv.modules GE ix).
  Definition changepc (pc:@ProgConfig GE)(t:tid)(b:Bit):ProgConfig:=
    { pc.(thread_pool), t,pc.(gm),b}.
  Definition mem_eq_pc (pc pc':@ProgConfig GE):Prop:=
    thread_pool pc = thread_pool pc' /\
    atom_bit pc = atom_bit pc' /\
    cur_tid pc = cur_tid pc' /\
    GMem.eq' (gm pc)(gm pc').
  Lemma mem_eq_pc_refl:forall p,mem_eq_pc p p.
  Proof. split;[|split;[|split;[|apply GMem.eq'_refl]]];auto. Qed.
  Lemma mem_eq_pc_sym:forall p p',mem_eq_pc p p'->mem_eq_pc p' p.
  Proof. destruct 1 as (?&?&?&?);split;[|split;[|split;[|eapply GMem.eq'_sym]]];eauto. Qed.
  Lemma mem_eq_pc_trans:forall p1 p2 p3,mem_eq_pc p1 p2 ->mem_eq_pc p2 p3->mem_eq_pc p1 p3.
  Proof. destruct 1 as (?&?&?&?),1 as (?&?&?&?);split;[|split;[|split;[|eapply GMem.eq'_trans]]];eauto;congruence. Qed.


  Lemma Memperm_validblock:
    forall m b ofs k p,
      GMemory.GMem.perm m b ofs k p ->
      GMemory.GMem.valid_block m b.
  Proof.
    destruct m.
    intros.
    unfold GMemory.GMem.valid_block.
    simpl .
    unfold GMemory.GMem.perm in H;simpl in H.
    apply NNPP;intro.
    eapply invalid_noaccess in H0;eauto.
    rewrite H0 in H.
    inversion H.
  Qed.

  Lemma localstep_memeff:
    forall i_x F cc m fp cc' m',
      step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m fp cc' m' ->
      LEffect m m' fp (FLists.get_fl (GlobEnv.freelists GE) F).
  Proof.
    intros.
    specialize (wdge i_x).
    inversion wdge.
    unfold corestep_local_eff in step_local_eff.
    eapply step_local_eff;eauto.
  Qed.
  Function getcurcore (pc:@ProgConfig GE):= ThreadPool.get_top pc.(thread_pool) pc.(cur_tid).
  Function getfl (c:@Core.t GE) := FLists.get_fl (GlobEnv.freelists GE) (Core.F c).
  Function getcurcs (pc:@ProgConfig GE):= ThreadPool.get_cs pc.(thread_pool) pc.(cur_tid).

  Lemma gettop_getcs_exists:
    forall thdp i c,
      @ThreadPool.get_top GE thdp i = Some c ->
      exists c',ThreadPool.get_cs thdp i = Some c'.
  Proof. unfold ThreadPool.get_top;intros. destruct ThreadPool.get_cs;eauto. inversion H. Qed.
  Lemma gettop_push_exists:
    forall thdp i c,@ThreadPool.get_top GE thdp i = Some c->
               forall mid c sg, exists c',ThreadPool.push thdp i mid c sg = Some c'.
  Proof.
    intros.
    apply gettop_getcs_exists in H as [].
    unfold ThreadPool.push.
    unfold ThreadPool.get_cs in H.
    rewrite H. eauto.
  Qed.
  Lemma coreupdate_exists:
    forall c cc,exists c', @Core.update GE c cc c'.
  Proof. intros. eexists. econstructor;eauto. Qed.
  Lemma gettop_update_exists:
    forall thdp i c,@ThreadPool.get_top GE thdp i = Some c->
               forall cc  c', Core.update c cc c' ->exists thdp', ThreadPool.update thdp i c' thdp'.
  Proof.
    intros.
    eapply gettop_getcs_exists in H as L.
    destruct L.
    unfold ThreadPool.get_top in H.
    rewrite H1 in H. destruct x;inversion H;subst.
    eexists. econstructor;eauto. econstructor;eauto.
  Qed.
  Lemma gettop_pop_exists:
    forall thdp i c,@ThreadPool.get_top GE thdp i = Some c->
               exists t,ThreadPool.pop thdp i = Some t.
  Proof.
    intros.
    unfold ThreadPool.get_top in H;unfold ThreadPool.get_cs in H.
    destruct Maps.PMap.get eqn:?;inversion H;clear H;subst.
    unfold ThreadPool.pop.
    rewrite Heqp.
    unfold CallStack.top in H1.
    destruct t;inversion H1;subst.
    simpl. eauto.
  Qed.
  Lemma update_gettop_exists:
    forall thdp i c thdp',@ThreadPool.update GE thdp i c thdp'->
                     exists c,ThreadPool.get_top thdp i = Some c.
  Proof.
    intros. inversion H;clear H;subst.
    unfold ThreadPool.get_top. rewrite H0.
    inversion H1;clear H1;subst.
    simpl. eauto.
  Qed.
  Lemma pop_gettop_exists:
    forall thdp i thdp',@ThreadPool.pop GE thdp i = Some thdp'->
                   exists c,ThreadPool.get_top thdp i= Some c.
  Proof. intros. unfold ThreadPool.pop in H. destruct Maps.PMap.get eqn:?;inversion H;clear H;subst. unfold ThreadPool.get_top;unfold ThreadPool.get_cs. rewrite Heqp. destruct CallStack.pop eqn:?;inversion H1;clear H1;subst. destruct t;inversion Heqo;subst;simpl;eauto. Qed.
  Lemma gettop_preserve:
    forall t1 t2, t1<>t2->
             forall thdp1 c,
               @ThreadPool.get_top GE thdp1 t1 = Some c->
               forall thdp2,
                 (exists c',@ThreadPool.update GE thdp1 t2 c' thdp2) \/
                 (ThreadPool.pop thdp1 t2 = Some thdp2)\/
                 (exists mid c' sg,ThreadPool.push thdp1 t2 mid c' sg = Some thdp2)
               ->
               ThreadPool.get_top thdp2 t1 = Some c.
  Proof. destruct 3 as[[]|[|[?[?[]]]]];intros;solv_thread;solv_thread. Qed.

    
  Lemma gettop_backwards_preserve:
    forall t1 t2, t1<>t2->
             forall thdp2 c,
               @ThreadPool.get_top GE thdp2 t1 = Some c->
               forall thdp1,
                 (exists c',@ThreadPool.update GE thdp1 t2 c' thdp2) \/
                 (ThreadPool.pop thdp1 t2 = Some thdp2)\/
                 (exists mid c' sg,ThreadPool.push thdp1 t2 mid c' sg = Some thdp2)
               ->
               ThreadPool.get_top thdp1 t1 = Some c.
  Proof. destruct 3 as[[]|[|[?[?[]]]]];intros;solv_thread;solv_thread. Qed.
  Lemma valid_tid_preserve:
    forall thdp1 i,
      @ThreadPool.valid_tid GE thdp1 i->
      forall thdp2 t,
        (exists c',@ThreadPool.update GE thdp1 t c' thdp2) \/
        (ThreadPool.pop thdp1 t = Some thdp2)\/
        (exists mid c' sg,ThreadPool.push thdp1 t mid c' sg = Some thdp2)->
        ThreadPool.valid_tid thdp2 i.
  Proof. destruct 2 as[[]|[|[?[?[]]]]];intros;solv_thread;solv_thread. Qed.

  Lemma valid_tid_backwards_preserve:
    forall thdp2 i,
      @ThreadPool.valid_tid GE thdp2 i->
      forall thdp1 t,
        (exists c',@ThreadPool.update GE thdp1 t c' thdp2) \/
        (ThreadPool.pop thdp1 t = Some thdp2)\/
        (exists mid c' sg,ThreadPool.push thdp1 t mid c' sg = Some thdp2)->
        ThreadPool.valid_tid thdp1 i.
  Proof. destruct 2 as[[]|[|[?[?[]]]]];intros;solv_thread;solv_thread. Qed.

  Lemma halted_preserve:
    forall thdp1 t,
      @ThreadPool.halted GE thdp1 t->
      forall thdp2 t',
        (exists c',@ThreadPool.update GE thdp1 t' c' thdp2) \/
        (ThreadPool.pop thdp1 t' = Some thdp2)\/
        (exists mid c' sg tp',ThreadPool.push thdp1 t' mid c' sg = Some thdp2 /\ ThreadPool.get_top thdp1 t' = Some tp')->
        ThreadPool.halted thdp2 t.
  Proof. destruct 2 as[[]|[|[?[?[?[?[]]]]]]];intros;solv_thread;econstructor;solv_thread. Qed.
 
  Lemma halted_preserve_alter:
    forall thdp2 t,
      @ThreadPool.halted GE thdp2 t->
      forall thdp1,ThreadPool.pop thdp1 t = Some thdp2->
              forall thdp t',
                (exists c',@ThreadPool.update GE thdp t' c' thdp1) \/
                (ThreadPool.pop thdp t' = Some thdp1 /\ t <> t')\/
                (exists mid c' sg tp',ThreadPool.push thdp t' mid c' sg = Some thdp1 /\ ThreadPool.get_top thdp1 t' = Some tp')->
                forall thdp',ThreadPool.pop thdp t = Some thdp'->
                        ThreadPool.halted thdp' t.
  Proof.  destruct 3 as [[]|[[]|[?[?[?[?[]]]]]]];intros;solv_thread; econstructor;solv_thread.  Qed.
  Lemma halted_backwards_preserve:
    forall thdp2 t,
      @ThreadPool.halted GE thdp2 t->
      forall thdp1 t',
        (exists c',@ThreadPool.update GE thdp1 t' c' thdp2) \/
        (ThreadPool.pop thdp1 t' = Some thdp2 /\ t <> t')\/
        (exists mid c' sg,ThreadPool.push thdp1 t' mid c' sg = Some thdp2)->
        ThreadPool.halted thdp1 t.
  Proof. destruct 2 as [[]|[[]|[?[?[]]]]];intros;solv_thread;econstructor;solv_thread.  Qed.
  Lemma thdp_update_unique:
    forall thdp t c thdp',
      @ThreadPool.update GE thdp t c thdp'->
      forall thdp1,ThreadPool.update thdp t c thdp1->
              thdp' = thdp1.
  Proof. intros;solv_thread. Qed.
  Lemma thdp_push_unique:
    forall thdp t mid c sg thdp' thdp'',
      @ThreadPool.push GE thdp t mid c sg = Some thdp'->
      ThreadPool.push thdp t mid c sg = Some thdp''->
      thdp'=thdp''.
  Proof. intros;solv_thread. Qed.

  Lemma thdp_pop_unique:
    forall thdp t thdp' thdp'',
      @ThreadPool.pop GE thdp t = Some thdp'->
      ThreadPool.pop thdp t = Some thdp''->
      thdp'=thdp''.
  Proof. intros;solv_thread. Qed.

  Lemma corestep_eff:
    forall pc l fp pc' c,
      @type_glob_step GE core pc l fp pc' ->
      getcurcore pc = Some c ->
      LEffect pc.(gm) pc'.(gm) fp (getfl c).
  Proof.
    intros.
    inversion H;subst.
    unfold getcurcore in H0;simpl in H0.
    rewrite H_tp_core in H0;inversion H0;clear H0;subst.
    eapply localstep_memeff;eauto.
  Qed.
  Lemma glob_step_eff:
    forall pc l fp pc' c,
      @glob_step GE pc l fp pc' ->
      getcurcore pc = Some c ->
      LEffect pc.(gm) pc'.(gm) fp (getfl c).
  Proof.
    intros.
    apply type_glob_step_exists in H as [].
    destruct x;[eapply corestep_eff;eauto| | | | | | | | |];Coqlib.inv H;try apply LEffect_refl.
  Qed.
  
  Lemma corestep_aftercore:
    forall pc l fp pc' ,
      @type_glob_step GE core pc l fp pc' ->
      exists c,getcurcore pc' = Some c.
  Proof.
    intros.
    inversion H;subst.

    exists c'.
    unfold getcurcore;simpl.
    unfold ThreadPool.get_top;unfold ThreadPool.get_cs.
    inversion H_tp_upd;subst;simpl.
    rewrite Maps.PMap.gsspec.
    destruct Coqlib.peq;[|contradiction].
    inversion H1;subst;auto.
  Qed.
  Lemma globstep_aftercore:
    forall x pc l fp pc',
      @type_glob_step GE x pc l fp pc'-> x <> glob_sw -> x <> glob_halt ->
      exists c,getcurcore pc' = Some c.
  Proof.
    intros.
    destruct x;inversion H;subst;unfold getcurcore;try contradiction;try (solv_thread;eexists;solv_thread;fail).
  Qed.
  Lemma corestar_aftercore:
    forall pc fp pc',
      tau_star (@type_glob_step GE core) pc fp pc' ->
      forall c0,getcurcore pc = Some c0 ->
      exists c,getcurcore pc' = Some c.
  Proof. induction 1;intros;[eexists|apply corestep_aftercore in H as [];apply IHtau_star in H as [];eexists];eauto. Qed.
  Lemma core_Fpreservation:
    forall pc l fp pc' c c',
      @type_glob_step GE core pc l fp pc' ->
      getcurcore pc = Some c ->
      getcurcore pc' = Some c' ->
      getfl c = getfl c'.
  Proof.
    intros.
    inversion H;clear H;subst.
    clear H_core_step wdge.
    unfold getcurcore in *;simpl in *.
    rewrite H_tp_core in H0;inversion H0;clear H0;subst.
    inversion H_tp_upd;clear H_tp_upd;subst.
    unfold ThreadPool.get_top in H_tp_core.
    rewrite H in H_tp_core.
    destruct cs;inversion H_tp_core;clear H_tp_core;subst.

    unfold ThreadPool.get_top in H1;unfold ThreadPool.get_cs in H1; simpl in H1.
    rewrite Maps.PMap.gsspec in H1.
    destruct Coqlib.peq;[|contradiction].
    inversion H0;clear H0;subst.
    inversion H1;clear H1;subst.
    inversion H6;clear H6;subst.
    auto.
  Qed.
  
  Lemma corestar_Fpreservation:
    forall pc fp pc' c c',
      tau_star (@type_glob_step GE core) pc fp pc' ->
      getcurcore pc = Some c ->
      getcurcore pc' = Some c' ->
      getfl c = getfl c'.
  Proof.
    intros.
    revert c c' H0 H1.
    induction H;subst;intros. rewrite H0 in H1;inversion H1;auto.
    assert(exists c1,getcurcore s' = Some c1).
    inversion H;subst.
    unfold getcurcore;simpl.
    exists c'0.
    inversion H_tp_upd;subst.
    unfold ThreadPool.get_top;unfold ThreadPool.get_cs;simpl.
    rewrite Maps.PMap.gsspec.
    destruct Coqlib.peq;[|contradiction].
    inversion H4;subst;auto.

    destruct H3 as [c1 ?].
    pose H3 as Tmp1.
    eapply core_Fpreservation in Tmp1;eauto.
    rewrite Tmp1.
    eapply IHtau_star;eauto.
  Qed.
  Lemma subset_effect:
    forall fp1 fp2,
      FP.subset fp1 fp2 ->
      Locs.subset (effects fp1)(effects fp2).
  Proof.
    intros.
    inversion H;subst.
    unfold effects.
    unfold Locs.subset in *.
    unfold Locs.belongsto in *.
    unfold Locs.union.
    intros.
    destruct (FP.writes fp1 b ofs)%bool eqn:eq1, ( FP.frees fp1 b ofs)%bool eqn:eq2;auto with bool.
  Qed.
  Lemma subset_depend:
    forall fp1 fp2,
      FP.subset fp1 fp2 ->
      Locs.subset (depends fp1)(depends fp2).
  Proof.
    intros.
    inversion H;subst.
    unfold depends.
    unfold Locs.subset in *.
    unfold Locs.belongsto in *.
    unfold Locs.union.
    intros.
    destruct (FP.cmps fp1 b ofs)%bool eqn:eq1, ( FP.reads fp1 b ofs)%bool eqn:eq2;auto with bool.
  Qed.
  Lemma perm_effect_lemma:
    forall m m' b ofs,
      perm_effect m m' b ofs->
      forall m0,
        perm_effect m m0 b ofs \/ perm_effect m0 m' b ofs.
  Proof.
    intros.
    inversion H;assert(GMemory.GMem.perm m0 b ofs k p \/ ~GMemory.GMem.perm m0 b ofs k p); try apply classic;destruct H2;[right;econstructor|left;econstructor|left;econstructor 2|right;econstructor 2];eauto.
  Qed.

  Lemma localstar_eff:
    forall i_x F cc m fp cc' m',
      InteractionSemantics.star (step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F)) cc m fp cc' m' ->
      LEffect m m' fp (FLists.get_fl (GlobEnv.freelists GE) F).
  Proof.
    intros.
    induction H.
    apply LEffect_refl.
    apply localstep_memeff in H.
    eapply LEffect_trans_union; eauto.
  Qed.

  Lemma corestar_eff:
    forall pc fp pc' c,
      tau_star (@type_glob_step GE core) pc fp pc' ->
      getcurcore pc = Some c ->
      LEffect pc.(gm) pc'.(gm) fp (getfl c).
  Proof.
    intros.
    revert c H0.
    induction H;intros.
    apply LEffect_refl.

    assert(exists c',getcurcore s' = Some c').
    eapply corestep_aftercore;eauto.
    destruct H2.
    assert(exists c'',getcurcore s''=Some c'').
    eapply corestar_aftercore;eauto.
    destruct H3.
    pose proof H2 as Tmp1.
    apply IHtau_star in Tmp1.
    pose proof H as Tmp2.
    eapply corestep_eff in Tmp2;eauto.
    assert(getfl x = getfl x0).
    eapply corestar_Fpreservation;eauto.
    assert(getfl c = getfl x).
    eapply core_Fpreservation;eauto.
    rewrite H5. rewrite H5 in Tmp2. 
    eapply LEffect_trans_union;eauto.
  Qed.

  Corollary localstep_locality1 :
    forall i_x F cc m fp cc' m',
      step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m fp cc' m' ->
      forall m1,
        LPre m m1 fp (FLists.get_fl (GlobEnv.freelists GE) F) ->
        exists m1', step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m1 fp cc' m1' /\ LPost m' m1' fp (FLists.get_fl (GlobEnv.freelists GE) F).
  Proof.
    intros.
    specialize (wdge i_x).
    inversion wdge.
    unfold corestep_locality_1 in step_locality_1.
    eapply step_locality_1;eauto.
  Qed.
  
  Corollary corestep_locality1 :
    forall pc l fp pc' c,
      @type_glob_step GE core pc l fp pc' ->
      getcurcore pc = Some c ->
      forall pc1, 
        getcurcore pc1 = Some c ->
        LPre pc.(gm) pc1.(gm) fp (getfl c) ->
        exists pc2 c',
          @type_glob_step GE core pc1 l fp pc2 /\ LPost pc'.(gm) pc2.(gm) fp (getfl c) /\ getcurcore pc2 = Some c' /\getcurcore pc' = Some c'.
  Proof.
    intros.
    unfold getcurcore in H1.
    unfold getcurcore in H0.
    inversion H;subst;simpl in *.
    rewrite H_tp_core in H0;inversion H0;clear H0;subst.
    
    eapply localstep_locality1 with(m1:=pc1.(GlobDefs.gm)) in H_core_step as [m2[]];eauto.
    assert(exists thdp'',ThreadPool.update pc1.(thread_pool) pc1.(cur_tid) c' thdp'').
    unfold ThreadPool.get_top in H1.
    destruct (ThreadPool.get_cs pc1.(thread_pool) pc1.(cur_tid)) eqn:eq3;[|inversion H1].
    destruct t0;inversion H1;clear H1;subst.
    eexists;econstructor;eauto.
    econstructor;eauto.
    destruct H4.
    exists {|thread_pool:=x;cur_tid:=pc1.(cur_tid);gm:=m2;atom_bit:=pc1.(atom_bit)|}.
    exists c'.
    split;auto.
    assert(pc1={|thread_pool:=pc1.(thread_pool);cur_tid:=pc1.(cur_tid);gm:=pc1.(GlobDefs.gm);atom_bit:=pc1.(atom_bit) |}). destruct pc1;auto.
    rewrite H5. simpl.
    econstructor;eauto.
    split;auto.

    unfold getcurcore;simpl.
    solv_thread.
  Qed.

 

  Definition Freelists := GlobEnv.freelists GE.
  Definition flmap (t:tid):=
    fun i:nat=> Freelists.(FLists.flist_content) (Freelists.(FLists.thread_flmap) t i).

  Definition allocated_block := GMem.valid_block.
  Definition GlobalAlloc (m1 m2:gmem)(t:tid):Prop:=
    forall b,
      ~ allocated_block m1 b ->
      allocated_block m2 b ->
      exists i,
        MemAux.in_fl (flmap t i) b. 
  Definition GlobalFreelistEq (m1 m2:gmem)(t:tid):Prop:=
    forall b i,
      MemAux.in_fl (flmap t i) b ->
      allocated_block m1 b <-> allocated_block m2 b.
  Lemma GlobalAlloc_refl: forall m t, GlobalAlloc m m t.
  Proof. unfold GlobalAlloc;intros;contradiction. Qed.
  
  Lemma GlobalFreelistEq_refl: forall m t, GlobalFreelistEq m m t.
  Proof. split;intro;auto. Qed.
  Lemma GlobalFreelistEq_comm: forall m1 m2 t,GlobalFreelistEq m1 m2 t ->GlobalFreelistEq m2 m1 t.
  Proof. split;intros;eapply H;eauto. Qed.
  Lemma LocalAlloc_GlobalAlloc:
    forall m1 m2 t i fl,
      LocalAlloc m1 m2 fl ->
      flmap t i = fl ->
      GlobalAlloc m1 m2 t.
  Proof.
    unfold LocalAlloc;unfold GlobalAlloc;intros.
    exists i. rewrite H0. eauto.
  Qed.
  Lemma GlobalFreelistEq_freelisteq:
    forall m1 m2 t i fl,
      GlobalFreelistEq m1 m2 t->
      flmap t i = fl ->
      FreelistEq m1 m2 fl.
  Proof.
    intros.
    unfold GlobalFreelistEq in H.
    unfold FreelistEq.
    intros.
    eapply H;eauto.
    rewrite H0;auto.
  Qed.
  Definition GEffect (m1 m2:gmem)(fp:FP.t)(t:tid):Prop:=
    MemEffect m1 m2 fp /\ GlobalAlloc m1 m2 t.
  Definition GPre (m1 m2:gmem)(fp:FP.t)(t:tid):Prop:=
    MemPre m1 m2 fp /\ GlobalFreelistEq m1 m2 t.
  Definition GPost (m1 m2:gmem)(fp:FP.t)(t:tid):Prop:=
    MemPost m1 m2 fp /\ GlobalFreelistEq m1 m2 t.
  Lemma GPre_comm:forall m1 m2 fp t, GPre m1 m2 fp t-> GPre m2 m1 fp t.
  Proof. unfold GPre;split;destruct H;[apply MemPre_comm|apply GlobalFreelistEq_comm];auto. Qed.
  Lemma GPre_subset:
    forall m1 m2 fp1 fp2 t,
      GPre m1 m2 fp1 t->
      FP.subset fp2 fp1 ->
      GPre m1 m2 fp2 t.
  Proof. destruct 1;split;auto;eapply MemPre_subset;eauto. Qed.
  Lemma GPost_comm:forall m1 m2 fp t, GPost m1 m2 fp t-> GPost m2 m1 fp t.
  Proof. unfold GPost;split;destruct H;[apply unchanged_content_comm|apply GlobalFreelistEq_comm];auto. Qed.
  Lemma GPost_union:
    forall m1 m2 m1' m2' fp1 fp2 t,
      GPost m1 m2 fp1 t-> GEffect m1 m1' fp2 t-> GEffect m2 m2' fp2 t->
      GPost m1' m2' fp2 t ->GPost m1' m2' (FP.union fp1 fp2) t.
  Proof.
    unfold GPost,GEffect;intros. Hsimpl.
    split;auto.
    eapply MemPost_MemEffect_MemPost_Rule;eauto.
  Qed.    
  Lemma LEffect_GEffect:
    forall t i m1 m2 fl fp,
      LEffect m1 m2 fp fl ->
      flmap t i = fl ->
      GEffect m1 m2 fp t.
  Proof.
    intros.
    destruct H.
    constructor;auto.
    unfold LocalAlloc in H1.
    unfold GlobalAlloc.
    intros.
    unfold allocated_block in *.
    exists i.
    rewrite H0.
    eapply H1;eauto.
  Qed.
 Lemma GPre_LEffect_GPost_Rule:
    forall m0 m1 m0' m1' fp1 fp2 fl t i,
      flmap t i = fl ->
      GPre m0 m0' (FP.union fp1 fp2) t->
      LEffect m0 m1 fp1 fl ->
      LEffect m0' m1' fp1 fl->
      GPost m1 m1' fp1 t ->
      GPre m1 m1' fp2 t.
  Proof.
    intros.
    destruct H0,H1,H2,H3.
    split;auto.
    eapply MemPre_MemEffect_MemPost_Rule;eauto.
  Qed.
  Lemma GPost_LEffect_GPost_Rule1:
    forall m0 m1 m0' m1' fp1 fp2 fl t i,
      flmap t i = fl ->
      GPost m0 m1 fp1 t ->
      LEffect m0 m0' fp2 fl ->
      LEffect m1 m1' fp2 fl ->
      GPost m0' m1' fp2 t ->
      GPost m0' m1' (FP.union fp1 fp2) t.
  Proof.
    intros until i.
    intros ? [] [] [] [].
    split;auto.
    eapply MemPost_MemEffect_MemPost_Rule;eauto.
  Qed.    

  Lemma GPre_GEffect_GPost_Rule:
    forall m0 m1 m0' m1' fp1 fp2 t ,
      GPre m0 m0' (FP.union fp1 fp2) t->
      GEffect m0 m1 fp1 t ->
      GEffect m0' m1' fp1 t->
      GPost m1 m1' fp1 t ->
      GPre m1 m1' fp2 t.
  Proof.
    intros.
    destruct H0,H1,H2,H.
    split;auto.
    eapply MemPre_MemEffect_MemPost_Rule;eauto.
  Qed.
  Lemma GPost_GEffect_GPost_Rule1:
    forall m0 m1 m0' m1' fp1 fp2 t ,
      GPost m0 m1 fp1 t ->
      GEffect m0 m0' fp2 t ->
      GEffect m1 m1' fp2 t ->
      GPost m0' m1' fp2 t ->
      GPost m0' m1' (FP.union fp1 fp2) t.
  Proof.
    intros until t.
    intros [] [] [] [].
    split;auto.
    eapply MemPost_MemEffect_MemPost_Rule;eauto.
  Qed.
    Hypothesis wd_GE:GlobEnv.wd GE.
  Lemma GEffect_fpsmile_disj_GPre_Rule:
    forall m0 m1 fp1 fp2 t1 t2,
      t1 <> t2 ->
      GEffect m0 m1 fp1 t1 ->
      FP.smile fp1 fp2 ->
      GPre m1 m0 fp2 t2.
  Proof.
    intros.
    pose proof GlobEnv.wd_fl _ wd_GE.
    destruct H0.
    constructor;auto.
    eapply MemEffect_fpsmile_MemPre_Rule;eauto.
    
    unfold GlobalFreelistEq;intros.
    pose proof ValidityPreserve _ _ _ H0.
    unfold GlobalAlloc in H3.
    split;unfold allocated_block in *;eauto;intro.
    apply NNPP;intro.
    edestruct H3;eauto.
    destruct H2.

    destruct H4,H8.
    eapply thread_fl_disj with(n1:=x)(n2:=i)in H.
    apply flist_disj in H.
    unfold flmap in *;unfold Freelists in *.
    rewrite <- H2 in H4.
    eapply H in H4;eauto.
  Qed.



  Definition thread_sim(pc:@ProgConfig GE)(pc':@ProgConfig GE):Prop:=
    cur_tid pc = cur_tid pc' /\
    atom_bit pc = atom_bit pc' /\
    getcurcs pc = getcurcs pc' /\
    pc.(thread_pool).(ThreadPool.next_fmap) pc.(cur_tid) = pc'.(thread_pool).(ThreadPool.next_fmap) pc'.(cur_tid).
  Lemma curcorefl_flmap_exists:
    forall thdp id c,
      ThreadPool.inv thdp->
      ThreadPool.get_top thdp id= Some c->
      exists i,flmap id i = getfl c.
  Proof.
    intros.
    solv_thread.
    pose proof @ThreadPool.cs_inv _ _ H _ _ Heqo.
    assert(List.In c (c::t1)). compute;auto.
    pose proof @ThreadPool.fid_belongsto _ _ _ _ H0 c H1 as [].
    unfold flmap;unfold getfl.
    exists x.
    rewrite<- H2;auto.
  Qed.
  Lemma corestep_Glocality:
    forall pc l fp pc' pc1,
      @type_glob_step GE core pc l fp pc' ->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool)->
      GPre pc.(gm) pc1.(gm) fp pc.(cur_tid) ->
      exists pc1',@type_glob_step GE core pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'. 
  Proof.
    intros [thdp tid tgm tbit] l fp pc' [thdp' tid' tgm' tbit'] ? ? invthdp ?.
    destruct H0 as (tideq&biteq&cseq&mapeq);simpl in *;subst.
    unfold getcurcs in cseq;simpl in cseq.
    inversion H;subst;simpl in *.

    eapply curcorefl_flmap_exists in invthdp  as L1;eauto.
    destruct L1,H1.
    eapply GlobalFreelistEq_freelisteq in H0 as L1;eauto.
    assert(LPre tgm tgm' fp (getfl c)). split;auto.
    eapply localstep_locality1 in H3;eauto.
    destruct H3 as (?&?&?&?).
    assert(ThreadPool.get_top thdp' tid' = Some c).
    unfold ThreadPool.get_top. rewrite <- cseq;auto.
    edestruct gettop_update_exists;eauto.
    eexists;split;econstructor;eauto.
    constructor;simpl;auto.
    Focus 2.
    split;[|split;[|split]];simpl;auto.
    unfold getcurcs;simpl;auto.
    solv_thread. solv_thread.
    
    apply localstep_memeff in H3 as [].
    apply localstep_memeff in H_core_step as [].

    clear c' cc' H_tp_core H_core_upd H_tp_upd H6 H7.
    clear x H0 L1.
    unfold GlobalFreelistEq in *.
    unfold allocated_block in *.
    pose proof ValidityPreserve _ _ _ H9;clear H9.
    pose proof ValidityPreserve _ _ _ H3;clear H3.
    unfold LocalAlloc in *.
    intros.
    specialize (H2 b i H3).

    assert(GMem.valid_block tgm b \/ ~ GMem.valid_block tgm b).
    apply classic.
    destruct H7.
    apply H2 in H7 as ?.
    apply H0 in H7.
    apply H6 in H9.
    split;auto.

    assert(~ GMem.valid_block tgm' b).
    intro. apply H2 in H9. contradiction.
    split;intro;eapply H5;eauto.
  Qed.



  Lemma callstep_Glocality:
    forall pc l fp pc' pc1,
      @type_glob_step GE call pc l fp pc'->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool)->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
      exists pc1',@type_glob_step GE call pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    intros [thdp tid tgm tbit] l fp pc' [thdp' tid' tgm' tbit'] ? [tideq [biteq [cseq mapeq]]] ? ?.
    unfold getcurcs in cseq; simpl in *;subst.
    Coqlib.inv H.

    assert(ThreadPool.get_top thdp' tid' = Some c).
    unfold ThreadPool.get_top. rewrite <-cseq. auto.
    edestruct gettop_push_exists with(mid:=new_ix)(c0:=cc')(sg:=sg);eauto.
    eexists;split. econstructor;eauto.
    simpl;split;auto.
    split. apply unchanged_content_emp.
    destruct H1;auto.
    unfold thread_sim;unfold getcurcs;simpl.
    split;[|split];auto;solv_thread;solv_thread.
  Qed.
  Lemma retstep_Glocality:
    forall pc l fp pc' pc1,
      @type_glob_step GE ret pc l fp pc'->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool)->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
      exists pc1',@type_glob_step GE ret pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    intros [thdp tid tgm tbit] ? ? ? [thdp' tid' tgm' tbit'] ? [tideq[biteq[cseq mapeq]]] ? ?.
    unfold getcurcs in cseq;simpl in * ;subst.
    Coqlib.inv H.

    assert(ThreadPool.get_top thdp' tid' = Some c).
    unfold ThreadPool.get_top. rewrite <- cseq;auto.
    edestruct gettop_pop_exists;eauto.

    assert(ThreadPool.get_top x tid' = Some c').
    solv_thread. solv_thread.
    edestruct gettop_update_exists;eauto.
    eexists;split;[econstructor;eauto|split];simpl.
    split. apply unchanged_content_emp.
    destruct H1;auto.
    unfold thread_sim;unfold getcurcs;solv_thread;solv_thread.
  Qed.

  Lemma entatstep_Glocality:
    forall pc l fp pc' pc1,
      @type_glob_step GE entat pc l fp pc' ->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool) ->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
      exists pc1',@type_glob_step GE entat pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    intros [thdp tid tgm tbit] ? ? ? [thdp' tid' tgm' tbit'] ? [tideq[biteq[cseq mapeq]]] ? ?.
    unfold getcurcs in cseq;simpl in * ;subst.
    Coqlib.inv H.

    assert(ThreadPool.get_top thdp' tid' = Some c).
    unfold ThreadPool.get_top. rewrite <- cseq;auto.
    edestruct gettop_update_exists;eauto.

    assert(ThreadPool.get_top x tid' = Some c').
    solv_thread. 
    eexists;split;[econstructor;eauto|split];simpl.
    split. apply unchanged_content_emp.
    destruct H1;auto.
    unfold thread_sim;unfold getcurcs;solv_thread;solv_thread.
  Qed.
 Lemma extatstep_Glocality:
    forall pc l fp pc' pc1,
      @type_glob_step GE extat pc l fp pc' ->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool) ->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
      exists pc1',@type_glob_step GE extat pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    intros [thdp tid tgm tbit] ? ? ? [thdp' tid' tgm' tbit'] ? [tideq[biteq[cseq mapeq]]] ? ?.
    unfold getcurcs in cseq;simpl in * ;subst.
    Coqlib.inv H.

    assert(ThreadPool.get_top thdp' tid' = Some c).
    unfold ThreadPool.get_top. rewrite <- cseq;auto.
    edestruct gettop_update_exists;eauto.

    assert(ThreadPool.get_top x tid' = Some c').
    solv_thread. 
    eexists;split;[econstructor;eauto|split];simpl.
    split. apply unchanged_content_emp.
    destruct H1;auto.
    unfold thread_sim;unfold getcurcs;solv_thread;solv_thread.
  Qed.

  Lemma efprintstep_Glocality:
    forall pc l fp pc' pc1,
      @type_glob_step GE efprint pc l fp pc' ->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool) ->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
      exists pc1',@type_glob_step GE efprint pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    intros [thdp tid tgm tbit] ? ? ? [thdp' tid' tgm' tbit'] ? [tideq[biteq[cseq mapeq]]] ? ?.
    unfold getcurcs in cseq;simpl in * ;subst.
    Coqlib.inv H.

    assert(ThreadPool.get_top thdp' tid' = Some c).
    unfold ThreadPool.get_top. rewrite <- cseq;auto.
    edestruct gettop_update_exists;eauto.

    assert(ThreadPool.get_top x tid' = Some c').
    solv_thread. 
    eexists;split;[econstructor;eauto|split];simpl.
    split. apply unchanged_content_emp.
    destruct H1;auto.
    unfold thread_sim;unfold getcurcs;solv_thread;solv_thread.
  Qed.



  Lemma globhaltstep_Glocality:
    forall pc l fp pc' pc1,
      @type_glob_step GE glob_halt pc l fp pc' ->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool) ->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
      exists pc1',@type_glob_step GE glob_halt pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    intros [thdp tid tgm tbit] ? ? ? [thdp' tid' tgm' tbit'] ? [tideq[biteq[cseq mapeq]]] ? ?.
    unfold getcurcs in cseq;simpl in * ;subst.
    Coqlib.inv H.

    assert(ThreadPool.get_top thdp' tid' = Some c).
    unfold ThreadPool.get_top. rewrite <- cseq;auto.
    edestruct gettop_pop_exists;eauto.

    assert(ThreadPool.halted x tid').
    solv_thread. econstructor;eauto;solv_thread.
    eexists;split;[econstructor;eauto|split];simpl.
    split. apply unchanged_content_emp.
    destruct H1;auto.
    unfold thread_sim;unfold getcurcs;solv_thread;solv_thread.
  Qed.



  
 

  Lemma globstep_Glocality:
    forall pc l fp pc' pc1,
      @glob_step GE pc l fp pc'->
      l <> sw ->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool)->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc)->
      exists pc2,glob_step pc1 l fp pc2 /\ GPost pc'.(gm) pc2.(gm) fp (cur_tid pc) /\ thread_sim pc' pc2.
  Proof.
    intros.
    apply type_glob_step_exists in H as [].
    destruct x;try(inversion H;fail).
    eapply corestep_Glocality in H;eauto.
    Hsimpl. Esimpl;eauto. eapply type_glob_step_elim;eauto.
    eapply callstep_Glocality in H;eauto.
    Hsimpl. Esimpl;eauto. eapply type_glob_step_elim;eauto.
    eapply retstep_Glocality in H;eauto.
    Hsimpl. Esimpl;eauto. eapply type_glob_step_elim;eauto.
    eapply entatstep_Glocality in H;eauto.
    Hsimpl. Esimpl;eauto. eapply type_glob_step_elim;eauto.
    eapply extatstep_Glocality in H;eauto.
    Hsimpl. Esimpl;eauto. eapply type_glob_step_elim;eauto.
    eapply efprintstep_Glocality in H;eauto.
    Hsimpl. Esimpl;eauto. eapply type_glob_step_elim;eauto.
    inversion H;subst;contradiction.
    eapply globhaltstep_Glocality in H;eauto.
    Hsimpl. Esimpl;eauto. eapply type_glob_step_elim;eauto.
  Qed.
  Lemma globstep_eff:
    forall pc l fp pc',
      @glob_step GE pc l fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      GEffect pc.(gm) pc'.(gm) fp pc.(cur_tid).
  Proof.
    intros.
    inversion H;subst;simpl;try(constructor;try apply MemEffect_refl;try unfold GlobalAlloc;try intros;contradiction).
    apply localstep_memeff in H_core_step as [];auto.
    eapply curcorefl_flmap_exists in H_tp_core as [];eauto.
    split;auto. 
    eapply LocalAlloc_GlobalAlloc;eauto.
  Qed.

  Lemma taustar_eff:
    forall pc fp pc',
      tau_star (@glob_step GE) pc fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      GEffect pc.(gm) pc'.(gm) fp pc.(cur_tid).
  Proof.
    induction 1;intros.
    constructor. apply MemEffect_refl.
    apply GlobalAlloc_refl.

    apply GE_mod_wd_tp_inv in H as L1;auto.
    specialize (IHtau_star L1).
    assert(cur_tid s = cur_tid s').
    Coqlib.inv H;auto.
    rewrite <- H2 in IHtau_star.
    apply globstep_eff in H;auto.
    destruct H,IHtau_star.
    constructor.
    eapply MemEffect_union_fp with(fp2:=fp') in H;eauto.
    eapply MemEffect_union_fp with(fp2:=fp) in H4;eauto.
    rewrite FP.union_comm_eq in H4.
    eapply MemEffect_trans;eauto.

    unfold GlobalAlloc in *.
    unfold allocated_block in *.
    intros.
    assert(GMem.valid_block (gm s') b \/ ~ GMem.valid_block (gm s') b).
    apply classic. destruct H8;eauto.
  Qed.           

  
  Lemma taustar_Glocality:
    forall pc fp pc' pc1,
      tau_star (@glob_step GE) pc fp pc'->
      ThreadPool.inv pc.(thread_pool)->
      thread_sim pc pc1->
      ThreadPool.inv pc1.(thread_pool)->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc)->
      exists pc2,tau_star glob_step pc1 fp pc2 /\ GPost pc'.(gm) pc2.(gm) fp (cur_tid pc) /\ thread_sim pc' pc2.
  Proof.
    intros until pc1. intros H H0;revert pc1.
    induction H;intros.
    Esimpl;eauto. constructor.
    inversion H2;subst. inversion H3;subst.
    constructor;auto.

    pose proof (FP.union_subset fp fp').
    pose proof (FP.union_subset fp' fp).
    rewrite FP.union_comm_eq in H6.
    eapply GPre_subset in H5;eauto.
    eapply GPre_subset in H6;eauto.
    assert(tau<>sw). intro R;inversion R.
    eapply globstep_Glocality in H as?;eauto.
    Hsimpl.
    eapply GE_mod_wd_tp_inv in H as ?;eauto.
    Hsimpl.
    assert(cur_tid s = cur_tid s'). inversion H;auto.
    apply globstep_eff in H as ?;auto.
    
    apply globstep_eff in H8 as ?;auto.
    assert(cur_tid pc1 = cur_tid s).
    inversion H2;auto.
    rewrite H15 in H14.
    eapply GPre_GEffect_GPost_Rule in H4 as ?;eauto.
    apply GE_mod_wd_tp_inv in H8 as ?;auto.
    rewrite H12 in H16.
    specialize (IHtau_star _ H10 H17 H16) as ?.
    Hsimpl.
    Esimpl;eauto. econstructor;eauto.
    eapply GPost_union;eauto.
    rewrite H12. eapply taustar_eff;eauto.
    inversion H10 as (?&_).
    rewrite H12. rewrite H21.
    eapply taustar_eff;eauto.
    rewrite H12;auto.
  Qed.

  
  Lemma npnsw_step_Glocality:
    forall pc l fp pc' pc1,
      @glob_npnsw_step GE pc l fp pc'->
      thread_sim pc pc1 ->
      ThreadPool.inv pc.(thread_pool)->
      GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
      exists pc1',@glob_npnsw_step GE pc1 l fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    intros.
    destruct H as [|[]];[eapply corestep_Glocality in H|eapply callstep_Glocality in H|eapply retstep_Glocality in H];eauto;destruct H as (p&?&?&?);exists p;repeat match goal with H:_|-_/\_ => split end;auto;[left|right;left|right;right];auto.
  Qed.
  
  Lemma npnsw_step_eff:
    forall pc l fp pc',
      @glob_npnsw_step GE pc l fp pc' ->
      ThreadPool.inv pc.(thread_pool) ->
      GEffect pc.(gm) pc'.(gm) fp pc.(cur_tid).
  Proof.
    intros.
    destruct H as [|[]];inversion H;subst;simpl.
    eapply localstep_memeff in H_core_step as [];auto.
    eapply curcorefl_flmap_exists in H_tp_core as [];eauto.
    split;auto. eapply LocalAlloc_GlobalAlloc;eauto.
    constructor. apply MemEffect_refl.
    unfold GlobalAlloc;intros;contradiction.
    constructor. apply MemEffect_refl.
    unfold GlobalAlloc;intros;contradiction.
  Qed.
  Lemma npnsw_step_thdpinv:
    forall pc l fp pc',
      @glob_npnsw_step GE pc l fp pc'->
      ThreadPool.inv pc.(thread_pool) ->
      ThreadPool.inv pc'.(thread_pool).
  Proof.
    destruct 1 as [|[]];intros; eapply type_glob_step_elim in H;eapply GE_mod_wd_tp_inv in H;eauto.
  Qed.
  Lemma npnsw_taustar_thdpinv:
    forall pc fp pc',
      tau_star (@glob_npnsw_step GE) pc fp pc'->
      ThreadPool.inv pc.(thread_pool) ->
      ThreadPool.inv pc'.(thread_pool).
  Proof. induction 1;intros;[|apply npnsw_step_thdpinv in H];auto. Qed.
  Lemma npnsw_taustar_eff:
    forall pc fp pc',
      tau_star (@glob_npnsw_step GE) pc fp pc'->
      ThreadPool.inv pc.(thread_pool) ->
      GEffect pc.(gm) pc'.(gm) fp pc.(cur_tid).
  Proof.
    induction 1;intros.
    constructor;[apply MemEffect_refl|unfold GlobalAlloc;intros;contradiction].

    apply npnsw_step_thdpinv in H as L1;auto.
    specialize (IHtau_star L1).
    assert(cur_tid s = cur_tid s').
    destruct H as [|[]];Coqlib.inv H;auto.
    rewrite <- H2 in IHtau_star.
    apply npnsw_step_eff in H;auto.
    destruct H,IHtau_star.
    constructor.
    eapply MemEffect_union_fp with(fp2:=fp') in H;eauto.
    eapply MemEffect_union_fp with(fp2:=fp) in H4;eauto.
    rewrite FP.union_comm_eq in H4.
    eapply MemEffect_trans;eauto.

    unfold GlobalAlloc in *.
    unfold allocated_block in *.
    intros.
    assert(GMem.valid_block (gm s') b \/ ~ GMem.valid_block (gm s') b).
    apply classic. destruct H8;eauto.
  Qed.


  Lemma npnsw_taustar_Glocality:
    forall pc fp pc',
      tau_star glob_npnsw_step pc fp pc'->
      forall pc1,
        thread_sim pc pc1 ->
        ThreadPool.inv pc.(thread_pool)->
        ThreadPool.inv pc1.(thread_pool) ->
        GPre pc.(gm) pc1.(gm) fp (cur_tid pc) ->
        exists pc1',tau_star glob_npnsw_step pc1 fp pc1' /\ GPost pc'.(gm) pc1'.(gm) fp (cur_tid pc) /\ thread_sim pc' pc1'.
  Proof.
    induction 1;intros.
    exists pc1;split;constructor;auto.
    destruct H2;constructor;auto.
    unfold MemPost. apply unchanged_content_emp.

    assert(GPre (gm s)(gm pc1) fp (cur_tid s)).
    destruct H4;constructor;auto.
    eapply MemPre_subset;eauto. apply FP.union_subset.

    eapply npnsw_step_Glocality in H5 as step1;eauto.
    destruct step1 as (pc1'&step1&Post1&sim1).
    apply npnsw_step_thdpinv in step1 as inv1;auto.
    apply npnsw_step_thdpinv in H as inv0;auto.
    apply npnsw_step_eff in step1 as Eff1;auto.
    apply npnsw_step_eff in H as Eff0;auto.
    assert(Eq1:cur_tid pc1 = cur_tid s).
    destruct H1;auto.
    rewrite Eq1 in Eff1.
    eapply GPre_GEffect_GPost_Rule in H4 as Pre2;eauto.
    assert(cur_tid s = cur_tid s').
    destruct H as [|[]];inversion H;auto.

    rewrite H6 in Pre2.
    eapply IHtau_star in sim1 as Tmp1;eauto.
    destruct Tmp1 as (pc2&star'&post'&sim').
    exists pc2.
    split. econstructor;eauto.
    split;auto.
    apply npnsw_taustar_eff in star' as Eff2;auto.
    apply npnsw_taustar_eff in H0 as Eff3;auto.
    eapply GPost_GEffect_GPost_Rule1;eauto;try congruence.
    assert(cur_tid pc1 = cur_tid pc1').
    destruct step1 as [L|[L|L]];inversion L;auto.
    congruence.
  Qed.

  Local Notation "{-| PC , T }" := 
    ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |})  (at level 70,right associativity).
  Lemma corestep_getanocore:
    forall pc pc1 fp t c,
      @type_glob_step GE core pc tau fp pc1 ->
      ThreadPool.get_top pc.(thread_pool) t = Some c ->
      t <> cur_tid pc->
      ThreadPool.get_top pc1.(thread_pool) t = Some c.
  Proof.
    inversion 1;subst;simpl in *;intros.
    unfold ThreadPool.get_top in *.
    unfold ThreadPool.get_cs in *.
    destruct (Maps.PMap.get t (ThreadPool.content thdp)) eqn:e1;[|inversion H0].
    inversion H_tp_upd;subst;simpl.
    rewrite Maps.PMap.gso;auto.
    rewrite e1;auto.
  Qed.
  Lemma corestar_getanocore:
    forall pc pc1 fp,
      tau_star (@type_glob_step GE core) pc fp pc1 ->
      forall t c,
        ThreadPool.get_top pc.(thread_pool) t = Some c ->
        t <> cur_tid pc->
        ThreadPool.get_top pc1.(thread_pool) t = Some c.
  Proof.
    induction 1;intros;auto.
    assert(cur_tid s = cur_tid s').
    inversion H;auto.
    eapply corestep_getanocore in H;eauto.
    eapply IHtau_star in H;eauto.
    rewrite <- H3;auto.
  Qed.
  Lemma dif_thd_disj_fl:
    forall pc t1 t2 c1 c2,
      ThreadPool.get_top pc.(thread_pool) t1 = Some c1 ->
      ThreadPool.get_top pc.(thread_pool) t2 = Some c2 ->
      t1 <> t2 ->
      GlobEnv.wd GE ->
      @ThreadPool.inv GE pc.(thread_pool) ->
      MemAux.disj (FLists.get_fl (GlobEnv.freelists GE) (Core.F c2)) (FLists.get_fl (GlobEnv.freelists GE) (Core.F c1)).
  Proof.
    intros.
    unfold ThreadPool.get_top in*;unfold ThreadPool.get_cs in *.
    destruct Maps.PMap.get eqn:e1;[|inversion H].
    destruct (Maps.PMap.get t2 (ThreadPool.content (thread_pool pc))) eqn:e2;[|inversion H0].
    destruct H3 as [_ _ _].
    apply cs_inv in e1 as [? _ _];apply cs_inv in e2 as [? _ _].
    edestruct fid_belongsto;eauto.
    destruct t;inversion H;subst. unfold List.In;eauto.
    edestruct fid_belongsto0;eauto.
    destruct t0;inversion H0;subst;unfold List.In;eauto.
    destruct H2 as [[] _ _ _].
    unfold FLists.get_tfid in *.
    apply flist_disj.
    specialize (thread_fl_disj t1 t2 x x0 H1).
    rewrite <- H3;rewrite <- H4;auto.
  Qed.
   
  Lemma local_reorder_rule2:
    forall i1 F1 cc1 m1 fp1 cc1' m1' i2 F2 fp2 cc2 cc2' m2,
      let md1:= GlobEnv.modules GE i1 in
      let fl1:= FLists.get_fl (GlobEnv.freelists GE) F1 in
      let md2:= GlobEnv.modules GE i2 in
      let fl2:= FLists.get_fl(GlobEnv.freelists GE) F2 in
      step (ModSem.lang md1)(ModSem.Ge md1) fl1 cc1 m1 fp1 cc1' m1' ->
      step (ModSem.lang md2)(ModSem.Ge md2) fl2 cc2 m1' fp2 cc2' m2 ->
      MemAux.disj fl1 fl2 ->
      FP.smile fp1 fp2 ->
      exists m', step (ModSem.lang md2)(ModSem.Ge md2) fl2 cc2 m1 fp2 cc2' m'/\
            exists m'',step (ModSem.lang md1)(ModSem.Ge md1) fl1 cc1 m' fp1 cc1' m'' /\
                  GMem.eq' m'' m2.
  Proof.
    intros.
    apply localstep_memeff in H as L1.
    eapply LEffect_fpsmile_LPre_Rule in H2 as L2;eauto.
    edestruct localstep_locality1;eauto.
    destruct H3.

    eexists. constructor;eauto.
    apply localstep_memeff in H3 as L3.
    apply disj_comm in H1 as H1'.
    apply fpsmile_sym in H2 as H2'.

    eapply LEffect_fpsmile_LPre_Rule in H2';eauto.
    apply LPre_comm in H2'.
    edestruct localstep_locality1 with (fp:=fp1) ;eauto.
    destruct H5.

    eexists;split;eauto.
    
    repeat match goal with [H:step _ _ _ _ _ _ _ _|-_]=> eapply localstep_memeff in H end.
    
    remember (FLists.get_fl (GlobEnv.freelists GE) F1) as f1.
    remember (FLists.get_fl (GlobEnv.freelists GE) F2) as f2.
    
    revert H H0 H2 H3 H4 H5 H6. clear;intros.
    eapply LEffect_LPost_fpsmile_memeq.
    exact H. exact H0. exact H2. exact H3. exact H4. exact H5. exact H6.
  Qed.
  Lemma ptree_set_sym:
    forall A i j m (v1 v2:A),
      i <> j ->
      Maps.PTree.set i v1 (Maps.PTree.set j v2 m) =
      Maps.PTree.set j v2 (Maps.PTree.set i v1 m).
  Proof. induction i;intros;destruct m,j;simpl;auto;try (rewrite IHi;auto;intro;subst);contradiction. Qed.
  Lemma pmap_set_sym:
    forall A i j m (v1 v2:A),
      i <> j ->
      Maps.PMap.set i v1 (Maps.PMap.set j v2 m) =
      Maps.PMap.set j v2 (Maps.PMap.set i v1 m).
  Proof. unfold Maps.PMap.set;simpl;intros;f_equal. eapply ptree_set_sym;eauto. Qed.                                              
  Lemma thdp_upd_dif_eq:
    forall thdp thdp1 thdp1' thdp2 thdp2' t1 t2 c1 c2,
      @ThreadPool.update GE thdp t1 c1 thdp1 ->
      ThreadPool.update thdp1 t2 c2 thdp2 ->
      ThreadPool.update thdp t2 c2 thdp1'->
      ThreadPool.update thdp1' t1 c1 thdp2' ->
      t1 <> t2 ->
      thdp2 = thdp2'.
  Proof.
    destruct 1,1,1,1;subst;simpl in *;intros.
    unfold ThreadPool.get_cs in *;simpl in *.
    rewrite Maps.PMap.gso in H2;auto.
    rewrite Maps.PMap.gso in H8;auto.
    rewrite H in H8;rewrite H2 in H5;inversion H5;inversion H8;clear H5 H8;subst.
    assert(cs'0 = cs'1). inversion H3;inversion H6;subst;auto;inversion H11;subst;auto.
    assert(cs'=cs'2). inversion H0;inversion H9;subst;auto;inversion H12;subst;auto.
    subst.
    f_equal.
    apply pmap_set_sym;auto.
  Qed.
 
  Lemma corestep_reorder_rule:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE core ({-|pc,t1}) tau fp1 pc1 ->
      @type_glob_step GE core ({-|pc1,t2}) tau fp2 pc2 ->
      t1 <> t2 ->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',type_glob_step core ({-|pc,t2}) tau fp2 pc1' /\
             exists pc2', type_glob_step core ({-|pc1',t1}) tau fp1 pc2' /\
                     mem_eq_pc pc2 ({-|pc2',t2}).
  Proof.
    intros.
    inversion H;inversion H0;clear H H0;subst;simpl in *.
    assert(MemAux.disj (FLists.get_fl (GlobEnv.freelists GE) (Core.F c))(FLists.get_fl (GlobEnv.freelists GE) (Core.F c0))).
    assert(ThreadPool.get_top (thread_pool pc) t2 = Some c0).
    unfold ThreadPool.get_top in H_tp_core0;unfold ThreadPool.get_cs in *.
    inversion H_tp_upd;subst;simpl in *.
    rewrite Maps.PMap.gso in H_tp_core0;auto.
    eapply dif_thd_disj_fl;eauto.

    eapply local_reorder_rule2 in H as [m'[?[m''[]]]];eauto.
    assert(L1:ThreadPool.get_top (thread_pool pc) t2 = Some c0).
    unfold ThreadPool.get_top in *;unfold ThreadPool.get_cs in *.
    destruct (Maps.PMap.get t2 (ThreadPool.content thdp')) eqn:e1;[|inversion H_tp_core0].
    inversion H_tp_upd;subst. simpl in e1.
    rewrite Maps.PMap.gso in e1;auto.
    rewrite e1;auto.
    edestruct local_core_step as [?[?[]]];eauto.
    assert(L2:ThreadPool.get_top x0 t1 = Some c).
    unfold ThreadPool.get_top in *;unfold ThreadPool.get_cs in *.
    inversion H7;subst;simpl.
    rewrite Maps.PMap.gso;auto.
    edestruct local_core_step as [?[?[]]];eauto.
    assert( x = c'0). inversion H6;inversion H_core_upd0;subst;auto.
    assert( x1 = c'). inversion H8;inversion H_core_upd;subst;auto.
    subst.
    assert( thdp'0 = x2).
    eapply thdp_upd_dif_eq;[apply H_tp_upd| | | | ];eauto.
    subst.
    econstructor;split.
    econstructor;eauto.
    econstructor;split;[|split].
    econstructor;eauto.
    auto. simpl.
    split;[|split;[|apply GMem.eq'_sym]];auto.
  Qed.

  
  Ltac solv_thread_sym:=
    intros;
    solv_thread;
    repeat try (econstructor;simpl;solv_thread;simpl);
    solv_thread;simpl;
    try f_equal;try rewrite pmap_set_sym;auto;
    try f_equal;auto.
  Lemma thdp_update_sym:
    forall t1 t2,
      t1 <> t2->
      forall thdp1 c1' thdp2 c2' thdp3,
        @ThreadPool.update GE thdp1 t1 c1' thdp2 ->
        ThreadPool.update thdp2 t2 c2' thdp3 ->
        exists thdp',ThreadPool.update thdp1 t2 c2' thdp' /\ ThreadPool.update thdp' t1 c1' thdp3.
  Proof.  solv_thread_sym. Qed.

  Lemma thdp_update_push_sym:
    forall t1 t2,
      t1<>t2->
      forall thdp1 c1 thdp2 mid c sg thdp3,
        @ThreadPool.update GE thdp1 t1 c1 thdp2->
        ThreadPool.push thdp2 t2 mid c sg = Some thdp3->
        exists thdp',ThreadPool.push thdp1 t2 mid c sg = Some thdp'/\ ThreadPool.update thdp' t1 c1 thdp3.
  Proof. solv_thread_sym. Qed.
  Lemma thdp_update_pop_sym:
    forall t1 t2,
      t1<>t2->
      forall thdp1 c1 thdp2 thdp3,
        @ThreadPool.update GE thdp1 t1 c1 thdp2->
        ThreadPool.pop thdp2 t2 = Some thdp3->
        exists thdp',ThreadPool.pop thdp1 t2 = Some thdp'/\
                ThreadPool.update thdp' t1 c1 thdp3.
  Proof. solv_thread_sym. Qed.
  Lemma thdp_push_sym:
    forall t1 t2,
      t1<>t2->
      forall thdp1 mid1 c1 sg1 thdp2 mid2 c2 sg2 thdp3,
        @ThreadPool.push GE thdp1 t1 mid1 c1 sg1 = Some thdp2->
        ThreadPool.push thdp2 t2 mid2 c2 sg2 = Some thdp3->
        exists thdp',ThreadPool.push thdp1 t2 mid2 c2 sg2 = Some thdp'/\
                ThreadPool.push thdp' t1 mid1 c1 sg1 = Some thdp3.
  Proof.
    solv_thread_sym.
    repeat f_equal.
    destruct Coqlib.peq;try contradiction;auto.
    apply FunctionalExtensionality.functional_extensionality;intro.
    repeat destruct Coqlib.peq;subst;auto;try contradiction.
  Qed.
  Lemma thdp_push_update_sym:
    forall t1 t2,t1<>t2->
            forall thdp1 mid1 c1 sg1 thdp2 c2 thdp3,
              @ThreadPool.push GE thdp1 t1 mid1 c1 sg1 = Some thdp2->
              ThreadPool.update thdp2 t2 c2 thdp3->
              exists thdp',ThreadPool.update thdp1 t2 c2 thdp'/\ ThreadPool.push thdp' t1 mid1 c1 sg1 = Some thdp3.
  Proof. solv_thread_sym. Qed.
  Lemma thdp_push_pop_sym:
    forall t1 t2,t1<>t2->
            forall thdp1 mid1 c1 sg1 thdp2 thdp3,
              @ThreadPool.push GE thdp1 t1 mid1 c1 sg1 = Some thdp2->
              ThreadPool.pop thdp2 t2 = Some thdp3->
              exists thdp',ThreadPool.pop thdp1 t2 = Some thdp'/\
                      ThreadPool.push thdp' t1 mid1 c1 sg1=Some thdp3.
  Proof. solv_thread_sym.  Qed.
  Lemma thdp_pop_sym_weak:
    forall t1 t2,t1<>t2->
            forall thdp1 thdp2 thdp3,
              @ThreadPool.pop GE thdp1 t1 = Some thdp2->
              ThreadPool.pop thdp2 t2 = Some thdp3->
              exists thdp',ThreadPool.pop thdp1 t2 = Some thdp' /\ ThreadPool.pop thdp' t1 = Some thdp3.
  Proof. solv_thread_sym. Qed.
  Lemma thdp_pop_sym:
    forall t1 t2,
      t1<>t2->
      forall thdp1 thdp2 c thdp3,
        @ThreadPool.pop GE thdp1 t1 = Some thdp2->
        ThreadPool.update thdp2 t1 c thdp3->
        forall thdp4 c' thdp5,
          ThreadPool.pop thdp3 t2 = Some thdp4->
          ThreadPool.update thdp4 t2 c' thdp5->
          exists tp2 tp3 tp4,
            ThreadPool.pop thdp1 t2 = Some tp2/\
            ThreadPool.update tp2 t2 c' tp3/\
            ThreadPool.pop tp3 t1 = Some tp4/\
            ThreadPool.update tp4 t1 c thdp5.                         
  Proof.
    solv_thread_sym.
    rewrite Maps.PMap.set2.
    rewrite pmap_set_sym;auto.
  Qed.
  Lemma thdp_pop_update_sym_weak:
    forall t1 t2,t1<>t2->
            forall thdp1 thdp2 c thdp3,
              @ThreadPool.pop GE thdp1 t1 = Some thdp2->
              ThreadPool.update thdp2 t2 c thdp3->
              exists thdp' ,
                ThreadPool.update thdp1 t2 c thdp'/\
                ThreadPool.pop thdp' t1 = Some thdp3.
  Proof. solv_thread_sym. Qed.
  Lemma thdp_pop_update_sym:
    forall t1 t2,t1<>t2->
            forall thdp1 thdp2 c thdp3 c' thdp4,
              @ThreadPool.pop GE thdp1 t1 = Some thdp2->
              ThreadPool.update thdp2 t1 c thdp3->
              ThreadPool.update thdp3 t2 c' thdp4->
              exists thdp' thdp'',
                ThreadPool.update thdp1 t2 c' thdp'/\
                ThreadPool.pop thdp' t1 = Some thdp''/\
                ThreadPool.update thdp'' t1 c thdp4.
  Proof.
    intros.
    edestruct thdp_update_sym as (?&?&?);eauto.
    edestruct thdp_pop_update_sym_weak as (?&?&?);eauto.
  Qed.
  Lemma thdp_pop_push_sym_weak:
    forall t1 t2,t1<>t2->
            forall thdp1 thdp2 mid c sg thdp3,
              @ThreadPool.pop GE thdp1 t1 = Some thdp2->
              ThreadPool.push thdp2 t2 mid c sg = Some thdp3->
              exists thdp',ThreadPool.push thdp1 t2 mid c sg = Some thdp'/\
                      ThreadPool.pop thdp' t1 = Some thdp3.
  Proof. solv_thread_sym.  Qed.
  Lemma thdp_pop_push_sym:
    forall t1 t2,t1<>t2->
            forall thdp1 c' thdp2 thdp3 mid c sg thdp4,
              @ThreadPool.pop GE thdp1 t1 = Some thdp2->
              ThreadPool.update thdp2 t1 c' thdp3->
              ThreadPool.push thdp3 t2 mid c sg = Some thdp4->
              exists thdp' thdp'',ThreadPool.push thdp1 t2 mid c sg = Some thdp'/\
                             ThreadPool.pop thdp' t1 = Some thdp'' /\
                             ThreadPool.update thdp'' t1 c' thdp4.
  Proof.
    intros.
    edestruct thdp_update_push_sym as (?&?&?);eauto.
    edestruct thdp_pop_push_sym_weak as (?&?&?);eauto.
  Qed.
  Lemma gettop_valid_tid:
    forall thdp c t,
      @ThreadPool.get_top GE thdp t = Some c->
      ThreadPool.inv thdp->
      ThreadPool.valid_tid thdp t.
  Proof.
    intros.
    solv_thread.
    destruct H0.
    unfold Coqlib.Plt.
    unfold BinPos.Pos.lt.
    apply NNPP;intro.
    assert(BinPos.Pos.ge t (ThreadPool.next_tid thdp)).
    auto.
    apply tp_finite in H0.
    rewrite Heqo in H0;inversion H0.
  Qed.
  Lemma step_switchable:
    forall l pc fp pc',
      @glob_step GE pc l fp pc' ->
      l <> sw ->
      atom_bit pc = O->
      ThreadPool.inv pc.(thread_pool)->
      forall t,
        glob_step ({-|pc,t}) sw FP.emp pc.
  Proof.
    intros.
    destruct pc as [thdp tid tgm tbit];simpl in *;subst.
    assert(exists c,ThreadPool.get_top thdp tid = Some c).
    inversion H;subst;eauto;contradiction.
    destruct H1.
    constructor;auto.
    eapply gettop_valid_tid in H1;eauto.
    intro;Coqlib.inv H2.
    solv_thread.
  Qed.

   Lemma mem_eq_local_step:
    forall m1 m2,
      GMem.eq' m1 m2->
      forall i_x F cc fp cc' m1',
        step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m1 fp cc' m1' ->
        exists m2',step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x)) (FLists.get_fl (GlobEnv.freelists GE) F) cc m2 fp cc' m2' /\ GMem.eq' m1' m2'. 
  Proof.
    intros.
    specialize (wdge i_x) as [].
    unfold eq_mem_eq_corestep in eq_mem_step.
    eapply eq_mem_step;eauto.
  Qed.

  Lemma mem_eq_corestep:
    forall pc pc',
      mem_eq_pc pc pc' ->
      forall fp pce,
        @type_glob_step GE core pc tau fp pce ->
        exists pce',@type_glob_step GE core pc' tau fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros.
    inversion H0;clear H0;subst.
    destruct pc';simpl in *.
    destruct H as (?&?&?&?);simpl in *;subst.
    eapply mem_eq_local_step in H_core_step as (?&?&?);eauto.
    eexists;split;econstructor;eauto.
  Qed.
  Lemma mem_eq_core_star:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall l fp pce,
        star (@type_glob_step GE core) pc l fp pce->
        exists pce',star (type_glob_step core) pc' l fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros. revert pc' H.
    induction H0;intros.
    eexists;split;[constructor|auto].
    assert(e=tau). inversion H;auto. subst.
    eapply mem_eq_corestep in H1 as (?&?&?);eauto.
    eapply IHstar in H2 as (?&?&?);eauto.
    eexists;split;[econstructor|];eauto.
  Qed.
    
  Lemma mem_eq_coreN:
    forall pc pc',
      mem_eq_pc pc pc' ->
      forall i fp pce,
        tau_N (@type_glob_step GE core) i pc fp pce ->
        exists pce',tau_N (@type_glob_step GE core) i pc' fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros.
    revert pc' H.
    induction H0;intros.
    destruct H as (?&?&?&?).
    eexists;split;econstructor;eauto.
    eapply mem_eq_corestep in H as (?&?&?);eauto.
    apply IHtau_N in H2 as (?&?&?).
    eexists;split;eauto.
    econstructor 2;eauto.
  Qed.
  Lemma mem_eq_corestar:
    forall pc pc',
      mem_eq_pc pc pc' ->
      forall fp pce,
        tau_star (@type_glob_step GE core) pc fp pce ->
        exists pce',tau_star (@type_glob_step GE core) pc' fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros. apply tau_star_tau_N_equiv in H0 as [].
    eapply mem_eq_coreN in H0 as (?&?&?);eauto.
    eexists;split;eauto.
    eapply tau_star_tau_N_equiv;eauto.
  Qed.
  Lemma mem_eq_globstep:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall x l fp pce,
        @type_glob_step GE x pc l fp pce ->
        exists pce',type_glob_step x pc' l fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros.
    destruct pc as [thdp0 tid0 tgm0 tbit0],pc' as [? ? tgm1 ?].
    destruct H as [L[L1[L2 L3]]].
    simpl in *;subst.
    destruct x;Coqlib.inv H0;try(eexists;split;econstructor;eauto;fail).
    eapply mem_eq_local_step in H_core_step as (?&?&?);eauto.
    eexists;split;econstructor;eauto.
  Qed.
  Lemma mem_eq_non_evt_star:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall fp pc'',
        non_evt_star glob_step pc fp pc''->
        exists pc1,non_evt_star glob_step pc' fp pc1 /\ mem_eq_pc pc'' pc1.
  Proof.
    intros.
    revert pc' H.
    induction H0;intros.
    exists pc'. split;auto. constructor.
    assert(exists i l,type_glob_step i s1 l fp1 s2 /\( l = tau \/ l = sw)).
    destruct H;eapply type_glob_step_exists in H as [];eauto.
    destruct H2 as (?&?&?&?).
    eapply mem_eq_globstep in H2 as (?&?&?);eauto.
    apply type_glob_step_elim in H2.
    eapply IHnon_evt_star in H4 as (?&?&?);eauto.
    exists x2;split;auto. econstructor;eauto.
    destruct H3;subst;auto.
  Qed.
    
  Lemma mem_eq_pc_finalstate:
    forall pc pc',
      mem_eq_pc pc pc'->
      final_state pc->
      final_state pc'.
  Proof.
    intros.
    inversion H as (?&?&?&?).
    inversion H0;subst.
    econstructor;eauto.
    rewrite H1 in *.
    auto.
  Qed.
  Lemma mem_eq_pc_abort:
    forall pc pc',
      mem_eq_pc pc pc'->
      abort pc->
      abort pc'.
  Proof.
    unfold abort;intros.
    inversion H as (?&?&?&?).
    rewrite H1 in *.
    rewrite H3 in *.
    destruct H0.
    split;auto.
    intros.
    apply type_glob_step_exists in H6 as [].
    apply mem_eq_pc_sym in H as L.
    eapply mem_eq_globstep in H6 as (?&?&?);eauto.
    apply type_glob_step_elim in H6;eauto.
  Qed.
  Lemma mem_eq_swstar:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall pc1,
        sw_star glob_step pc pc1 ->
        exists pc1',sw_star glob_step pc' pc1' /\ mem_eq_pc pc1 pc1'.
  Proof.
    intros.
    revert pc' H.
    induction H0;intros.
    exists pc'. split. constructor. auto.
    apply type_glob_step_exists in H as [].
    destruct x ;try(inversion H;fail).
    eapply mem_eq_globstep in H as [?[]];eauto.
    specialize (IHsw_star _ H2) as [?[]].
    exists x0. split;auto. econstructor 2;eauto. apply type_glob_step_elim in H;auto.
  Qed.
     
  Lemma mem_eq_pc_silent_diverge:
    forall pc pc',
      mem_eq_pc pc pc'->
      silent_diverge glob_step pc->
      silent_diverge glob_step pc'.
  Proof.
    cofix.
    intros.
    inversion H0;subst.
    eapply mem_eq_swstar with(pc':=pc') in H1 as [?[]];auto.
    apply type_glob_step_exists in H2 as [].
    eapply mem_eq_globstep with(pc':=x) in H2 as [?[]];auto.
    apply type_glob_step_elim in H2.
    econstructor;eauto.
  Qed.
    
  Inductive starN : nat -> @ProgConfig GE->list glabel ->FP.t->@ProgConfig GE ->Prop:=
  | star0:forall s,starN 0 s nil FP.emp s
  | star_step':forall i s1 e fp1 s2 l fp2 s3,
      glob_step s1 e fp1 s2->
      starN i s2 l fp2 s3->
      starN (S i) s1 (cons e l) (FP.union fp1 fp2) s3.

  Lemma star_starN_equiv:
    forall pc pc' l fp,
      star (@glob_step GE) pc l fp pc' <-> exists i,starN i pc l fp pc'.
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
 
  Lemma mem_eq_globstar:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall l fp pce,
        star (@glob_step GE) pc l fp pce ->
        exists pce',star glob_step pc' l fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros.
    apply star_starN_equiv in H0 as [].
    revert pc pc' l fp pce H H0.
    induction x;intros.
    inversion H0;subst. eexists;split;eauto;constructor.
    inversion H0;subst.
    eapply type_glob_step_exists in H2 as L0.
    destruct L0.
    eapply mem_eq_globstep in H as L1;eauto.
    destruct L1 as (?&?&?).
    eapply type_glob_step_elim in H4.
    eapply IHx in H5 as [?[]];eauto.
    eexists;split;eauto.
    econstructor;eauto.
  Qed.
    
  Lemma mem_eq_glob_taustar:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall fp pce,
        tau_star (@glob_step GE) pc fp pce ->
        exists pce',tau_star glob_step pc' fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros;apply tau_star_tau_N_equiv in H0 as [];revert pc pc' fp pce H H0;induction x;intros;inversion H0;subst.
    eexists;econstructor;eauto;constructor.
    eapply type_glob_step_exists in H2 as L0.
    destruct L0.
    eapply mem_eq_globstep in H as L1;eauto.
    destruct L1 as (?&?&?).
    eapply type_glob_step_elim in H4.
    eapply IHx in H5 as [?[]];eauto.
    eexists;split;eauto. econstructor;eauto.
  Qed.
  Lemma mem_eq_glob_tauN:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall i fp pce,
        tau_N (@glob_step GE) i pc fp pce->
        exists pce',tau_N glob_step i pc' fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros pc pc' H i;revert pc pc' H;induction i;intros;inversion H0;subst.
    eexists;econstructor;eauto;constructor.
    eapply type_glob_step_exists in H2 as L0.
    destruct L0.
    eapply mem_eq_globstep in H as L1;eauto.
    destruct L1 as (?&?&?).
    eapply type_glob_step_elim in H4.
    eapply IHi in H5 as [?[]];eauto.
    eexists;split;eauto. econstructor;eauto.
  Qed.
  Lemma mem_eq_npnsw_step_star:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall fp pce,
        tau_star (@glob_npnsw_step GE) pc fp pce ->
        exists pce',tau_star glob_npnsw_step pc' fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros;apply tau_star_tau_N_equiv in H0 as [];revert pc pc' fp pce H H0;induction x;intros;inversion H0;subst.
    eexists;econstructor;eauto;constructor.

    assert(exists pc'',glob_npnsw_step pc' tau fp0 pc'' /\ mem_eq_pc s' pc'').
    destruct H2 as [|[]];eapply mem_eq_globstep in H as [?[]];eauto;eexists;split;eauto;[left|right;left|right;right];eauto.
    destruct H1 as (?&?&?).
    eapply IHx in H4 as [?[]];eauto.
    eexists;split;eauto. econstructor;eauto.
  Qed.

  Lemma mem_eq_npnsw_step_starN:
    forall pc pc',
      mem_eq_pc pc pc'->
      forall i fp pce,
        tau_N (@glob_npnsw_step GE) i pc fp pce ->
        exists pce',tau_N glob_npnsw_step i pc' fp pce' /\ mem_eq_pc pce pce'.
  Proof.
    intros;revert pc pc' fp pce H H0;induction i;intros;inversion H0;subst.
    eexists;econstructor;eauto;constructor.

    assert(exists pc'',glob_npnsw_step pc' tau fp0 pc'' /\ mem_eq_pc s' pc'').
    destruct H2 as [|[]];eapply mem_eq_globstep in H as [?[]];eauto;eexists;split;eauto;[left|right;left|right;right];eauto.
    destruct H1 as (?&?&?).
    eapply IHi in H4 as [?[]];eauto.
    eexists;split;eauto. econstructor;eauto.
  Qed.


  Lemma np_predict_tau_star:
    forall ge pc fp fp' t,
      @np_predict ge pc t fp fp'->
      exists pc',tau_star np_step ({-|pc,t}) fp pc'.
  Proof.
    intros.
    Coqlib.inv H;apply np_normal_tau_N_exists in H0 as (?&?&?&?&?);eexists;eapply tau_star_tau_N_equiv;eauto.
  Qed.
  Lemma tau_star_glob_star:
    forall ge pc fp pc',
      tau_star (@np_step ge) pc fp pc'->
      tau_star glob_step pc fp pc'.
  Proof.
    induction 1.
    constructor.
    econstructor 2;eauto.
    revert H;clear;intro.
    inversion H;subst.
    econstructor;eauto.
    eapply GlobSemantics.Call;eauto.
    eapply GlobSemantics.Return;eauto.
    eapply GlobSemantics.Halt;eauto.
    eapply GlobSemantics.Ent_Atom;eauto.
  Qed.
  Lemma np_step_glob_step:
    forall ge pc l fp pc',
      @np_step ge pc l fp pc'->
      exists l',star (@glob_step ge) pc l' fp pc'.
  Proof.
    intros.
    eapply type_step_exists in H as [].
    destruct x.
    assert(l=tau). inversion H;auto. subst.
    eapply core_step_equiv in H.
    rewrite <- FP.fp_union_emp with(fp:=fp).
    eexists;econstructor 2;eauto. eapply type_glob_step_elim;eauto. constructor.
    assert(l=tau). inversion H;auto. subst.
    eapply call_step_equiv in H;eapply type_glob_step_elim in H.
    rewrite <- FP.fp_union_emp with(fp:=fp).
    eexists;econstructor 2;eauto. constructor.
    
    assert(l=tau). inversion H;auto. subst.
    eapply ret_step_equiv in H;eapply type_glob_step_elim in H.
    rewrite <- FP.fp_union_emp with(fp:=fp).
    eexists;econstructor 2;eauto. constructor.
    
    assert(l=tau). inversion H;auto. subst.
    eapply entat_step_equiv in H;eapply type_glob_step_elim in H.
    rewrite <- FP.fp_union_emp with(fp:=fp).
    eexists;econstructor 2;eauto. constructor.

    assert(l=sw). inversion H;auto. subst.
    assert(fp=FP.emp). inversion H;auto. subst.
    eapply extat_step_equiv in H as (?&?).
    eapply type_glob_step_elim in H.
    eapply type_glob_step_elim in H0.
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    eexists;econstructor 2;eauto. 
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    econstructor 2;eauto. constructor.

    assert(l=sw). inversion H;auto. subst.
    assert(fp=FP.emp). inversion H;auto. subst.
    eapply thrdhalt_step_equiv in H as (?&?).
    eapply type_glob_step_elim in H.
    eapply type_glob_step_elim in H0.
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    eexists;econstructor 2;eauto. 
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    econstructor 2;eauto. constructor.

    assert(l=tau). inversion H;auto. subst.
    assert(fp=FP.emp). inversion H;auto. subst.
    eapply allhalt_step_equiv in H as (?&?).
    eapply type_glob_step_elim in H.
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    eexists;econstructor 2;eauto.  constructor.

    assert(exists x,l=evt x). inversion H;subst;eauto.
    destruct H0. subst.
    assert(fp=FP.emp). inversion H;auto. subst.
    eapply efprint_step_equiv in H as (?&?).
    eapply type_glob_step_elim in H.
    eapply type_glob_step_elim in H0.
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    eexists;econstructor 2;eauto. 
    rewrite <- FP.fp_union_emp with(fp:=FP.emp).
    econstructor 2;eauto. constructor.

    inversion H. inversion H.
  Qed.
    
  Lemma np_star_glob_star:
    forall ge pc l fp pc',
      star (@np_step ge) pc l fp pc' ->
      exists l',star (@glob_step ge) pc l' fp pc'.
  Proof.
    induction 1. exists nil;constructor.
    eapply  np_step_glob_step in H as [].
    destruct IHstar.
    revert H H1;clear;intros.
    induction H.
    exists x0. rewrite FP.emp_union_fp. auto.
    destruct IHstar;auto.
    eexists (cons e x).
    rewrite<- FP.fp_union_assoc.
    econstructor;eauto.
  Qed.
  Lemma npnsw_step_I_corestep:
    forall ge pc l fp pc',
      @glob_npnsw_step ge pc l fp pc' ->
      atom_bit pc = I ->
      type_glob_step core pc l fp pc'.
  Proof. destruct 1 as [|[]];intro;auto;inversion H;subst;inversion H0. Qed.
  Lemma npnsw_taustar_I_core_taustar:
    forall ge pc fp pc',
      tau_star (@glob_npnsw_step ge) pc  fp pc' ->
      atom_bit pc = I ->
      tau_star (type_glob_step core) pc fp pc'.
  Proof.
    induction 1;intros;econstructor.
    eapply npnsw_step_I_corestep;eauto.
    eapply npnsw_step_I_corestep in H;eauto.
    assert(atom_bit s' = I). inversion H;subst;auto.
    eauto.
  Qed.
  Lemma npnsw_step_pc_valid_tid_preservation:
    forall ge pc l fp pc' t,
      @glob_npnsw_step ge pc l fp pc' ->
      GSimDefs.pc_valid_tid pc t ->
      GSimDefs.pc_valid_tid pc' t.
  Proof.
    destruct 1 as [|[]];Coqlib.inv H;unfold GSimDefs.pc_valid_tid;intros;destruct H;simpl in *;split;try match goal with [H: ~ _ |- ~ _] => intro;contradict H end;solv_thread;econstructor;eauto;solv_thread.
  Qed.

  Lemma npnsw_taustar_pc_valid_tid_preservation:
    forall ge pc fp pc' t,
      tau_star (@glob_npnsw_step ge) pc fp pc'->
      GSimDefs.pc_valid_tid pc t ->
      GSimDefs.pc_valid_tid pc' t.
  Proof. induction 1;intros;auto;eapply npnsw_step_pc_valid_tid_preservation in H;eauto. Qed.
    
  Lemma npnsw_step_O_preservation:
    forall ge pc l fp pc',
      @glob_npnsw_step ge pc l fp pc'->
      atom_bit pc = O ->
      atom_bit pc' = O.
  Proof. destruct 1 as [|[]];inversion H;auto. Qed.
  Lemma npnsw_taustar_O_preservation:
    forall ge pc fp pc',
      tau_star (@glob_npnsw_step ge) pc fp pc'->
      atom_bit pc = O ->
      atom_bit pc' = O.
  Proof. induction 1;auto;intros. apply npnsw_step_O_preservation in H;auto. Qed.
  Lemma npnsw_step_tid_preservation:
    forall ge pc l fp pc',
      @glob_npnsw_step ge pc l fp pc'->
      cur_tid pc = cur_tid pc'.
  Proof. destruct 1 as [|[]];inversion H;auto. Qed.
  Lemma npnsw_taustar_tid_preservation:
    forall ge pc fp pc',
      tau_star (@glob_npnsw_step ge) pc fp pc'->
      cur_tid pc = cur_tid pc'.
  Proof. induction 1;auto. apply npnsw_step_tid_preservation in H;congruence. Qed.
  Lemma npnsw_step_diff_thread_sim:
    forall  pc l fp pc' t,
      glob_npnsw_step pc l fp pc'->
      t <> cur_tid pc ->
      thread_sim ({-|pc,t})({-|pc',t}).
  Proof.
    intros.
    unfold thread_sim. unfold getcurcs.
    destruct H as [|[]];Coqlib.inv H; repeat match goal with H:_|-_/\_ => split end;solv_thread;solv_thread; destruct Coqlib.peq;subst;try contradiction;auto.
  Qed.
  Lemma npnsw_taustar_diff_thread_sim:
    forall  pc fp pc' t,
      tau_star glob_npnsw_step pc fp pc'->
      t <> cur_tid pc ->
      thread_sim ({-|pc,t})({-|pc',t}).
  Proof.
    intros.
    revert t H0;induction H;intros;auto.
    unfold thread_sim;auto.

    edestruct IHtau_star as (?&?&?&?).
    destruct H as [H|[H|H]];Coqlib.inv H;eauto.
    eapply npnsw_step_diff_thread_sim in H as (?&?&?&?);eauto.
    unfold thread_sim.
    repeat match goal with H:_|-_/\_ => split end;congruence.
  Qed.
  Lemma tau_star_to_star:
    forall (A:Type) step (s1:A) fp (s2:A),
      tau_star step s1 fp s2 ->
      exists l,star step s1 l fp s2.
  Proof.
    induction 1. exists nil. constructor.
    destruct IHtau_star.
    exists (cons tau x). econstructor;eauto.
  Qed.
  Lemma cons_star_star:
    forall (A:Type) step (s1 s2 s3:A) l1 l2 fp1 fp2,
      star step s1 l1 fp1 s2 ->
      star step s2 l2 fp2 s3 ->
      star step s1 (app l1 l2)(FP.union fp1 fp2) s3.
  Proof.
    induction 1;intros.
    simpl. rewrite FP.emp_union_fp. auto.
    specialize (IHstar H1).
    assert(app (cons e l) l2 = cons e (app l l2));auto.
    rewrite H2.
    rewrite<- FP.fp_union_assoc.
    econstructor;eauto.
  Qed.
  Lemma npnsw_star_glob_star:
    forall ge pc l fp pc',
      star (@glob_npnsw_step ge) pc l fp pc'->
      star glob_step pc l fp pc'.
  Proof. induction 1;intros;econstructor;eauto;destruct H as [|[]];eapply type_glob_step_elim;eauto. Qed.

  Lemma extended_glob_reorder_case1:
    forall x t1 t2 l1 l2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE core ({-|pc,t1}) l1 fp1 pc1->
      @type_glob_step GE x ({-|pc1,t2}) l2 fp2 pc2->
      atom_bit pc1 = atom_bit pc2 ->
      t1 <> t2->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',type_glob_step x ({-|pc,t2}) l2 fp2 pc1' /\
             exists pc2',type_glob_step core ({-|pc1',t1}) l1 fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).

    Proof.
    intros.
    destruct pc as [thdp tid tgm tbit];simpl in *;subst.
    destruct x;Coqlib.inv H;Coqlib.inv H0;simpl in *;try(inversion H1;inversion H2;fail);subst.
    {
      edestruct thdp_update_sym as (?&?&?);eauto.
      assert(thdp = thread_pool ({thdp,tid,tgm,O})). auto. 
      edestruct local_reorder_rule2 with(fp1:=fp1) as (?&?&?&?&?);eauto.
      eapply disj_comm; eapply dif_thd_disj_fl;eauto.
      rewrite <- H_tp_core;f_equal;eauto.
      eapply gettop_backwards_preserve;eauto.
      eauto.
      eexists;split.
      econstructor;eauto.
      eapply gettop_backwards_preserve;eauto.
      eexists;split;simpl.
      econstructor;eauto.
      eapply gettop_preserve;eauto.
      split;[|split;[|split]];simpl;auto.
      apply GMem.eq'_sym;auto.
    }
    {
      edestruct thdp_update_push_sym as (?&?&?);eauto.
      eexists;split.
      econstructor 2;eauto.
      eapply gettop_backwards_preserve;eauto.
      eexists;split;simpl.
      econstructor;eauto.
      eapply gettop_preserve;eauto.
      right;right;eauto.
      simpl. apply mem_eq_pc_refl.
    }
    {
      edestruct thdp_update_pop_sym as (?&?&?);eauto.
      edestruct thdp_update_sym as (?&?&?);eauto.
      eexists;split.
      econstructor 3;eauto.
      eapply gettop_backwards_preserve;eauto.
      eapply gettop_backwards_preserve;eauto.
      eexists;split;simpl.
      econstructor;eauto.
      eapply gettop_preserve with(thdp2:=x) in H_tp_core;eauto.
      eapply gettop_preserve;eauto.
      simpl. apply mem_eq_pc_refl.
    }
    {
      edestruct thdp_update_sym as (?&?&?);eauto.
      eexists;split.
      econstructor 7;eauto.
      eapply gettop_backwards_preserve;eauto.
      eexists;split;simpl.
      econstructor;eauto.
      eapply gettop_preserve ;eauto.
      simpl. apply mem_eq_pc_refl.
    }
    {
      eexists;split.
      econstructor;eauto.
      eapply valid_tid_backwards_preserve;eauto.
      intro;contradict H_not_halted.
      eapply halted_preserve;eauto.
      eexists;split.
      econstructor;eauto.
      simpl; apply mem_eq_pc_refl.      
    }
    {
      edestruct thdp_update_pop_sym as (?&?&?);eauto.
      eexists;split.
      econstructor 4;eauto.
      eapply gettop_backwards_preserve;eauto.
      eapply halted_backwards_preserve;eauto.
      eexists;split.
      econstructor;eauto;simpl.
      eapply gettop_preserve;eauto.
      simpl. apply mem_eq_pc_refl.
    }
  Qed.
  Ltac clear_ands:=
    try match goal with
        | H : _ |- _ /\ _ => split
        | H : _ |- exists _, _ => eexists
        end.
  
  Ltac gettop_simpl:=
    try match goal with
          H:_|-ThreadPool.get_top _ _ = _ =>
          try (eapply gettop_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eauto;fail);fail);
          try (eapply gettop_backwards_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eauto;fail);fail) end.

  Ltac build_step:=
    try match goal with
        | H : _ |- type_glob_step ?a _ _ _ _ => econstructor;gettop_simpl;eauto;gettop_simpl end.
  Ltac valid_tid_simpl:=
    try match goal with
          H:_|- ThreadPool.valid_tid _ _ =>
          try (eapply valid_tid_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eauto;fail);fail);
          try (eapply valid_tid_backwards_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eauto;fail);fail) end.
  Ltac halted_preserve_auto':=
    try match goal with
          | H: _ |- ThreadPool.halted _ _ =>
            try (eapply halted_backwards_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eauto;fail);fail);
            try (eapply halted_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eexists;eexists;eexists;eexists;esplit;eauto;fail);fail)
          | H: ~ ThreadPool.halted _ ?t |- ~ ThreadPool.halted _ ?t =>
            intro;contradict H;
            try (eapply halted_backwards_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eauto;fail);fail);
            try (eapply halted_preserve;eauto;try (left;eauto;fail);try(right;left;eauto;fail);try(right;right;eexists;eexists;eexists;eexists;esplit;eauto;fail);fail)
        end.
  
  Ltac mem_eq_tactic:=
    simpl;
    try match goal with H:_|-mem_eq_pc ?a ?a => apply mem_eq_pc_refl end.
                    
  Lemma extended_glob_reorder_case2:
    forall x t1 t2 l1 l2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE call ({-|pc,t1}) l1 fp1 pc1->
      @type_glob_step GE x ({-|pc1,t2}) l2 fp2 pc2->
      atom_bit pc1 = atom_bit pc2->
      t1 <> t2->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',type_glob_step x ({-|pc,t2}) l2 fp2 pc1'/\
             exists pc2',type_glob_step call ({-|pc1',t1}) l1 fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    destruct pc as [thdp tid tgm tbit];simpl in *;subst.
    
    destruct x;inversion H;inversion H0;subst;simpl in *;try (inversion H1;inversion H17;fail);[edestruct thdp_push_update_sym as (?&?&?)|edestruct thdp_push_sym as (?&?&?)|edestruct thdp_push_pop_sym as (?&?&?);eauto; edestruct thdp_push_update_sym as (?&?&?)| edestruct thdp_push_update_sym as (?&?&?)| |edestruct thdp_push_pop_sym as (?&?&?)];eauto; do 2 clear_ands;build_step;valid_tid_simpl;halted_preserve_auto';do 2 clear_ands;build_step;mem_eq_tactic.    
    eapply gettop_preserve with(thdp2:=x) in H_tp_core;eauto.
    eapply gettop_preserve;eauto.    
  Qed.
  Ltac steptac:=
    do 2 clear_ands;build_step;valid_tid_simpl;halted_preserve_auto';mem_eq_tactic.
  Lemma extended_glob_reorder_case3:
    forall x t1 t2 l1 l2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE ret ({-|pc,t1}) l1 fp1 pc1->
      @type_glob_step GE x ({-|pc1,t2}) l2 fp2 pc2->
      atom_bit pc1 = atom_bit pc2->
      t1 <> t2->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',type_glob_step x ({-|pc,t2}) l2 fp2 pc1'/\
             exists pc2',type_glob_step ret ({-|pc1',t1}) l1 fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    destruct pc as [thdp tid tgm tbit];simpl in *;subst.
    destruct x;inversion H;inversion H0;subst;simpl in *;try (inversion H1;inversion H17;fail).
    edestruct thdp_pop_update_sym as (?&?&?&?&?);eauto.
    steptac.
    revert H2 H_tp_core0 H_tp_upd H_tp_pop;clear;intros.
    solv_thread;solv_thread.
    steptac.
    revert H6 H7 H_tp_caller H_tp_pop;clear;intros.
    solv_thread; solv_thread.
    
    edestruct thdp_pop_push_sym as (?&?&?&?&?);eauto.
    steptac.
    revert H_tp_core0 H_tp_upd H_tp_pop H2;clear;intros.
    solv_thread. solv_thread.
    steptac.
    revert H2 H_tp_caller H_tp_pop H6 H7;clear;intros.
    solv_thread;solv_thread;contradiction.

    edestruct thdp_pop_sym as (?&?&?&?&?&?&?);eauto.
    steptac.
    revert H2 H_tp_core0 H_tp_upd H_tp_pop;clear;intros;solv_thread;solv_thread;try contradiction.
    revert H2 H6 H_tp_caller0 H_tp_pop0 H_tp_upd H_tp_pop;clear;intros;solv_thread;solv_thread;try contradiction.
    eapply gettop_preserve with(thdp2:=x) in H_tp_core;eauto.
    eapply gettop_preserve in H_tp_core;eauto.
    eexists;econstructor;simpl.
    eapply GReturn with(c1:=c)(res1:=res);eauto.
    revert H_tp_pop H_tp_caller H6 H7 H8 H2;clear;intros.
    solv_thread. solv_thread;contradiction.
    apply mem_eq_pc_refl.

    edestruct thdp_pop_update_sym as (?&?&?&?&?);eauto.
    steptac.
    revert H2 H_tp_core0 H_tp_upd H_tp_pop;clear;intros;solv_thread;solv_thread;contradiction.
    steptac.
    revert H2 H6 H7 H8 H_tp_caller H_tp_pop;clear;intros;solv_thread;solv_thread;try contradiction.

    steptac.
    solv_thread.
    intro;contradict H_not_halted;econstructor;solv_thread.
    rewrite Maps.PMap.gso;auto.
    steptac.

    edestruct thdp_update_pop_sym as (?&?&?);eauto.
    edestruct thdp_pop_sym_weak as (?&?&?);eauto.
    eexists;split.
    eapply gettop_backwards_preserve with(thdp1:=thdp') in H_tp_core0;eauto.
    eapply gettop_backwards_preserve in H_tp_core0;eauto.
    econstructor;eauto.
    revert H2 H8 H_thread_halt H_tp_pop H_tp_upd H_tp_pop0;clear;intros.
    solv_thread;solv_thread.
    econstructor;solv_thread.

    exists ({thdp'0,t1,tgm,O});simpl.
    split;[|apply mem_eq_pc_refl].
    eapply gettop_preserve with(thdp2:=x0) in H_tp_core;eauto.
    econstructor;eauto.    
    revert H2 H_tp_pop H_tp_caller H8 H9;clear;intros.
    solv_thread;solv_thread;contradiction.
  Qed.
    
  Lemma extended_glob_reorder_case4:
    forall x t1 t2 l1 l2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE efprint ({-|pc,t1}) l1 fp1 pc1->
      @type_glob_step GE x ({-|pc1,t2}) l2 fp2 pc2->
      atom_bit pc1 = atom_bit pc2->
      t1 <> t2->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',type_glob_step x ({-|pc,t2}) l2 fp2 pc1'/\
             exists pc2',type_glob_step efprint ({-|pc1',t1}) l1 fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    destruct pc as [thdp tid tgm tbit];Coqlib.inv H;Coqlib.inv H0;simpl in *;try(inversion H1;fail);[edestruct thdp_update_sym as (?&?&?)|edestruct thdp_update_push_sym as (?&?&?)|edestruct thdp_update_pop_sym as (?&?&?);eauto;edestruct thdp_update_sym as (?&?&?)|edestruct thdp_update_pop_sym as (?&?&?)|edestruct thdp_update_sym as (?&?&?)| ];eauto;steptac;steptac.
    eapply gettop_preserve with(thdp2:=x) in H_tp_core;eauto.
    eapply gettop_preserve with(thdp2:=x0) in H_tp_core;eauto.
  Qed.
  
  Lemma multisw:
    forall pc pc1 pc2,
      @type_glob_step GE glob_sw pc sw FP.emp pc1->
      type_glob_step glob_sw pc1 sw FP.emp pc2->
      type_glob_step glob_sw pc sw FP.emp pc2.
  Proof.
    inversion 1;inversion 1;subst.
    constructor;auto.
  Qed.
  Lemma uselesssw:
    forall pc1 pc2,
      @glob_step GE pc1 sw FP.emp pc2->
      cur_tid pc1 = cur_tid pc2->
      pc1 = pc2.
  Proof. inversion 1;simpl;intro;subst;auto. Qed.

  Lemma extended_glob_reorder_case5:
    forall x t1 t2 l1 l2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE glob_halt ({-|pc,t1}) l1 fp1 pc1->
      @type_glob_step GE x ({-|pc1,t2}) l2 fp2 pc2->
      atom_bit pc1 = atom_bit pc2->
      t1 <> t2->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      l2 <> sw->
      exists pc1',type_glob_step x ({-|pc,t2}) l2 fp2 pc1'/\
             exists pc2',type_glob_step glob_halt ({-|pc1',t1}) l1 fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    destruct pc as [thdp tid tgm tbit];simpl in *;subst.
    Coqlib.inv H;Coqlib.inv H0;try(inversion H1;fail);try contradiction.
    edestruct thdp_pop_update_sym_weak as (?&?&?);eauto.
    steptac. steptac.
    edestruct thdp_pop_push_sym_weak as (?&?&?);eauto.
    steptac;steptac.
    edestruct thdp_pop_sym_weak as (?&?&?);eauto.
    edestruct thdp_pop_update_sym_weak as (?&?&?);eauto.
    steptac.
    eapply gettop_preserve with(thdp2:=x) in H_tp_core;eauto.
    eapply gettop_preserve with(thdp2:=x0) in H_tp_core;eauto.
    steptac.
    revert H2 H_tp_core H_tp_pop H_thread_halt H H7 H8;clear;intros.
    solv_thread. econstructor;solv_thread.

    edestruct thdp_pop_sym_weak as (?&?&?);eauto.
    steptac.
    steptac.

    edestruct thdp_pop_update_sym_weak as (?&?&?);eauto.
    steptac.
    steptac.
  Qed.



  Lemma globstep_reorder_rule:
     forall x y t1 t2 l1 l2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE y ({-|pc,t1}) l1 fp1 pc1->
      @type_glob_step GE x ({-|pc1,t2}) l2 fp2 pc2->
      atom_bit pc = atom_bit pc1 ->
      atom_bit pc1 = atom_bit pc2->
      t1 <> t2->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      l1 <> sw->
      l2 <> sw->
      exists pc1',type_glob_step x ({-|pc,t2}) l2 fp2 pc1'/\
             exists pc2',type_glob_step y ({-|pc1',t1}) l1 fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    destruct y;try (Coqlib.inv H;try contradiction;rewrite <- H13 in H1;Coqlib.inv H1;fail).
    eapply extended_glob_reorder_case1;eauto.
    eapply extended_glob_reorder_case2;eauto.
    eapply extended_glob_reorder_case3;eauto.
    eapply extended_glob_reorder_case4;eauto.
    eapply extended_glob_reorder_case5;eauto.
  Qed.

   Lemma corestar_reorder_rule:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE core ({-|pc,t1}) tau fp1 pc1 ->
      tau_star (@type_glob_step GE core) ({-|pc1,t2}) fp2 pc2 ->
      t1 <> t2 ->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',tau_star (type_glob_step core) ({-|pc,t2}) fp2 pc1' /\
             exists pc2', type_glob_step core ({-|pc1',t1}) tau fp1 pc2' /\
                     mem_eq_pc pc2 ({-|pc2',t2}).
  Proof.
    intros until fp2.
    intros H H0.
    apply tau_star_tau_N_equiv in H0 as [].
    revert t1 t2 pc pc1 pc2 fp1 fp2 H H0.
    induction x;intros;inversion H0;clear H0;subst.
    eexists;split;econstructor;split;eauto.
    split;[|split;[|split]];auto;apply GMem.eq'_refl.
    eapply corestep_reorder_rule in H6 as (?&?&?&?&?);eauto.
    eapply mem_eq_coreN in H7 as (?&?&?);eauto.
    eapply IHx in H7 as (?&?&?&?&?);eauto.
    eexists;split.
    econstructor 2;eauto.
    assert(({-|x0,t2}) = x0). destruct x0;inversion H0;subst;auto.
    rewrite <-H11;eauto.
    eexists;split;eauto.
    eapply mem_eq_pc_trans;eauto.
    eapply fpsmile_subset;eauto. rewrite FP.union_comm_eq. apply FP.union_subset.
    destruct x0,pc;inversion H0;clear H0;subst;simpl in *.
    eapply ThreadPool.upd_top_inv;eauto.
    eapply fpsmile_subset;eauto;apply FP.union_subset.
  Qed.


  Lemma glob_npnsw_step_type:
    forall pc l fp pc',
      @glob_npnsw_step GE pc l fp pc'->
      exists x,type_glob_step x pc l fp pc' /\ (x = core \/ x = call \/ x = ret).
  Proof. destruct 1 as [|[]];eauto. Qed.

  Lemma npnswstep_reorder:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @glob_npnsw_step GE ({-|pc,t1}) tau fp1 pc1->
      glob_npnsw_step ({-|pc1,t2}) tau fp2 pc2->
      t1 <> t2 ->
      FP.smile fp1 fp2->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',glob_npnsw_step ({-|pc,t2}) tau fp2 pc1' /\
             exists pc2',glob_npnsw_step ({-|pc1',t1}) tau fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    apply glob_npnsw_step_type in H as (x&step1&type1).
    apply glob_npnsw_step_type in H0 as (y&step2&type2).
    assert(atom_bit pc = atom_bit pc1).
    inversion type1 as [|[]];inversion step1;subst;auto;try inversion H0.
    assert(atom_bit pc1 = atom_bit pc2).
    inversion type2 as [|[]];inversion step2;subst;auto;try inversion H5.
    assert(tau<>sw). intro. inversion H5.
    eapply globstep_reorder_rule in H2;eauto.
    destruct H2 as (?&?&?&?&?).
    unfold glob_npnsw_step.
    exists x0;split;eauto.
    inversion type2 as [|[]];subst;eauto.
    exists x1;split;eauto.
    inversion type1 as [|[]];subst;auto.
  Qed.

  Lemma npnswstep_star_reorder:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @glob_npnsw_step GE ({-|pc,t1}) tau fp1 pc1->
      tau_star glob_npnsw_step ({-|pc1,t2}) fp2 pc2->
      t1 <> t2 ->
      FP.smile fp1 fp2->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',tau_star glob_npnsw_step ({-|pc,t2}) fp2 pc1'/\
             exists pc2',glob_npnsw_step ({-|pc1',t1}) tau fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    apply tau_star_tau_N_equiv in H0 as [].
    revert t1 t2 pc pc1 pc2 fp1 fp2 H H0 H1 H2 H3 H4.
    induction x;intros;Coqlib.inv H0.
    exists ({-|pc,t2}). split;[constructor|exists pc1;split;auto;apply mem_eq_pc_refl].

    assert(FP.smile fp1 fp).
    eapply fpsmile_subset;eauto. apply FP.union_subset.
    assert(FP.smile fp1 fp').
    rewrite FP.union_comm_eq in H2.
    eapply fpsmile_subset in H2;eauto. apply FP.union_subset.

    eapply npnswstep_reorder in H0;eauto.
    destruct H0 as (pc1'&step1&pc2'&step2&memeq').
    
    eapply mem_eq_npnsw_step_starN in memeq';eauto.
    destruct memeq' as (pce'&tauN'&memeq').
    assert(cur_tid s' = t2).
    destruct H6 as [H6|[H6|H6]];Coqlib.inv H6;auto.
    rewrite H0 in tauN'.
    eapply IHx in H5;eauto.
    destruct H5 as (?&?&?&?&?).
    exists x0. split;eauto.
    econstructor;eauto.
    assert(pc1' = ({-|pc1',t2})).
    destruct step1 as [s1|[s1|s1]];Coqlib.inv s1;auto.
    rewrite <- H10 in H5. auto.

    exists x1. split;auto.
    assert(cur_tid pc2 = cur_tid pce').
    destruct memeq' as (?&?&?&?);auto.
    rewrite H10.
    eapply mem_eq_pc_trans;eauto.

    eapply npnsw_step_thdpinv;eauto.
  Qed.


  Lemma npnswstep_corestar_reorder:
    forall t1 t2 pc pc1 pc2 fp1 fp2,
      @glob_npnsw_step GE ({-|pc,t1}) tau fp1 pc1->
      tau_star (type_glob_step core) ({-|pc1,t2}) fp2 pc2->
      t1 <> t2 ->
      FP.smile fp1 fp2->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',tau_star (type_glob_step core) ({-|pc,t2}) fp2 pc1'/\
             exists pc2',glob_npnsw_step ({-|pc1',t1}) tau fp1 pc2' /\
                    mem_eq_pc pc2 ({-|pc2',cur_tid pc2}).
  Proof.
    intros.
    apply tau_star_tau_N_equiv in H0 as [].
    revert t1 t2 pc pc1 pc2 fp1 fp2 H H0 H1 H2 H3 H4.
    induction x;intros;Coqlib.inv H0.
    exists ({-|pc,t2}). split;[constructor|exists pc1;split;auto;apply mem_eq_pc_refl].

    assert(FP.smile fp1 fp).
    eapply fpsmile_subset;eauto. apply FP.union_subset.
    assert(FP.smile fp1 fp').
    rewrite FP.union_comm_eq in H2.
    eapply fpsmile_subset in H2;eauto. apply FP.union_subset.

    apply glob_npnsw_step_type in H as L1.
    destruct L1 as [?[]].
    eapply globstep_reorder_rule in H0 as L1;eauto.
    destruct L1 as (pc1'&step1&pc2'&step2&memeq1).
    eapply mem_eq_coreN in memeq1 as L1;eauto.
    destruct L1 as (?&?&?).
    assert(cur_tid s' = t2). Coqlib.inv H6;auto.
    rewrite H12 in *;clear H12.
    assert(glob_npnsw_step ({-|pc1',t1}) tau fp1 pc2'). destruct H9 as [|[]];subst;unfold glob_npnsw_step;auto.
    eapply IHx in H12;eauto.
    destruct H12 as (pc10&star1&pc20&step'&?).
    exists pc10. split. econstructor;eauto. assert(cur_tid pc1' = t2). inversion step1;auto. assert(pc1' = ({-|pc1',t2})). destruct pc1';subst;auto. rewrite H14;auto.
    exists pc20. split;auto. eapply mem_eq_pc_trans;eauto.
    assert(cur_tid x1 = cur_tid pc2). destruct H11 as (?&?&?&?);auto.
    rewrite <- H13;auto.

    Coqlib.inv step1.
    eapply ThreadPool.upd_top_inv;eauto.
    destruct H9 as [|[]];subst;inversion H8;auto.
    Coqlib.inv H6;auto.
    intro L;inversion L.
    intro L;inversion L.
  Qed.


  Lemma outofatom_glob_reorder_rule:
    forall pc pc1 pc2 pc3 fp1 fp2 x y l1 l2,
      atom_bit pc = O ->
      atom_bit pc1 = O->
      atom_bit pc2 = O ->
      atom_bit pc3 = O->
      cur_tid pc1 <> cur_tid pc2->
      l1 <> sw ->
      l2 <> sw ->
      @type_glob_step GE x pc l1 fp1 pc1->
      type_glob_step glob_sw pc1 sw FP.emp pc2->
      type_glob_step y pc2 l2 fp2 pc3->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      type_glob_step glob_sw pc sw FP.emp ({-|pc,cur_tid pc2})/\
      exists pc',type_glob_step y ({-|pc,cur_tid pc2}) l2 fp2 pc' /\
            type_glob_step glob_sw pc' sw FP.emp ({-|pc',cur_tid pc})/\
            exists pc'',type_glob_step x ({-|pc',cur_tid pc}) l1 fp1 pc'' /\
                   mem_eq_pc pc3 ({-|pc'',cur_tid pc3}).
  Proof.
    intros.
    assert(pc = {-|pc,cur_tid pc}). destruct pc;auto.
    rewrite H12 in H6.
    assert(pc2 = ({-|pc1,cur_tid pc2})).
    inversion H7;subst;auto.
    rewrite H13 in H7.
    rewrite H13 in H8.
    assert(cur_tid pc=cur_tid pc1). Coqlib.inv H6;auto;contradiction.
    rewrite <-H14 in H3;clear H14.
    destruct x;try (Coqlib.inv H6;inversion H0;try contradiction;fail).
    {
      eapply extended_glob_reorder_case1 with(pc1:=pc1)in H6 as (?&?&?&?&?);eauto.
      split.
      eapply type_glob_step_elim in H6.
      eapply step_switchable with(t:=cur_tid pc) in H6.
      simpl in H6. rewrite <- H12 in H6.
      inversion H6;subst.
      econstructor;eauto.
      auto.
      auto.
      auto.

      exists x. split;auto.
      split.
      eapply type_glob_step_elim in H14 as L1.
      eapply step_switchable with(t:=cur_tid x) in L1;eauto.
      simpl in L1.
      assert(x = ({-|x,cur_tid x})). destruct x;auto.
      rewrite H16.
      inversion L1;subst.
      econstructor;eauto.

      assert(atom_bit x = atom_bit pc).
      inversion H8;subst;try inversion H0;try inversion H2;inversion H6;subst;simpl in *;auto.
      rewrite <-H22 in H.
      inversion H.
      rewrite H in H16.
      rewrite <- H16.
      destruct x;simpl;auto.
      eapply type_glob_step_elim in H6.
      eapply GE_mod_wd_tp_inv in H6;eauto.

      exists x0;split;auto.
      congruence.
    }
    {
      eapply extended_glob_reorder_case2 with(pc1:=pc1) in H6 as L1;eauto.
      destruct L1 as (?&?&?&?&?).
      split.
      eapply type_glob_step_elim in H14.
      eapply step_switchable in H14.
      inversion H14;subst.
      destruct pc;simpl in *;subst.
      econstructor;eauto.
      auto.
      destruct pc;simpl in *;auto.
      destruct pc;simpl in *;auto.

      eexists;split;eauto.
      split.
      destruct x;simpl in *;subst.
      eapply type_glob_step_elim in H15.
      eapply step_switchable in H15;eauto.
      Coqlib.inv H15.
      econstructor;eauto.
      simpl;inversion H8;subst;inversion H0;inversion H2;inversion H14;subst;auto.
      congruence.
      simpl.
      apply type_glob_step_elim in H14.
      apply GE_mod_wd_tp_inv in H14;auto.
      eexists x0;split;auto.
      congruence.
      Unshelve.
      remember (cur_tid pc) as t1;auto.
      auto.
    }
    {
      eapply extended_glob_reorder_case3 with(pc1:=pc1) in H6 as L1;eauto;try congruence.
      destruct L1 as (?&?&?&?&?).
      split.
      eapply type_glob_step_elim in H14.
      destruct pc;subst;simpl in *.
      eapply step_switchable in H14;auto.
      Coqlib.inv H14.
      econstructor;eauto.
      exists x;split;auto.
      split.
      eapply type_glob_step_elim in H15.
      eapply step_switchable in H15;auto.
      destruct x;subst;simpl in *.
      Coqlib.inv H15;econstructor;eauto.
      simpl. inversion H8;inversion H0;inversion H2;subst;inversion H14;subst;auto.
      simpl. try congruence.
      inversion H27.
      simpl.
      assert(ThreadPool.inv (thread_pool ({-|pc,cur_tid pc2}))).
      destruct pc;auto.
      eapply GE_mod_wd_tp_inv in H17;eauto.
      eapply type_glob_step_elim in H14;eauto.
      eexists;split;eauto.
      Unshelve.
      auto.
      remember (cur_tid pc)as t1;auto.
    }
    {
      inversion H6;subst.
      rewrite H in H18;inversion H18.
    }
    {
      eapply extended_glob_reorder_case4 with(pc1:=pc1) in H6 as L1;eauto;try congruence.
      destruct L1 as (?&?&?&?&?).
      split.
      eapply type_glob_step_elim in H14.
      destruct pc;simpl in *.
      eapply step_switchable in H14;eauto.
      inversion H14;clear H14;subst.
      econstructor;eauto.

      eexists;split;eauto.
      split.
      eapply type_glob_step_elim in H15;eauto.
      destruct x;simpl in *;subst.
      eapply step_switchable in H15;eauto.
      inversion H15;clear H15;subst;eauto. econstructor;eauto.
      simpl. inversion H8;inversion H0;inversion H2;subst;inversion H14;subst;auto;try congruence.
      inversion H27.
      simpl.
      assert(ThreadPool.inv (GlobDefs.thread_pool ({-|pc,GlobDefs.cur_tid pc2}))).
      destruct pc;auto.
      apply type_glob_step_elim in H14.
      eapply GE_mod_wd_tp_inv in H17;eauto.
      auto.

      eexists;split;eauto.
      Unshelve. auto. auto.
    }
    {
      eapply extended_glob_reorder_case5 with(pc1:=pc1) in H6 as L1;eauto;try congruence. destruct L1 as (?&?&?&?&?).
      split.
      eapply type_glob_step_elim in H14.
      destruct pc;simpl in *.
      eapply step_switchable in H14;eauto.
      inversion H14;clear H14;subst.
      econstructor;eauto.

      eexists;split;eauto.
      split.
      eapply type_glob_step_elim in H15;eauto.
      destruct x;simpl in *;subst.
      eapply step_switchable in H15;eauto.
      inversion H15;clear H15;subst;eauto. econstructor;eauto.
      simpl. inversion H8;inversion H0;inversion H2;subst;inversion H14;subst;auto;try congruence.
      inversion H27.
      simpl.
      assert(ThreadPool.inv (GlobDefs.thread_pool ({-|pc,GlobDefs.cur_tid pc2}))).
      destruct pc;auto.
      apply type_glob_step_elim in H14.
      eapply GE_mod_wd_tp_inv in H17;eauto.
      auto.

      eexists;split;eauto.
      Unshelve. auto. auto.
    }
  Qed.
 


  Inductive stepN:(@ProgConfig GE->glabel->FP.t->@ProgConfig GE->Prop)->nat->@ProgConfig GE->list glabel->FP.t->@ProgConfig GE->Prop:=
  | stepN_emp:forall step pc,stepN step 0 pc nil FP.emp pc
  | stepN_cons:forall step i pc l fp l' fp' pc' pc'',
      stepN step i pc' l' fp' pc''->
      step pc l fp pc'->
      stepN step (S i) pc (cons l l')(FP.union fp fp') pc''.

  Lemma stepN_star:
    forall step i pc l fp pc',
      stepN step i pc l fp pc'->star step pc l fp pc'.
  Proof.  induction i;inversion 1;subst;econstructor;eauto. Qed.
  Lemma star_stepN:
    forall step pc l fp pc',
      star step pc l fp pc'->exists i,stepN step i pc l fp pc'.
  Proof. induction 1;intros;try destruct IHstar;eexists;econstructor;eauto. Qed.
  Lemma mem_eq_corestepN:
    forall i pc l fp pc' pc1,
      mem_eq_pc pc pc1->
      stepN (type_glob_step core) i pc l fp pc'->
      exists pc1',stepN (type_glob_step core) i pc1 l fp pc1' /\ mem_eq_pc pc' pc1'.
  Proof.
    induction i;inversion 2;subst.
    eexists;split;eauto;constructor.
    assert(l0=tau).
    inversion H4;auto.
    subst.

    eapply mem_eq_corestep in H as (?&?&?);eauto.
    eapply IHi in H1 as (?&?&?);eauto.
    eexists;split;eauto. econstructor;eauto.
  Qed.
    

  Lemma entat_afterstep:
    forall pc pc' x l fp,
      atom_bit pc = I ->
      @type_glob_step GE x pc l fp pc' ->
      x = core \/ x = extat.
  Proof.
    intros.
    destruct x;auto;inversion H0;subst;inversion H.
  Qed.


  Lemma mem_eq_pc_change:
    forall t pc pc',
      mem_eq_pc pc pc'->
      mem_eq_pc ({-|pc,t})({-|pc',t}).
  Proof.
    intros.
    destruct H as (?&?&?&?).
    unfold mem_eq_pc;simpl;auto.
  Qed.

 

  Definition atom_block (pc:@ProgConfig GE)(l:list glabel)(fp:FP.t)(pc':@ProgConfig GE):Prop:=
    exists pc1 l' pc2,
      type_glob_step entat pc tau FP.emp pc1 /\
      star (type_glob_step core) pc1 l' fp pc2 /\
      type_glob_step extat pc2 tau FP.emp pc' /\
      l = app (cons tau  l') (cons tau nil).
  Definition half_atom_block (pc:@ProgConfig GE)(l:list glabel)(fp:FP.t)(pc':@ProgConfig GE):Prop:=
    exists pc1 l1,
      type_glob_step entat pc tau FP.emp pc1 /\
      star (type_glob_step core) pc1 l1 fp pc' /\
      l = cons tau l1.
   
  Lemma adjust_list_order:
    forall l1 l2,
      app(app (cons tau l1)(cons tau nil)) l2 = (cons tau(app l1(cons tau l2))).
  Proof. intros;rewrite <-List.app_assoc;auto. Qed.


  Lemma changepc_curtid: forall pc:@ProgConfig GE,({-|pc,cur_tid pc}) = pc.
  Proof. destruct pc;auto. Qed.
  Lemma appnil:forall A l,@app A l nil = l.
  Proof. induction l;auto. rewrite <- IHl.  simpl;rewrite<- List.app_assoc;auto. Qed.



  Lemma atomblock_open_reorderstep1:
    forall x l t1 t2 pc pc1 pc2 fp,
      @type_glob_step GE x ({-|pc,t1}) l fp pc1->
      atom_bit pc = atom_bit pc1 ->
      l <> sw ->
      t1 <> t2 ->
      type_glob_step entat ({-|pc1,t2}) tau FP.emp pc2 ->
      exists pc1',type_glob_step entat ({-|pc,t2}) tau FP.emp pc1' /\
             exists pc2',type_glob_step x (changepc pc1' t1 O) l fp pc2' /\
                    thread_pool pc2' = thread_pool pc2 /\
                    gm pc2' = gm pc2.
  Proof.
    intros.
    Coqlib.inv H;try contradiction;try (inversion H0;fail);Coqlib.inv H3.
    edestruct thdp_update_sym as (?&?&?);eauto;steptac;steptac;auto.
    edestruct thdp_push_update_sym as (?&?&?);eauto;steptac;steptac;auto.
    edestruct thdp_pop_update_sym as (?&?&?&?&?);eauto;steptac;steptac;auto.
    eapply gettop_backwards_preserve with(thdp1:=thdp') in H_tp_core0;eauto.
    eapply gettop_backwards_preserve;eauto.
    revert H_tp_pop H_tp_caller H H3;clear;intros;try (solv_thread;solv_thread).
    edestruct thdp_pop_update_sym_weak as (?&?&?);eauto;steptac;steptac;auto.
    rewrite <- H9 in H0;inversion H0.
    edestruct thdp_update_sym as (?&?&?);eauto;steptac;steptac;auto.
  Qed.
  
  Lemma atomblock_open_reorderstep2:
    forall x l t1 t2 pc pc1 pc2 fp,
      @type_glob_step GE x (changepc pc t1 O) l fp pc1->
      atom_bit pc1 = O ->
      l <> sw ->
      t1 <> t2 ->
      type_glob_step extat (changepc pc1 t2 I) tau FP.emp pc2 ->
      exists pc1',type_glob_step extat (changepc pc t2 I) tau FP.emp pc1' /\
             exists pc2',type_glob_step x (changepc pc1' t1 O) l fp pc2' /\
                    thread_pool pc2' = thread_pool pc2 /\
                    gm pc2' = gm pc2.
  Proof.
    intros.
    Coqlib.inv H;try contradiction;Coqlib.inv H3.
    edestruct thdp_update_sym as (?&?&?);eauto;steptac;steptac;auto.
    edestruct thdp_push_update_sym as (?&?&?);eauto;steptac;steptac;auto.
    edestruct thdp_pop_update_sym as (?&?&?&?&?);eauto;steptac;steptac;auto.
    eapply gettop_backwards_preserve with(thdp1:=thdp') in H_tp_core0;eauto.
    eapply gettop_backwards_preserve;eauto.
    revert H_tp_pop H_tp_caller H H3;clear;intros;try (solv_thread;solv_thread).
    edestruct thdp_pop_update_sym_weak as (?&?&?);eauto;steptac;steptac;auto.
    inversion H0.
    edestruct thdp_update_sym as (?&?&?);eauto;steptac;steptac;auto.
  Qed.
  
  Lemma atomblock_open_reorder_corestep:
    forall x l t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE x (changepc pc t1 O) l fp1 pc1 ->
      atom_bit pc1 = O ->
      l <> sw ->
      t1 <> t2 ->
      type_glob_step core (changepc pc1 t2 I) tau fp2 pc2 ->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',type_glob_step core (changepc pc t2 I) tau fp2 pc1'/\
             exists pc2',type_glob_step x (changepc pc1' t1 O) l fp1 pc2' /\
                    thread_pool pc2' = thread_pool pc2 /\
                    GMem.eq' pc2'.(gm) pc2.(gm).
  Proof.    
    intros.
    assert(type_glob_step core ({-|pc1,t2}) tau fp2 (changepc pc2 t2 O)).
    destruct pc1,pc2;Coqlib.inv H3;unfold changepc;simpl in *;subst.
    econstructor;eauto.
    pose proof H0 as L1.
    symmetry in H0.
    specialize (globstep_reorder_rule core x t1 t2 l tau (changepc pc t1 O) pc1 (changepc pc2 t2 O) fp1 fp2 H H7 H0 L1 H2 H4 H5 H6 H1) as L2.
    destruct L2 as (?&?&?&?&?). intro. inversion H8.
    exists (changepc x0 t2 I);split.
    unfold changepc in *;simpl in *.
    inversion H8;subst;simpl in *. econstructor;eauto.
    exists (changepc x1 t1 O);split.
    unfold changepc in *;simpl in *.
    inversion H9;subst;try contradiction;try (econstructor;eauto;fail).
    inversion H;subst;inversion H0.
    inversion H;subst;inversion H0.
    unfold changepc in *;destruct H10 as (?&?&?&?);simpl in *.
    split;auto.
    apply GMem.eq'_sym;auto.
  Qed.

  




    
  Lemma atomblock_open_reorder_core_tauN:
    forall i x l t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE x (changepc pc t1 O) l fp1 pc1 ->
      atom_bit pc1 = O ->
      l <> sw ->
      t1 <> t2 ->
      tau_N (type_glob_step core) i (changepc pc1 t2 I) fp2 pc2 ->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',tau_N (type_glob_step core) i (changepc pc t2 I) fp2 pc1'/\
             exists pc2',type_glob_step x (changepc pc1' t1 O) l fp1 pc2' /\
                    thread_pool pc2' = thread_pool pc2 /\
                    GMem.eq' pc2'.(gm) pc2.(gm).
  Proof.
    induction i;intros; Coqlib.inv H3.
    eexists;split;[constructor|].
    unfold changepc in *;simpl.
    eexists;split;eauto.
    split;[auto|apply GMem.eq'_refl].
    assert(s' = changepc s' t2 I).
    inversion H8;subst;unfold changepc;simpl;auto.
    rewrite H3 in H9.
    eapply atomblock_open_reorder_corestep in H8 as L1;eauto.
    destruct L1 as (?&?&?&?&?&?).
    assert(mem_eq_pc (changepc x1 t2 I) s').
    unfold changepc. unfold mem_eq_pc;simpl.
    split;auto.
    split. inversion H8;auto.
    split;[inversion H8|];auto.
    apply mem_eq_pc_sym in H13.
    rewrite H3 in H13.
    eapply mem_eq_coreN in H13 as L2;eauto.
    destruct L2 as (?&?&?).
    eapply IHi in H14 as L3;eauto.
    destruct L3 as (?&?&?&?&?&?).
    assert(x0 = changepc x0 t2 I).
    inversion H7;auto.
    rewrite H20 in H7.
    exists x3;split.
    econstructor 2;eauto.
    eexists;split;eauto.
    destruct H15 as (?&?&?&?).
    split;try congruence.
    eapply GMem.eq'_trans;eauto.
    apply GMem.eq'_sym;auto.

    inversion H;subst;try contradiction;inversion H0;inversion H10;subst;auto.
    eapply fpsmile_subset;eauto. rewrite FP.union_comm_eq. apply FP.union_subset.
    eapply GE_mod_wd_tp_inv with(pc:=(changepc pc t2 I));auto.
    eapply type_glob_step_elim;eauto.
    eapply fpsmile_subset;eauto. apply FP.union_subset.
  Qed.
  Lemma atomblock_open_reorder_corestar:
    forall x l t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE x (changepc pc t1 O) l fp1 pc1 ->
      atom_bit pc1 = O ->
      l <> sw ->
      t1 <> t2 ->
      tau_star  (type_glob_step core) (changepc pc1 t2 I) fp2 pc2 ->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc1',tau_star (type_glob_step core) (changepc pc t2 I) fp2 pc1'/\
             exists pc2',type_glob_step x (changepc pc1' t1 O) l fp1 pc2' /\
                    thread_pool pc2' = thread_pool pc2 /\
                    GMem.eq' pc2'.(gm) pc2.(gm).
  Proof.
    intros.
    apply tau_star_tau_N_equiv in H3 as [i].
    eapply atomblock_open_reorder_core_tauN in H3;eauto.
    destruct H3 as (?&?&?&?&?&?).
    apply tauN_taustar in H3.
    repeat (eexists;eauto).
  Qed.
  
  Lemma taustar_fpconflict_split:
    forall A step pc pc' fp1,
      @tau_star A step pc fp1 pc'->
      forall fp2,
        FP.conflict fp1 fp2 ->
        exists fp10 fp11 pc10 pc11,
          tau_star step pc fp10 pc10 /\
          step pc10 tau fp11 pc11 /\
          FP.smile fp2 fp10 /\ FP.conflict fp2 fp11 /\
          FP.subset fp10 fp1 /\ FP.subset fp11 fp1.
  Proof.
    induction 1;intros.
    apply FP.emp_never_conflict in H as [];contradiction.
    assert(FP.smile fp fp2 \/ ~FP.smile fp fp2). apply classic.
    destruct H2.
    assert(FP.conflict fp' fp2).
    apply NNPP;intro.
    apply FP.smile_conflict_compat in H3.
    eapply fpsmile_union in H2;eauto.
    rewrite FP.union_comm_eq in H2.
    apply FP.smile_conflict_compat in H2.
    contradiction.

    eapply IHtau_star in H3 as (fp10&fp11&pc10&pc11&star1&step1&smile1&conflict1&subset1&subset2).
    exists (FP.union fp fp10),fp11,pc10,pc11.
    split. econstructor;eauto.
    split;auto.
    split. apply fpsmile_sym. apply fpsmile_union;auto. apply fpsmile_sym;auto.
    split;auto.
    split. rewrite FP.union_comm_eq. rewrite FP.union_comm_eq with(fp2:=fp'). apply FP.union2_subset;auto.
    eapply fpsubset_trans;eauto. rewrite FP.union_comm_eq. apply FP.union_subset.

    exists FP.emp,fp,s,s'.
    split. constructor.
    split;auto.
    split. apply NNPP;intro. apply smile_conflict in H3. apply FP.emp_never_conflict in H3 as [];contradiction.
    split. apply FP.conflict_sym. apply smile_conflict;auto.
    split.
    assert(forall fp,FP.subset FP.emp fp).
    clear;intros.
    destruct fp.
    econstructor;Locs.unfolds;intros;simpl;inversion H.
    apply H3.

    apply FP.union_subset.
  Qed.
    
    
    


  Lemma changeatombit_corestep_preserve:
    forall pc fp pc',
      (@type_glob_step GE core) pc tau fp pc'->
      type_glob_step core (changepc pc (cur_tid pc) O) tau fp (changepc pc'(cur_tid pc) O).
  Proof.
    inversion 1;subst.
    econstructor;eauto.
  Qed.
  Lemma changeatombit_corestar_preserve:
    forall pc fp pc',
      tau_star (@type_glob_step GE core) pc fp pc'->
      tau_star (type_glob_step core) (changepc pc (cur_tid pc) O) fp (changepc pc'(cur_tid pc) O).
  Proof.
    intros.
    induction H.
    constructor.
    assert(type_glob_step core (changepc s (cur_tid s) O) tau fp (changepc s' (cur_tid s) O)).
    destruct s;Coqlib.inv H;econstructor;eauto.
    assert(cur_tid s' = cur_tid s).
    Coqlib.inv H;auto.
    rewrite H2 in *.
    econstructor;eauto.
  Qed.
  Lemma changeatombitI_corestar_preserve:
    forall pc fp pc',
      tau_star (@type_glob_step GE core) pc fp pc'->
      tau_star (type_glob_step core) (changepc pc (cur_tid pc) I) fp (changepc pc'(cur_tid pc) I).
  Proof.
    intros.
    induction H.
    constructor.
    assert(type_glob_step core (changepc s (cur_tid s) I) tau fp (changepc s' (cur_tid s) I)).
    destruct s;Coqlib.inv H;econstructor;eauto.
    assert(cur_tid s' = cur_tid s).
    Coqlib.inv H;auto.
    rewrite H2 in *.
    econstructor;eauto.
  Qed.






  Lemma changepc_again:
    forall pc t i t' i',
      changepc (changepc pc t' i') t i = changepc pc t i .
  Proof. destruct pc;auto. Qed.
  Lemma mem_eq_pc_changepc:
    forall pc pc' t x,
      mem_eq_pc pc pc'->
      mem_eq_pc (changepc pc t x)(changepc pc' t x).
  Proof.
    unfold mem_eq_pc;destruct 1 as (?&?&?&?).
    unfold changepc;simpl;auto.
  Qed.
    

  Lemma corestar_taustar:
    forall pc l fp pc',
      star (@type_glob_step GE core) pc l fp pc'->
      tau_star (type_glob_step core) pc fp pc'.
  Proof.
    induction 1. constructor.
    econstructor;eauto. inversion H;subst;auto.
  Qed.
  Lemma corestep_changebit:
    forall pc l fp pc' x,
      @type_glob_step GE core pc l fp pc'->
      type_glob_step core (changepc pc (cur_tid pc) x) l fp (changepc pc'(cur_tid pc) x).
  Proof. inversion 1;subst;econstructor;eauto. Qed.
  Lemma corestar_changebit:
    forall pc l fp pc' x,
      star (@type_glob_step GE core) pc l fp pc'->
      star (@type_glob_step GE core) (changepc pc (cur_tid pc) x) l fp (changepc pc' (cur_tid pc) x).
  Proof.
    induction 1;intros.
    constructor.
    assert(cur_tid s1 =cur_tid s2). inversion H;auto.
    eapply corestep_changebit with(x:=x) in H;eauto.
    rewrite H1 in *.
    econstructor;eauto.
  Qed.
  Lemma corestepN_changebit:
    forall i pc l fp pc' x,
      stepN (@type_glob_step GE core) i pc l fp pc'->
      stepN (@type_glob_step GE core) i (changepc pc (cur_tid pc) x) l fp (changepc pc' (cur_tid pc) x).
  Proof.
    induction i;inversion 1;subst.
    constructor.
    assert(cur_tid pc = cur_tid pc'0). inversion H3;auto.
    eapply corestep_changebit in H3.
    eapply IHi in H1.
    rewrite <- H0 in H1.
    econstructor;eauto.
  Qed.


  Lemma half_atom_block_glob_predict_star_alter:
    forall t pc l fp pc',
      half_atom_block ({-|pc,t}) l fp pc'->
      glob_predict_star_alter pc t I fp .
  Proof.
    unfold half_atom_block;intros.
    destruct H as (?&?&?&?&?).
    rewrite <- FP.emp_union_fp with (fp:=fp).
    econstructor;eauto.
    constructor.
    inversion H;auto.
    eapply corestar_taustar;eauto.
  Qed.


  Definition atomblockN (i:nat)(pc:@ProgConfig GE)(fp:FP.t)(pc':ProgConfig):Prop:=
    exists pc1,type_glob_step entat pc tau FP.emp pc1 /\
          exists pc2,tau_N (type_glob_step core) i pc1 fp pc2 /\
                type_glob_step extat pc2 tau FP.emp pc'.
  Lemma step_equiv_tau_star_equiv:
    forall (step1:@ProgConfig GE->glabel->FP.t-> @ProgConfig GE->Prop) step2,
      (forall fp pc pc',step1 pc tau fp pc' <-> step2 pc tau fp pc')->
      forall fp pc pc',tau_star step1 pc fp pc' <-> tau_star step2 pc fp pc'.
  Proof.
    split;intro;induction H0; [constructor|econstructor 2;eauto;eapply H;eauto|constructor|econstructor 2;eauto;eapply H;eauto].
  Qed.
  Lemma corestar_tid_bit_preserve:
    forall pc pc' fp,
      tau_star (@type_glob_step GE core) pc fp pc'->
      cur_tid pc = cur_tid pc' /\
      atom_bit pc = atom_bit pc'.
  Proof.
    induction 1;auto.
    destruct IHtau_star.
    rewrite <- H1. rewrite <- H2.
    inversion H;subst;auto.
  Qed.
  Lemma step_memeqpc_preserve:
    forall pc pc' l fp x pc1 pc1',
      @type_glob_step GE x pc l fp pc'->
      @type_glob_step GE x pc1 l fp pc1' ->
      x <> core ->
      x <> glob_sw ->
      mem_eq_pc pc pc1 ->
      mem_eq_pc pc' pc1'.
    Proof.
      intros.
      destruct pc as [thdp tid tgm tbit], pc1 as [thdp' tid' tgm' tbit'],H3 as (?&?&?&?);simpl in *;subst.
      unfold mem_eq_pc.
      destruct x;Coqlib.inv H;Coqlib.inv H0;try contradiction;split;simpl;auto;
        repeat
         ( match goal with
           | [H1: ?P = _, H2: ?P = _ |- _] =>
             rewrite H1 in H2;inversion H2;clear H1 H2;subst
           | [H1: ?P = _ , H2: _ = ?P |- _] =>
             rewrite H1 in H2;inversion H2;clear H1 H2;subst
           | [H1: _ = ?P, H2: _ = ?P |- _] =>
             rewrite <- H1 in H2;inversion H2;clear H1 H2;subst
           | [H1: ?a ?b ?c ?d _,H2:?a ?b ?c ?d _|-_]=>
             Coqlib.inv H1;Coqlib.inv H2
           end
         );try trivial.
    Qed.
    
  Lemma atomblock_reorder:
    forall x i l t1 t2 pc pc1 pc2 fp1 fp2,
      @type_glob_step GE x ({-|pc,t1}) l fp1 pc1 ->
      atom_bit pc = atom_bit pc1 ->
      l <> sw ->
      t1 <> t2 ->
      atomblockN i ({-|pc1,t2}) fp2 pc2 ->
      FP.smile fp1 fp2 ->
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      exists pc',atomblockN i ({-|pc,t2}) fp2 pc' /\ exists pc'',type_glob_step x ({-|pc',t1}) l fp1 pc'' /\ mem_eq_pc pc2 ({-|pc'',cur_tid pc2}).
  Proof.
    unfold atomblockN;intros.
    destruct H3 as (?&?&?&?&?).
    eapply atomblock_open_reorderstep1 in H as L1;eauto.
    destruct L1 as (?&?&?&?&?&?).
    assert(mem_eq_pc x0 (changepc x3 t2 I)).
    unfold changepc;unfold mem_eq_pc;simpl.
    split;auto.
    split;auto. inversion H3;auto.
    split;auto. inversion H3;auto.
    rewrite H12;apply GMem.eq'_refl.
    eapply mem_eq_coreN in H13 as (?&?&?);eauto.
    eapply atomblock_open_reorder_core_tauN in H10 as L2;eauto.
    destruct L2 as (?&?&?&?&?&?).

    assert(exists pc',type_glob_step extat (changepc x6 t2 I) tau FP.emp pc').
    inversion H8;subst.
    unfold changepc;destruct x4,x6;simpl in * ;subst.
    destruct H14 as (?&?&?&?);simpl in *;subst.
    apply tauN_taustar in H13.
    eapply corestar_tid_bit_preserve in H13 as [? _];simpl in *;subst.
    steptac.
    destruct H19.

    eapply atomblock_open_reorderstep2 in H19 as L1;eauto.
    destruct L1 as (?&?&?&?&?&?).

    repeat clear_ands.
    eauto.
    assert(x2 = changepc x2 t2 I).
    inversion H9;auto.
    rewrite H24;eauto.
    assert(x5 = changepc x5 t2 I).
    apply tauN_taustar in H15 as T.
    apply corestar_tid_bit_preserve in T as [];simpl in *.
    destruct x5;unfold changepc;simpl in *;subst;auto.
    rewrite H24;eauto.
    assert( ({-|x8,t1}) = changepc x8 t1 O).
    destruct x8;unfold changepc;simpl in *;subst;f_equal.
    inversion H20;auto.
    rewrite H24;eauto.

    assert(mem_eq_pc x0 (changepc x3 t2 I)).
    repeat try (split;[inversion H3;subst;auto|];simpl).
    rewrite H12;apply GMem.eq'_refl.

    assert(mem_eq_pc x4 (changepc x6 t2 I)).
    apply tauN_taustar in H13 as T2.
    apply corestar_tid_bit_preserve in T2 as [];simpl in *.
    unfold mem_eq_pc;repeat clear_ands;simpl;auto.
    apply GMem.eq'_sym;auto.

    eapply mem_eq_pc_trans in H25 as L;eauto.
    eapply step_memeqpc_preserve in L;try apply H19;eauto.
    eapply mem_eq_pc_trans;eauto.
    split;auto.
    split;auto. inversion H19;subst;simpl. inversion H;subst;inversion H0;inversion H21;subst;simpl;auto. rewrite H27 in H31;inversion H31.
    split;simpl. destruct L as (?&?&?&?);auto.
    rewrite H23. apply GMem.eq'_refl.
    intro contra;inversion contra.
    intro contra;inversion contra.
    inversion H;subst;inversion H0;inversion H16;subst;simpl;auto. rewrite H21 in H25;inversion H25.
    inversion H;subst;inversion H0;inversion H10;subst;simpl;auto. rewrite H16 in H20;inversion H20.

    inversion H9;subst;simpl.
    eapply ThreadPool.upd_top_inv;eauto.
  Qed.

  Lemma List_i_split:
    forall (A:Type)(i:nat)(l:list A)(p:A),
      List.nth_error l i = Some p->
      exists l1 l2,
        l=app l1 (cons p l2) /\ length l1 = i .
  Proof.
    induction i;intros.
    Coqlib.inv H.
    destruct l;Coqlib.inv H1.
    exists nil,l;auto.
    Coqlib.inv H.
    destruct l;Coqlib.inv H1.
    apply IHi in H0 as [?[?]].
    exists (cons a x),x0.
    destruct H.
    rewrite H.
    split;auto.
    destruct x.
    inversion H0;subst;auto.
    compute. f_equal. auto.
  Qed.
           

End Reorder.


Section PRaceLemmas.
  Variable GE:GlobEnv.t.
  Definition invpc (pc:@ProgConfig GE):Prop:=ThreadPool.inv pc.(thread_pool).
  Definition cur_valid_id (pc:@ProgConfig GE):=pc_valid_tid pc pc.(cur_tid).
  Lemma pc_cur_tid :
    forall pc:@ProgConfig GE,
      ({-|pc,cur_tid pc}) = pc.
  Proof. destruct pc;auto. Qed.
  Lemma cur_valid_id_sw:
    forall pc,atom_bit pc = O->cur_valid_id pc->
         forall t,type_glob_step glob_sw ({-|pc,t}) sw FP.emp pc.
  Proof. destruct pc,2;simpl in *;subst;intros;econstructor;eauto. Qed.
  Lemma cur_valid_id_nohalt:
    forall pc,
      invpc pc ->
      cur_valid_id pc->
      forall pc' l fp,
        ~ type_glob_step glob_halt pc' l fp pc.
  Proof. destruct 2;intros. intro. inversion H2;subst. contradiction. Qed.
  Lemma npnsw_step_cur_valid_id:
    forall pc l fp pc',
      glob_npnsw_step pc l fp pc'->
      invpc pc ->
      cur_valid_id pc.
  Proof.
    unfold invpc;unfold cur_valid_id;unfold pc_valid_tid;unfold GSimDefs.pc_valid_tid.
    intros.
    destruct H as [|[]];Coqlib.inv H;simpl in *;subst;split;try( eapply gettop_valid_tid;eauto);intro halt;inversion halt;subst;unfold ThreadPool.get_top in *;rewrite H in H_tp_core;inversion H1;subst;inversion H_tp_core.
  Qed.
  Lemma npnsw_star_fpnotemp_cur_valid_id:
    forall pc fp pc',
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool) ->
      tau_star (@glob_npnsw_step GE) pc fp pc' ->
      fp<> FP.emp ->
      cur_valid_id pc.
  Proof.
    intros pc fl pc' wdge invpc ?  ?;unfold cur_valid_id.
    induction H;intros.
    contradiction.
    assert(fp = FP.emp \/ fp <> FP.emp).
    apply classic.
    destruct H2.
    subst.
    rewrite FP.emp_union_fp in H0.
    apply IHtau_star in H0.
    assert(cur_tid s = cur_tid s').
    destruct H as [|[]];Coqlib.inv H;auto.
    rewrite<- H2 in H0.
    destruct H as [|[]];Coqlib.inv H;unfold pc_valid_tid in *;unfold GSimDefs.pc_valid_tid in *;simpl in *;subst;destruct H0;split.
    eapply valid_tid_backwards_preserve;eauto.
    intro;contradict H0.
    eapply halted_preserve;eauto.
    eapply valid_tid_backwards_preserve;eauto.
    right. right. eauto.
    intro;contradict H0;eapply halted_preserve;eauto.
    right;right;eauto. repeat eexists. eauto. eauto.
    eapply valid_tid_backwards_preserve with(thdp1:=thdp') in H;eauto.
    eapply valid_tid_backwards_preserve;eauto.
    intro;contradict H0.
    eapply halted_preserve with(thdp2:=thdp')in H3;eauto.
    eapply halted_preserve;eauto.

    eapply npnsw_step_thdpinv;eauto.
    eapply npnsw_step_cur_valid_id;eauto.
  Qed.
 Lemma glob_predict_fpnotemp_validtid:
    forall pc b t fp,
      glob_predict pc t b fp ->
      ThreadPool.inv pc.(thread_pool)->
      fp<>FP.emp ->
      @pc_valid_tid GE pc t.
  Proof.
    inversion 1;subst;intros.
    Coqlib.inv H0.
    split. eapply gettop_valid_tid;eauto.
    intro;solv_thread.
    Coqlib.inv H0. split. eapply gettop_valid_tid;eauto.
    intro;solv_thread.
  Qed.
  Lemma GE_mod_wd_star_tp_inv2:
    forall GE pc l fp pc',
      GlobEnv.wd GE ->
      @ThreadPool.inv GE (thread_pool pc) ->
      star glob_step pc l fp pc' -> ThreadPool.inv (thread_pool pc').
  Proof.
    induction 3;intros. auto.
    apply GE_mod_wd_tp_inv in H1;auto.
  Qed.
  Lemma GE_mod_wd_npstar_tp_inv:
    forall pc l fp pc',
      star (@np_step GE) pc l fp pc' ->
      GlobEnv.wd GE ->
      ThreadPool.inv pc.(thread_pool) ->
      ThreadPool.inv pc'.(thread_pool).
  Proof.
    induction 1;auto;intros.
    eapply IHstar;auto.
    inversion H;subst;simpl in *.
    eapply ThreadPool.upd_top_inv;eauto.
    eapply ThreadPool.push_inv;eauto.
    eapply ThreadPool.pop_inv in H_tp_pop;eauto.
    eapply ThreadPool.upd_top_inv;eauto.
    eapply ThreadPool.pop_inv;eauto.
    eapply ThreadPool.pop_inv;eauto.
    eapply ThreadPool.upd_top_inv;eauto.
    eapply ThreadPool.upd_top_inv;eauto.
    eapply ThreadPool.upd_top_inv;eauto.
  Qed.
  Lemma lang_wd_mod_wd:
    forall NL L p gm ge pc t,
      wd_langs (fst p)->
      @init_config NL L p gm ge pc t->
      forall ix,mod_wd (GlobEnv.modules ge ix).
  Proof.
    intros.
    inversion H0 as [[] _ _ _ _ _ _ _ _];subst.
    specialize (ge_init ix) as [l[]].
    unfold mod_wd.
    inversion H2;subst;simpl.
    apply List.nth_error_In in H1.
    auto.
  Qed.

  Lemma npnswstep_cur_valid_tid:
    forall pc l fp pc',
      invpc pc->
      @glob_npnsw_step GE pc l fp pc'->
      cur_valid_id pc.
  Proof. inversion 2 as [|[]];try (inversion H1;subst;split;[eapply gettop_valid_tid;eauto|intro;solv_thread]). Qed.

  Lemma glob_tau_no_atom_type:
    forall x pc fp pc',
      @type_glob_step GE x pc tau fp pc'->
      atom_bit pc' = atom_bit pc ->
      x = glob_halt \/ x = core \/ x = call \/ x = ret.
  Proof. destruct x;intros;auto;inversion H;subst;inversion H0. Qed.
  
  Lemma npnswstep_taustep:
    forall pc l fp pc',@glob_npnsw_step GE pc l fp pc'->l = tau.
  Proof. inversion 1 as [|[]];inversion H0;auto. Qed.
  Lemma npnswstep_l1:
    forall pc l fp pc',@glob_npnsw_step GE pc l fp pc'->exists i,type_glob_step i pc l fp pc' /\ (i=core \/ i=call \/ i = ret).
  Proof. inversion 1 as [|[]];eauto. Qed.
  Lemma npnswstep_l3:
    forall pc l fp pc' i,@type_glob_step GE i pc l fp pc'->(i=core\/i=call\/i=ret)->glob_npnsw_step pc l fp pc'.
  Proof. destruct 2 as [|[]];subst;unfold glob_npnsw_step;eauto. Qed.
  Lemma npnswstep_l2:
    forall pc l fp pc',@glob_npnsw_step GE pc l fp pc'->atom_bit pc = atom_bit pc'.
  Proof. inversion 1 as [|[]];inversion H0;auto. Qed.
  Lemma npnswstar_bit:
    forall pc fp pc',tau_star (@glob_npnsw_step GE) pc fp pc'->atom_bit pc = atom_bit pc'.
  Proof. induction 1;intros;auto. apply npnswstep_l2 in H;congruence. Qed.
  Lemma core_tau_star_star:
    forall ge pc fp pc',
      tau_star (@type_glob_step ge core) pc fp pc'->
      exists l,star glob_step pc l fp pc'.
  Proof.
    induction 1;intros.
    eexists;constructor.
    destruct IHtau_star.
    eexists. econstructor;eauto. eapply type_glob_step_elim;eauto.
  Qed.
  Lemma core_tau_star_tau_star:
    forall ge pc fp pc',
      tau_star (@type_glob_step ge core) pc fp pc'->
      tau_star glob_step pc fp pc'.
  Proof.
    induction 1;intros. constructor.
    econstructor;eauto.
    eapply type_glob_step_elim;eauto.
  Qed.

  Lemma predict_step_ex:
    forall x y pc t1 t2 l1 fp1 pc1 l2 fp2 pc2,
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      (forall ix,mod_wd (GlobEnv.modules GE ix))->
      @type_glob_step GE x ({-|pc,t1}) l1 fp1 pc1 ->
      type_glob_step y ({-|pc,t2}) l2 fp2 pc2->
      FP.smile fp1 fp2 ->
      x=core\/x=call\/x=ret -> l2 <> sw ->
      t2 <> t1->
      exists pc',type_glob_step y ({-|pc1,t2}) l2 fp2 pc'.
  Proof.
    intros.
    
    apply npnswstep_l3 in H2;auto.
    eapply npnsw_step_eff in H2 as ?;auto.
    eapply npnsw_step_diff_thread_sim in H2 as ?;eauto.
    simpl in H9.
    eapply GEffect_fpsmile_disj_GPre_Rule in H8 as ?;eauto.
    apply GPre_comm in H10.
    destruct y;subst;try(inversion H3;subst;inversion H1;contradiction).
    eapply corestep_Glocality in H3;eauto.
    Hsimpl;eauto.
    eapply callstep_Glocality in H3;eauto. Hsimpl;eauto.
    eapply retstep_Glocality in H3;eauto. Hsimpl;eauto.
    eapply entatstep_Glocality in H3;eauto;Hsimpl;eauto.
    eapply extatstep_Glocality in H3;eauto;Hsimpl;eauto.
    eapply efprintstep_Glocality in H3;eauto;Hsimpl;eauto.
    inversion H3;subst;contradiction.
    eapply globhaltstep_Glocality in H3;eauto;Hsimpl;eauto.
  Qed.

  Lemma predict_step_ex_alt:
    forall x pc t1 t2 fp1 pc1  pc2,
      GlobEnv.wd GE->
      ThreadPool.inv pc.(thread_pool)->
      (forall ix,mod_wd (GlobEnv.modules GE ix))->
      @type_glob_step GE x (changepc GE pc t1 O) tau fp1 pc1 ->
      type_glob_step extat ({-|pc,t2}) tau FP.emp pc2->
      x=core\/x=call\/x=ret ->
      t2 <> t1->
      exists pc', type_glob_step extat (changepc GE pc1 t2 I) tau FP.emp pc'.
  Proof.
    unfold changepc;intros.
    inversion H3;subst.
    destruct H4 as [|[]];subst;inversion H2;subst;clear H2 H3.
    {
      simpl.
      assert(exists t',ThreadPool.update thdp'0 t2 c' t').
      solv_thread.
      eexists. econstructor;solv_thread. econstructor. eauto.
      destruct H2.
      eexists.
      econstructor;eauto. 
      solv_thread.
    }
    {
      simpl.
      assert(exists t',ThreadPool.update thdp'0 t2 c' t').
      solv_thread.
      eexists. econstructor;solv_thread. econstructor. eauto.
      destruct H2.
      eexists.
      econstructor;eauto. 
      solv_thread. solv_thread.
    }
    {
      simpl.
      assert(exists t',ThreadPool.update thdp'' t2 c' t').
      solv_thread.
      eexists. econstructor. solv_thread. econstructor. eauto. eauto.
      destruct H2.
      eexists.
      econstructor;eauto.
      clear H2.
      solv_thread. solv_thread.
      destruct Coqlib.peq;try contradiction. auto.
    }
  Qed.
    
    
   Lemma npnswstep_changebitO:
    forall pc l fp pc',
      glob_npnsw_step pc l fp pc'->
      glob_npnsw_step (changepc GE pc (cur_tid pc) O) l fp (changepc GE pc'(cur_tid pc) O).
   Proof. inversion 1 as [|[]];inversion H0;subst;unfold changepc;simpl;[left|right;left|right;right];econstructor;eauto. Qed.

   Lemma tauN_I_split:
    forall i pc fp pc',
      tau_N (@glob_step GE) i pc fp pc'->
      atom_bit pc = I->
      (tau_N (type_glob_step core) i pc fp pc') \/
      (exists pc1 j fp1 pc2 fp2 k,
          tau_N (type_glob_step core) j pc fp1 pc1 /\
          type_glob_step extat pc1 tau FP.emp pc2 /\
          tau_N glob_step k pc2 fp2 pc' /\
          FP.union fp1 fp2 = fp /\ j+k+1=i).
  Proof.
    induction i;intros.
    {
      inversion H;subst.
      left. constructor.
    }
    {
      inversion H;subst.
      destruct (atom_bit s') eqn:?.
      {
        apply type_glob_step_exists in H2 as [].
        destruct x;try(inversion H1;subst;inversion H0;inversion Heqb;fail).
        inversion H1;subst. simpl in *. subst. inversion Heqb.
        assert(fp0=FP.emp). inversion H1;auto. subst.
        right. Esimpl;eauto. constructor.
        Lia.lia.
      }
      {
        apply type_glob_step_exists in H2 as [].
        destruct x;try(inversion H1;subst;inversion Heqb;inversion H0;fail).
        eapply IHi in H3;eauto.
        destruct H3.
        {
          left. econstructor;eauto.
        }
        {
          Hsimpl.
          right;Esimpl;eauto. econstructor;eauto.
          rewrite <- H5. rewrite FP.fp_union_assoc;auto.
          Lia.lia.
        }
      }
    }
  Qed.
  Lemma coretauN_globtauN:
    forall  i pc fp pc',
      tau_N (@type_glob_step GE core) i pc fp pc'->
      tau_N glob_step i pc fp pc'.
  Proof.
    induction i;intros;Coqlib.inv H.
    constructor.
    eapply IHi in H2;eauto.
    econstructor;eauto. eapply type_glob_step_elim;eauto.
  Qed.
  Lemma thdp_inv_npstar:
    forall pc l fp pc',
      GlobEnv.wd GE->
      star (@np_step GE) pc l fp pc'->
      ThreadPool.inv pc.(thread_pool) ->
      ThreadPool.inv pc'.(thread_pool).
  Proof.
    induction 2;auto.
    intro.
    apply IHstar.
    eapply GlobSim.GlobSim.thp_inv_preservation;eauto.
  Qed.

    Lemma init_property_1:
    forall NL L p gm ge pc t,
      @init_config NL L p gm ge pc t->
      ThreadPool.valid_tid pc.(thread_pool) t.
  Proof.
    intros NL L p gm ge [thdp tid tgm tbit] t [];auto.
  Qed.

  
  Lemma config_thdp_init_property1:
    forall NL L p gm pc t,
      @init_config NL L p gm GE pc t->
      forall i,
        ThreadPool.valid_tid pc.(thread_pool) i->
        ~ThreadPool.halted pc.(thread_pool) i.
  Proof.
    destruct 1;intros.
    destruct pc as [thdp tid tgm tbit].
    simpl in *;subst.
    clear H H0 H2 H3 H4.
    revert t H6.
    induction H1;intros.
    
    compute -[cur_tid] in H6.
    destruct t;inversion H6.

    unfold ThreadPool.valid_tid in *.
    unfold ThreadPool.spawn in H9.
    simpl in H9.
    apply Coqlib.Plt_succ_inv in H9.
    destruct H9.
    apply IHinit in H2;auto.
    intro;contradict H2.
    Coqlib.inv H3.
    econstructor;solv_thread.
    
    rewrite H2.
    intro.
    solv_thread.
  Qed.


  Corollary init_property_1_alt :
    forall NL L p gm pc t,
      @init_config NL L p gm GE pc t->
      pc_valid_tid pc t.
  Proof.
    intros.
    eapply init_property_1 in H as L1;eauto.
    eapply config_thdp_init_property1 in H as L2;eauto.
    split;auto.
  Qed.
    


  Lemma thdp_inv_race_config_equiv:
    forall  pc,
      ThreadPool.inv pc.(thread_pool) ->
      race_config pc -> @np_race_config_base GE pc.
  Proof.
    intros.
    {
      apply race_equiv in H0.
      pose predict_equiv as H1.
      symmetry in H1.
      eapply predict_equiv_race_equiv in H0;eauto.
      Coqlib.inv H0.
      
      apply FP.emp_never_conflict in H6 as L1.
      destruct L1 as [L3 L4].
      eapply glob_predict_fpnotemp_validtid in H3 as L1;eauto.
      eapply glob_predict_fpnotemp_validtid in H4 as L2;eauto.
      Coqlib.inv H3;Coqlib.inv H4.
      {
        edestruct npnsw_step_cur_valid_id with(fp:=fp1);auto.
        left;eauto. auto.
        edestruct npnsw_step_cur_valid_id with(fp:=fp2).
        left;eauto. auto.
        assert(atom_bit pc = atom_bit pc').
        Coqlib.inv H0;auto.
        assert(atom_bit pc = atom_bit pc'0).
        Coqlib.inv H3;auto.
        apply core_step_equiv in H0. apply type_step_elim in H0.
        apply tau_plus_1 in H0. apply tau_plus2star in H0.
        apply core_step_equiv in H3. apply type_step_elim in H3.
        apply tau_plus_1 in H3.
        apply tau_plus2star in H3.
        econstructor 1 with(id1:=t1)(id2:=t2);eauto.
      }
      {
        assert(atom_bit pc = atom_bit pc').
        inversion H0;auto.
        apply core_step_equiv in H0.
        apply type_step_elim in H0.
        apply tau_plus_1 in H0.
        apply tau_plus2star in H0.
        apply corestar_tid_bit_preserve in H8 as L5.
        destruct L5 as [_].
        apply star_core_step_equiv in H8.
        apply entat_step_equiv in H3.
        assert(atom_bit pc <> atom_bit pc'0).
        Coqlib.inv H3;auto. intro T;inversion T.
        apply type_step_elim in H3.
        apply FP.conflict_sym in H6.
        assert(t2<>t1). intro;subst;contradiction.
        eapply race_atom_1 with(id1:=t2)(id2:=t1)(fp3:=FP.emp)(pc1:=({-|pc,t2}));eauto.
        constructor.
        revert H8;clear;induction 1.
        constructor.
        econstructor 2;eauto.
        eapply type_step_elim;eauto.
      }
      {
        assert(atom_bit pc = atom_bit pc'0).
        inversion H3;auto.
        apply core_step_equiv in H3.
        apply type_step_elim in H3.
        apply tau_plus_1 in H3.
        apply tau_plus2star in H3.
        apply corestar_tid_bit_preserve in H7 as L5.
        destruct L5 as [_].
        apply star_core_step_equiv in H7.
        apply entat_step_equiv in H0.
        assert(atom_bit pc <> atom_bit pc').
        Coqlib.inv H0;auto. intro T;inversion T.
        apply type_step_elim in H0.
        eapply race_atom_1 with(id1:=t1)(id2:=t2)(fp3:=FP.emp)(pc1:=({-|pc,t1}));eauto.
        constructor.
        revert H7;clear;induction 1.
        constructor.
        econstructor 2;eauto.
        eapply type_step_elim;eauto.
      }
      {
        inversion H5;contradiction.
      }
    }
  Qed.

End PRaceLemmas.
  



Section Race_Proof.
  Lemma np_race_config_base_case0_star_race:
    forall ge (pc:@ProgConfig ge) id1 id2 fp1 fp2 pc1 pc2,
      (forall ix : fintype.ordinal (GlobEnv.M ge), mod_wd (GlobEnv.modules ge ix)) ->
      GlobEnv.wd ge ->
      ThreadPool.inv pc.(thread_pool)->
      atom_bit pc = O ->
      GSimDefs.pc_valid_tid pc id1 ->
      GSimDefs.pc_valid_tid pc id2 ->
      id1 <> id2 ->
      tau_star np_step ({-|pc, id1}) fp1 pc1->
      atom_bit pc = atom_bit pc1 ->
      tau_star np_step ({-|pc, id2}) fp2 pc2 ->
      atom_bit pc = atom_bit pc2 ->
      FP.conflict fp1 fp2 ->
    
      star_race glob_predict pc.
  Proof.
    intros ge pc id1 id2 fp1 fp2 pc1 pc2 modwdge wdge thdpinv  bitO;intros.
    eapply conflict_min_rule_extended in H6;eauto.
    destruct H6 as (pc10&pc11&fp10&fp11&star1&biteq1&step1&biteq2&pc20&pc21&fp20&fp21&star2&biteq3&step2&biteq4&fpsmile1&fpsmile2&fpsmile3&fpconflict1&_).
    clear H2 H3 H4 H5 pc1 pc2 fp1 fp2.
    eapply nptaustar_nohalt in star1;eauto.
    eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star1;eauto.
    eapply nptaustar_nohalt in star2;eauto.
    eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star2;eauto.
    
    eapply npnsw_taustar_eff in star1 as Eff1;eauto.
    eapply GEffect_fpsmile_disj_GPre_Rule in fpsmile1 as Pre1;eauto.
    assert(fpsmile4:FP.smile fp10 (FP.union fp20 fp21)). eapply fpsmile_sym;eapply fpsmile_union;apply fpsmile_sym;auto.
    eapply GEffect_fpsmile_disj_GPre_Rule in fpsmile4 as Pre1';eauto. 
    assert(gmeq:gm ({-|pc,id1}) = gm ({-|pc,id2})). destruct pc;auto.
    rewrite gmeq in Pre1.
    assert(gmeq': (gm ({-|pc10, id2})) = gm pc10). destruct pc10;auto.
    rewrite <- gmeq' in Pre1. apply GPre_comm in Pre1.
    eapply npnsw_taustar_diff_thread_sim in star1 as thread_sim1;eauto.
    simpl in thread_sim1.
    eapply npnsw_taustar_thdpinv in star1 as thdpinv1;eauto.
    eapply npnsw_taustar_Glocality in star2 as G1;eauto.
    destruct G1 as (pc1'&star2'&Post0&thread_sim2).
    apply FP.emp_never_conflict in fpconflict1 as fp1.
    destruct fp1 as [fp11notemp fp21notemp].
    eapply type_step_exists in step2 as [x step2].
    destruct x;try(inversion step2;subst;inversion biteq2;contradiction;fail).
    eapply type_step_exists in step1 as [x step1].
    destruct x;try(inversion step1;subst;inversion biteq1;contradiction;fail).
    apply core_step_equiv in step1.
    apply core_step_equiv in step2.
    
    eapply npnsw_taustar_eff in star2' as Eff2;eauto.
    eapply npnsw_taustar_thdpinv in star2' as thdpinv2;eauto.
    eapply fpsmile_sym in fpsmile1.
    eapply fpsmile_sym in fpsmile3.
    eapply GEffect_fpsmile_disj_GPre_Rule in Eff2 as Pre2;eauto.
    assert(gmeq3:gm ({-|pc10,id2}) = gm pc10);auto.
    assert(gmeq4:gm pc1' = gm ({-|pc1',id1}));auto.
    rewrite gmeq3 in Pre2.
    apply GPre_comm in Pre2.
    apply npnsw_taustar_tid_preservation in star1 as tid1.
    simpl in tid1.
    rewrite tid1 in Pre2.
    rewrite gmeq4 in Pre2.
    eapply npnsw_taustar_diff_thread_sim in star2' as thread_sim';eauto.
    simpl in thread_sim'.
    assert(E1:({-|pc10,id1}) = pc10). destruct pc10;subst;auto.
    rewrite E1 in thread_sim';clear E1.
    eapply corestep_Glocality in Pre2 as G;eauto.
    destruct G as (pc3&step3&Post3&thread_sim3).
    
    simpl in Post0. apply GPost_comm in Post0.
    eapply npnsw_taustar_eff in star2 as Eff';auto.
    eapply GPre_GEffect_GPost_Rule in Pre1';eauto.
    eapply npnsw_taustar_tid_preservation in star2 as tid2.
    simpl in tid2.
    rewrite tid2 in Pre1'.
    apply GPre_comm in Pre1'.
    eapply npnsw_taustar_thdpinv in star2 as thdpinv3;eauto.
    eapply corestep_Glocality in Pre1' as G;eauto.
    destruct G as (pc4&step4&Post4&thread_sim4).
    
    apply npnsw_taustar_O_preservation in star1 as O1;auto.
    apply npnsw_taustar_tid_preservation in star2' as tid3;auto.
    simpl in tid3.
    assert(race glob_predict pc1').
    econstructor;eauto.
    econstructor;eauto. eapply npnsw_taustar_O_preservation;eauto. 
    econstructor;eauto.
    assert(L:pc1' = ({-|pc1',id2})). destruct pc1';subst;auto.
    rewrite <- L. eauto.
    eapply npnsw_taustar_O_preservation;eauto.
    left;intro contra;inversion contra.
    
    revert star1 star2 star2' step1 step2 step3 step4 H2 thdpinv H H0 H1 modwdge wdge O1 bitO;clear;intros.
    eapply npnsw_taustar_pc_valid_tid_preservation in star1 as valid;eauto.
    destruct valid as [v1 v2].
    assert(swstep1:glob_step pc10 sw FP.emp ({-|pc10,id2})).
    destruct pc10;simpl in *;subst; econstructor;eauto.
    assert(swstep0:glob_step pc sw FP.emp ({-|pc,id1})).
    destruct pc,H;simpl in *;subst; econstructor;eauto.
    eapply tau_star_to_star in star1 as [].
    eapply npnsw_star_glob_star in H3;eauto.
    eapply star_step in H3;eauto.
    eapply star_cons_step in swstep1 as [];eauto.
    eapply tau_star_to_star in star2' as [].
    eapply npnsw_star_glob_star in H5.
    eapply cons_star_star in H5;eauto.
    rewrite FP.emp_union_fp in H5.
    rewrite FP.fp_union_emp in H5.
    unfold star_race.
    exists (app x0 x1),(FP.union fp10 fp20),pc1';split;auto.
  Qed.
  Lemma np_race_config_base_star_race:
    forall ge (pc:@ProgConfig ge),
      (forall ix : fintype.ordinal (GlobEnv.M ge), mod_wd (GlobEnv.modules ge ix)) ->
      GlobEnv.wd ge ->
      np_race_config_base pc -> atom_bit pc = O ->
      ThreadPool.inv pc.(thread_pool)->
      star_race glob_predict pc.
  Proof.
    intros ge pc modwdge wdge ?  bitO ?.
    inversion H;subst.
    {
      eapply np_race_config_base_case0_star_race with(id1:=id1);eauto.
    } 
    {
      assert(FP.conflict fp1 fp2 \/ ~FP.conflict fp1 fp2).
      apply classic.
      destruct H14.
      eapply np_race_config_base_case0_star_race with(id1:=id1)(id2:=id2) in H14;eauto.
      eapply FP.smile_conflict_compat in H14.

      eapply conflict_min_rule_extended in H13;eauto.
      clear H9 H10 H11 H12 pc2 pc11.      
      destruct H13 as (pc11&pc12&fp11&fp12&star1&biteq1&step1&biteq2&pc20&pc21&fp21&fp22&star2&biteq3&step2&biteq4&fpsmile1&fpsmile2&fpsmile3&fpconflict1&_&_&fpsmile4&fpsmile5).
      eapply fpsmile_subset in fpsmile4;eauto.
      eapply fpsmile_subset in fpsmile5;eauto.
      clear H14 fp2 fp10.
      eapply nptaustar_nohalt in H4;eauto.
      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in H4;eauto.
      eapply npnsw_taustar_eff in H4 as Eff0;eauto.
      eapply npnsw_taustar_O_preservation in H4 as O0;eauto.
      eapply npnsw_taustar_pc_valid_tid_preservation in H4 as v0;eauto.
      eapply npnsw_taustar_thdpinv in H4 as inv0;eauto.
      eapply npnsw_taustar_tid_preservation in H4 as tideq0;eauto.

      simpl in *.
      rewrite O0 in H8;destruct (atom_bit pc10) eqn:biteq5;try contradiction;clear H8.
      apply type_step_exists in H7 as [].
      destruct x;try(inversion H7;subst;inversion biteq5;contradiction;fail).
      inversion H7;subst. simpl in *;subst. rewrite O0 in biteq5;inversion biteq5.
      eapply entat_step_equiv in H7.
      assert(inv1: ThreadPool.inv pc10.(thread_pool)).
      eapply GE_mod_wd_tp_inv;eauto. eapply type_glob_step_elim;eauto.
      assert(biteq6: cur_tid pc10 = id1).
      Coqlib.inv H7;eauto.

      rewrite biteq1 in biteq5.
      eapply nptaustar_nohalt in star1;eauto.
      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star1;eauto.
      rewrite <- biteq1 in biteq2.
      apply type_step_exists in step1 as [x step1].
      destruct x;try (inversion step1;subst;inversion biteq1;inversion biteq2;contradiction;fail).
      eapply core_step_equiv in step1.
      assert(Tmp:glob_npnsw_step pc11 tau fp12 pc12). left;auto.
      eapply tau_plus_1 in Tmp;eauto.
      eapply tau_plus2star in Tmp.
      eapply tau_star_star in Tmp;eauto.
      rewrite <- biteq1 in biteq5.
      clear pc11 biteq1 star1 step1.
      rename Tmp into star1.

      eapply nptaustar_nohalt in star2;eauto.
      eapply nonhalt_biteq_taustar_npnsw_tau_star_equiv in star2;eauto.
      eapply npnsw_taustar_eff in star2 as Eff1;eauto.
      eapply npnsw_taustar_O_preservation in star2 as O1;eauto.
      eapply npnsw_taustar_pc_valid_tid_preservation with(t:=id1)in star2 as v1;eauto.
      eapply npnsw_taustar_thdpinv in star2 as inv2;eauto.
      eapply npnsw_taustar_tid_preservation in star2 as tideq1;eauto;simpl in *.
      assert(fpsmile6:FP.smile fp21 (FP.union fp1 (FP.union fp11 fp12))).
      apply fpsmile_sym. eapply fpsmile_union;eauto. eapply fpsmile_union;eauto.
      eapply GEffect_fpsmile_disj_GPre_Rule in Eff1 as Pre1;eauto.
      eapply npnsw_taustar_diff_thread_sim in star2 as thread_sim1;eauto.
      simpl in *.
      assert(sw1:glob_step pc sw FP.emp ({-|pc,id2})).
      destruct pc,H2;simpl in *;subst;econstructor;eauto.
      
      eapply GEffect_fpsmile_disj_GPre_Rule with(fp2:=fp1) in Eff1 as Pre2;eauto;try apply fpsmile_sym;auto.
      eapply npnsw_taustar_Glocality in H4 as G1;eauto;simpl;try apply GPre_comm;auto.
      destruct G1 as (pc1'&star3&Post1&sim2).
      eapply npnsw_taustar_eff in star3 as Eff2;eauto.
      eapply npnsw_taustar_O_preservation in star3 as O2;eauto.
      eapply npnsw_taustar_thdpinv in star3 as inv3;eauto.
      eapply npnsw_taustar_tid_preservation in star3 as tideq2;eauto;simpl in *.

      assert(glob_step pc sw FP.emp ({-|pc,id2})).
      destruct pc,H2;simpl in *;subst;econstructor;eauto.
      unfold star_race.
      apply tau_star_to_star in star2 as Star2.
      apply tau_star_to_star in star3 as Star3.
      destruct Star2 as [l Star2].
      destruct Star3 as [l' Star3].
      apply npnsw_star_glob_star in Star2.
      apply npnsw_star_glob_star in Star3.
      eapply star_step in H8;eauto.
      assert(glob_step pc20 sw FP.emp ({-|pc20,id1})).
      destruct pc20,v1;simpl in*;subst. rewrite bitO. econstructor;eauto.
      eapply star_cons_step in H9 as [];eauto.
      eapply cons_star_star in Star3;eauto.
      rewrite FP.emp_union_fp in *;rewrite FP.fp_union_emp in *.
      clear H8 H9 Star2.
      do 4 eexists;eauto.
      assert(conflict2:FP.conflict (FP.union fp11 fp12) fp22).
      rewrite FP.union_comm_eq;apply conflict_union;auto.

      assert(Pre3:GPre ge (gm pc1')(gm pc1) FP.emp id1).
      constructor. constructor.
      apply unchanged_content_emp.
      apply unchanged_content_emp.
      intros. inversion H8.
      destruct Post1;apply GlobalFreelistEq_comm;auto.

      eapply entatstep_Glocality in H7 as G;eauto;try apply GPre_comm;try rewrite <-tideq0;eauto.

      destruct G as (pc2 & entatstep & Post2 &sim3).
      assert(tideq3:cur_tid pc2 = id1). inversion entatstep;subst;auto.
      assert(tideq4:cur_tid pc10 = id1). inversion H7;subst;auto.
      assert(biteq7:atom_bit pc2 = I). inversion entatstep;auto.
      assert(inv4:ThreadPool.inv pc2.(thread_pool)).
      eapply GE_mod_wd_tp_inv;eauto. eapply type_glob_step_elim;eauto.
      assert(gmeq1:gm pc2 = gm pc1'). inversion entatstep;auto.
      assert(gmeq2:gm pc10 = gm pc1). inversion H7;auto.
      rewrite gmeq1 in Post2. rewrite gmeq2 in Post2.
      apply GPost_comm in Post1.
      eapply GPre_GEffect_GPost_Rule in Post1 as Pre4;eauto.
      rewrite <- gmeq1 in Pre4. rewrite <- gmeq2 in Pre4.
      apply GPre_comm in Pre4.
      rewrite<- biteq6 in Pre4.
      eapply npnsw_taustar_Glocality in star1 as G1;eauto.
      destruct G1 as (pc13 & star4&Post3&sim4).
      
      apply  npnsw_taustar_I_core_taustar in star4;auto.
      assert(pc1' = ({-|pc1',id1})). destruct pc1';simpl in *;subst;auto.
      econstructor 1 with(fp1:=(FP.union fp11 fp12));eauto.
      econstructor 2;eauto.
      rewrite <- H8;eauto.

      eapply GEffect_fpsmile_disj_GPre_Rule in Eff2 as Pre5;eauto.
      eapply FP.emp_never_conflict in fpconflict1 as [_ ?].
      apply type_step_exists in step2 as [y step2].
      destruct y;try(inversion step2;subst;contradiction).
      eapply core_step_equiv in step2.
      apply GPre_comm in Pre5.
      rewrite tideq1 in Pre5.
      eapply npnsw_taustar_diff_thread_sim in star3 as sim';eauto.
      assert(eq1:pc20 = ({-|pc20,id2})).
      destruct pc20;simpl in *;subst;auto.
      assert(eq2:gm pc1' =gm ({-|pc1',id2})).
      auto.
      rewrite eq2 in Pre5.
      simpl in sim'. rewrite <- eq1 in sim'.
      eapply corestep_Glocality in step2;eauto.

      destruct step2 as (?&?&_).
      econstructor;eauto.
      right;intro contra;inversion contra.
    }
  Qed.

  Lemma NPRace_Race_Config:
    forall NL L p gm ge pc t
    (H1:True),
    @wd_langs NL L (fst p) ->
    init_config p gm ge pc t->
    (*np_safe_config pc->*)
    np_race_config pc \/ np_star_race_config pc->
    star_race_config pc.
  Proof.
    intros.
    assert(wdge:GlobEnv.wd ge). inversion H0;auto. inversion H3;auto.
    assert(invthdp:ThreadPool.inv (thread_pool pc)). inversion H0;eapply ThreadPool.init_inv;eauto.
    assert(bO:atom_bit pc = O). inversion H0;auto.
    assert(exists l fp pc',star np_step pc l fp pc' /\ np_race_config_base pc' /\ atom_bit pc' = O).
    {
      destruct H2.
      + eapply np_race_config_np_race_config_base_equiv in H2;eauto.
        Esimpl;eauto. constructor.
      + eapply np_star_race_config_np_race_config_1_equiv in H2;eauto.
        unfold np_race_config_1 in H2.
        Hsimpl. eapply star_cons_step in H3 as ?;eauto;Hsimpl.
        Esimpl;try apply H5;eauto.  inversion H3;subst;auto;try contradiction.
    }
    Hsimpl.
    unfold star_race_config.

    apply GE_mod_wd_npstar_tp_inv in H3 as v1;auto.
    apply np_star_glob_star in H3 as [].
    
    eapply np_race_config_base_star_race in H4;eauto.
    pose proof predict_equiv as L1.
    eapply predict_equiv_to_star_race_equiv in H4;eauto.
    eapply star_race_equiv in H4.
    unfold star_race_config in H4.

    destruct H4 as (?&?&?&?&?).
    eapply cons_star_star in H4;eauto.

    unfold wd_langs in H.
    unfold mod_wd.
    revert H H0;clear;intros.
    inversion H0;clear H0;subst.
    inversion H1;clear H1;subst.
    specialize (ge_init ix) as [?[]].
    eapply List.nth_error_In in H0;eauto.
    eapply H in H0.
    inversion H1;subst;simpl in *;auto.
  Qed.
  Lemma NPRace_Race:
    forall NL L p,
      @wd_langs NL L (fst p)->
      np_race_prog p ->
      race_prog p.
  Proof.
    intros.
    apply np_race_prog_nprace_prog_equiv in H0.
    unfold nprace_prog in H0.
    destruct H0 as (gm&ge&pc&init&statement).
    assert(wdge:GlobEnv.wd ge). inversion init;auto. inversion H0;auto.
    assert(invthdp:ThreadPool.inv (thread_pool pc)). inversion init;eapply ThreadPool.init_inv;eauto.
    
    
    exists gm,ge,pc,(cur_tid pc);split;auto.
    unfold star_race_config.
    unfold np_race_config_0 in statement.
    unfold np_race_config_1 in statement.

    assert(exists l fp pc',star np_step pc l fp pc' /\ np_race_config_base pc' /\ atom_bit pc' = O).    
    destruct statement.
    exists nil,FP.emp,pc;split. constructor. split. destruct H0;auto.
    inversion init;auto.

    destruct H0 as (?&?&?&?&?&?&?&?&?).
    eapply star_cons_step in H1 as R;eauto.
    destruct R.
    do 4 eexists;eauto.
    split;auto.
    inversion H1;subst;try contradiction;auto.

    destruct H0 as (?&?&?&?&?&?).
    apply GE_mod_wd_npstar_tp_inv in H0 as v1;auto.
    apply np_star_glob_star in H0 as [].
    
    eapply np_race_config_base_star_race in H1;eauto.
    pose proof predict_equiv as L1.
    eapply predict_equiv_to_star_race_equiv in H1;eauto.
    eapply star_race_equiv in H1.
    unfold star_race_config in H1.

    destruct H1 as (?&?&?&?&?).
    eapply cons_star_star in H1;eauto.

    unfold wd_langs in H.
    unfold mod_wd.
    revert H init;clear;intros.
    inversion init;clear init;subst.
    inversion H0;clear H0;subst.
    specialize (ge_init ix) as [?[]].
    eapply List.nth_error_In in H0;eauto.
    eapply H in H0.
    inversion H9;subst;simpl in *;auto.
  Qed.

  
End Race_Proof.
