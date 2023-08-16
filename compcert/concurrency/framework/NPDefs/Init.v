Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics GlobSemantics_Lemmas NPSemantics TypedSemantics .

Require Import Classical Wf Arith.
(** This file contains lemmas for initialization of program configuration. *)
Local Definition pc_valid_tid {ge}:= @GSimDefs.pc_valid_tid ge.
Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:= D|}(at level 70,right associativity).
Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).
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
Lemma config_thdp_init_property1:
    forall NL L p gm ge pc t,
      @init_config NL L p gm ge pc t->
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
    Lemma init_property_1:
    forall NL L p gm ge pc t,
      @init_config NL L p gm ge pc t->
      ThreadPool.valid_tid pc.(thread_pool) t.
  Proof.
    intros NL L p gm ge [thdp tid tgm tbit] t [];auto.
  Qed.
  Corollary init_property_1_alt :
    forall NL L p gm ge pc t,
      @init_config NL L p gm ge pc t->
      pc_valid_tid pc t.
  Proof.
    intros.
    eapply init_property_1 in H as L1;eauto.
    eapply config_thdp_init_property1 in H as L2;eauto.
    split;auto.
  Qed.
    
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
  Lemma init_free:
    forall NL (L:@langs NL)(p:prog L) gm ge pc t,
      init_config p gm ge pc pc.(cur_tid) ->
      pc_valid_tid pc t->
      init_config p gm ge ({-|pc,t}) t.
  Proof.
    unfold pc_valid_tid;inversion 1;subst.
    econstructor;eauto.
    inversion H9. 
    tauto.
  Qed.
  Lemma init_pair_lemma:
    forall NL L sc tc e sgm sge spc tgm tge tpc i i',
      @init_config NL L (sc,e) sgm sge spc i->
      @init_config NL L (tc,e) tgm tge tpc i'->
      @init_config NL L (tc,e) tgm tge ({-|tpc,i}) i.
  Proof.
    intros.
    apply init_property_1_alt in H as ?.
    eapply init_pair_valid_tid in H1;eauto.
    eapply init_free;eauto.
    inversion H0;subst;auto.
  Qed.

 