Require Import Footprint InteractionSemantics GAST GMemory
        GlobDefs ETrace GlobSemantics GlobSemantics_Lemmas NPSemantics TypedSemantics .

Require Import DRF USimDRF NPDRF.

Require Import Classical Wf Arith.
(** This file contains lemmas about footprints used in the proof of semantics equivalence of P and NP*) 
Lemma tauN_taustar:
  forall i ge (step:@ProgConfig ge->glabel->FP.t->@ProgConfig ge->Prop) pc fp pc',
    tau_N step i pc fp pc'->tau_star step pc fp pc'.
Proof.
  induction i;intros. inversion H;subst. constructor.
  inversion H;subst. econstructor;eauto.
Qed.
Lemma GE_mod_wd_tp_inv:
  forall GE pc l fp pc',
    GlobEnv.wd GE -> 
    ThreadPool.inv (thread_pool pc) ->
    @glob_step GE pc l fp pc' ->
    ThreadPool.inv (thread_pool pc').
Proof.
  intros.
  destruct pc, pc'.
  inversion H1; clear H1; subst; simpl in *.
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
  { eapply ThreadPool.upd_top_inv; eauto. }
  eapply ThreadPool.upd_top_inv; eauto.
  eapply ThreadPool.upd_top_inv; eauto.
  eauto.
Qed.
Section Loc_FP_Lemmas.
  Lemma union_sym_eq:
    forall l1 l2,Locs.union l1 l2=Locs.union l2 l1.
  Proof. intros;apply Locs.locs_eq;apply Locs.union_sym. Qed.
  Lemma intersect_sym_eq:
    forall l1 l2,Locs.intersect l1 l2 =Locs.intersect l2 l1.
  Proof. intros;apply Locs.locs_eq;apply Locs.intersect_sym. Qed.
  Lemma union_assoc_eq:
    forall l1 l2 l3,Locs.union l1 (Locs.union l2 l3)=Locs.union (Locs.union l1 l2) l3.
  Proof. intros;apply Locs.locs_eq;apply Locs.union_assoc. Qed.
  Lemma union_intersect_distr_eq:
    forall l1 l2 l3,Locs.union (Locs.intersect l1 l3)(Locs.intersect l2 l3) =
               Locs.intersect(Locs.union l1 l2) l3.
  Proof. intros;apply Locs.locs_eq;apply Locs.union_intersect_distr. Qed.
  Lemma union_intersect_dist2:
    forall l1 l2 l3 l4,
      Locs.intersect(Locs.union l1 l2)(Locs.union l3 l4) =
      Locs.union (Locs.union (Locs.intersect l1 l3)(Locs.intersect l1 l4))(Locs.union (Locs.intersect l2 l3) (Locs.intersect l2 l4)).
  Proof.
    intros.
    rewrite <-union_intersect_distr_eq.
    do 2 rewrite intersect_sym_eq with (l2:=Locs.union l3 l4).
    do 2 rewrite <- union_intersect_distr_eq.
    do 2 rewrite intersect_sym_eq with(l1:=l1).
    do 2 rewrite intersect_sym_eq with(l1:=l2).
    reflexivity.
  Qed.
  Lemma locs_smile_comm:
    forall l1 l2,
      Locs.smile l1 l2 ->
      Locs.smile l2 l1.
  Proof.
    Locs.unfolds;intros.
    specialize (H b ofs).
    destruct l1 eqn:?,l2 eqn:?;eauto.
  Qed.
  Lemma FPSmile_EffectSmile:
    forall fp1 fp2,
      FP.smile fp1 fp2 ->
      Locs.smile (effects fp1)(effects fp2).
  Proof.
    intros.
    unfold effects.
    destruct H as [_ _ _ [] ? ?].
    unfold Locs.smile in *.
    rewrite union_intersect_dist2.
    rewrite intersect_sym_eq in H0.
    repeat match goal with [H:Locs.eq _ _|- _]=>apply Locs.locs_eq in H;rewrite H end.
    assert(Locs.union Locs.emp Locs.emp = Locs.emp).
    apply Locs.locs_eq;apply Locs.union_emp.
    repeat rewrite H1.
    apply Locs.eq_refl.
  Qed.
  Lemma smile_subset:
    forall l1 l2 l3,
      Locs.smile l1 l2 ->
      Locs.subset l3 l2 ->
      Locs.smile l1 l3.
  Proof.
    Locs.unfolds;intros.
    specialize (H b ofs).
    specialize (H0 b ofs).
    destruct l1 eqn:e1,l2 eqn:e2;auto;inversion H.
    destruct l3 eqn:e3;[destruct H0|];auto.
  Qed.
  Lemma fpsmile_subset:
    forall fp1 fp2 fp3,
      FP.smile fp1 fp2 ->
      FP.subset fp3 fp2->
      FP.smile fp1 fp3.
  Proof.
    inversion 1;inversion 1.
    repeat match goal with [H: _/\_|-_]=> destruct H end.
    constructor;try constructor;
    try (eapply smile_subset;[|eassumption];assumption);
    try (apply locs_smile_comm;eapply smile_subset;[|eassumption];apply locs_smile_comm;assumption).
  Qed.
  Lemma disj_comm{A:Type}: forall s1 s2,@MemAux.disj A s1 s2->MemAux.disj s2 s1.
  Proof. inversion 1;constructor;eauto. Qed.
  Lemma fpsmile_sym: forall fp1 fp2,FP.smile fp1 fp2->FP.smile fp2 fp1.
  Proof. intros. apply FP.smile_conflict_compat. apply FP.smile_conflict_compat in H. intro. contradict H. apply FP.conflict_sym. assumption. Qed.
  Lemma fpsmile_union_elim:
    forall fp1 fp2 fp3,
      FP.smile fp1 (FP.union fp2 fp3)->
      FP.smile fp1 fp2.
  Proof.
    intros.
    eapply fpsmile_subset;eauto.
    apply FP.union_subset.
  Qed.
  Lemma fpsmile_union_elim2:
    forall fp1 fp2 fp3,
      FP.smile fp1 (FP.union fp2 fp3)->
      FP.smile fp1 fp3.
  Proof.
    intros.
    rewrite FP.union_comm_eq in H.
    eapply fpsmile_union_elim;eauto.
  Qed.
  Lemma fpsmile_union_sp:
    forall fp1 fp2 fp3,
      FP.smile fp1 (FP.union fp2 fp3)->
      FP.smile fp1 fp2 /\ FP.smile fp1 fp3.
  Proof.
    split;[eapply fpsmile_union_elim|eapply fpsmile_union_elim2];eauto.
  Qed.
  Lemma locsmile_union':
    forall l1 l2 l3,
      Locs.smile l1 l2->
      Locs.smile l1 l3->
      Locs.smile l1 (Locs.union l2 l3).
  Proof.
    Locs.unfolds.
    intros.
    specialize (H b ofs);specialize (H0 b ofs).
    destruct l1,l2,l3;auto.
  Qed.
  Lemma fpconflict_dif_trans:
    forall fp1 fp2 fp3,
      FP.conflict fp1 (FP.union fp2 fp3)->
      FP.smile fp1 fp2->
      FP.conflict fp1 fp3.
  Proof.
    intros.
    apply NNPP;intro. apply FP.smile_conflict_compat in H1.
    apply smile_conflict in H. contradict H.
    destruct H0,H1.
    repeat match goal with [H: _/\_|-_]=> destruct H end.
    constructor;try split;try apply locsmile_union';auto;apply locs_smile_comm;apply locsmile_union';apply locs_smile_comm;auto.
  Qed.
  
  Lemma fpsmile_union:
    forall fp1 fp2 fp3,
      FP.smile fp1 fp3 ->
      FP.smile fp2 fp3 ->
      FP.smile (FP.union fp1 fp2) fp3.
  Proof.
    intros fp1 fp2 fp3 [] [].
    repeat match goal with H: _ /\ _ |- _ => destruct H end.
    apply fpsmile_sym.
    constructor;try (split;[|apply locs_smile_comm]);try rewrite fpfrees_union_alloc;try rewrite fpreads_union_alloc;try rewrite fpwrites_union_alloc;try rewrite fpcmps_union_alloc;try eapply locsmile_union';eauto;eapply locs_smile_comm;eauto.
  Qed.
  
  Lemma fpconflict_union:
    forall fp1 fp2 fp3,
      FP.conflict fp1 (FP.union fp2 fp3)->
      FP.conflict fp1 fp2 \/ FP.conflict fp1 fp3.
  Proof.
    intros.
    apply NNPP;intro.
    apply not_or_and in H0.
    destruct H0.
    apply FP.smile_conflict_compat in H0.
    apply FP.smile_conflict_compat in H1.
    apply fpsmile_sym in H0. apply fpsmile_sym in H1.
    eapply fpsmile_union in H0;eauto.
    rewrite FP.union_comm_eq in H0.
    apply fpsmile_sym in H0.
    apply FP.smile_conflict_compat in H0.
    contradiction.
  Qed.
  Lemma star_cons_step{GE}:
    forall step l fp l2 fp2 (pc pc1 pc2:@ProgConfig GE),
      star step pc l fp pc1 ->
      step pc1 l2 fp2 pc2 ->
      exists l',star step pc l' (FP.union fp fp2) pc2.
  Proof.
    intros.
    induction H.
    exists (cons l2 nil). rewrite FP.union_comm_eq. econstructor;eauto. constructor.
    apply IHstar in H0 as [].
    rewrite <- FP.fp_union_assoc.
    exists (cons e x). econstructor;eauto.
  Qed.
  Lemma fpconflict_tauN_rule1{GE}:
    forall i pc1 pc fp1 fp2,
      FP.conflict fp1 fp2->
      tau_N (@glob_step GE) i pc fp2 pc1 ->
      exists j k pc' pc'' fp0' fp1' fp2',
        tau_N glob_step j pc fp0' pc' /\
        glob_step pc' tau fp1' pc'' /\
        tau_N glob_step k pc'' fp2' pc1 /\
        FP.union fp0' (FP.union fp1' fp2') = fp2 /\
        FP.conflict fp1 fp1' /\
        j + k + 1 = i.
  Proof.
    induction i;intros.
    inversion H0;subst. apply FP.fp_never_conflict_emp in H as [].
    inversion H0;subst.
    assert(FP.conflict fp1 fp \/ ~ FP.conflict fp1 fp);[apply classic|];destruct H1.
    do 7 eexists.
    split. constructor.
    split. apply H2.
    split. eauto.
    rewrite FP.emp_union_fp. split;auto.
    split;auto.
    Omega.omega.
    apply FP.smile_conflict_compat in H1.
    eapply fpconflict_dif_trans in H1 as L1;eauto.

    eapply IHi in L1;eauto.
    destruct L1 as (?&?&?&?&?&?&?&?&?&?&?&?&?).    
    repeat eexists;[econstructor 2| | | | |];eauto.
    rewrite <- H7;repeat rewrite FP.fp_union_assoc;auto.
    Omega.omega.
  Qed.
  Lemma fpconflict_taustar_rule1{GE}:
    forall pc1 pc fp1 fp2,
      FP.conflict fp1 fp2->
      tau_star (@glob_step GE) pc fp2 pc1 ->
      exists pc' pc'' fp0' fp1' fp2',
        tau_star glob_step pc fp0' pc' /\
        glob_step pc' tau fp1' pc'' /\
        tau_star glob_step pc'' fp2' pc1 /\
        FP.union fp0' (FP.union fp1' fp2') = fp2 /\
        FP.conflict fp1 fp1'.
  Proof.
    intros. apply tau_star_tau_N_equiv in H0 as [].
    eapply fpconflict_tauN_rule1 in H0;eauto.
    destruct H0 as (?&?&?&?&?&?&?&?&?&?&?&?&?).
    repeat eexists;try (apply tau_star_tau_N_equiv;eexists);eauto.
  Qed.

  Lemma fpfrees_union_alloc:
    forall fp1 fp2,
      FP.frees (FP.union fp1 fp2) = Locs.union (FP.frees fp1)(FP.frees fp2).
  Proof. intros [] [];auto. Qed.
  Lemma fpreads_union_alloc:
    forall fp1 fp2,
      FP.reads (FP.union fp1 fp2) = Locs.union (FP.reads fp1)(FP.reads fp2).
  Proof. intros [] [];auto. Qed.
  Lemma fpwrites_union_alloc:
    forall fp1 fp2,
      FP.writes (FP.union fp1 fp2) = Locs.union (FP.writes fp1)(FP.writes fp2).
  Proof. intros [] [];auto. Qed.
  Lemma fpcmps_union_alloc:
    forall fp1 fp2,
      FP.cmps (FP.union fp1 fp2) = Locs.union (FP.cmps fp1)(FP.cmps fp2).
  Proof. intros [] [];auto. Qed.  

  Lemma fpsubset_trans:
    forall l1 l2 l3,
      FP.subset l1 l2 ->
      FP.subset l2 l3 ->
      FP.subset l1 l3.
  Proof.
    intros [] [] [] [] [].
    simpl in *.
    econstructor;eauto;simpl;eapply Locs.subset_trans;eauto.
  Qed.
  Lemma conflict_min_rule{ge}:
    forall pc1 fp1 pc1' pc2 fp2 pc2',
      tau_star (@np_step ge) pc1 fp1 pc1' -> atom_bit pc1 = atom_bit pc1' ->
      tau_star (@np_step ge) pc2 fp2 pc2' -> 
      FP.conflict fp1 fp2 ->
      exists pc10 pc11 fp10 fp11,
        tau_star np_step pc1 fp10 pc10 /\ atom_bit pc1 = atom_bit pc10 /\
        np_step pc10 tau fp11 pc11 /\ atom_bit pc10 = atom_bit pc11 /\
        FP.smile fp10 fp2 /\ 
        FP.conflict fp11 fp2 /\
        FP.subset fp10 fp1 /\ FP.subset fp11 fp1.
  Proof.
    intros until pc2'.
    intros H H0 L' H1 .

    induction H.
    apply FP.emp_never_conflict in H1 as []. contradiction.
    assert(L:atom_bit s' = atom_bit s).
    inversion H;auto.
    rewrite <- H3 in H0. simpl in H0.
    eapply tau_star_tau_N_equiv in H2 as [].
    eapply GlobSim.GlobSim.tau_N_bit_backwards_preservation in H2;eauto.
    rewrite <- H6 in H2. inversion H2.
    assert(FP.conflict fp fp2 \/ ~ FP.conflict fp fp2). apply classic.
    destruct H3.
    exists s,s',FP.emp,fp.
    split;constructor;auto.
    split;auto.
    split;auto.
    split. apply FP.smile_conflict_compat. intro. apply FP.conflict_sym in H4. apply FP.fp_never_conflict_emp in H4;auto.
    split;auto.
    split. unfold FP.emp. constructor;simpl;apply Locs.subset_emp.
    apply FP.union_subset.
    apply FP.smile_conflict_compat in H3.
    apply FP.conflict_sym in H1.
    apply fpsmile_sym in H3.
    eapply fpconflict_dif_trans in H3 as L1;eauto.
    apply FP.conflict_sym in L1.
    rewrite H0 in L.
    specialize (IHtau_star L L1).
    destruct IHtau_star as (?&?&?&?&?&?&?&?&?&?&?&?).
    exists x,x0,(FP.union fp x1),x2.
    split;auto. econstructor ;eauto.
    split;auto. congruence.
    split;auto.
    split;auto.
    split.
    eapply fpsmile_union;eauto. eapply fpsmile_sym;eauto.
    split;auto.
    split;auto.
    rewrite FP.union_comm_eq.
    rewrite FP.union_comm_eq with(fp1:=fp).
    eapply FP.union2_subset;auto.

    assert(FP.subset fp' (FP.union fp fp')).
    rewrite FP.union_comm_eq. eapply FP.union_subset;eauto.
    eapply fpsubset_trans;eauto.
  Qed.

  Lemma conflict_min_rule_extended{ge}:
    forall pc1 fp1 pc1' pc2 fp2 pc2',
      tau_star (@np_step ge) pc1 fp1 pc1' -> atom_bit pc1 = atom_bit pc1' ->
      tau_star (@np_step ge) pc2 fp2 pc2' -> atom_bit pc2 = atom_bit pc2' ->
      FP.conflict fp1 fp2 ->
      exists pc10 pc11 fp10 fp11,
        tau_star np_step pc1 fp10 pc10 /\ atom_bit pc1 = atom_bit pc10 /\
        np_step pc10 tau fp11 pc11 /\ atom_bit pc10 = atom_bit pc11 /\
        exists pc20 pc21 fp20 fp21,
          tau_star np_step pc2 fp20 pc20 /\ atom_bit pc2 = atom_bit pc20 /\
          np_step pc20 tau fp21 pc21 /\ atom_bit pc20 = atom_bit pc21 /\
          FP.smile fp10 fp20 /\ FP.smile fp10 fp21 /\ FP.smile fp11 fp20 /\
          FP.conflict fp11 fp21 /\
          FP.subset fp10 fp1 /\ FP.subset fp11 fp1 /\ FP.subset fp20 fp2 /\ FP.subset fp21 fp2.
  Proof.
    intros.
    eapply conflict_min_rule in H3 as(pc10&pc11&fp10&fp11&?&?&?&?&?&?&?&?);eauto.
    apply FP.conflict_sym in H8.
    eapply conflict_min_rule with(pc3:=pc2) in H8 as (pc20&pc21&fp20&fp21&?&?&?&?&?&?&?&?);eauto.
    Focus 2.
    rewrite<- FP.fp_union_emp with(fp:=fp11).
    econstructor;eauto. constructor.

    exists pc10,pc11,fp10,fp11.
    repeat split;auto.
    exists pc20,pc21,fp20,fp21.
    apply FP.conflict_sym in H15.
    repeat match goal with H:_|-_/\_=>split end;auto.
    eapply fpsmile_subset;eauto.
    eapply fpsmile_subset;eauto.
    eapply fpsmile_sym;eauto.
  Qed.

End Loc_FP_Lemmas.

Lemma MemEffect_MemPost_fpsmile_memeq:
  forall m0 m1 m1' m2' m2 fp1 fp2,
    MemEffect m0 m1 fp1 ->
    MemEffect m1 m2 fp2->
    FP.smile fp1 fp2 ->
    MemEffect m0 m1' fp2 ->
    MemPost m2 m1' fp2 ->
    MemEffect m1' m2' fp1 ->
    MemPost m1 m2' fp1 ->
    GMem.eq' m2' m2.
Proof.
  intros. 
  apply FPSmile_EffectSmile in H1 as L1.
  apply fpsmile_sym in H1.
  apply FPSmile_EffectSmile in H1 as L2.
  pose proof LocSmile_belongsto_relation (effects fp1)(effects fp2) L1.
  pose proof LocSmile_belongsto_relation (effects fp2)(effects fp1) L2.
  apply unchanged_content_memeq with(l:=Locs.union (effects fp1)(effects fp2)).

  clear H1 L1 L2.
  {
    eapply unchanged_content_implies. apply belongsto_union.
    apply unchanged_content_union.
    {
      apply unchanged_content_comm.
      eapply unchanged_content_trans;eauto.
      apply unchanged_content_comm; eauto.
      destruct H0 as []. 
      eapply unchanged_content_implies;eauto.
    }
    {
      destruct H4 as []; apply unchanged_content_comm;eapply unchanged_content_trans;eauto;eapply unchanged_content_implies;eauto.
    }
  }
  {
    destruct H as [],H0 as [], H2 as [],H4 as [].
    repeat match goal with[H:unchanged_content _ _ _ |-_]=> eapply unchanged_content_implies with(P':=notbelongsto (Locs.union(effects fp1)(effects fp2))) in H;[|apply notbelongsto_union] end.
    eapply unchanged_content_trans.
    apply unchanged_content_comm.
    eapply unchanged_content_trans.
    eapply MemContentPreserve1.
    eauto.
    eapply unchanged_content_trans with(m1:=m1);eauto.
  }
Qed.
Lemma LEffect_LPost_fpsmile_memeq:
  forall m0 m1 m1' m2' m2 f1 f2 fp1 fp2,
    LEffect m0 m1 fp1 f1 ->
    LEffect m1 m2 fp2 f2->
    FP.smile fp1 fp2 ->
    LEffect m0 m1' fp2 f2 ->
    LPost m2 m1' fp2 f2 ->
    LEffect m1' m2' fp1 f1 ->
    LPost m1 m2' fp1 f1 ->
    GMem.eq' m2' m2.
Proof.
  intros.
  destruct H,H0,H2,H3,H4,H5.
  eapply MemEffect_MemPost_fpsmile_memeq with(m0:=m0)(m1:=m1)(m2:=m2);eauto.
Qed.