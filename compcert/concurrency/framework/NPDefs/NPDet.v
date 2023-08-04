Require Import Coqlib AST Values.

Require Import Blockset Footprint GMemory InteractionSemantics GAST
        GlobDefs ETrace NPSemantics
        Injections TypedSemantics. 

Require Import Arith Wf Classical_Prop FunctionalExtensionality.
(** This file contains the lemma [np_step_det], which says that if the languages are deterministic, then the non-preemptive semantics is also deterministic. *)
Module NPDet.
  Section det_def.
    Context {GE:GlobEnv.t}.
    Definition language_det : Prop :=
      forall ix, mod_det (GlobEnv.modules GE ix) /\ mod_wd (GlobEnv.modules GE ix).
    Lemma init_det:
      forall NL L p gm pc t,
        det_langs (fst p)->
        wd_langs (fst p) ->
        @init_config NL L p gm GE pc t->
        language_det.
    Proof. {
        intros.
        unfold language_det.
        unfold det_langs in H.
        unfold wd_langs in H0.
        inversion H1 as [[] _ _ _ _ _ _ _ _];subst.
        intro.
        specialize (ge_init ix) as [l[]].
        unfold mod_det;unfold mod_wd.
        inversion H3;subst;simpl.
        apply List.nth_error_In in H2;auto.
      }
    Qed.
  End det_def.
  Section TypestepDet.
    Context {GE:GlobEnv.t}.
    Context {ldet:@language_det GE}.
    Ltac unfoldldet:=
      unfold language_det in ldet;unfold mod_det in ldet;unfold mod_wd in ldet;unfold lang_det in ldet.
    Lemma external_not_halt:
      forall L,
        wd L ->
        forall ge p s,
          at_external L ge p = Some s -> halt L p = None.
    Proof.
      intros.
      pose proof (atext_not_halt _ H) as atext_not_halt. clear H.
      unfold at_external_halted_excl in atext_not_halt.
      specialize (atext_not_halt ge p) as [|];auto.
      rewrite H in H0;inversion H0.
    Qed.
    Lemma halt_not_external:
      forall L,
        wd L ->
        forall ge p s,
          halt L p = Some s->at_external L ge p = None .
    Proof.
      intros.
      pose proof (atext_not_halt _ H) as atext_not_halt. clear H.
      unfold at_external_halted_excl in atext_not_halt.
      specialize (atext_not_halt ge p) as [|];auto.
      rewrite H in H0;inversion H0.
    Qed.
    Lemma core_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step core pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = core.
    Proof. {
        intros.
        unfoldldet.
        inversion H;subst.
        specialize (ldet (Core.i c)) as [].
        pose proof H_core_step as L1.
        pose proof H_core_step as L2.
        apply (step_not_atext _ H2) in L1.
        apply (step_not_halt _ H2) in L2.
        inversion H0;subst;auto;rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;clear H_tp_core0;subst; try (rewrite L1 in H_core_atext;inversion H_core_atext);try (rewrite L2 in H_core_halt;inversion H_core_halt).
      }
    Qed.
    Lemma call_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step call pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = call.
    Proof.
      intros.
      unfoldldet.
      inversion H;subst.
      pose proof  (ldet (Core.i c)) as [].
      inversion H0;subst;auto;rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;clear H_tp_core0;subst;[eapply core_unique in H;eauto| | | | |]; try (eapply external_not_halt in H_core_atext;eauto; rewrite H_core_atext in H_core_halt;inversion H_core_halt).
      unfold not_primitive in H_not_prim.
      destruct (peq funid print);[inversion H_not_prim|].
      destruct (peq funid ent_atom);[inversion H_not_prim|].
      rewrite H_core_atext in H_core_atext0;inversion H_core_atext0;subst.
      contradiction.

      unfold not_primitive in H_not_prim.
      destruct (peq funid print);[inversion H_not_prim|].
      rewrite H_core_atext in H_core_atext0;inversion H_core_atext0;subst.
      contradiction.
    Qed.
    Lemma ret_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step ret pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = ret.
    Proof.
      intros.
      unfoldldet.
      inversion H;subst.
      pose proof  (ldet (Core.i c)) as [].
      inversion H0;subst;auto;rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;clear H_tp_core0;subst ;[eapply core_unique in H;eauto|eapply call_unique in H;eauto | | | |];try (eapply external_not_halt in H_core_atext;eauto; rewrite H_core_atext in H_core_halt;inversion H_core_halt);try ( rewrite H_tp_pop in H_tp_pop0;inversion H_tp_pop0;clear H_tp_pop0;subst; inversion H_thread_halt;subst; unfold ThreadPool.get_top in H_tp_caller;  rewrite H3 in H_tp_caller; inversion H4;subst;inversion H_tp_caller).
    Qed.
    
    Lemma thrdhalt_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step thrdhalt pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = thrdhalt.
    Proof.
      intros.
      unfoldldet.
      inversion H;subst.
      pose proof  (ldet (Core.i c)) as [].
      inversion H0;subst;auto;rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;clear H_tp_core0;subst;[eapply core_unique in H;eauto|eapply call_unique in H;eauto |eapply ret_unique in H;eauto | | |].
      rewrite H_tp_pop in H_tp_pop0;inversion H_tp_pop0;subst.
      rewrite H_core_halt in H_core_halt0;inversion H_core_halt0;subst.
      clear H_core_halt0 H_tp_pop0 H_thread_halt0.
      apply H_all_thread_halted in H_thread_valid.
      contradiction.
      
      apply external_not_halt in H_core_atext;auto.
      rewrite H_core_atext in H_core_halt.
      inversion H_core_halt.
      
      apply external_not_halt in H_core_atext;auto.
      rewrite H_core_atext in H_core_halt.
      inversion H_core_halt.
    Qed.
    
    Lemma allhalt_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step allhalt pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = allhalt.
    Proof.
      intros.
      unfoldldet.
      inversion H;subst.
      pose proof  (ldet (Core.i c)) as [].
      inversion H0;subst;auto;rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;clear H_tp_core0;subst;[eapply core_unique in H|eapply call_unique in H|eapply ret_unique in H | eapply thrdhalt_unique in H| |];eauto;apply external_not_halt in H_core_atext;auto;rewrite H_core_atext in H_core_halt;inversion H_core_halt.
    Qed.
    
    Lemma entat_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step entat pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = entat.
    Proof.
      intros.
      unfoldldet.
      inversion H;subst.
      pose proof  (ldet (Core.i c)) as [].
      inversion H0;subst;auto;rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;clear H_tp_core0;subst;[eapply core_unique in H|eapply call_unique in H|eapply ret_unique in H | eapply thrdhalt_unique in H|eapply allhalt_unique in H |];eauto.
      rewrite H_core_atext in H_core_atext0;inversion H_core_atext0.
    Qed.
    
    Lemma extat_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step extat pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = extat.
    Proof.
      intros.
      unfoldldet.
      inversion H;subst.
      pose proof  (ldet (Core.i c)) as [].
      inversion H0;subst;auto.
      eapply core_unique in H;eauto.
    Qed.

    Lemma efprint_unique:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step efprint pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        t = efprint.
    Proof.
      intros.
      unfoldldet.
      inversion H;subst.
      pose proof  (ldet (Core.i c)) as [].
      inversion H0;subst;auto;[eapply core_unique in H|eapply call_unique in H|eapply ret_unique in H | eapply thrdhalt_unique in H|eapply allhalt_unique in H |eapply entat_unique in H];eauto.
    Qed.
    
    Theorem type_unique:
      forall t1 t2 pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step t1 pc l1 fp1 pc1 ->
        @type_np_step GE t2 pc l2 fp2 pc2 ->
        t2 = t1.
    Proof.
      intros.
      destruct t1; [eapply core_unique|eapply call_unique|eapply ret_unique| eapply entat_unique |eapply extat_unique |eapply thrdhalt_unique|eapply allhalt_unique|eapply efprint_unique|inversion H|inversion H];eauto.
    Qed.
    
    Lemma type_label_det:
      forall t pc fp1 l1 pc1 fp2 l2 pc2,
        type_np_step t pc l1 fp1 pc1 ->
        @type_np_step GE t pc l2 fp2 pc2 ->
        l1 = l2.
    Proof.
      intros.
      inversion H;inversion H0;subst;auto;inversion H6.
      inversion H7;subst.
      rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;subst.
      rewrite H_core_atext in H_core_atext0;inversion H_core_atext0;subst;auto.
    Qed.
    
    Lemma type_footprint_det:
      forall t pc l fp1 pc1 fp2 pc2,
        type_np_step t pc l fp1 pc1 ->
        @type_np_step GE t pc l fp2 pc2 ->
        fp1 = fp2.
    Proof.
      intros.
      destruct t;inversion H;inversion H0;subst;auto.
      inversion H6;clear H6 H7;subst.
      rewrite H_tp_core in H_tp_core0;inversion H_tp_core0;subst.
      unfoldldet.
      specialize (ldet (Core.i c0)) as [].
      eapply H1 in H_core_step.
      apply H_core_step in H_core_step0 as (?&?&?).
      auto.
    Qed.
    
    Ltac rewrite_inv H1 H2 :=
      rewrite H1 in H2;inversion H2;clear H2;subst.
    Lemma typestep_det:
      forall t pc l fp pc1 pc2,
        @type_np_step GE t pc l fp pc1 ->
        type_np_step t pc l fp pc2 ->
        pc1.(thread_pool) = pc2.(thread_pool) /\
        pc1.(gm) = pc2.(gm) /\
        pc1.(atom_bit) = pc2.(atom_bit).
    Proof.
      intros.
      unfoldldet.
      destruct t;inversion H;inversion H0;subst;inversion H6;clear H6 H7;subst;simpl;rewrite_inv H_tp_core H_tp_core0.
      specialize (ldet (Core.i c0)) as [].
      eapply H1 in H_core_step;apply H_core_step in H_core_step0 as (?&?&?);subst.
      inversion H_core_upd;inversion H_core_upd0;subst.
      inversion H_tp_upd;inversion H_tp_upd0;subst.
      rewrite H4 in H8;inversion H8;subst.
      inversion H5;inversion H9;subst;inversion H13;subst;auto.
      
      
      rewrite_inv H_core_atext H_core_atext0.
      rewrite_inv H_mod_id H_mod_id0.
      rewrite_inv H_new_core H_new_core0.
      rewrite_inv H_tp_push H_tp_push0.
      auto.
      
      rewrite_inv H_core_halt H_core_halt0.
      rewrite_inv H_tp_pop H_tp_pop0.
      rewrite_inv H_tp_caller H_tp_caller0.
      rewrite_inv H_core_aftext H_core_aftext0.
      inversion H_core_upd;inversion H_core_upd0;subst.
      inversion H_tp_upd;inversion H_tp_upd0;subst.
      rewrite H1 in H5;inversion H5;subst.
      inversion H6;inversion H2;subst;inversion H11;subst;auto.
      
      rewrite_inv H_core_atext H_core_atext0.
      rewrite_inv H_core_aftext H_core_aftext0.
      inversion H_core_update;inversion H_core_update0;subst.
      inversion H_tp_upd;inversion H_tp_upd0;subst.
      rewrite H1 in H5;inversion H5;subst.
      inversion H6;inversion H2;subst;inversion H11;subst;auto.
      
      rewrite_inv H_core_atext H_core_atext0.
      rewrite_inv H_core_aftext H_core_aftext0.
      inversion H_core_update;inversion H_core_update0;subst.
      inversion H_tp_upd;inversion H_tp_upd0;subst.
      rewrite H1 in H5;inversion H5;subst.
      inversion H6;inversion H2;subst;inversion H11;subst;auto.
      
      rewrite_inv H_core_halt H_core_halt0.
      rewrite_inv H_tp_pop H_tp_pop0.
      auto.
      
      rewrite_inv H_core_halt H_core_halt0.
      rewrite_inv H_tp_pop H_tp_pop0;auto.
      
      rewrite_inv H_core_atext H_core_atext0.
      rewrite_inv H_core_aftext H_core_aftext0.
      inversion H_core_update;inversion H_core_update0;subst.
      inversion H_tp_upd;inversion H_tp_upd0;subst.
      rewrite H1 in H5;inversion H5;subst.
      inversion H6;inversion H2;subst;inversion H11;subst;auto.
    Qed.
    
    Lemma typestep_taustep_det:
      forall t pc fp pc1 pc2,
        @type_np_step GE t pc tau fp pc1 ->
        type_np_step t pc tau fp pc2 ->
        pc1.(cur_tid) = pc2.(cur_tid).
    Proof.
      intros.
      assert(cur_tid pc = cur_tid pc1).
      inversion H;subst;auto;try contradiction.
      rewrite <- H1.
      inversion H0;subst;auto;try contradiction.
    Qed.

    Lemma np_step_det:
     forall (pc pc' pc'':@ProgConfig GE) fp fp' l1 l2,
        np_step pc l1 fp pc' -> np_step pc l2 fp' pc'' ->
        l1 = l2 /\ fp = fp' /\
        pc'.(thread_pool) = pc''.(thread_pool) /\
        pc'.(gm) =  pc''.(gm) /\
        pc'.(atom_bit) = pc''.(atom_bit).
    Proof.
      intros.
      apply type_step_exists in H0 as [].
      apply type_step_exists in H as [].
      pose proof H0 as Tmp1.
      eapply type_unique in Tmp1;try apply H;subst.
      pose proof H0 as Tmp1.
      eapply type_label_det in Tmp1;try apply H;subst.
      pose proof H0 as Tmp1.
      eapply type_footprint_det in Tmp1;try apply H;subst.
      eapply typestep_det in H0 as (?&?&?);try apply H;subst;auto.
    Qed.
    End TypestepDet.
End NPDet.
