(** Lifting a well-bracketed local atomic-wrapper path to the CASCompCert
    global semantics.

    This file is deliberately language-generic.  In particular, the two
    marker steps below can only be instantiated when the language of the
    active module exposes [ent_atom] and [ext_atom] through [at_external].
    For the concrete Clight wrappers that language is
    [Clight_IS_2_with_markers]; ordinary client modules continue to use the
    unmodified [Clight_IS_2]. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
From mathcomp.boot Require Import fintype.

Require Import compcert.concurrency.common.ETrace.
Require Import compcert.concurrency.common.Footprint.
Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.common.GlobDefs.
Require Import compcert.concurrency.common.GlobSemantics.
Require Import compcert.concurrency.common.InteractionSemantics.

From Stdlib Require Import List.
Import ListNotations.

Module ClightAtomicGlobalSteps.

  Section OneModule.

    Context {GE : GlobEnv.t}.
    Variable ix : 'I_(GlobEnv.M GE).

    Local Definition md : ModSem.t := GlobEnv.modules GE ix.
    Local Definition lang : Language := ModSem.lang md.
    Local Definition ge : lang.(G) := ModSem.Ge md.

    Variable F : fid.
    Local Definition fl : MemAux.freelist :=
      FLists.get_fl (GlobEnv.freelists GE) F.

    (** A local core star updates exactly the top frame of the selected
        thread and leaves the scheduler and atomic bit unchanged.  Stating
        the resulting stack explicitly makes the lemma compositional across
        the two marker boundaries. *)
    Lemma local_star_to_global_star
        (c0 : lang.(core)) (m0 : GMemory.gmem) fp
        (c1 : lang.(core)) (m1 : GMemory.gmem)
        (Hlocal : InteractionSemantics.star (step lang ge fl)
          c0 m0 fp c1 m1) :
      forall (tp : @ThreadPool.t GE) t sg d cs,
        ThreadPool.get_cs tp t =
          Some (Core.Build_t ix c0 sg F :: cs) ->
        exists tp',
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp t m0 d) fp
            (Build_ProgConfig GE tp' t m1 d) /\
          ThreadPool.get_cs tp' t =
            Some (Core.Build_t ix c1 sg F :: cs).
    Proof.
      induction Hlocal as
        [c m | c m fp0 c' m' fp1 c'' m'' Hstep Hstar IH];
        intros tp t sg d cs Hcs.
      - exists tp. split; [constructor | exact Hcs].
      - set (ctop := Core.Build_t ix c' sg F).
        set (tp1 := ThreadPool.Build_t
          (PMap.set t (Some (ctop :: cs)) (ThreadPool.content tp))
          (ThreadPool.next_tid tp) (ThreadPool.next_fmap tp)).
        assert (Hcore_update :
          Core.update (Core.Build_t ix c sg F) c' ctop).
        { constructor. reflexivity. }
        assert (Htp_update : ThreadPool.update tp t ctop tp1).
        { econstructor.
          - exact Hcs.
          - econstructor. exact Hcore_update.
          - reflexivity. }
        assert (Hglobal :
          glob_step (Build_ProgConfig GE tp t m d) ETrace.tau fp0
            (Build_ProgConfig GE tp1 t m' d)).
        { eapply GlobSemantics.Corestep
            with (c := Core.Build_t ix c sg F)
                 (cc' := c') (c' := ctop).
          - unfold ThreadPool.get_top. rewrite Hcs. reflexivity.
          - exact Hstep.
          - exact Hcore_update.
          - exact Htp_update. }
        assert (Hcs1 : ThreadPool.get_cs tp1 t = Some (ctop :: cs)).
        { unfold ThreadPool.get_cs, tp1. simpl.
          rewrite PMap.gss. reflexivity. }
        destruct (IH tp1 t sg d cs Hcs1) as (tp2 & Hglobstar & Hcs2).
        exists tp2. split.
        + econstructor; eauto.
        + exact Hcs2.
    Qed.

    Lemma ent_atom_global_step
        (c c' : lang.(core)) (tp : @ThreadPool.t GE)
        t sg cs gm
        (Hcs : ThreadPool.get_cs tp t =
          Some (Core.Build_t ix c sg F :: cs))
        (Hat : at_external lang ge c =
          Some (GAST.ent_atom, GAST.ent_atom_sg, []))
        (Hafter : after_external lang c None = Some c') :
      exists tp',
        glob_step (Build_ProgConfig GE tp t gm O) ETrace.tau FP.emp
          (Build_ProgConfig GE tp' t gm I) /\
        ThreadPool.get_cs tp' t =
          Some (Core.Build_t ix c' sg F :: cs).
    Proof.
      set (ctop := Core.Build_t ix c' sg F).
      set (tp1 := ThreadPool.Build_t
        (PMap.set t (Some (ctop :: cs)) (ThreadPool.content tp))
        (ThreadPool.next_tid tp) (ThreadPool.next_fmap tp)).
      assert (Hcore_update :
        Core.update (Core.Build_t ix c sg F) c' ctop).
      { constructor. reflexivity. }
      assert (Htp_update : ThreadPool.update tp t ctop tp1).
      { econstructor.
        - exact Hcs.
        - econstructor. exact Hcore_update.
        - reflexivity. }
      exists tp1. split.
      - eapply GlobSemantics.Ent_Atom
          with (c := Core.Build_t ix c sg F)
               (cc' := c') (c' := ctop); eauto.
        unfold ThreadPool.get_top. rewrite Hcs. reflexivity.
      - unfold ThreadPool.get_cs, tp1. simpl.
        rewrite PMap.gss. reflexivity.
    Qed.

    Lemma ext_atom_global_step
        (c c' : lang.(core)) (tp : @ThreadPool.t GE)
        t sg cs gm
        (Hcs : ThreadPool.get_cs tp t =
          Some (Core.Build_t ix c sg F :: cs))
        (Hat : at_external lang ge c =
          Some (GAST.ext_atom, GAST.ext_atom_sg, []))
        (Hafter : after_external lang c None = Some c') :
      exists tp',
        glob_step (Build_ProgConfig GE tp t gm I) ETrace.tau FP.emp
          (Build_ProgConfig GE tp' t gm O) /\
        ThreadPool.get_cs tp' t =
          Some (Core.Build_t ix c' sg F :: cs).
    Proof.
      set (ctop := Core.Build_t ix c' sg F).
      set (tp1 := ThreadPool.Build_t
        (PMap.set t (Some (ctop :: cs)) (ThreadPool.content tp))
        (ThreadPool.next_tid tp) (ThreadPool.next_fmap tp)).
      assert (Hcore_update :
        Core.update (Core.Build_t ix c sg F) c' ctop).
      { constructor. reflexivity. }
      assert (Htp_update : ThreadPool.update tp t ctop tp1).
      { econstructor.
        - exact Hcs.
        - econstructor. exact Hcore_update.
        - reflexivity. }
      exists tp1. split.
      - eapply GlobSemantics.Ext_Atom
          with (c := Core.Build_t ix c sg F)
               (cc' := c') (c' := ctop); eauto.
        unfold ThreadPool.get_top. rewrite Hcs. reflexivity.
      - unfold ThreadPool.get_cs, tp1. simpl.
        rewrite PMap.gss. reflexivity.
    Qed.

    (** Any three local segments separated by exposed enter/exit calls form
        one silent global atomic macro.  Exposure of the marker calls is an
        explicit premise here; the concrete Clight marker filter discharges
        those premises in [clight_atomic_global_clight].  The middle segment
        runs with the global atomic bit set. *)
    Theorem bracketed_local_paths_to_global_atomic
        (c0 cent cent_resume cext cext_resume cfinal : lang.(core))
        (gm0 gm1 gm2 gm3 : GMemory.gmem)
        fp0 fp1 fp2
        (Hto_ent : InteractionSemantics.star (step lang ge fl)
          c0 gm0 fp0 cent gm1)
        (Hat_ent : at_external lang ge cent =
          Some (GAST.ent_atom, GAST.ent_atom_sg, []))
        (Hafter_ent : after_external lang cent None = Some cent_resume)
        (Hinside : InteractionSemantics.star (step lang ge fl)
          cent_resume gm1 fp1 cext gm2)
        (Hat_ext : at_external lang ge cext =
          Some (GAST.ext_atom, GAST.ext_atom_sg, []))
        (Hafter_ext : after_external lang cext None = Some cext_resume)
        (Hfrom_ext : InteractionSemantics.star (step lang ge fl)
          cext_resume gm2 fp2 cfinal gm3) :
      forall (tp : @ThreadPool.t GE) t sg cs,
        ThreadPool.get_cs tp t =
          Some (Core.Build_t ix c0 sg F :: cs) ->
        exists tp' fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp t gm0 O) fp
            (Build_ProgConfig GE tp' t gm3 O) /\
          ThreadPool.get_cs tp' t =
            Some (Core.Build_t ix cfinal sg F :: cs).
    Proof.
      intros tp t sg cs Hcs.
      destruct (local_star_to_global_star _ _ _ _ _ Hto_ent
        tp t sg O cs Hcs) as (tp0 & Hglob0 & Hcs0).
      destruct (ent_atom_global_step cent cent_resume tp0 t sg cs gm1
        Hcs0 Hat_ent Hafter_ent) as (tp1 & Hent & Hcs1).
      destruct (local_star_to_global_star _ _ _ _ _ Hinside
        tp1 t sg I cs Hcs1) as (tp2 & Hglob1 & Hcs2).
      destruct (ext_atom_global_step cext cext_resume tp2 t sg cs gm2
        Hcs2 Hat_ext Hafter_ext) as (tp3 & Hext & Hcs3).
      destruct (local_star_to_global_star _ _ _ _ _ Hfrom_ext
        tp3 t sg O cs Hcs3) as (tp4 & Hglob2 & Hcs4).
      assert (Hent_star :
        exists fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp0 t gm1 O) fp
            (Build_ProgConfig GE tp1 t gm1 I)).
      { exists (FP.union FP.emp FP.emp). econstructor; eauto. constructor. }
      assert (Hext_star :
        exists fp,
          ETrace.tau_star (@glob_step GE)
            (Build_ProgConfig GE tp2 t gm2 I) fp
            (Build_ProgConfig GE tp3 t gm2 O)).
      { exists (FP.union FP.emp FP.emp). econstructor; eauto. constructor. }
      destruct Hent_star as (fpe & Hent_star).
      destruct Hext_star as (fpx & Hext_star).
      pose proof (@ETrace.tau_star_star
        (@ProgConfig GE) (@glob_step GE) _ _ _ _ _
        Hglob0 Hent_star) as H01.
      pose proof (@ETrace.tau_star_star
        (@ProgConfig GE) (@glob_step GE) _ _ _ _ _
        H01 Hglob1) as H012.
      pose proof (@ETrace.tau_star_star
        (@ProgConfig GE) (@glob_step GE) _ _ _ _ _
        H012 Hext_star) as H0123.
      pose proof (@ETrace.tau_star_star
        (@ProgConfig GE) (@glob_step GE) _ _ _ _ _
        H0123 Hglob2) as Hall.
      eexists tp4, _. split; eauto.
    Qed.

    Lemma tau_star_is_star pc fp pc' :
      ETrace.tau_star (@glob_step GE) pc fp pc' ->
      exists labels, ETrace.star (@glob_step GE) pc labels fp pc'.
    Proof.
      induction 1.
      - exists []. constructor.
      - destruct IHtau_star as [labels Hlabels].
        exists (ETrace.tau :: labels). econstructor; eauto.
    Qed.

  End OneModule.

  Section Scheduling.

    Context {GE : GlobEnv.t}.

    Lemma thread_pool_update_preserves_other_stack
        (tp tp' : @ThreadPool.t GE) t c
        (Hupdate : ThreadPool.update tp t c tp') :
      forall other, other <> t ->
        ThreadPool.get_cs tp' other = ThreadPool.get_cs tp other.
    Proof.
      intros other Hother.
      inversion Hupdate; subst tp'; clear Hupdate.
      unfold ThreadPool.get_cs. simpl.
      rewrite PMap.gso; auto.
    Qed.

    Lemma thread_pool_push_preserves_other_stack
        (tp tp' : @ThreadPool.t GE) t ix c sg
        (Hpush : ThreadPool.push tp t ix c sg = Some tp') :
      forall other, other <> t ->
        ThreadPool.get_cs tp' other = ThreadPool.get_cs tp other.
    Proof.
      intros other Hother.
      unfold ThreadPool.push in Hpush.
      destruct (PMap.get t (ThreadPool.content tp));
        inversion Hpush; subst tp'; clear Hpush.
      unfold ThreadPool.get_cs. simpl.
      rewrite PMap.gso; auto.
    Qed.

    Lemma thread_pool_pop_preserves_other_stack
        (tp tp' : @ThreadPool.t GE) t
        (Hpop : ThreadPool.pop tp t = Some tp') :
      forall other, other <> t ->
        ThreadPool.get_cs tp' other = ThreadPool.get_cs tp other.
    Proof.
      intros other Hother.
      unfold ThreadPool.pop in Hpop.
      destruct (PMap.get t (ThreadPool.content tp)) as [cs |];
        try discriminate.
      destruct (CallStack.pop cs); inversion Hpop; subst tp'; clear Hpop.
      unfold ThreadPool.get_cs. simpl.
      rewrite PMap.gso; auto.
    Qed.

    (** A silent global step keeps the selected thread fixed and can update
        only that thread's call stack. *)
    Lemma tau_glob_step_preserves_other_stacks
        (pc pc' : @ProgConfig GE) fp
        (Hstep : glob_step pc ETrace.tau fp pc') :
      cur_tid pc' = cur_tid pc /\
      forall other, other <> cur_tid pc ->
        ThreadPool.get_cs (thread_pool pc') other =
        ThreadPool.get_cs (thread_pool pc) other.
    Proof.
      inversion Hstep; subst; simpl.
      - split; [reflexivity |].
        eapply thread_pool_update_preserves_other_stack; eauto.
      - split; [reflexivity |].
        eapply thread_pool_push_preserves_other_stack; eauto.
      - split; [reflexivity |].
        intros other Hother.
        transitivity (ThreadPool.get_cs thdp' other).
        + eapply thread_pool_update_preserves_other_stack; eauto.
        + eapply thread_pool_pop_preserves_other_stack; eauto.
      - split; [reflexivity |].
        eapply thread_pool_pop_preserves_other_stack; eauto.
      - split; [reflexivity |].
        eapply thread_pool_update_preserves_other_stack; eauto.
      - split; [reflexivity |].
        eapply thread_pool_update_preserves_other_stack; eauto.
    Qed.

    Lemma tau_star_preserves_other_stacks
        (pc pc' : @ProgConfig GE) fp
        (Hstar : ETrace.tau_star (@glob_step GE) pc fp pc') :
      cur_tid pc' = cur_tid pc /\
      forall other, other <> cur_tid pc ->
        ThreadPool.get_cs (thread_pool pc') other =
        ThreadPool.get_cs (thread_pool pc) other.
    Proof.
      induction Hstar.
      - split; [reflexivity | intros; reflexivity].
      - destruct (tau_glob_step_preserves_other_stacks _ _ _ H)
          as [Hcur_step Haway_step].
        destruct IHHstar as [Hcur_star Haway_star].
        split; [congruence |].
        intros other Hother.
        transitivity (ThreadPool.get_cs (thread_pool s') other).
        + apply Haway_star. congruence.
        + apply Haway_step. exact Hother.
    Qed.

    (** Silent execution never spawns a thread.  Calls may advance the
        selected thread's fresh-frame counter, but every other counter is
        preserved. *)
    Lemma tau_glob_step_preserves_pool_metadata
        (pc pc' : @ProgConfig GE) fp
        (Hstep : glob_step pc ETrace.tau fp pc') :
      ThreadPool.next_tid (thread_pool pc') =
        ThreadPool.next_tid (thread_pool pc) /\
      forall other, other <> cur_tid pc ->
        ThreadPool.next_fmap (thread_pool pc') other =
        ThreadPool.next_fmap (thread_pool pc) other.
    Proof.
      inversion Hstep; subst; simpl.
      - inversion H_tp_upd; subst. split; reflexivity.
      - unfold ThreadPool.push in H_tp_push.
        destruct (PMap.get t (ThreadPool.content thdp));
          inversion H_tp_push; subst; clear H_tp_push; simpl.
        split; [reflexivity |].
        intros other Hother.
        destruct (peq t other); [congruence | reflexivity].
      - unfold ThreadPool.pop in H_tp_pop.
        destruct (PMap.get t (ThreadPool.content thdp)) as [cs0 |];
          try discriminate.
        destruct (CallStack.pop cs0);
          inversion H_tp_pop; subst thdp'; clear H_tp_pop.
        inversion H_tp_upd; subst. split; reflexivity.
      - unfold ThreadPool.pop in H_tp_pop.
        destruct (PMap.get t (ThreadPool.content thdp)) as [cs0 |];
          try discriminate.
        destruct (CallStack.pop cs0);
          inversion H_tp_pop; subst; clear H_tp_pop.
        split; reflexivity.
      - inversion H_tp_upd; subst. split; reflexivity.
      - inversion H_tp_upd; subst. split; reflexivity.
    Qed.

    Lemma tau_star_preserves_pool_metadata
        (pc pc' : @ProgConfig GE) fp
        (Hstar : ETrace.tau_star (@glob_step GE) pc fp pc') :
      ThreadPool.next_tid (thread_pool pc') =
        ThreadPool.next_tid (thread_pool pc) /\
      forall other, other <> cur_tid pc ->
        ThreadPool.next_fmap (thread_pool pc') other =
        ThreadPool.next_fmap (thread_pool pc) other.
    Proof.
      induction Hstar.
      - split; [reflexivity | intros; reflexivity].
      - destruct (tau_glob_step_preserves_other_stacks _ _ _ H)
          as [Hcur_step _].
        destruct (tau_glob_step_preserves_pool_metadata _ _ _ H)
          as [Hnext_step Hfmap_step].
        destruct IHHstar as [Hnext_star Hfmap_star].
        split; [congruence |].
        intros other Hother.
        transitivity (ThreadPool.next_fmap (thread_pool s') other).
        + apply Hfmap_star. congruence.
        + apply Hfmap_step. exact Hother.
    Qed.

    (** Atomic call macros run with their selected thread as [cur_tid].  This
        adapter always prefixes one genuine global [Switch] step and then
        exposes the silent macro as an ordinary labelled star.  The rule
        permits [current = t], so no distinct-thread premise is required. *)
    Lemma switch_then_tau_star_is_star
        (tp tp' : @ThreadPool.t GE) current t gm gm' fp
        (Hvalid : ThreadPool.valid_tid tp t)
        (Hnot_halted : ~ ThreadPool.halted tp t)
        (Htau : ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm O) fp
          (Build_ProgConfig GE tp' t gm' O)) :
      exists labels,
        ETrace.star (@glob_step GE)
          (Build_ProgConfig GE tp current gm O)
          (ETrace.sw :: labels) fp
          (Build_ProgConfig GE tp' t gm' O).
    Proof.
      destruct (tau_star_is_star _ _ _ Htau) as [labels Hstar].
      exists labels.
      assert (Hswitch :
        glob_step
          (Build_ProgConfig GE tp current gm O)
          ETrace.sw FP.emp
          (Build_ProgConfig GE tp t gm O)).
      { eapply GlobSemantics.Switch; eauto. }
      assert (Hcombined :
        ETrace.star (@glob_step GE)
          (Build_ProgConfig GE tp current gm O)
          (ETrace.sw :: labels) (FP.union FP.emp fp)
          (Build_ProgConfig GE tp' t gm' O)).
      { econstructor; eauto. }
      rewrite FP.emp_union_fp in Hcombined.
      exact Hcombined.
    Qed.

    Corollary scheduled_tau_star_with_pool_preservation
        (tp tp' : @ThreadPool.t GE) current t gm gm' fp
        (Hvalid : ThreadPool.valid_tid tp t)
        (Hnot_halted : ~ ThreadPool.halted tp t)
        (Htau : ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm O) fp
          (Build_ProgConfig GE tp' t gm' O)) :
      exists labels,
        ETrace.star (@glob_step GE)
          (Build_ProgConfig GE tp current gm O)
          (ETrace.sw :: labels) fp
          (Build_ProgConfig GE tp' t gm' O) /\
        (forall other, other <> t ->
          ThreadPool.get_cs tp' other = ThreadPool.get_cs tp other) /\
        ThreadPool.next_tid tp' = ThreadPool.next_tid tp /\
        (forall other, other <> t ->
          ThreadPool.next_fmap tp' other =
            ThreadPool.next_fmap tp other).
    Proof.
      destruct (switch_then_tau_star_is_star tp tp' current t
        gm gm' fp Hvalid Hnot_halted Htau) as [labels Hstar].
      destruct (tau_star_preserves_other_stacks _ _ _ Htau)
        as [_ Hstacks].
      destruct (tau_star_preserves_pool_metadata _ _ _ Htau)
        as [Hnext Hfmap].
      exists labels. repeat split; assumption.
    Qed.

  End Scheduling.

  Section CallAndReturn.

    Context {GE : GlobEnv.t}.
    Variables caller_ix wrapper_ix : 'I_(GlobEnv.M GE).

    Local Definition caller_md : ModSem.t :=
      GlobEnv.modules GE caller_ix.
    Local Definition caller_lang : Language := ModSem.lang caller_md.
    Local Definition caller_ge : caller_lang.(G) := ModSem.Ge caller_md.

    Local Definition wrapper_md : ModSem.t :=
      GlobEnv.modules GE wrapper_ix.
    Local Definition wrapper_lang : Language := ModSem.lang wrapper_md.
    Local Definition wrapper_ge : wrapper_lang.(G) := ModSem.Ge wrapper_md.

    (** Enclose a complete wrapper macro in the genuine inter-module [Call]
        and [Return] rules.  In particular, this theorem records that the
        caller may use a different language instance from the wrapper: the
        marker filter is consulted only on the active wrapper frame. *)
    Theorem call_wrapper_macro_and_return
        (caller caller' : caller_lang.(core))
        (wrapper0 wrapper_final : wrapper_lang.(core))
        (tp tp_push : @ThreadPool.t GE) t caller_F caller_sg cs
        funid call_sg args gm0 gm1 res
        (Hcs : ThreadPool.get_cs tp t =
          Some (Core.Build_t caller_ix caller caller_sg caller_F :: cs))
        (Hat_call : at_external caller_lang caller_ge caller =
          Some (funid, call_sg, args))
        (Hnot_primitive : GAST.not_primitive funid)
        (Hget_mod : GlobEnv.get_mod GE funid = Some wrapper_ix)
        (Hinit : init_core wrapper_lang wrapper_ge funid args =
          Some wrapper0)
        (Hpush : ThreadPool.push tp t wrapper_ix wrapper0 call_sg =
          Some tp_push)
        (Hmacro :
          let wrapper_F := FLists.get_tfid (GlobEnv.freelists GE) t
            (ThreadPool.next_fmap tp t) in
          forall tp0,
            ThreadPool.get_cs tp0 t =
              Some (Core.Build_t wrapper_ix wrapper0 call_sg wrapper_F ::
                Core.Build_t caller_ix caller caller_sg caller_F :: cs) ->
            exists tp1 fp,
              ETrace.tau_star (@glob_step GE)
                (Build_ProgConfig GE tp0 t gm0 O) fp
                (Build_ProgConfig GE tp1 t gm1 O) /\
              ThreadPool.get_cs tp1 t =
                Some
                  (Core.Build_t wrapper_ix wrapper_final call_sg wrapper_F ::
                   Core.Build_t caller_ix caller caller_sg caller_F :: cs))
        (Hhalt : halt wrapper_lang wrapper_final = Some res)
        (Hafter : after_external caller_lang caller
          (res_sg call_sg res) = Some caller') :
      exists tp' fp,
        ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm0 O) fp
          (Build_ProgConfig GE tp' t gm1 O) /\
        ThreadPool.get_cs tp' t =
          Some (Core.Build_t caller_ix caller' caller_sg caller_F :: cs).
    Proof.
      assert (Htop : ThreadPool.get_top tp t =
        Some (Core.Build_t caller_ix caller caller_sg caller_F)).
      { unfold ThreadPool.get_top. rewrite Hcs. reflexivity. }
      assert (Hcall :
        glob_step (Build_ProgConfig GE tp t gm0 O) ETrace.tau FP.emp
          (Build_ProgConfig GE tp_push t gm0 O)).
      { eapply GlobSemantics.Call
          with (c := Core.Build_t caller_ix caller caller_sg caller_F)
               (funid := funid) (sg := call_sg) (args := args)
               (new_ix := wrapper_ix) (cc' := wrapper0); eauto. }
      unfold ThreadPool.get_cs in Hcs.
      unfold ThreadPool.push in Hpush.
      rewrite Hcs in Hpush.
      inversion Hpush; subst tp_push; clear Hpush.
      set (wrapper_F := FLists.get_tfid (GlobEnv.freelists GE) t
        (ThreadPool.next_fmap tp t)).
      assert (Hpush_cs :
        ThreadPool.get_cs
          (ThreadPool.Build_t
            (PMap.set t
              (Some
                (Core.Build_t wrapper_ix wrapper0 call_sg wrapper_F ::
                 Core.Build_t caller_ix caller caller_sg caller_F :: cs))
              (ThreadPool.content tp))
            (ThreadPool.next_tid tp)
            (fun i' =>
              if peq t i' then S (ThreadPool.next_fmap tp t)
              else ThreadPool.next_fmap tp i')) t =
        Some
          (Core.Build_t wrapper_ix wrapper0 call_sg wrapper_F ::
           Core.Build_t caller_ix caller caller_sg caller_F :: cs)).
      { unfold ThreadPool.get_cs. simpl. rewrite PMap.gss. reflexivity. }
      cbn zeta in Hcall.
      specialize (Hmacro _ Hpush_cs).
      destruct Hmacro as (tp_done & fp_macro & Hmacro_star & Hdone_cs).

      set (caller_top :=
        Core.Build_t caller_ix caller caller_sg caller_F).
      set (caller_top' :=
        Core.Build_t caller_ix caller' caller_sg caller_F).
      set (tp_pop := ThreadPool.Build_t
        (PMap.set t (Some (caller_top :: cs))
          (ThreadPool.content tp_done))
        (ThreadPool.next_tid tp_done) (ThreadPool.next_fmap tp_done)).
      set (tp_final := ThreadPool.Build_t
        (PMap.set t (Some (caller_top' :: cs))
          (ThreadPool.content tp_pop))
        (ThreadPool.next_tid tp_pop) (ThreadPool.next_fmap tp_pop)).

      assert (Hpop : ThreadPool.pop tp_done t = Some tp_pop).
      { unfold ThreadPool.pop, ThreadPool.get_cs in *.
        rewrite Hdone_cs. reflexivity. }
      assert (Hpop_cs :
        ThreadPool.get_cs tp_pop t = Some (caller_top :: cs)).
      { unfold ThreadPool.get_cs, tp_pop. simpl.
        rewrite PMap.gss. reflexivity. }
      assert (Hcaller_top : ThreadPool.get_top tp_pop t =
        Some caller_top).
      { unfold ThreadPool.get_top. rewrite Hpop_cs. reflexivity. }
      assert (Hcaller_update : Core.update caller_top caller' caller_top').
      { constructor. reflexivity. }
      assert (Hfinal_update :
        ThreadPool.update tp_pop t caller_top' tp_final).
      { econstructor.
        - exact Hpop_cs.
        - econstructor. exact Hcaller_update.
        - reflexivity. }
      assert (Hwrapper_top : ThreadPool.get_top tp_done t =
        Some (Core.Build_t wrapper_ix wrapper_final call_sg wrapper_F)).
      { unfold ThreadPool.get_top. rewrite Hdone_cs. reflexivity. }
      assert (Hreturn :
        glob_step (Build_ProgConfig GE tp_done t gm1 O)
          ETrace.tau FP.emp
          (Build_ProgConfig GE tp_final t gm1 O)).
      { eapply GlobSemantics.Return
          with
            (c := Core.Build_t wrapper_ix wrapper_final call_sg wrapper_F)
            (res := res) (thdp' := tp_pop) (c' := caller_top)
            (cc'' := caller') (c'' := caller_top').
        - exact Hwrapper_top.
        - exact Hhalt.
        - exact Hpop.
        - exact Hcaller_top.
        - exact Hafter.
        - exact Hcaller_update.
        - exact Hfinal_update. }
      assert (Hcall_star : exists fp,
        ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp t gm0 O) fp
          (Build_ProgConfig GE
            (ThreadPool.Build_t
              (PMap.set t
                (Some
                  (Core.Build_t wrapper_ix wrapper0 call_sg wrapper_F ::
                   Core.Build_t caller_ix caller caller_sg caller_F :: cs))
                (ThreadPool.content tp))
              (ThreadPool.next_tid tp)
              (fun i' =>
                if peq t i' then S (ThreadPool.next_fmap tp t)
                else ThreadPool.next_fmap tp i'))
            t gm0 O)).
      { exists (FP.union FP.emp FP.emp). econstructor; eauto. constructor. }
      assert (Hreturn_star : exists fp,
        ETrace.tau_star (@glob_step GE)
          (Build_ProgConfig GE tp_done t gm1 O) fp
          (Build_ProgConfig GE tp_final t gm1 O)).
      { exists (FP.union FP.emp FP.emp). econstructor; eauto. constructor. }
      destruct Hcall_star as (fp_call & Hcall_star).
      destruct Hreturn_star as (fp_return & Hreturn_star).
      pose proof (@ETrace.tau_star_star
        (@ProgConfig GE) (@glob_step GE) _ _ _ _ _
        Hcall_star Hmacro_star) as Hcall_macro.
      pose proof (@ETrace.tau_star_star
        (@ProgConfig GE) (@glob_step GE) _ _ _ _ _
        Hcall_macro Hreturn_star) as Hall.
      exists tp_final,
        (FP.union (FP.union fp_call fp_macro) fp_return).
      split; [exact Hall |].
      unfold ThreadPool.get_cs, tp_final. simpl.
      rewrite PMap.gss. reflexivity.
    Qed.

  End CallAndReturn.

End ClightAtomicGlobalSteps.
