From mathcomp.ssreflect Require Import fintype ssrnat.
Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import CUAST.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset DRF.

Require Import Languages.
Require Import TSOGlobSem GlobSemantics TSOGlobUSim
        RGRels ClientSim AsmClientSim ObjectSim.

Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.
Require Import InteractionSemantics.

Require Import SCSemLemmas TSOStepAuxLemmas TSOSemLemmas.

(** Lemmas.. *)
Lemma ordinal_eq_dec:
  forall M (i1 i2: 'I_M), {i1 = i2} + {i1 <> i2}.
Proof.
  destruct i1, i2.
  destruct (Nat.eq_dec m m0); subst; [left|right].
  f_equal. apply proof_irr.
  intro. inv H. auto.
Qed.

Lemma helper1:
  forall A: Type,
  forall P Q: A -> Prop,
    (exists (x: A), P x /\ (P x -> Q x)) ->
    (exists (x: A), P x /\ Q x).
Proof. clear. intros A P Q (x & HP & HQ). eauto. Qed.

Lemma helper2:
  forall A B: Type,
  forall P Q: A -> B -> Prop,
    (exists (x: A) (y: B), P x y /\ (P x y -> Q x y)) ->
    (exists (x: A) (y: B), P x y /\ Q x y).
Proof. clear. intros A B P Q (x & y & HP & HQ). eauto. Qed.

Require GDefLemmas.

Lemma unbuffer_safe_unbuffer:
  forall tm t,
    unbuffer_safe tm ->
    tso_buffers tm t <> nil ->
    unbuffer tm t <> None.
Proof.
  clear. intros. inv H. specialize (ABIS t). unfold unbuffer.
  destruct (tso_buffers tm t). contradiction.
  edestruct ABIS; eauto. rewrite H. intro; discriminate.
Qed.

Lemma tso_sc_initRel_Ic:
  forall SGE TGE sgm tgm,
    tso_sc_initRel SGE TGE sgm tgm ->
    Ic sgm (tsomem_init tgm).
Proof.
  unfold tsomem_init.
  constructor.
  { clear.  
    econstructor; simpl; intros; discriminate. }
  { intros. simpl in *. inv H2. inv H4. }
  { intros. simpl in *. inv H0. inv H; eauto. }
  { unfold buf_alloc_invalid. intros. simpl in *. auto. }
  { unfold buf_alloc_norep. simpl. intros. destruct j; inv H1. }
Qed.

Lemma ptree_set_reorder:
  forall A i j m (v1 v2:A),
    i <> j ->
    Maps.PTree.set i v1 (Maps.PTree.set j v2 m) =
    Maps.PTree.set j v2 (Maps.PTree.set i v1 m).
Proof. induction i;intros;destruct m,j;simpl;auto;try (rewrite IHi;auto;intro;subst);contradiction. Qed.

Lemma pmap_set_reorder:
  forall A i j m (v1 v2:A),
    i <> j ->
    Maps.PMap.set i v1 (Maps.PMap.set j v2 m) =
    Maps.PMap.set j v2 (Maps.PMap.set i v1 m).
Proof. unfold Maps.PMap.set;simpl;intros;f_equal. eapply ptree_set_reorder;eauto. Qed.

Lemma star_corestep_LocalAlloc:
  forall Lang Ge fl c m fp c' m',
    wd Lang ->
    star (step Lang Ge fl) c m fp c' m' ->
    LocalAlloc m m' fl.
Proof.
  clear. intros Lang Ge fl c m fp c' m' Hwd Hstep.
  induction Hstep. apply LocalAlloc_refl.
  eapply LocalAlloc_trans; eauto. apply step_local_eff in H; eauto. destruct H; eauto.
Qed.
(** end lemmas... *)



Section Invs.
  (* Compilation units of source/target client code *)
  Variable (scunits: @cunits NL L).
  Variable (tcunits: list AsmTSO.comp_unit).

  Inductive client_id : @cunits NL L ->
                        list AsmTSO.comp_unit -> Prop :=
  | client_cu_nil: client_id nil nil
  | client_cu_cons:
      forall cu scus tcus,
        client_id scus tcus ->
        nodup_gd_ident (cu_defs cu) = true ->
        nodup_ef (cu_defs cu) = true ->
        client_id ((Build_cunit NL L id1 cu) :: scus)
                  (cu :: tcus).

  Lemma client_id_cunit_eq:
    forall scunits tcunits x scu tcu,
      client_id scunits tcunits ->
      nth_error scunits x = Some {| lid := id1 ; cu := scu |} ->
      nth_error tcunits x = Some tcu ->
      scu = tcu.
  Proof.
    clear. unfold L. simpl. intros until 1. revert x scu tcu.
    induction H. destruct x; discriminate.
    destruct x. simpl. clear. unfold L, id1 in *. simpl in *. intros.
    assert (forall T (x y: T) , Some x = Some y -> x = y).
    { clear. intros. inv H. auto. }
    apply H1 in H. clear H1. inv H0. 
    assert (forall id cu1 cu2, Build_cunit _ L id cu1 = Build_cunit _ L id cu2 -> cu1 = cu2).
    { clear. intros. inversion H. apply Eqdep_dec.inj_pair2_eq_dec in H1; auto. apply ordinal_eq_dec. }
    apply H0 in H. auto.
    simpl. intros. eapply IHclient_id; eauto.
  Qed.

  Lemma client_id_nodup:
    forall scunits tcunits x scu,
      client_id scunits tcunits ->
      nth_error scunits x = Some {| lid := id1 ; cu := scu |} ->
      nodup_gd_ident (cu_defs scu) = true /\ nodup_ef (cu_defs scu) = true.
  Proof.
    clear. unfold L. simpl. intros until 1. revert x scu.
    induction H. destruct x; discriminate.
    destruct x. simpl. revert H0 H1. clear. unfold L, id1 in *. simpl in *. intros.
    assert (forall T (x y: T) , Some x = Some y -> x = y).
    { clear. intros. inv H. auto. }
    apply H2 in H. clear H2. 
    assert (forall id cu1 cu2, Build_cunit _ L id cu1 = Build_cunit _ L id cu2 -> cu1 = cu2).
    { clear. intros. inversion H. apply Eqdep_dec.inj_pair2_eq_dec in H1; auto. apply ordinal_eq_dec. }
    apply H2 in H. subst scu. auto.
    simpl. intros. eapply IHclient_id; eauto.
  Qed.

  Hypothesis (H_client_code: client_id scunits tcunits).

  (* object unit *)
  Variable (oscu: @cunit NL L).
  Variable (otcu: AsmTSO.comp_unit).
  
  Inductive objcu_sim (Ro Go: ASM_local.genv -> tid -> stRel) (Io: ASM_local.genv -> stInv):
    @cunit NL L -> AsmTSO.comp_unit -> Prop :=
  | Objcu_sim: forall (scu: SpecLang.comp_unit)
                 (tcu: AsmTSO.comp_unit),
      objectsim Ro Go Io SpecLang.speclang scu tcu ->
      objcu_sim Ro Go Io (Build_cunit NL L id2 scu) tcu.
  
  Variable (Ro Go: ASM_local.genv -> tid -> stRel).
  Variable (Io: ASM_local.genv -> stInv).
  
  Hypothesis (H_object_sim: objcu_sim Ro Go Io oscu otcu).
  Hypothesis (H_RP: RespectPerm Io Ro Go).
  
  (* Thread entries *)
  Variable (e: entries).

  (* constraints on rely/guarantees *)
  Hypothesis (H_sta_co: forall ge t, Sta Ic (Go ge t)).
  Hypothesis (H_sta_cc: forall t, Sta Ic (Gc t)).
  Hypothesis (H_sta_oc: forall ge t, Sta (Io ge) (Gc t)).
  Hypothesis (H_sta_oo: forall ge t, Sta (Io ge) (Go ge t)).

  Hypothesis (H_rg_cc: forall t t', Implies (Gc t) (Rc t')).
  Hypothesis (H_rg_oc: forall ge t t', Implies' Ic (Go ge t) (Rc t')).
  Hypothesis (H_rg_co: forall t ge t', t <> t' -> Implies' (Io ge) (Gc t) (Ro ge t')).
  Hypothesis (H_rg_oo: forall ge t t', t <> t' -> Implies (Go ge t) (Ro ge t')).

  Hypothesis (H_sta_c_ub: UBSta Ic).
  Hypothesis (H_sta_o_ub: forall ge, UBSta (Io ge)).
  Hypothesis (H_rg_ub_c: forall t, UBImplies Ic (Rc t)).
  Hypothesis (H_rg_ub_o: forall ge t, UBImplies (Io ge) (Ro ge t)).

  (** This section defines invariants on global environments *)
  Section GEInvs.
    
    Inductive mod_sim_client: ModSem.t -> ASM_local.genv -> Prop :=
    | Mod_sim_client:
        forall sge tge ms,
          @clientsim_properties Rc Gc Ic AsmLang sge sge tge ms ->
          mod_sim_client (ModSem.Build_t AsmLang sge sge) tge.
    Inductive mod_sim_object: ModSem.t -> ASM_local.genv -> Prop :=
    | Mod_sim_object:
        forall sge tge ms,
          @objectsim_properties Ro Go Io SpecLang.speclang sge sge tge ms ->
          mod_sim_object (ModSem.Build_t SpecLang.speclang sge sge) tge.

    (** TODO: i_obj property *)
    Inductive GE_mod_sim (M: nat) : 'I_M -> GlobEnv.t -> TSOGlobEnv.t -> Prop :=
    | GE_mod_sim_intro:
        forall i_obj get_mod get_mod' modules modules' bound fls,
          (forall fnid, get_mod' fnid = get_mod fnid) ->
          (forall i_x,
              ( mod_sim_client (modules i_x) (modules' i_x)
                /\ nat_of_ord i_x <> nat_of_ord i_obj )
              \/
              ( mod_sim_object (modules i_x) (modules' i_x)
                /\ i_x = i_obj )
          )->
          GE_mod_sim M
                     i_obj
                     (GlobEnv.Build_t M modules get_mod bound fls)
                     (TSOGlobEnv.Build_t M modules' get_mod' bound fls)
    .

    Lemma init_genvs_sim:
      forall SGE TGE sgm tgm spc tpc ts t,
        tso_sc_initRel SGE TGE sgm tgm ->
        init_config (oscu :: scunits, e) sgm SGE spc ts ->
        tso_initconfig (otcu :: tcunits, e) tgm TGE tpc t ->
        exists i_obj : 'I_(TSOGlobEnv.M TGE),
          GE_mod_sim _ i_obj SGE TGE.
    Proof.
      revert H_client_code H_object_sim. clear. intros.
      destruct SGE, TGE. simpl in *.
      inv H0. clear H3 H4 H5 H6 H7 H9 H10.
      inv H1. clear H3 H4 H5 H6 H7 H9 H10.
      simpl in *.
      exploit (@GlobEnv.mod_num NL L). eauto. simpl.
      exploit TSOGlobEnv.mod_num. eauto. simpl. intros.
      assert (M = M0).
      { revert H_client_code H1 H3. clear. intro H. revert M M0.
        induction H; intros; simpl in *. congruence.
        subst. f_equal. eauto. }
      exploit init_rel_ge_bound. eauto. simpl.
      exploit init_rel_freelists. eauto. simpl.
      pose proof (init_rel_ge_match _ _ _ _ H) as Hgenvmatch. simpl in *. revert Hgenvmatch.
      pose proof (init_rel_get_mod _ _ _ _ H) as Hgetmod. simpl in *. revert Hgetmod.
      intros. subst freelists0 ge_bound0.
      clear spc tpc H. subst.
      destruct H2. simpl in *. clear get_mod_init ge_wd mod_num.
      destruct H0. simpl in *. clear get_mod_init mod_num.
      revert get_mod modules get_mod0 modules0 ge_init ge_init0 Hgenvmatch Hgetmod.
      simpl. rewrite H4. intros.
      eexists (@Ordinal _ 0%nat _). Unshelve. 2: eauto.
      econstructor.
      (* get mod *)
      intro. destruct (Hgetmod fnid); auto.
      f_equal. destruct x, y. simpl in H. subst. assert (i = i0) by apply proof_irr. subst. auto.
      intros. specialize (ge_init i_x). specialize (ge_init0 i_x).
      (* modsim *)
      destruct ge_init as [scu [Hscu Hsinit]].
      destruct ge_init0 as [tcu [Htcu Htinit]].
      destruct i_x as [x I].
      clear get_mod get_mod0 Hgetmod. simpl in *.
      destruct x; [right|left].
      (* object sim *)
      simpl in *. inv Hscu. inv Htcu. split. inv Hsinit. 
      inv H_object_sim. simpl in *. revert H. unfold L. simpl. intro.
      inversion H0. subst. exploit H1. eauto. eauto.
      specialize (Hgenvmatch (Ordinal I) (Ordinal I)). simpl in *.
      rewrite <- H in Hgenvmatch. simpl in *. apply Hgenvmatch. auto.
      intros [ms Hsim]. econstructor; eauto.
      f_equal. apply proof_irr.
      (* client sim *)
      simpl in *. clear H_object_sim Ro Go Io oscu otcu e ge_bound freelists tgm H4.
      assert (lid L scu = id1).
      { revert Hscu H_client_code. clear. intros.
        apply nth_error_In in Hscu. clear x. revert scu Hscu. induction H_client_code.
        intros. inv Hscu.
        intros. inv Hscu. simpl. auto. auto. }
      destruct scu. simpl in H. subst lid. simpl in Hsinit.
      exploit client_id_cunit_eq; eauto. intro.
      exploit client_id_nodup; eauto. intros [? ?].
      split.
      inv Hsinit. simpl in *. unfold L. simpl.
      inv H3. pose proof (clientsim_hold tcu).
      exploit H; simpl. eauto. eauto. econstructor. 2: exact H4. eauto. exact Htinit. 
      specialize (Hgenvmatch (Ordinal I) (Ordinal I)). rewrite <- H2 in Hgenvmatch. simpl in *.
      eapply Hgenvmatch. auto.
      intros [ms Hsim].
      econstructor; eauto.
      intro. inv H2.
    Qed.
    
  End GEInvs.
  
  (** runtime module invariants *)
  Section RMInvs.
    Context {SGE: GlobEnv.t}.
    Context {TGE: TSOGlobEnv.t}.

    Inductive core_sim_client (iobj: 'I_(TSOGlobEnv.M TGE))
      : tid -> @Core.t SGE -> gmem -> @TSOCore.t TGE -> tsomem -> Prop :=
    | Core_sim_client: forall (t: tid) ix ix' sc tc ms sm tm sg flid
                         (H_clientlang: (ModSem.lang (GlobEnv.modules SGE ix)) = AsmLang),
        nat_of_ord ix' <> iobj ->
        @clientsim_properties
          Rc Gc Ic (ModSem.lang (GlobEnv.modules SGE ix))
          (ModSem.Ge (GlobEnv.modules SGE ix))
          (ModSem.ge (GlobEnv.modules SGE ix))
          (TSOGlobEnv.modules TGE ix')
          ms ->
        ms t (sc, sm) (tc, tm) ->
        core_sim_client iobj t (Core.Build_t ix sc sg flid) sm
                        (TSOCore.Build_t TGE ix' tc sg flid) tm.

    Inductive core_sim_object (iobj: 'I_(TSOGlobEnv.M TGE))
      :  tid -> @Core.t SGE -> gmem -> @TSOCore.t TGE -> tsomem -> Prop :=
    | Core_sim_object: forall t ix sc tc ms sm tm sg flid
                         (H_objectlang: (ModSem.lang (GlobEnv.modules SGE ix)) = SpecLang.speclang),
        @objectsim_properties
          Ro Go Io (ModSem.lang (GlobEnv.modules SGE ix))
          (ModSem.ge (GlobEnv.modules SGE ix))
          (ModSem.Ge (GlobEnv.modules SGE ix))
          (TSOGlobEnv.modules TGE iobj)
          ms ->
        ms t (sc, sm) (tc, tm) ->
        core_sim_object iobj t (Core.Build_t ix sc sg flid) sm
                        (TSOCore.Build_t TGE iobj tc sg flid) tm.
    
  End RMInvs.

  (** thread pool invariants *)
  Definition ThreadClientSim SGE TGE i_obj
             (sm: gmem) (tm: tsomem) (t: tid)
             (scs: @CallStack.t SGE) (tcs: list (@TSOCore.t TGE)) : Prop :=
    List.Forall2 (fun sc tc => core_sim_client i_obj t sc sm tc tm) scs tcs.

  Lemma ThreadClientSim_Sta_Gc:
    forall SGE TGE i_obj sm tm t scs tcs sm' tm' t'
      (Hsep: sep_obj_client_block sm'),
      Gc t' sm tm sm' tm' ->
      ThreadClientSim SGE TGE i_obj sm tm t scs tcs ->
      ThreadClientSim SGE TGE i_obj sm' tm' t scs tcs.
  Proof.
    intros. induction H0. constructor.
    constructor; auto.
    inv H0. econstructor; eauto.
    eapply ClientSim.match_rely; eauto.
    eapply H_rg_cc; eauto. 
  Qed.

  Lemma ThreadClientSim_Sta_Go:
    forall SGE TGE i_obj ge sm tm t scs tcs sm' tm' t'
      (Hsep: sep_obj_client_block sm'),
      Ic sm tm ->
      Go ge t' sm tm sm' tm' ->
      ThreadClientSim SGE TGE i_obj sm tm t scs tcs ->
      ThreadClientSim SGE TGE i_obj sm' tm' t scs tcs.
  Proof.
    intros. induction H1. constructor.
    constructor; auto.
    inv H1. econstructor; eauto.
    eapply ClientSim.match_rely; eauto.
    eapply H_rg_oc; eauto.
  Qed.

  Lemma ThreadClientSim_Sta_UB:
    forall SGE TGE i_obj sm tm t scs tcs sm' tm'
      (Hsep: sep_obj_client_block sm'),
      Ic sm tm ->
      G_ub sm tm sm' tm' ->
      ThreadClientSim SGE TGE i_obj sm tm t scs tcs ->
      ThreadClientSim SGE TGE i_obj sm' tm' t scs tcs.
  Proof.
    intros. induction H1. constructor.
    constructor; auto.
    inv H1. econstructor; eauto.
    eapply ClientSim.match_rely; eauto.
    eapply H_rg_ub_c; auto.
  Qed.

  Inductive ThreadSim SGE TGE iobj (sm: gmem) (tm: tsomem) (t: tid)
    : @CallStack.t SGE -> list (@TSOCore.t TGE) -> Prop :=
  | ThreadSimClient: forall scs tcs,
      ThreadClientSim SGE TGE iobj sm tm t scs tcs ->
      ThreadSim SGE TGE iobj sm tm t scs tcs
  | ThreadSimObject: forall sc scs tc tcs,
      core_sim_object iobj t sc sm tc tm ->
      ThreadClientSim SGE TGE iobj sm tm t scs tcs ->
      ThreadSim SGE TGE iobj sm tm t (sc :: scs) (tc :: tcs).
  
  Record ThreadSims SGE TGE iobj
         (stp: @ThreadPool.t SGE) (ttp: @TSOThrdPool.t TGE)
         (sm: gmem) (tm: tsomem) : Prop :=
    { 
      thread_simulation:
        forall t,
          option_rel
            (ThreadSim SGE TGE iobj sm tm t)
            (ThreadPool.get_cs stp t)
            (PMap.get t (TSOThrdPool.content ttp))
      ;

      tp_inv_src:
        ThreadPool.inv stp;
      
      valid_tid_eq:
        ThreadPool.next_tid stp = TSOThrdPool.next_tid ttp
      ;

      next_fmap_eq:
        forall t, ThreadPool.next_fmap stp t = TSOThrdPool.next_fmap ttp t
      ;
    }.
  
  Lemma ge_mod_sim_thdp_init_thrdsims:
    forall SGE TGE i_obj stp ttp sm tm,
      GE_mod_sim _ i_obj SGE TGE ->
      @ThreadPool.init SGE e stp ->
      @TSOThrdPool.init TGE e ttp ->
      GlobEnv.init_mem SGE sm ->
      TSOGlobEnv.init_mem TGE tm ->
      tso_sc_initRel SGE TGE sm tm ->
      ThreadSims SGE TGE i_obj stp ttp sm (tsomem_init tm).
  Proof.
    intros SGE TGE i_obj stp ttp sm tm GEMODSIM.
    destruct SGE, TGE. simpl in *.
    inv GEMODSIM; simpl.
    apply Eqdep.EqdepTheory.inj_pair2 in H3.
    apply Eqdep.EqdepTheory.inj_pair2 in H0.
    apply Eqdep.EqdepTheory.inj_pair2 in H7.
    apply Eqdep.EqdepTheory.inj_pair2 in H6.
    subst get_mod2 modules2 get_mod0 modules0. simpl in *.
    revert H10 H2. 
    intros H10 H2 STPINIT TTPINIT SINITMEM TINITMEM Hinitrel.
    exploit tso_sc_initRel_Ic. eauto. intro HIc.
    assert (get_mod' = get_mod).
    { apply functional_extensionality. auto. }
    subst get_mod'. clear H2. rename H10 into Hsim. 
    pose proof (Hsim i_obj). destruct H as [[_ H]|[H _]]; [congruence|].
    inv H. rename H0 into Hobj. 
    exploit match_initmem. eauto.
    inv SINITMEM. simpl in H. specialize (H i_obj). rewrite <-Hobj in H. eapply H.
    inv TINITMEM. simpl in H. specialize (H i_obj). eauto. eauto.
    intro HIo.
    revert stp ttp STPINIT TTPINIT. induction e.
    { intros. inv STPINIT; inv TTPINIT. econstructor; simpl.
      intros. unfold ThreadPool.get_cs. simpl. do 2 rewrite PMap.gi. constructor.
      apply ThreadPool.emp_inv. auto. auto. }
    { intros. inv STPINIT. inv TTPINIT. simpl in *.
      exploit IHe0. eauto. eauto.
      intro H. constructor.
      { unfold ThreadPool.spawn, TSOThrdPool.spawn. simpl.
        exploit valid_tid_eq. eauto. intro Hnext. rewrite Hnext.
        intro t. destruct (peq t (TSOThrdPool.next_tid thdp0)).
        { (* new core sim *)
          clear H. subst. unfold ThreadPool.get_cs; simpl. do 2 rewrite PMap.gss.
          constructor.
          exploit next_fmap_eq. eauto. intro Hfmap. rewrite Hfmap.
          rewrite H2 in H4. inv H4.
          destruct (ordinal_eq_dec _ m_id0 i_obj).
          { (* object core *)
            assert (exists ms, objectsim_properties Ro Go Io
                                               (ModSem.ge (modules i_obj)) (ModSem.Ge (modules i_obj))
                                               (modules' i_obj) ms).
            { rewrite <- Hobj. simpl. eauto. }
            destruct H as [ms' Hobjsim]. clear H1.
            subst m_id0. exploit match_init. eauto. eauto. intros (sc & Hinit & Hmatch).
            apply ThreadSimObject. econstructor. 
            simpl. rewrite <- Hobj. auto.
            simpl. eauto.
            assert (sc = cc). rewrite H5 in Hinit. inv Hinit. auto. subst sc.
            eapply Hmatch. auto. econstructor. }
          { (* client core *)
            pose proof (Hsim m_id0) as H. destruct H as [[H _] | [_ H]]; [|congruence].
            inv H.
            assert (exists ms0',  clientsim_properties Rc Gc Ic
                                                 (ModSem.Ge (modules m_id0)) (ModSem.ge (modules m_id0))
                                                 (modules' m_id0) ms0').
            { rewrite <- H0. simpl. eauto. }
            destruct H as [ms0' Hcltsim]. clear H4.
            exploit ClientSim.match_init. eauto. eauto. intros (sc & Hinit & Hmatch).
            apply ThreadSimClient. econstructor. econstructor.
            simpl. rewrite <- H0. auto.
            intro. apply n. revert H; clear. destruct m_id0, i_obj. simpl. intro.
            subst. f_equal. auto using proof_irr.
            eauto.
            assert (sc = cc). rewrite H5 in Hinit. inv Hinit. auto. subst sc.
            eapply Hmatch. auto.
            eapply init_rel_sgm_sep. eauto.
            constructor.
          }
        }
        { (* old core *)
          exploit thread_simulation. eauto. instantiate (1:= t).
          unfold ThreadPool.get_cs; simpl. rewrite PMap.gso; auto. rewrite PMap.gso; auto. }
      }
      { eapply ThreadPool.spawn_inv. eauto. inv H; auto. }
      { simpl. inv H. congruence. }
      { simpl. inv H. intro. specialize (next_fmap_eq0 t). rewrite next_fmap_eq0, valid_tid_eq0. auto. }
    }
  Qed.

  Lemma GE_mod_sim_source_lang_asm_or_spec:
    forall SGE TGE M i_obj,
      GE_mod_sim M i_obj SGE TGE ->
      forall ix, ModSem.lang (GlobEnv.modules SGE ix) = AsmLang \/
            ModSem.lang (GlobEnv.modules SGE ix) = SpecLang.speclang.
  Proof.
    clear. intros. inv H.
    destruct (H1 ix) as [[Hasm _]|[Hspec _]]; [inv Hasm|inv Hspec]; simpl; [left|right].
    rewrite <- H. auto.
    rewrite <- H. auto.
  Qed.
  
  (* TODO: move to ? *)
  Definition fl_valid_eq (t: tid) (fl: MemAux.freelist) (sm: gmem) (tm: tsomem) : Prop :=
    forall tgm', apply_buffer (tso_buffers tm t) (memory tm) = Some tgm' ->
            (forall b n, FLists.get_block fl n = b ->
                    GMem.valid_block sm b <-> GMem.valid_block tgm' b).

  Definition thread_buffered_alloc_local fls tm : Prop :=
    forall t b lo hi,
      In (BufferedAlloc b lo hi) (tso_buffers tm t) ->
      exists fn n,
        let fl := FLists.get_tfl fls t fn in
        b = FLists.get_block fl n.
  
  Record MS (SGE: GlobEnv.t) (TGE: TSOGlobEnv.t) (i_obj: 'I_(TSOGlobEnv.M TGE))
         (spc: @ProgConfig SGE) (tpc: @TSOProgConfig TGE): Prop :=
    {
      (* sc GlobEnv wd *)
      GE_wd:
        GlobEnv.wd SGE;
      (* GlobEnvs equiv *)
      GE_eq:
        GE_mod_sim (TSOGlobEnv.M TGE) i_obj SGE TGE;
      (* tid eq *)
      tid_eq:
        cur_tid spc = cid tpc;
      (* atomic bit is zero *)
      atom_bit_0:
        atom_bit spc = O;
      (* client memory invariant *)
      mem_inv_client:
        Ic (gm spc) (tm tpc);
      (* object memory invariant *)
      mem_inv_object:
        Io (TSOGlobEnv.modules TGE i_obj)
           (gm spc) (tm tpc);

      (* source config safe *)
      source_safe:
        safe_state glob_step GlobSemantics.abort spc;
      (* source config DRF *)
      source_drf:
        ~ star_race_config spc;
      
      (* thread pool related by local simulations *)
      thdp_sims:
        ThreadSims SGE TGE i_obj (thread_pool spc) (thrdpool tpc) (gm spc) (tm tpc);

      (* freelists are *)
      fls_embed:
        FLs_embed (TSOGlobEnv.freelists TGE) tpc.(tm)
      ;
      (* inv thdp *)
      inv_thdp:
        inv TGE (thrdpool tpc);
      (* buffered allocs in thread's freelists*)
      buffered_alloc_local:
        thread_buffered_alloc_local (TSOGlobEnv.freelists TGE) (tm tpc);

      (* fl valid eq *)
      fl_valid_match:
        forall t fn,
          let fl := FLists.get_tfl (TSOGlobEnv.freelists TGE) t fn in
          fl_valid_eq t fl (gm spc) (tm tpc)
      ;

      (* sep obj client block *)
      MS_sep_obj_client_blocks:
        sep_obj_client_block (gm spc)
      ;
      
    }.
  Lemma MS_tge_flwd:
    forall SGE TGE i spc tpc,
      MS SGE TGE i spc tpc ->
      FLists.wd (TSOGlobEnv.freelists TGE).
  Proof.
    destruct 1. destruct GE_wd0. inv GE_eq0. destruct TGE;simpl in *. inv H3. auto.
  Qed.
    
  Lemma apply_buffer_item_validity_eq_stable:
    forall b tm1 tm2 bi tm1' tm2',
      GMem.valid_block tm1 b <-> GMem.valid_block tm2 b ->
      apply_buffer_item bi tm1 = Some tm1' ->
      apply_buffer_item bi tm2 = Some tm2' ->
      GMem.valid_block tm1' b <-> GMem.valid_block tm2' b.
  Proof.
    clear. intros b tm1 tm2 bi tm1' tm2' Heq A B.
    destruct bi. 
    { (* alloc *)
      simpl in *. unfold alloc in *. simpl in *. inv A; inv B.
      unfold GMem.valid_block. simpl. tauto. }
    { simpl in *. unfold free in *.
      destruct range_perm_dec; inv A.
      destruct range_perm_dec; inv B.
      unfold unchecked_free; simpl. tauto. }
    { simpl in *. unfold store in *.
      destruct valid_access_dec; inv A. destruct valid_access_dec; inv B. tauto. }
  Qed.
  
  Lemma apply_buffer_validity_eq_stable:
    forall b tm1 tm2 buf tm1' tm2',
      GMem.valid_block tm1 b <-> GMem.valid_block tm2 b ->
      apply_buffer buf tm1 = Some tm1' ->
      apply_buffer buf tm2 = Some tm2' ->
      GMem.valid_block tm1' b <-> GMem.valid_block tm2' b.
  Proof.
    clear. intros b tm1 tm2 buf. revert tm1 tm2. induction buf.
    intros. inv H0; inv H1; tauto.
    intros tm1 tm2 tm2' tm1' Heq Happly2 Happly1.
    inv Happly1. inv Happly2.
    destruct (apply_buffer_item a tm1) eqn:A; [|discriminate].
    destruct (apply_buffer_item a tm2) eqn:B; [|discriminate].
    simpl in *. eapply IHbuf; try exact H1; try exact H0; clear H0 H1 IHbuf.
    eapply apply_buffer_item_validity_eq_stable; eauto.
  Qed.
      
  Lemma buffered_alloc_local_fl_valid_match_preserve_by_unbuffer:
    forall fls sm tm t tm',
      FLists.wd fls ->
      unbuffer_safe tm ->
      thread_buffered_alloc_local fls tm ->
      (forall t fn,
          let fl := FLists.get_tfl fls t fn in
          fl_valid_eq t fl sm tm) ->
      unbuffer tm t = Some tm' ->
      (forall t fn,
          let fl := FLists.get_tfl fls t fn in
          fl_valid_eq t fl sm tm').
  Proof.
    clear. intros fls sm tm t tm' Hwd HUBS Hbuffered_local Hvalid_eq Hunbuffer.
    intros. simpl in Hvalid_eq. specialize (Hvalid_eq t0 fn). subst fl.
    unfold unbuffer in Hunbuffer.
    destruct (peq t t0).
    { subst. destruct (tso_buffers tm t0) eqn:Hbuffer. discriminate.
      destruct (apply_buffer_item b (memory tm)) eqn:Happly; inv Hunbuffer.
      revert Hvalid_eq. unfold fl_valid_eq. intros.
      simpl in H. unfold tupdate in H. destruct peq;[|contradiction].
      rewrite Hbuffer in Hvalid_eq. simpl in Hvalid_eq.
      rewrite Happly in Hvalid_eq. simpl in Hvalid_eq.
      specialize (Hvalid_eq tgm' H b1 n H0). tauto. }
    { destruct (tso_buffers tm t) eqn:Hbuffer. discriminate.
      destruct (apply_buffer_item b (memory tm)) eqn: Happly; inv Hunbuffer.
      unfold tupdate. unfold fl_valid_eq in *. simpl; intros.
      destruct peq. congruence. clear n1.
      destruct tm as [bufs tgm].
      exploit TSOMemLemmas.unbuffer_safe_apply_buffer. eauto.
      instantiate (1:= t0). simpl in *. intros [tgm'' Happlybuf].
      specialize (Hvalid_eq tgm'' Happlybuf b1 n0 H0). rewrite Hvalid_eq.
      revert Happly H Happlybuf. intro.
      assert (GMem.valid_block g b1 <-> GMem.valid_block tgm b1).
      { destruct b. 
        { (* alloc *)
          exploit Hbuffered_local. simpl. rewrite Hbuffer. simpl. left. eauto.
          simpl. intros (fn' & n' & Hb).
          assert (b <> b1).
          { subst b b1. eapply FLists.flist_disj. eauto.
            eapply FLists.thread_fl_disj; eauto. }
          clear Hb H0.
          simpl in Happly. inv Happly. unfold GMem.valid_block. simpl.
          split; tauto.
        }
        { simpl in Happly. unfold free in Happly.
          destruct range_perm_dec; inv Happly. unfold unchecked_free; simpl. tauto. }
        { simpl in Happly. unfold store in Happly.
          destruct valid_access_dec; inv Happly. tauto. }
      }
      revert H. clear. generalize (bufs t0). clear.
      intros. eapply apply_buffer_validity_eq_stable; try exact H0; try exact Happlybuf. tauto.
    }
  Qed.
  
  Lemma abort_condition_abort:
    forall SGE spc ix sc sg flid scs,
      ThreadPool.get_cs (thread_pool spc) (cur_tid spc) =
      Some ({| Core.i := ix; Core.c := sc; Core.sg := sg; Core.F := flid |} :: scs) ->
      (forall FP sc' sm',
          ~ step (ModSem.lang (GlobEnv.modules SGE ix)) (ModSem.Ge (GlobEnv.modules SGE ix))
            (FLists.get_fl (GlobEnv.freelists SGE) flid) sc (gm spc) FP sc' sm') ->
      (at_external (ModSem.lang (GlobEnv.modules SGE ix)) (ModSem.Ge (GlobEnv.modules SGE ix)) sc = None) ->
      (forall ores, after_external (ModSem.lang (GlobEnv.modules SGE ix)) sc ores = None) ->
      (halt (ModSem.lang (GlobEnv.modules SGE ix)) sc = None) ->
      GlobSemantics.abort spc.
  Proof.
    clear. intros.
    split. intro. unfold ThreadPool.get_cs in H. inv H4. GDefLemmas.solv_thread. inv H6.
    intros. inv H4; auto; exfalso.
    { GDefLemmas.solv_thread'. simpl in *. eapply H0. eauto. }
    { GDefLemmas.solv_thread'. }
    { GDefLemmas.solv_thread'. }
    { GDefLemmas.solv_thread'. }
    { GDefLemmas.solv_thread'. }
    { GDefLemmas.solv_thread'. }
    { GDefLemmas.solv_thread'. }
  Qed.

  Lemma buffered_alloc_local_tm_alloc_not_fl:
    forall fls t fn tm,
      FLists.wd fls ->
      thread_buffered_alloc_local fls tm ->
      tm_alloc_not_fl tm (FLists.get_tfl fls t fn) t .
  Proof.
    clear. unfold thread_buffered_alloc_local, tm_alloc_not_fl.
    intros fls t fn tm WD H t' blk n lo hi Htid Hinbuffer.
    apply H in Hinbuffer. destruct Hinbuffer as [fn' [n' Hblk]].
    subst. inv WD. intro. eapply flist_disj.
    eapply thread_fl_disj. eauto. eauto.
  Qed.

  Inductive tso_client_step_fp
            (TGE: TSOGlobEnv.t)
            i_obj
            (tpc: @TSOProgConfig TGE)
            (fp: FP.t)
    : Prop :=
  | tso_client_step_intro : forall tC tcs tc' b' tm',
      (TSOThrdPool.content (thrdpool tpc)) !! (cid tpc) = Some (tC :: tcs) ->
      nat_of_ord (TSOCore.i tC) <> i_obj ->
      tsostep (TSOGlobEnv.modules TGE (TSOCore.i tC))
              (FLists.get_fl (TSOGlobEnv.freelists TGE) (TSOCore.F tC)) 
              (TSOCore.c tC) (tso_buffers (tm tpc) (cid tpc), memory (tm tpc))
              fp
              tc' (b', tm') ->
      tso_client_step_fp TGE i_obj tpc fp.
  
  Definition no_conflicting_client_fp
             (TGE: TSOGlobEnv.t) i_obj (tpc: @TSOProgConfig TGE) : Prop :=
    forall fp, tso_client_step_fp TGE i_obj tpc fp ->
          ~ conflictc (cid tpc) fp (tso_buffers (tm tpc)).

  (*
  Inductive client_core
            {SGE: GlobEnv.t}
            {TGE: TSOGlobEnv.t}
            (t: tid)
            (spc: @ProgConfig SGE) (tpc: @TSOProgConfig TGE): Prop :=
  | client_core_intro:
      forall (tC : TSOCore.t) (tcs : list TSOCore.t) 
        (sC : Core.t) (scs : list Core.t),
        (TSOThrdPool.content (thrdpool tpc)) !! t = Some (tC :: tcs) ->
        (ThreadPool.content (thread_pool spc)) !! t = Some (sC :: scs) ->
        core_sim_client t sC (gm spc) tC (tm tpc) ->
        client_core t spc tpc.
  *)  

  Inductive client_core
            (TGE: TSOGlobEnv.t)
            (i_obj: 'I_(TSOGlobEnv.M TGE))
            (t: tid)
            (tpc: @TSOProgConfig TGE)
    : Prop :=
  | client_core_intro: forall tC tcs,
      (TSOThrdPool.content (thrdpool tpc)) !! t = Some (tC :: tcs) ->
      nat_of_ord (TSOCore.i tC) <> i_obj ->
      client_core TGE i_obj t tpc.

  Lemma eq_config_eq_client_core:
    forall TGE i_obj t tpc tpc',
      eq_config TGE tpc tpc' ->
      client_core TGE i_obj t tpc ->
      client_core TGE i_obj t tpc'.
  Proof.
    clear. intros. destruct tpc, tpc'. 
    inv H0. inv H. simpl in *; subst.
    econstructor; eauto.
  Qed.

  Lemma client_core_dec:
    forall TGE i_obj tpc,
      {client_core TGE i_obj (cid tpc) tpc} +
      {~ client_core TGE i_obj (cid tpc) tpc}.
  Proof.
    clear. intros. destruct tpc. simpl.
    destruct ((TSOThrdPool.content thrdpool) !! cid) eqn:Hcs.
    destruct l. right. intro. inv H. simpl in *. congruence.
    destruct t. destruct (Nat.eq_dec i i_obj).
    right. intro. inv H. simpl in *. rewrite Hcs in H0. inv H0. simpl in *. apply H1. auto.
    left. econstructor; eauto.
    right. intro. inv H. simpl in *. congruence.
  Qed.
  
  Lemma match_fls_eq:
    forall SGE TGE iobj spc tpc,
      MS SGE TGE iobj spc tpc ->
      GlobEnv.freelists SGE = TSOGlobEnv.freelists TGE.
  Proof. intros. inv H. inv GE_eq0. simpl in *. rewrite <- H3. auto. Qed.

  Require AsmWD SpecLangWDDET.

  Lemma GE_mod_sim_source_lang_wd:
    forall SGE TGE M i_obj,
      GE_mod_sim M i_obj SGE TGE ->
      forall ix, mod_wd (GlobEnv.modules SGE ix).
  Proof.
    clear. unfold mod_wd. intros. eapply GE_mod_sim_source_lang_asm_or_spec in H.
    destruct H as [H|H]; simpl in *; rewrite H. 
    apply AsmWD.Asm_wd.
    apply SpecLangWDDET.SpecLang_wd.
  Qed.
  
  Lemma MS_src_step_gmem_forward:
    forall SGE TGE i_obj spc tpc l fp spc',
      MS SGE TGE i_obj spc tpc ->
      glob_step spc l fp spc' ->
      GMem.forward (gm spc) (gm spc').
  Proof.
    clear. intros. inv H0; try auto using GMem.forward_refl; simpl in *.
    apply GE_eq in H. eapply GE_mod_sim_source_lang_wd in H.
    eapply step_forward. eauto. eauto.
  Qed.

  Lemma MS_src_tau_star_step_gmem_forward:
    forall SGE TGE i_obj spc tpc fp spc',
      MS SGE TGE i_obj spc tpc ->
      tau_star glob_step spc fp spc' ->
      GMem.forward (gm spc) (gm spc').
  Proof.
    intros. exploit GE_eq; eauto. intro GE_EQ. pose proof (GE_mod_sim_source_lang_wd _ _ _ _ GE_EQ) as WD. 
    revert WD H0. clear. intros.
    induction H0; [auto using GMem.forward_refl| intros].
    eapply GMem.forward_trans; eauto.
    inv H; auto using GMem.forward_refl; simpl.
    eapply step_forward. eapply WD. eauto.
  Qed.
  
  Lemma MS_client_core_step_client_fp:
    forall SGE TGE i_obj spc tpc fp spc',
      MS SGE TGE i_obj spc tpc ->
      client_core TGE i_obj (cid tpc) tpc ->
      glob_step spc ETrace.tau fp spc' ->
      client_fp (gm spc) (gm spc') fp.
  Proof.
    clear. intros. exploit thdp_sims. eauto. intro Sims.
    inv H1; simpl; try (apply client_emp_fp; auto; fail).
    unfold ThreadPool.get_top in H_tp_core.
    destruct (ThreadPool.get_cs thdp t) eqn:H_cs; [|inv H_tp_core].
    destruct t0 as [|x cs]; inv H_tp_core. clear H_core_upd H_tp_upd.
    eapply thread_simulation in Sims. simpl in *. rewrite H_cs in Sims. inv Sims.
    inv H3.
    { inv H1. inv H5. simpl in *. apply MS_sep_obj_client_blocks in H.
      revert H H_core_step H_clientlang. clear.
      destruct (GlobEnv.modules SGE ix). simpl in *.
      generalize (FLists.get_fl (GlobEnv.freelists SGE) flid).
      intros fl Hsep H_core_step H_clientlang. subst lang.
      revert Hsep H_core_step. clear. intros Hsep Hstep.
      apply AsmLang_step_client_fp in Hstep; auto. tauto. }
    { inv H5. inv H0. simpl in *. erewrite <- tid_eq in H4; eauto.
      simpl in H4. rewrite H4 in H2. inv H2. simpl in *. congruence. }
  Qed.

  Lemma MS_client_core_step_obj_mem_eq:
    forall SGE TGE i_obj spc tpc fp spc',
      MS SGE TGE i_obj spc tpc ->
      client_core TGE i_obj (cid tpc) tpc ->
      glob_step spc ETrace.tau fp spc' ->
      (forall b ofs, obj_mem (gm spc) b ofs <-> obj_mem (gm spc') b ofs).
  Proof.
    clear. intros. exploit thdp_sims. eauto. intro Sims.
    inv H1; simpl; try (tauto; fail).
    unfold ThreadPool.get_top in H_tp_core.
    destruct (ThreadPool.get_cs thdp t) eqn:H_cs; [|inv H_tp_core].
    destruct t0 as [|x cs]; inv H_tp_core. clear H_core_upd H_tp_upd.
    eapply thread_simulation in Sims. simpl in *. rewrite H_cs in Sims. inv Sims.
    inv H3.
    { inv H1. inv H5. simpl in *. apply MS_sep_obj_client_blocks in H.
      revert H H_core_step H_clientlang. clear.
      destruct (GlobEnv.modules SGE ix). simpl in *.
      generalize (FLists.get_fl (GlobEnv.freelists SGE) flid).
      intros fl Hsep H_core_step H_clientlang. subst lang.
      revert Hsep H_core_step. clear. intros Hsep Hstep.
      apply AsmLang_step_client_fp in Hstep; auto.
      destruct Hstep as [_ [A _]]. rewrite A. tauto. }
    { inv H5. inv H0. simpl in *. erewrite <- tid_eq in H4; eauto.
      simpl in H4. rewrite H4 in H2. inv H2. simpl in *. congruence. }
  Qed.

  Lemma GE_mod_sim_source_step_sep_obj_clt_preserved:
    forall SGE TGE M i_obj (spc: @ProgConfig SGE) fp spc',
      GE_mod_sim M i_obj SGE TGE ->
      sep_obj_client_block (gm spc) ->
      glob_step spc ETrace.tau fp spc' ->
      sep_obj_client_block (gm spc').
  Proof.
    intros SGE TGE M i_obj spc fp spc' H H0 H1.
    inv H1; (try simpl; auto).
    pose proof (GE_mod_sim_source_lang_asm_or_spec _ _ _ _ H) as H'.
    revert H' H0 H_core_step; clear. destruct c; simpl in *. clear.
    intros H' H. specialize (H' i). revert H H'.
    generalize dependent (GlobEnv.modules SGE i). intros.
    destruct t. simpl in *. destruct H' as [Hasm|Hspec]; subst lang.
    eapply AsmLang_step_client_fp in H_core_step; tauto.
    eapply SpecLang_step_sep in H_core_step; auto.
  Qed.
  
  Lemma MS_source_step_sep_obj_clt_preserved:
    forall SGE TGE i_obj spc tpc fp spc',
      MS SGE TGE i_obj spc tpc ->
      glob_step spc ETrace.tau fp spc' ->
      sep_obj_client_block (gm spc').
  Proof.
    clear. intros SGE TGE i_obj spc tpc fp spc' H H0.
    eapply GE_mod_sim_source_step_sep_obj_clt_preserved in H0; inv H; eauto.
  Qed.

  Lemma MS_source_tau_star_step_sep_obj_clt_preserved:
    forall SGE TGE i_obj spc tpc fp spc',
      MS SGE TGE i_obj spc tpc ->
      tau_star glob_step spc fp spc' ->
      sep_obj_client_block (gm spc').
  Proof.
    clear. intros SGE TGE i_obj spc tpc fp spc' H.
    exploit GE_eq. eauto. intros HGE Hstar.
    apply MS_sep_obj_client_blocks in H. revert HGE Hstar H. clear. intros until 2.
    induction Hstar; eauto using GE_mod_sim_source_step_sep_obj_clt_preserved.
  Qed.
  
  Lemma MS_preserved_after_unbuffer:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      forall t tpc',
        tso_globstep tpc (ub t) FP.emp tpc' ->
        MS SGE TGE i_obj spc tpc'.
  Proof.
    intros SGE TGE i_obj spc tpc Hmatch t tpc' Hunbuffer.
    destruct spc. pose proof Hunbuffer as Hunbuffer'.
    inv Hunbuffer'. eapply (unbuffer_G_ub gm) in H_unbuf.
    { constructor; try (inv Hmatch; auto; fail); simpl in *.
      eapply H_sta_c_ub; eauto. inv Hmatch; auto.
      eapply H_sta_o_ub; eauto. inv Hmatch; auto.
      { exploit thdp_sims. eauto. simpl. intros.
        constructor; inv H; auto.
        intro. destruct (thread_simulation0 t1).
        constructor.
        constructor. inv H.
        eapply ThreadSimClient. eapply ThreadClientSim_Sta_UB; eauto. inv Hmatch; auto. inv Hmatch; auto.
        eapply ThreadSimObject. inv H0. econstructor; eauto.
        eapply ObjectSim.match_rely; eauto.
        eapply H_rg_ub_o; eauto. inv Hmatch; auto.
        eapply ThreadClientSim_Sta_UB; eauto. inv Hmatch; auto. inv Hmatch; auto.
      }
      exploit FLs_embed_preserved; eauto.
      inv Hmatch. simpl in *. inv GE_eq0. rewrite <- H3. inv GE_wd0. simpl in *. auto.
      inv Hmatch. eauto.
      { unfold thread_buffered_alloc_local. intros.
        inv Hunbuffer. unfold unbuffer in H_unbuf0.
        eapply buffered_alloc_local in Hmatch. eapply Hmatch. simpl.
        destruct (peq t t1). subst.
        destruct (tso_buffers tm t1); inv H_unbuf0.
        destruct apply_buffer_item; inv H1. simpl in H.
        unfold tupdate in H. destruct peq; [|contradiction].
        simpl. eauto.
        destruct (tso_buffers tm t); inv H_unbuf0.
        destruct apply_buffer_item; inv H1. simpl in H.
        unfold tupdate in H. destruct peq; [congruence|auto].
      }
      { (* fl_valid_eq *)
        eapply buffered_alloc_local_fl_valid_match_preserve_by_unbuffer.
        erewrite <- match_fls_eq; eauto. apply GlobEnv.wd_fl. eapply GE_wd. eauto.
        eapply Ic_unbuffer_safe. eapply mem_inv_client. eauto. 
        eapply buffered_alloc_local. eauto.
        intros. eapply fl_valid_match in Hmatch.  eauto.
        inv Hunbuffer. eauto.
      }
    }
  Qed.


  Lemma fl_valid_eq_rel_tm_gm_vb:
    forall t fl sm tm,
      fl_valid_eq t fl sm tm ->
      rel_tm_gm_vb sm tm fl t.
  Proof.
    clear. unfold fl_valid_eq, rel_tm_gm_vb. intros.
    specialize (H _ H1 _ _ H0). tauto.
  Qed.

  Local Hint Resolve fl_valid_eq_rel_tm_gm_vb.
  
  Lemma apply_buffer_app_split:
    forall buf1 buf2 tm tm',
      apply_buffer (buf1 ++ buf2) tm = Some tm' ->
      exists tm1,
        apply_buffer buf1 tm = Some tm1 /\
        apply_buffer buf2 tm1 = Some tm'.
  Proof.
    clear. induction buf1; intros; simpl in *; eauto.
    destruct (apply_buffer_item a tm); inv H. rewrite H1.
    apply IHbuf1 in H1. simpl in *. auto.
  Qed.
  
  Lemma fl_valid_eq_stable:
    forall fls t0 fn0 sm tm sm' bis tgm'
      (HUBS: unbuffer_safe tm)
      (HWD: FLists.wd fls)
      (H_fl_valid_eq: forall t fn,
          let fl := FLists.get_tfl fls t fn in
          fl_valid_eq t fl sm tm)
      (H_forward: GMem.forward sm sm')
      (H_src_new_block_in_fl: forall b,
          GMem.valid_block sm' b ->
          ~ GMem.valid_block sm b ->
          FLists.bbelongstof fls (FLists.get_tfid fls t0 fn0) b)
      (H_tgt_new_block_in_fl: forall b lo hi,
          In (BufferedAlloc b lo hi) bis ->
          FLists.bbelongstof fls (FLists.get_tfid fls t0 fn0) b)
      (H_eq_local: rel_tm_gm_vb sm' (tsoupd tm t0 (tso_buffers tm t0 ++ bis) tgm')
                                (FLists.get_tfl fls t0 fn0) t0)
      (H_eq_validity: GMem.validblocks tgm' = GMem.validblocks (memory tm)),
      (forall t fn,
          let fl := FLists.get_tfl fls t fn in
          fl_valid_eq t fl sm' (tsoupd tm t0 (tso_buffers tm t0 ++ bis) tgm')).
  Proof.
    clear. intros.
    destruct (peq t0 t).
    { (* t0 = t *)
      unfold fl_valid_eq. intros tgm'' Happly'.
      subst t0. destruct (Nat.eq_dec fn0 fn).
      { (* fn0 = fn *)
        subst fn0. intros. exploit H_eq_local. subst fl. eauto. simpl. eauto. tauto. }
      { (* fn0 <> fn *)
        intros b0 n0 Hb0.
        assert (forall b lo hi, In (BufferedAlloc b lo hi) bis -> b <> b0).
        { intros. apply H_tgt_new_block_in_fl in H.
          destruct H as [n' Hb]. subst b0 b fl.
          eapply FLists.flist_disj. eauto.
          eapply FLists.thread_fl_norep; eauto. }
        clear H_tgt_new_block_in_fl; rename H into H_tgt_new_block_in_fl.
        assert (forall b, GMem.valid_block sm' b -> ~ GMem.valid_block sm b -> b <> b0).
        { intros. exploit H_src_new_block_in_fl; eauto. intros [n' Hb].
          subst b b0. eapply FLists.flist_disj. eauto. eapply FLists.thread_fl_norep; eauto. }
        clear H_src_new_block_in_fl; rename H into H_src_new_block_in_fl.
        assert (GMem.valid_block sm' b0 <-> GMem.valid_block sm b0).
        { split. intro. destruct (in_dec peq b0 (GMem.validblocks sm)); auto.
          exploit H_src_new_block_in_fl. eauto. eauto. auto. contradiction. 
          eapply GMem.dom_forward; eauto. }
        clear H_src_new_block_in_fl. rewrite H. clear H.
        specialize (H_fl_valid_eq t fn). simpl in H_fl_valid_eq. unfold fl_valid_eq in *.
        unfold tsoupd in *. simpl in *. unfold tupdate in *. destruct peq;[|contradiction].
        assert (exists tgm1', apply_buffer (tso_buffers tm t) (memory tm) = Some tgm1').
        { destruct tm. simpl in *. eapply TSOMemLemmas.unbuffer_safe_apply_buffer. eauto. }
        destruct H as [tgm1' Happly1'].
        exploit apply_buffer_app_split. eauto. intros [tgm1 [Happly1 Happly2]].
        assert (GMem.valid_block tgm'' b0 <-> GMem.valid_block tgm1 b0).
        { revert Happly2 H_tgt_new_block_in_fl. clear. revert tgm1 tgm''.
          induction bis. simpl. intros. inv Happly2. tauto.
          simpl. intros. destruct (apply_buffer_item a tgm1) eqn:A; [simpl in Happly2|inv Happly2].
          erewrite IHbis; eauto. revert A H_tgt_new_block_in_fl. clear.
          destruct a; simpl in *.
          unfold alloc. inversion 1; subst. clear A. unfold GMem.valid_block. simpl. intros B.
          split; auto. intros. destruct H; auto. 
          exploit B; eauto. contradiction.
          unfold free, unchecked_free, GMem.valid_block. destruct range_perm_dec; inversion 1; simpl; tauto.
          unfold store, GMem.valid_block. destruct valid_access_dec; inversion 1; simpl; tauto. }
        rewrite H. clear H Happly2 H_tgt_new_block_in_fl Happly'.
        rewrite H_fl_valid_eq; try exact Happly1'; eauto. clear H_fl_valid_eq.
        eapply apply_buffer_validity_eq_stable; eauto. unfold GMem.valid_block. rewrite H_eq_validity. tauto.
      }
    }
    { (* t0 <> t *)
      clear H_tgt_new_block_in_fl H_eq_local.
      unfold fl_valid_eq in *. unfold tsoupd, tupdate. simpl. destruct peq; [congruence|].
      intros tgm'' Happly' b n' Hb.
      assert (exists tgm1', apply_buffer (tso_buffers tm t) (memory tm) = Some tgm1').
      { destruct tm. simpl in *. eapply TSOMemLemmas.unbuffer_safe_apply_buffer. eauto. }
      destruct H as [tgm1' Happly].
      specialize (H_fl_valid_eq t fn tgm1' Happly b n' Hb).
      assert (forall b0, GMem.valid_block sm' b0 -> ~ GMem.valid_block sm b0 -> b <> b0).
      { intros. exploit H_src_new_block_in_fl; eauto. intros [n0' Hb0].
        subst b b0. eapply FLists.flist_disj. eauto. eapply FLists.thread_fl_disj; eauto. }
      clear H_src_new_block_in_fl.
      assert (GMem.valid_block sm' b <-> GMem.valid_block sm b).
      { split. intro. destruct (in_dec peq b (GMem.validblocks sm)); auto.
        exploit H. eauto. eauto. auto. contradiction. 
        eapply GMem.dom_forward; eauto. }
      clear H. rewrite H0. rewrite H_fl_valid_eq. clear H0 H_fl_valid_eq.
      eapply apply_buffer_validity_eq_stable; eauto.
      unfold GMem.valid_block. rewrite H_eq_validity. tauto.
    }
  Qed.

  Lemma fl_valid_eq_stable':
    forall fls t0 fn0 sm tm sm' buf0' tgm'
      (HUBS: unbuffer_safe tm)
      (HWD: FLists.wd fls)
      (H_fl_valid_eq: forall t fn,
          let fl := FLists.get_tfl fls t fn in
          fl_valid_eq t fl sm tm)
      (H_forward: GMem.forward sm sm')
      (H_src_new_block_in_fl: forall b,
          GMem.valid_block sm' b ->
          ~ GMem.valid_block sm b ->
          FLists.bbelongstof fls (FLists.get_tfid fls t0 fn0) b)
      (H_step: exists ge c c' fp, tsostep ge (FLists.get_tfl fls t0 fn0)
                                  c (tso_buffers tm t0, memory tm) fp
                                  c' (buf0', tgm'))
      (H_eq_local: rel_tm_gm_vb sm' (tsoupd tm t0 buf0' tgm') (FLists.get_tfl fls t0 fn0) t0),
      (forall t fn,
          let fl := FLists.get_tfl fls t fn in
          fl_valid_eq t fl sm' (tsoupd tm t0 buf0' tgm')).
  Proof.
    intros. destruct H_step as (ge & c & c' & fp & H_step).
    exploit TSOAuxDefs.TSO_step_access_validity_preserve. eauto. intros [_ H_eq_validity].
    exploit tsostep_buffered_alloc_in_fl. eauto. intros [bis [Hbuffer' H_tgt_new_block_in_fl]].
    subst buf0'. eapply fl_valid_eq_stable; eauto.
  Qed.

  Lemma MS_preserved_after_ub_star:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      forall t tpc',
        ub_star TGE t tpc tpc' ->
        MS SGE TGE i_obj spc tpc'.
  Proof.
    intros. revert spc H. induction H0; auto.
    intros. eapply MS_preserved_after_unbuffer in H; eauto.
  Qed.

  Lemma MS_preserved_after_sw:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      forall tpc',
        tso_globstep tpc sw FP.emp tpc' ->
        exists spc', glob_step spc ETrace.sw FP.emp spc' /\
                MS SGE TGE i_obj spc' tpc'.
  Proof.
    intros SGE TGE i_obj spc tpc Hmatch tpc' Hswstep.
    destruct spc. pose proof Hswstep as Hswstep'. inv Hswstep'.
    inversion Hmatch. simpl in *. subst.
    eapply helper1.
    eexists. split. econstructor. exploit valid_tid_eq; eauto. intro A.
    unfold ThreadPool.valid_tid. rewrite A. eauto.
    intro. apply H_not_halted. exploit thread_simulation; eauto. instantiate (1:= t').
    intro A. inv A.
    inv H. congruence.
    inv H. unfold ThreadPool.get_cs in *. rewrite <- H0 in H3. inv H3. inv H4. inv H2. inv H.
    constructor. auto.
    intro Hsswstep.
    constructor; auto.
    (* safe *)
    intros ls fp s' Hstar'.
    eapply source_safe; eauto.
    eapply etrace_star_star; eauto. eapply ETrace.star_step. eauto. econstructor.
    (* drf *)
    intro.
    eapply source_drf; eauto. destruct H as (ls & fp & s' & Hstar' & RACE).
    econstructor. eexists _, s'. split; auto.
    eapply etrace_star_star; eauto. eapply ETrace.star_step. eauto. econstructor.
  Qed.

  Lemma MS_tm_alloc_not_fl:
    forall SGE TGE i_obj spc tpc t fn,
      MS SGE TGE i_obj spc tpc ->
      tm_alloc_not_fl (tm tpc)
                      (FLists.get_tfl (TSOGlobEnv.freelists TGE) t fn) t.
  Proof.
    clear. intros SGE TGE i_obj spc tpc t fn MATCH.
    unfold tm_alloc_not_fl. intros t' blk n lo hi Hteq Hbi.
    exploit buffered_alloc_local; eauto. intros (fn' & n' & Hblk). simpl in Hblk.
    rewrite Hblk. unfold FLists.get_tfl, FLists.get_tfid.
    unfold MemAux.get_block, FLists.get_block. clear Hblk.
    erewrite <- match_fls_eq; eauto.
    exploit GE_wd. eauto. intros WD. apply GlobEnv.wd_fl in WD.
    eapply FLists.thread_fl_disj in Hteq; eauto.
    intro C. eapply FLists.flist_disj; eauto.
  Qed.
        
  Lemma MS_preserved_after_tau_non_conflicting_client_step:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      forall tpc' fp,
        tso_globstep tpc tau fp tpc' ->
        client_core TGE i_obj (cid tpc) tpc ->
        ~ conflictc (cid tpc) fp (tso_buffers (tm tpc)) ->
        exists FP spc',
          glob_step spc ETrace.tau FP spc' /\
          fpmatchc FP fp /\
          MS SGE TGE i_obj spc' tpc'.
  Proof.
    intros SGE TGE i_obj spc tpc Hmatch tpc' fpT' Htsostep.
    exploit match_fls_eq; eauto. intro Hflseq.
    pose proof Htsostep as Htsostep'. inv Htsostep'. 
    (* module tau step *)
    { destruct spc.
      exploit tid_eq; eauto. simpl. intro; subst cur_tid.
      exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
      exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
      instantiate (1:= t) in Htsim. simpl in *.
      rewrite H_tp_core in Htsim.
      inv Htsim. inv H1.
      (* client step *)
      { intros _. inv H0. inv H4. pose proof H2 as Hcmatch.
        eapply ClientSim.match_tau in H2; eauto.
        destruct H2 as [STEP|ABORT].
        (* sc step *)
        { destruct STEP as (tfp & sc' & sm' & Hstep & 
                            [(Hnonconflict & Hfp & HGc & Hmatch' & Halloc & Hvalideq)|
                             (Hconflict & Hfp)]);
          [intros _ | contradiction].
          (* non-conflicting footprint *)
          { eexists. simpl in *. rewrite <- Hflseq in Hstep.
            exploit core_step_globstep; eauto.
            intros (thread_pool' & Hgstep & Hthdpupd).
            exists {|thread_pool := thread_pool';
                cur_tid := t;
                gm := sm';
                atom_bit := O |}.
            split. eauto.
            split. eauto.
            (* match after step *)
            constructor; auto; simpl in *; try (inv Hmatch; eauto; fail).
            eapply H_sta_cc; eauto. destruct Hmatch; auto.
            eapply H_sta_oc; eauto. destruct Hmatch; auto.
            intros ls fp s' Hstar'. eapply source_safe; eauto. eapply ETrace.star_step; eauto.
            intro. eapply source_drf; eauto. destruct H2 as (ls & fp & s' & Hstar' & RACE).
            do 3 eexists. split;[eapply ETrace.star_step; eauto|auto].
            (* thread sims... *)
            { inv Hthdpupd. inv H3. inv H4. inv H3. apply Eqdep_dec.inj_pair2_eq_dec in H7. subst.
              rewrite H2 in H; inv H. 
              constructor.
              { intro. unfold ThreadPool.get_cs. simpl.
                inv H_tp_upd. inv H_core_upd. simpl in *.
                destruct (peq t t0).
                (* case: t = t0 *)
                { subst t0. simpl in *. do 2 rewrite PMap.gss.
                  constructor. eapply ThreadSimClient.
                  constructor.
                  econstructor; eauto.
                  eapply ThreadClientSim_Sta_Gc; eauto.
                  
                  eapply GE_mod_sim_source_step_sep_obj_clt_preserved in Hgstep. eauto.
                  eapply GE_eq. eauto.
                  eapply MS_sep_obj_client_blocks. eauto.
                  
                  rewrite H_tp_core in H. inv H. auto.
                }
                (* case: t <> t0 *)
                { do 2 (rewrite PMap.gso; eauto).
                  exploit thdp_sims; eauto. intro Htpsim.
                  exploit thread_simulation; eauto. intro Htsim. instantiate (1:= t0) in Htsim.
                  simpl in *. inv Htsim; unfold ThreadPool.get_cs, CallStack.t in *.
                  rewrite <- H6. constructor.
                  rewrite <- H3. constructor.
                  inv H7.
                  eapply ThreadSimClient.
                  eapply ThreadClientSim_Sta_Gc; eauto.

                  eapply GE_mod_sim_source_step_sep_obj_clt_preserved in Hgstep. eauto.
                  eapply GE_eq. eauto.
                  eapply MS_sep_obj_client_blocks. eauto.
                  
                  rewrite H_tp_core in H. inv H. auto.
                  
                  eapply ThreadSimObject.
                  inv H8. econstructor; eauto. eapply ObjectSim.match_rely; eauto.
                  eapply H_rg_co; eauto. eapply mem_inv_object in Hmatch; eauto.
                  eapply ThreadClientSim_Sta_Gc; eauto.

                  eapply GE_mod_sim_source_step_sep_obj_clt_preserved in Hgstep. eauto.
                  eapply GE_eq. eauto.
                  eapply MS_sep_obj_client_blocks. eauto.
                }
              }
              { eapply ThreadPool.upd_top_inv.
                destruct Hmatch. destruct thdp_sims0. eauto.
                simpl. unfold ThreadPool.get_top. rewrite H2. simpl. eauto.
                econstructor; eauto. simpl. econstructor; eauto.
                econstructor; eauto. econstructor; eauto.
              }
              { inv H_tp_upd. simpl. exploit thdp_sims; eauto. destruct 1. auto. }
              { inv H_tp_upd. simpl. exploit thdp_sims; eauto. destruct 1. auto. }
              apply ordinal_eq_dec.
            }
            (* fl embed... *)
            { exploit FLs_embed_preserved; try (inv Hmatch; eauto; fail).
              erewrite <- match_fls_eq; eauto. apply GlobEnv.wd_fl. eapply GE_wd; eauto. }
            (* inv thdp *)
            {
              eapply glob_step_inv_preserve in Htsostep;eauto.
              eapply MS_tge_flwd;eauto.
              eapply inv_thdp;eauto.
            }
            (* buffered alloc local *)
            { exploit tsostep_buffered_alloc_in_fl. eauto.
              symmetry in H. eapply ThreadPool.cs_inv in H. eapply ThreadPool.fid_belongsto in H; [|simpl; eauto].
              revert H Hmatch. clear. simpl; intros H Hmatch (tail & Hbuffer & Hbufalloc) t0 b lo hi H0.
              subst buf'. simpl in *. unfold tupdate in H0. destruct (peq t0 t).
              subst. simpl in *. eapply in_app in H0. destruct H0.
              eapply buffered_alloc_local; eauto.
              destruct H as [fn H]. 
              apply Hbufalloc in H0. destruct H0 as [n H0].
              exists fn, n. subst flid. unfold FLists.get_tfl. erewrite <- match_fls_eq in *; eauto. 
              eapply buffered_alloc_local; eauto.
              eapply tp_inv_src. eapply thdp_sims in Hmatch; eauto. }
            (* fl_valid_eq *)
            { exploit (@ThreadPool.fid_belongsto SGE).
              eapply ThreadPool.cs_inv. eapply tp_inv_src. eapply thdp_sims. eauto. simpl. eauto. simpl; left; eauto.
              intros [fn Hflid]. simpl in Hflid.
              eapply fl_valid_eq_stable'; eauto.
              eapply Ic_unbuffer_safe. eapply mem_inv_client in Hmatch. eauto.
              erewrite <- match_fls_eq; eauto.
              apply GlobEnv.wd_fl. eapply GE_wd. eauto.
              intros. eapply fl_valid_match in Hmatch. simpl in Hmatch. eauto.
              exploit MS_src_step_gmem_forward; eauto.
              exploit step_local_eff; eauto. eapply GE_mod_sim_source_lang_wd. eapply GE_eq. eauto.
              intros [_ Hnewblock]. intros. subst flid. erewrite <- match_fls_eq; eauto.
              eapply Hnewblock; eauto.
              subst flid. simpl in *. erewrite match_fls_eq in H_core_step; eauto.
              unfold tsoupd. subst flid. erewrite match_fls_eq in Hvalideq; eauto.
            }
            (* sep obj client block *)
            eapply MS_source_step_sep_obj_clt_preserved in Hgstep; eauto. 
          }
        }
        (* sc abort *)
        { intros _. exfalso.
          eapply source_safe. eauto. eapply ETrace.star_refl.
          split. 
          (* thread not halted *)
          revert H; clear. intros.
          simpl. intro. inv H0. rewrite H1 in H. inv H. inv H2.
          (* no glob step except for sw *)
          erewrite <- match_fls_eq in ABORT; eauto. simpl in *.
          assert (Hnatext: at_external (ModSem.lang (GlobEnv.modules SGE ix))
                                       (ModSem.Ge (GlobEnv.modules SGE ix))
                                       sc
                           = None).
          { apply thdp_sims in Hmatch. apply thread_simulation with (t0 := t) in Hmatch; simpl in Hmatch.
            rewrite <- H, H_tp_core in Hmatch. inv Hmatch.
            erewrite <- ClientSim.match_at_external; eauto.
            eapply tsostep_not_atext; eauto.
          }
          assert (Hnhalt: halt (ModSem.lang (GlobEnv.modules SGE ix)) sc = None).
          { apply thdp_sims in Hmatch. apply thread_simulation with (t0 := t) in Hmatch; simpl in Hmatch.
            rewrite <- H, H_tp_core in Hmatch. inv Hmatch.
            erewrite <- ClientSim.match_halted; eauto.
            eapply tsostep_not_halted; eauto. }
          intros.
          { inv H2; auto; exfalso.
            { (* tau step *)
              GDefLemmas.solv_thread. eapply ABORT. eauto.
            }
            all: GDefLemmas.solv_thread; simpl in *; try congruence;
              rewrite <- H in *; simpl in *;
                GDefLemmas.solv_thread; simpl in *; try congruence.
          }
        }
        { (* tm_alloc_not_fl *)
          exploit (@ThreadPool.fid_belongsto SGE).
          eapply ThreadPool.cs_inv. eapply tp_inv_src. eapply thdp_sims. eauto. simpl. eauto. simpl; left; eauto.
          intros [fn Hflid]. simpl in Hflid. subst flid. simpl in *.
          intros t' blk n lo hi Hneq Hinbuffer C.
          exploit MS_tm_alloc_not_fl; eauto.
          erewrite match_fls_eq in C; eauto.
        }
        { (* rel_tm_gm_vb *)
          exploit (@ThreadPool.fid_belongsto SGE).
          eapply ThreadPool.cs_inv. eapply tp_inv_src. eapply thdp_sims. eauto. simpl. eauto. simpl; left; eauto.
          intros [fn Hflid]. simpl in Hflid. subst flid. simpl in *.
          eapply fl_valid_eq_rel_tm_gm_vb. simpl. erewrite match_fls_eq; eauto.
          inv Hmatch; eauto.
        }
      }
      (* object step *)
      { revert H4 H_tp_core. clear. intros Hsimobj ? Hclient. exfalso.
        inv Hclient. simpl in *. rewrite H_tp_core in H. inv H.
        inv Hsimobj. simpl in *. congruence. }
    }
    (* call *)
    { destruct spc.
      exploit tid_eq; eauto. simpl. intro; subst cur_tid.
      exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
      exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
      instantiate (1:=t) in Htsim. simpl in *. rewrite H_tp_core in Htsim.
      inv Htsim. inv H1.
      { (* client call *)
        inv H0. inv H4. pose proof H2 as Hcmatch.
        eapply ClientSim.match_at_external in H2; eauto.
        exploit GE_eq. eauto. intro A. simpl in *.
        destruct SGE, TGE. inv A. simpl in *.
        repeat match goal with
               | H: existT _ _ ?x = existT _ _ ?y |- _ =>
                 apply Eqdep.EqdepTheory.inj_pair2 in H; subst
               end.
        assert (exists ms_new sc_new,
                     let: G_new := ModSem.Ge (modules new_ix) in
                     let: ge_new := ModSem.ge (modules new_ix) in
                     ((clientsim_properties Rc Gc Ic G_new ge_new (modules0 new_ix) ms_new
                       /\ nat_of_ord new_ix <> i_obj /\ ModSem.lang (modules new_ix) = AsmLang)
                      \/
                      (objectsim_properties Ro Go Io ge_new G_new (modules0 new_ix) ms_new
                       /\ new_ix = i_obj /\ ModSem.lang (modules new_ix) = SpecLang.speclang)
                     )
                     /\ init_core (ModSem.lang (modules new_ix)) G_new funid args = Some sc_new
                     /\ ms_new t (sc_new, gm) (cc', tm))
            as (ms_new & sc_new & Hnewcore_sim & Hinit_new & Hms_new).
        { destruct (H15 new_ix) as [[Hcsim Hmodid]|[Hosim Hmodid]].
            (* client module *)
            inv Hcsim. exploit ClientSim.match_init; eauto.
            intros (sc_new & Hinit_new & Hms_new).
            exploit (Hms_new t gm tm). inv Hmatch. auto. inv Hmatch. auto. clear Hms_new; intro Hms_new.
            simpl. exists ms0, sc_new. split; auto.
            (* object module *)
            inv Hosim. exploit ObjectSim.match_init; eauto.
            intros (sc_new & Hinit_new & Hms_new).
            exploit (Hms_new t gm tm). inv Hmatch. auto. clear Hms_new; intro Hms_new.
            simpl. exists ms0, sc_new. split; auto. }
        intros _ _.
        do 2 eexists. match goal with |- ?A /\ ?B => assert A end.
        eapply Call; simpl; eauto.
        unfold ThreadPool.get_top. rewrite <- H. simpl. eauto.
        simpl. rewrite <- H2. eauto.
        rewrite <- H_mod_id. eauto.
        unfold ThreadPool.push, ThreadPool.get_cs in *. rewrite <- H. eauto.
        split. auto.
        split. apply FP.subset_refl.
        (* match after call step *)
        { simpl. constructor; simpl; try (inv Hmatch; auto; fail).
          (* safe *)
          intros ls fp s' Hstar'.
          eapply source_safe; eauto.
          eapply ETrace.star_step. eauto. eauto.
          (* drf *)
          intro.
          eapply source_drf; eauto. destruct H4 as (ls & fp & s' & Hstar' & RACE).
          econstructor. eexists _, s'. split; auto. eapply ETrace.star_step; eauto.
          (* thread sims... *)
          { constructor.
            { intro. unfold ThreadPool.get_cs. simpl.
              unfold TSOThrdPool.push in *. rewrite H_tp_core in H_tp_push. inv H_tp_push. simpl in *.
              destruct (peq t t0).
              (* case: t = t0 *)
              { subst t0. simpl in *. do 2 rewrite PMap.gss.
                unfold CallStack.push. 
                constructor. destruct Hnewcore_sim as [[Hnewcore_csim [Hix_new Hlang]]|[Hnewcore_osim [Hix_new Hlang]]].
                (* case: client module *)
                eapply ThreadSimClient.
                constructor.
                erewrite next_fmap_eq. econstructor; eauto.  inv Hmatch; eauto.
                simpl in *.
                constructor; auto.
                econstructor; eauto.
                (* case: object module *)
                eapply ThreadSimObject.
                erewrite next_fmap_eq. subst. econstructor; eauto. inv Hmatch; eauto.
                constructor; auto.
                econstructor; eauto.
              }
              (* case: t <> t0 *)
              { do 2 (rewrite PMap.gso; eauto).
                exploit thdp_sims; eauto. intro Htpsim.
                exploit thread_simulation; eauto. 
              }
            }

            eapply ThreadPool.push_inv;(try (inv Hmatch; eauto; fail)).
            apply thdp_sims in Hmatch. apply tp_inv_src in Hmatch. eauto.
            simpl. unfold ThreadPool.push, ThreadPool.get_cs in *. rewrite <- H. eauto.
            simpl. unfold TSOThrdPool.push in H_tp_push. GDefLemmas.solv_thread.
            apply thdp_sims in Hmatch. eapply valid_tid_eq; eauto.
            simpl. unfold TSOThrdPool.push in H_tp_push. GDefLemmas.solv_thread.
            intro. apply thdp_sims in Hmatch.
            (erewrite next_fmap_eq; eauto). simpl.
            (erewrite next_fmap_eq; eauto). simpl. 
            rewrite Nat.add_1_r. auto.
          }
          (* inv thdp *)
          {
            eapply glob_step_inv_preserve in Htsostep;eauto.
            eapply MS_tge_flwd;eauto.
            eapply inv_thdp;eauto.
          }
        }
      }
      { (* object call - impossible case *)
        intro. exfalso. inv H0. inv H4. apply H2.
        simpl in H1. rewrite H_tp_core in H1. inv H1. simpl. auto.
      }
    }
    (* return *)
    { destruct spc.
      exploit tid_eq; eauto. simpl. intro; subst cur_tid.
      exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
      exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim; instantiate (1:=t) in Htsim.
      simpl in *. rewrite H_tp_core in Htsim.
      inv Htsim. inv H1.
      (* client return *)
      {
        (* callee return *)
        inv H0. inv H4. 
        exploit ClientSim.match_halted; eauto. intro Hhalt. simpl in *. rewrite H_core_halt in Hhalt.
        (* caller after external *)
        inv H5. inv H7. 
        exploit ClientSim.match_after_external. exact H4. exact H5. eauto.
        intros (sc0' & Haftext & Hcmatch_caller'). simpl in *.
        clear H2.
        (* cosntruct glob step *)
        intros _ _. apply helper2. do 2 eexists. split.
        eapply Return; simpl in *; eauto.
        unfold ThreadPool.get_top. rewrite <- H. simpl. eauto.
        simpl. eauto.
        unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
        unfold ThreadPool.get_top, ThreadPool.get_cs. simpl. rewrite PMap.gss.
        simpl. eauto.
        simpl. eauto.
        econstructor; eauto.
        econstructor; eauto.
        unfold ThreadPool.get_top, ThreadPool.get_cs. simpl. rewrite PMap.gss. eauto.
        simpl. econstructor; eauto. econstructor. eauto.
        simpl.
        intro Hglobtaustep.
        split. apply FP.subset_refl.
        (* match after tau step *)
        { constructor; try (inv Hmatch; eauto; fail).
          (* safe *)
          intros ls fp s' Hstar'. 
          eapply source_safe; eauto. eapply ETrace.star_step; eauto. 
          (* drf *)
          intro.
          eapply source_drf; eauto. destruct H2 as (ls & fp & s' & Hstar' & RACE).
          econstructor. eexists _, s'. split; auto. eapply ETrace.star_step; eauto.
          (* thread sims... *)
          { constructor.
            { intro. unfold ThreadPool.get_cs. simpl.
              unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. inv H_tp_pop. simpl in *.
              inv H_tp_upd; simpl in *.
              destruct (peq t t0).
              (* case: t = t0 *)
              { subst t0. simpl in *. repeat rewrite PMap.gss in *. inv H2.
                constructor. 
                eapply ThreadSimClient.
                constructor. inv H_core_upd. simpl. econstructor; eauto.
                inv H4. auto. 
              }
              (* case: t <> t0 *)
              { do 4 (rewrite PMap.gso; eauto).
                exploit thdp_sims; eauto. intro Htpsim.
                exploit thread_simulation; eauto. 
              }
            }
            (* tp inv *)
            exploit (@ThreadPool.pop_inv SGE).
            inv Hmatch; eapply tp_inv_src; eauto. simpl.
            unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
            simpl. intro. eapply thdp_inv_upd; eauto.
            econstructor. unfold ThreadPool.get_cs; simpl. rewrite PMap.gss. eauto.
            econstructor. econstructor. eauto. simpl. eauto.
            (* tp next tid *)
            simpl. inv H_tp_upd. unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. 
            inv H_tp_pop. simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
            (* next fmap *)
            intro. 
            inv H_tp_upd. unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. 
            inv H_tp_pop. simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
          }
          (* inv thdp *)
          {
            eapply glob_step_inv_preserve in Htsostep;eauto.
            eapply MS_tge_flwd;eauto.
            eapply inv_thdp;eauto.
          }
        }
      }
      (* object return *)
      { intro Hclient. exfalso. inv Hclient; inv H4. simpl in *.
        rewrite H0 in H_tp_core. inv H_tp_core. simpl in *. auto. }
    }
    (* thread halt *)
    { destruct spc.
      exploit tid_eq; eauto. simpl. intro; subst cur_tid.
      exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
      exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
      instantiate (1:=t) in Htsim. simpl in *. rewrite H_tp_core in Htsim.
      inv Htsim. intros Hclient _. apply helper2.
      inv H1.
      (* client halt *)
      { inv H0. inv H4. inv H5. eexists _, _. split.
        eapply Halt.
        unfold ThreadPool.get_top, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
        erewrite <- ClientSim.match_halted; eauto.
        unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
        econstructor. unfold ThreadPool.get_cs. simpl. rewrite PMap.gss. eauto. constructor.
        intros Hglobtaustep.
        split. apply FP.subset_refl.
        { constructor; try (inv Hmatch; eauto; fail).
          (* safe *)
          intros ls fp s' Hstar'. 
          eapply source_safe; eauto. eapply ETrace.star_step; eauto. 
          (* drf *)
          intro.
          eapply source_drf; eauto. destruct H3 as (ls & fp & s' & Hstar' & RACE).
          econstructor. eexists _, s'. split; auto. eapply ETrace.star_step; eauto.
          (* thread sims... *)
          { constructor.
            { intro. unfold ThreadPool.get_cs. simpl.
              unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. inv H_tp_pop. simpl in *.
              destruct (peq t t0).
              (* case: t = t0 *)
              { subst t0. simpl in *. repeat rewrite PMap.gss in *.
                constructor. constructor. constructor.
              }
              (* case: t <> t0 *)
              { do 2 (rewrite PMap.gso; eauto).
                exploit thdp_sims; eauto. intro Htpsim.
                exploit thread_simulation; eauto. 
              }
            }
            (* tp inv *)
            exploit (@ThreadPool.pop_inv SGE).
            inv Hmatch; eapply tp_inv_src; eauto. simpl.
            unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
            simpl. auto.
              (* tp next tid *)
            simpl. unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. 
            inv H_tp_pop. simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
            (* next fmap *)
            intro. 
            unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. inv H_tp_pop.
            simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
          }
          (* inv thdp *)
          {
            eapply glob_step_inv_preserve in Htsostep;eauto.
            eapply MS_tge_flwd;eauto.
            eapply inv_thdp;eauto.
          }
        }
      }
      { (* object case *)
        inv Hclient. inv H4. simpl in *. rewrite H_tp_core in H0. inv H0. simpl in *. congruence.
      }
    }
  Qed.
  
    
  Lemma MS_tau_step_fp_cases:
    forall SGE TGE i_obj spc tpc fp tpc',
      MS SGE TGE i_obj spc tpc ->
      tso_globstep tpc tau fp tpc' ->
      (client_core TGE i_obj (cid tpc) tpc ->
       ~ conflictc (cid tpc) fp (tso_buffers (tm tpc))) ->
      (client_core TGE i_obj (cid tpc) tpc /\
       exists fpS spc',
         glob_step spc ETrace.tau fpS spc' /\
         fpmatchc fpS fp /\
         MS SGE TGE i_obj spc' tpc')
      \/
      (~ client_core TGE i_obj (cid tpc) tpc /\
       exists fpS spc',
         tau_star glob_step spc fpS spc' /\
         MS SGE TGE i_obj spc' tpc' /\
         obj_fp (gm spc) (gm spc') fp).
  Proof.
    intros SGE TGE i_obj spc tpc fp tpc' Hmatch Htsostep Hconflict.
    destruct (client_core_dec TGE i_obj tpc) as [HC|HO]; [left|right]; split; auto.
    { specialize (Hconflict HC).
      exploit MS_preserved_after_tau_non_conflicting_client_step; eauto.
    }
    { clear Hconflict. 
      exploit match_fls_eq; eauto. intro Hflseq.
      pose proof Htsostep as Htsostep'. inv Htsostep'. 
      (* module tau step *)
      { destruct spc.
        exploit tid_eq; eauto. simpl. intro; subst cur_tid.
        exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
        exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
        instantiate (1:=t) in Htsim. simpl in *. rewrite H_tp_core in Htsim.
        inv Htsim. inv H1.
        (* client step *)
        { exfalso. apply HO. econstructor; eauto. inv H0. simpl in *. inv H4. eauto. }
        (* object step *)
        { inv H4. simpl in *. pose proof H1 as Homatch.
          eapply ObjectSim.match_tau in H1; eauto.
          destruct H1 as [Htaustar|Hatomblock].
          { (* sc star step *)
            destruct Htaustar as (sfp & sc' & sm' & Htaustar & HMatchOrAbort).
            rewrite <- Hflseq in Htaustar.
            exploit core_star_globstep_star; eauto.
            intros (thread_pool' & Hglobtaustar & [Hmult | Hzero]).
            { (* multiple step *)
              do 2 eexists; split; [eauto|].
              destruct HMatchOrAbort as [(HGo & Hcmatch' & Halloc & Hvalideq & Hobjfp) |Habort]; [|exfalso].
              (* matched *)
              { split.
                constructor; try (inv Hmatch; eauto; fail); simpl in *.
                eapply H_sta_co; inv Hmatch; eauto.
                eapply H_sta_oo; inv Hmatch; eauto.
                (* safe *)
                intros ls fp' s' Hstar'.
                exploit taustar_etrace_star; eauto. intros [ls' Hstar''].
                eapply source_safe; eauto. eapply etrace_star_star; eauto.
                (* drf *)
                intro. eapply source_drf; eauto. destruct H1 as (ls & fp' & s' & Hstar' & RACE).
                exploit taustar_etrace_star; eauto. intros [ls' Hstar''].
                do 3 eexists. split;[eapply etrace_star_star; eauto|auto].
                (* thread sims... *)
                { inv Hmult. inv H2. inv H3. inv H2.
                  apply Eqdep_dec.inj_pair2_eq_dec in H6;[|apply ordinal_eq_dec]. subst.
                  rewrite H1 in H; inv H.
                  constructor.
                  { intro. unfold ThreadPool.get_cs. simpl.
                    inv H_tp_upd. inv H_core_upd. simpl in *.
                    destruct (peq t t0).
                    (* case: t = t0 *)
                    { subst t0. simpl in *. do 2 rewrite PMap.gss.
                      constructor. eapply ThreadSimObject.
                      econstructor; eauto.
                      eapply ThreadClientSim_Sta_Go; eauto.
                      eapply MS_source_tau_star_step_sep_obj_clt_preserved in Hglobtaustar; eauto.
                      eapply mem_inv_client in Hmatch; eauto.
                      rewrite H_tp_core in H. inv H. auto.
                    }
                    (* case: t <> t0 *)
                    { do 2 (rewrite PMap.gso; eauto).
                      exploit thdp_sims; eauto. intro Htpsim.
                      exploit thread_simulation; eauto. intro Htsim. instantiate (1:= t0) in Htsim.
                      simpl in *. inv Htsim; unfold ThreadPool.get_cs, CallStack.t in *.
                      rewrite <- H4. constructor.
                      rewrite <- H2. constructor.
                      inv H6.
                      eapply ThreadSimClient.
                      eapply ThreadClientSim_Sta_Go; eauto.
                      eapply MS_source_tau_star_step_sep_obj_clt_preserved in Hglobtaustar; eauto.
                      eapply mem_inv_client in Hmatch; eauto.
                      eapply ThreadSimObject.
                      inv H7. econstructor; eauto. eapply ObjectSim.match_rely; eauto.
                      eapply H_rg_oo; eauto.
                      eapply ThreadClientSim_Sta_Go; eauto.
                      eapply MS_source_tau_star_step_sep_obj_clt_preserved in Hglobtaustar; eauto.
                      eapply mem_inv_client in Hmatch; eauto.
                    }
                  }
                  { eapply ThreadPool.upd_top_inv.
                    apply thdp_sims in Hmatch. destruct Hmatch. eauto.
                    simpl. unfold ThreadPool.get_top. rewrite H1. simpl. eauto.
                    econstructor; eauto. simpl. econstructor; eauto.
                    econstructor; eauto. econstructor; eauto.
                  }
                  { inv H_tp_upd. simpl. exploit thdp_sims; eauto. destruct 1. auto. } 
                  { inv H_tp_upd. simpl. exploit thdp_sims; eauto. destruct 1. auto. } 
                }
                (* fl embed ... *)
                exploit FLs_embed_preserved. rewrite <- Hflseq. 
                apply GlobEnv.wd_fl. eapply GE_wd; eauto.
                inv Hmatch; eauto. eauto. simpl. auto.
                (* inv thdp *)
                {
                  eapply glob_step_inv_preserve in Htsostep;eauto.
                  eapply MS_tge_flwd;eauto.
                  eapply inv_thdp;eauto.
                }
                (* alloc *)
                exploit tsostep_buffered_alloc_in_fl. eauto.
                symmetry in H. eapply ThreadPool.cs_inv in H. eapply ThreadPool.fid_belongsto in H; [|simpl; eauto].
                revert H Hmatch. clear. simpl; intros H Hmatch (tail & Hbuffer & Hbufalloc) t0 b lo hi H0.
                subst buf'. simpl in H0. unfold tupdate in H0. destruct (peq t0 t).
                subst. eapply in_app in H0. destruct H0.
                eapply buffered_alloc_local; eauto.
                destruct H as [fn H]. 
                apply Hbufalloc in H0. destruct H0 as [n H0].
                exists fn, n. subst flid. unfold FLists.get_tfl. erewrite <- match_fls_eq in *; eauto. 
                eapply buffered_alloc_local; eauto.
                eapply tp_inv_src. eapply thdp_sims in Hmatch; eauto.
                (* fl_valid_eq *)
                { exploit (@ThreadPool.fid_belongsto SGE).
                  eapply ThreadPool.cs_inv. eapply tp_inv_src. eapply thdp_sims. eauto. simpl. eauto. simpl; left; eauto.
                  intros [fn Hflid]. simpl in Hflid.
                  eapply fl_valid_eq_stable'; eauto.
                  eapply Ic_unbuffer_safe. eapply mem_inv_client in Hmatch; eauto.
                  erewrite <- match_fls_eq; eauto. eapply GlobEnv.wd_fl. eapply GE_wd. eauto.
                  intros. eapply fl_valid_match in Hmatch. simpl in Hmatch. eauto.
                  exploit MS_src_tau_star_step_gmem_forward; eauto.
                  eapply star_corestep_LocalAlloc in Htaustar. intros.
                  subst flid. erewrite <- match_fls_eq; eauto. eapply Htaustar; eauto.
                  eapply GE_mod_sim_source_lang_wd. eapply GE_eq. eauto.
                  subst flid. simpl in *. erewrite match_fls_eq in H_core_step; eauto.
                  unfold tsoupd. subst flid.
                  erewrite match_fls_eq in Hvalideq; eauto.
                }
                (* sep obj client block *)
                { eapply MS_source_tau_star_step_sep_obj_clt_preserved in Hglobtaustar; eauto. }
                (* obj_fp *)
                simpl. auto.
              }
              { (* abort *)
                exploit taustar_etrace_star. eauto. intros [ls ETraceStar].
                eapply source_safe. eauto. eauto.
                split.
                (* thread not halted *)
                revert H Hmult; clear. intros.
                simpl. intro. inv H0. inv Hmult.
                unfold ThreadPool.get_cs in H1. simpl in H1. rewrite PMap.gss in H1. inv H1.
                inv H3. inv H2.
                (* no glob step except for sw *)
                rewrite <- Hflseq in Habort.
                destruct Habort as (Habort & Hnatext & Hnaftext & Hnhalt).
                intros.
                { inv H1; auto; exfalso.
                  GDefLemmas.solv_thread. eapply Habort. eauto.                  
                  { revert H_core_atext. GDefLemmas.solv_thread; simpl in *.
                    intro; congruence. }
                  { revert H_core_halt. GDefLemmas.solv_thread; simpl in *.
                    intro. congruence. } 
                  { revert H_core_halt. GDefLemmas.solv_thread; simpl in *.
                    intro. congruence. }
                  { revert H_core_atext. GDefLemmas.solv_thread; simpl in *.
                    intro; congruence. }
                  { revert H_core_atext. GDefLemmas.solv_thread; simpl in *.
                    intro; congruence. }                  
                }
              }
            }
            { (* zero step *)
              destruct Hzero as (A & B & C & D). subst.
              do 2 eexists. split. econstructor.
              destruct HMatchOrAbort as [Hmatch' | Habort].
              (* match after star step *)
              { destruct Hmatch' as [HGo [Homatch' (Halloc & Hvalideq & Hobjfp)]]. split.
                constructor; try (inv Hmatch; eauto; fail); simpl in *.
                eapply H_sta_co; inv Hmatch; eauto.
                eapply H_sta_oo; inv Hmatch; eauto.
                constructor.
                { intro. unfold ThreadPool.get_cs. 
                  inv H_tp_upd. inv H_core_upd. simpl in *.
                  destruct (peq t t0).
                  (* case: t = t0 *)
                  { subst t0. unfold ThreadPool.get_cs in *. rewrite <- H. simpl.
                    rewrite PMap.gss.
                    constructor. eapply ThreadSimObject.
                    econstructor; eauto.
                    eapply ThreadClientSim_Sta_Go; eauto.
                    eapply MS_source_tau_star_step_sep_obj_clt_preserved in Hglobtaustar; eauto.
                    eapply mem_inv_client in Hmatch; eauto.
                    rewrite H_tp_core in H1. inv H1. auto.
                  }
                  (* case: t <> t0 *)
                  { rewrite PMap.gso; eauto.
                    exploit thdp_sims; eauto. intro Htpsim.
                    exploit thread_simulation; eauto. intro Htsim. instantiate (1:= t0) in Htsim.
                    simpl in *. inv Htsim; unfold ThreadPool.get_cs, CallStack.t in *.
                    rewrite <- H3. constructor.
                    rewrite <- H2. constructor.
                    inv H4.
                    eapply ThreadSimClient.
                    eapply ThreadClientSim_Sta_Go; eauto.
                    eapply MS_source_tau_star_step_sep_obj_clt_preserved in Hglobtaustar; eauto.
                    eapply mem_inv_client in Hmatch; eauto.
                    eapply ThreadSimObject.
                    inv H6. econstructor; eauto. eapply ObjectSim.match_rely; eauto.
                    eapply H_rg_oo; eauto.
                    eapply ThreadClientSim_Sta_Go; eauto.
                    eapply MS_source_tau_star_step_sep_obj_clt_preserved in Hglobtaustar; eauto.
                    eapply mem_inv_client in Hmatch; eauto.                    
                  }
                }
                { exploit thdp_sims; eauto. destruct 1. eauto. }
                { inv H_tp_upd. simpl. exploit thdp_sims; eauto. destruct 1. eauto. }
                { inv H_tp_upd. simpl. exploit thdp_sims; eauto. destruct 1. eauto. }
                (* Fls embed *)
                exploit FLs_embed_preserved.
                rewrite <- Hflseq. eapply GE_wd. eauto.
                eapply fls_embed. eauto. eauto. simpl. auto.
                 (* inv thdp *)
                {
                  eapply glob_step_inv_preserve in Htsostep;eauto.
                  eapply MS_tge_flwd;eauto.
                  eapply inv_thdp;eauto.
                }
                (* buffered alloc *)
                { exploit tsostep_buffered_alloc_in_fl. eauto.
                  symmetry in H. eapply ThreadPool.cs_inv in H. eapply ThreadPool.fid_belongsto in H; [|simpl; eauto].
                  revert H Hmatch. clear. simpl; intros H Hmatch (tail & Hbuffer & Hbufalloc) t0 b lo hi H0.
                  subst buf'. simpl in H0. unfold tupdate in H0. destruct (peq t0 t).
                  subst. apply in_app in H0. destruct H0.
                  eapply buffered_alloc_local; eauto.
                  destruct H as [fn H]. 
                  apply Hbufalloc in H0. destruct H0 as [n H0].
                  exists fn, n. subst flid. unfold FLists.get_tfl. erewrite <- match_fls_eq in *; eauto. 
                  eapply buffered_alloc_local; eauto.
                  eapply tp_inv_src. eapply thdp_sims in Hmatch; eauto. }
                (* fl_valid_eq *)
                { exploit (@ThreadPool.fid_belongsto SGE).
                  eapply ThreadPool.cs_inv. eapply tp_inv_src. eapply thdp_sims. eauto. simpl. eauto. simpl; left; eauto.
                  intros [fn Hflid]. simpl in Hflid.
                  eapply fl_valid_eq_stable'; eauto.
                  eapply Ic_unbuffer_safe. eapply mem_inv_client in Hmatch; eauto.
                  erewrite <- match_fls_eq; eauto. eapply GlobEnv.wd_fl. eapply GE_wd. eauto.
                  intros. eapply fl_valid_match in Hmatch. simpl in Hmatch. eauto.
                  exploit MS_src_tau_star_step_gmem_forward; eauto.
                  eapply star_corestep_LocalAlloc in Htaustar. intros.
                  subst flid. erewrite <- match_fls_eq; eauto. eapply Htaustar; eauto.
                  eapply GE_mod_sim_source_lang_wd. eapply GE_eq. eauto.
                  subst flid. simpl in *. erewrite match_fls_eq in H_core_step; eauto.
                  unfold tsoupd. subst flid.
                  erewrite match_fls_eq in Hvalideq; eauto.
                }
                (* obj_fp *)
                simpl. auto.
              }
              { (* abort after zero step... *)
                exploit taustar_etrace_star. eauto. intros [ls Htaustar'].
                exfalso. eapply source_safe. eauto. eauto. 
                split.
                (* thread not halted *)
                revert H; clear. intros.
                simpl. intro. inv H0. rewrite H1 in H. inv H. inv H2.
                (* no glob step except for sw *)
                rewrite <- Hflseq in Habort.
                destruct Habort as (Habort & Hnatext & Hnaftext & Hnhalt).
                intros.
                { inv H1; auto; exfalso.
                  GDefLemmas.solv_thread. eapply Habort. eauto.
                  { revert H_core_atext. GDefLemmas.solv_thread; simpl in *.
                    rewrite <- H in H_tp_core0. GDefLemmas.solv_thread. congruence. }
                  { revert H_core_halt. GDefLemmas.solv_thread; simpl in *.
                    rewrite <- H in H_tp_core0. GDefLemmas.solv_thread. congruence. }
                  { revert H_core_halt. GDefLemmas.solv_thread; simpl in *.
                    rewrite <- H in H_tp_core0. GDefLemmas.solv_thread. congruence. }
                  { revert H_core_atext. GDefLemmas.solv_thread; simpl in *. congruence. }
                  { revert H_core_atext. GDefLemmas.solv_thread; simpl in *. congruence. }
                }
              }
            }
          }
          { (* sc atomic block *)
            destruct Hatomblock as (sfp_star & sc_ent & sm_ent & sc_ent'
                                    & sfp_star' & sc_ext & sm_ext & sc_ext'
                                    & Hstar & Hent & Hent'
                                    & Hatomstar & HExtOrAbort).
            rewrite <- Hflseq in *.
            (* glob tau star step *)
            exploit core_star_globstep_star. exact Hstar. rewrite <- H.  eauto.
            intros (tp' & Hglobstar & Htp').
            (* glob ent atom step *)
            assert (Hglobent: exists tp'', glob_step {| thread_pool := tp'; cur_tid := t; gm := sm_ent; atom_bit := O |}
                                                ETrace.tau FP.emp
                                                {| thread_pool := tp''; cur_tid := t; gm := sm_ent; atom_bit := I |}
                                      /\
                                      ThreadPool.update tp' t
                                                        {| Core.i := ix; Core.c := sc_ent'; Core.sg := sg; Core.F := flid |}
                                                        tp'').
            { destruct Htp' as [Htp'|Htp'].

              eexists. split. econstructor; eauto.
              GDefLemmas.solv_thread.
              simpl. eauto.
              simpl. eauto.
              econstructor; eauto.
              econstructor; eauto. GDefLemmas.solv_thread. econstructor. econstructor. eauto.
              econstructor. GDefLemmas.solv_thread.
              econstructor. econstructor. eauto. simpl. auto.
              
              destruct Htp' as (A&B&C&D). subst.
              eexists. split. econstructor; eauto.
              GDefLemmas.solv_thread. rewrite <- H. simpl. eauto.
              simpl. eauto.
              simpl. eauto.
              econstructor; eauto.
              econstructor; eauto. GDefLemmas.solv_thread. econstructor. econstructor. eauto.
              econstructor. GDefLemmas.solv_thread. rewrite <- H. eauto.
              econstructor. econstructor. eauto. simpl. auto.
            }
            destruct Hglobent as [tp'' [Hglobent Htp'']].
            (* glob atom star step *)
            exploit core_star_globstep_star.
            exact Hatomstar.
            { instantiate (4:= tp'').
              instantiate (3:= t).
              instantiate (2:= sg).
              instantiate (1:= scs).
              destruct Htp' as [Htp'|(A&B&C&D)]; GDefLemmas.solv_thread. }
            intros (tp''' & Hglobatomstar & Htp''').
            instantiate (1:= O) in Hglobstar.
            instantiate (1:= I) in Hglobatomstar.
            
            destruct HExtOrAbort as [ (Hext & Hext' & HGo & Homatch' & Halloc & Hvalideq & Hobjfp) | Habort ].
            { (* ext atom and match *)
              (* glob ext atom step *)
              assert (Hglobext:
                        exists tp'''', glob_step {| thread_pool := tp'''; cur_tid := t; gm := sm_ext; atom_bit := I |}
                                            ETrace.tau FP.emp
                                            {| thread_pool := tp''''; cur_tid := t; gm := sm_ext; atom_bit := O |}
                                  /\
                                  ThreadPool.update tp''' t
                                                    {| Core.i := ix; Core.c := sc_ext'; Core.sg := sg; Core.F := flid |}
                                                    tp'''').
              { destruct Htp''' as [Htp'''|(A'&B'&C'&D')]; subst; GDefLemmas.solv_thread; simpl in *.

                eexists. split. econstructor; simpl in *.
                unfold ThreadPool.get_top, ThreadPool.get_cs. simpl. repeat rewrite PMap.gss. simpl. eauto.
                eauto. eauto. econstructor. simpl. eauto.
                econstructor. unfold ThreadPool.get_cs. simpl. repeat rewrite PMap.gss. eauto.
                econstructor. econstructor; eauto. simpl. eauto.
                econstructor. unfold ThreadPool.get_cs. simpl. repeat rewrite PMap.gss. eauto.
                econstructor. econstructor. eauto. simpl. eauto.

                eexists. split. econstructor; simpl in *.
                unfold ThreadPool.get_top, ThreadPool.get_cs. simpl. repeat rewrite PMap.gss. simpl. eauto.
                eauto. eauto. econstructor. simpl. eauto.
                econstructor. unfold ThreadPool.get_cs. simpl. repeat rewrite PMap.gss. eauto.
                econstructor. econstructor; eauto. simpl. eauto.
                econstructor. unfold ThreadPool.get_cs. simpl. repeat rewrite PMap.gss. eauto.
                econstructor. econstructor. eauto. simpl. eauto.
              }
              destruct Hglobext as [tp'''' [Hglobext Htp'''']].

              (* sc atomic block and match *)
              exists (FP.union sfp_star
                          (FP.union FP.emp
                                    (FP.union sfp_star'
                                              (FP.union FP.emp FP.emp)))).
              exists {| thread_pool := tp''''; cur_tid := t; gm := sm_ext; atom_bit := O |}.
              assert (tau_star glob_step {| thread_pool := thread_pool; cur_tid := t; gm := gm; atom_bit := O |}
                               (FP.union sfp_star (FP.union FP.emp (FP.union sfp_star' (FP.union FP.emp FP.emp))))
                               {| thread_pool := tp''''; cur_tid := t; gm := sm_ext; atom_bit := O |}) as Htaustar.
              { eapply tau_star_star. exact Hglobstar.
                eapply tau_star_cons. exact Hglobent.
                eapply tau_star_star. exact Hglobatomstar.
                eapply tau_star_cons. exact Hglobext.
                eapply tau_star_0. }
              split. auto. split.
              constructor; try (inv Hmatch; eauto; fail); simpl in *.
              eapply H_sta_co; inv Hmatch; eauto.
              eapply H_sta_oo; inv Hmatch; eauto.
              (* safe *)
              intros ls fp' s' Hstar'. 
              exploit taustar_etrace_star. exact Htaustar. intros [ls' Hstar'0].
              eapply source_safe; eauto. eapply etrace_star_star; eauto. 
              (* drf *)
              intro.
              exploit taustar_etrace_star. exact Htaustar. intros [ls' Hstar'0].
              eapply source_drf; eauto. destruct H1 as (ls & fp' & s' & Hstar' & RACE).
              econstructor. eexists _, s'. split; auto. eapply etrace_star_star; eauto.
              (* thread sims... *)
              constructor.
              { intro. unfold ThreadPool.get_cs. 
                inv H_tp_upd. inv H_core_upd. simpl in *. rewrite H_tp_core in H1. inv H1. 
                destruct (peq t t0).
                (* case: t = t0 *)
                { subst t0. unfold ThreadPool.get_cs in *. rewrite PMap.gss.
                  destruct Htp''' as [Htp'''|(A'&B'&C'&D')]; 
                    destruct Htp' as [Htp'|(A&B&C&D)]; subst; simpl in *.
                  { GDefLemmas.solv_thread.
                    econstructor; eauto.
                    apply ThreadSimObject. econstructor; eauto.
                    eapply ThreadClientSim_Sta_Go; eauto.
                    eapply MS_source_tau_star_step_sep_obj_clt_preserved in Htaustar; eauto.
                    eapply mem_inv_client in Hmatch; eauto.
                  }
                  { GDefLemmas.solv_thread.
                    econstructor; eauto.
                    apply ThreadSimObject. econstructor; eauto.
                    eapply ThreadClientSim_Sta_Go; eauto.
                    eapply MS_source_tau_star_step_sep_obj_clt_preserved in Htaustar; eauto.                    
                    eapply mem_inv_client in Hmatch; eauto.
                  }
                  { GDefLemmas.solv_thread.
                    econstructor; eauto.
                    apply ThreadSimObject. econstructor; eauto.
                    eapply ThreadClientSim_Sta_Go; eauto.
                    eapply MS_source_tau_star_step_sep_obj_clt_preserved in Htaustar; eauto.
                    eapply mem_inv_client in Hmatch; eauto.
                  }
                  { GDefLemmas.solv_thread.
                    econstructor; eauto.
                    apply ThreadSimObject. econstructor; eauto.
                    eapply ThreadClientSim_Sta_Go; eauto.
                    eapply MS_source_tau_star_step_sep_obj_clt_preserved in Htaustar; eauto.
                    eapply mem_inv_client in Hmatch; eauto.
                  }
                }
                (* case: t <> t0 *)
                { rewrite PMap.gso; eauto.
                  exploit thdp_sims; eauto. intro Htpsim.
                  exploit thread_simulation; eauto. intro Htsim. instantiate (1:= t0) in Htsim.
                  simpl in *.
                  assert ((ThreadPool.content tp'''') !! t0 = (ThreadPool.content thread_pool) !! t0).
                  { revert Htp' Htp'' Htp''' Htp'''' n. clear. intros.
                    destruct Htp''' as [Htp'''|(A'&B'&C'&D')]; 
                      destruct Htp' as [Htp'|(A&B&C&D)]; subst; simpl in *;
                        GDefLemmas.solv_thread; repeat destruct peq; try congruence. }
                  rewrite H1. clear H1.
                  inv Htsim; unfold ThreadPool.get_cs, CallStack.t in *.
                  rewrite <- H2. constructor.
                  rewrite <- H1. constructor.
                  inv H3.
                  eapply ThreadSimClient.
                  eapply ThreadClientSim_Sta_Go; eauto.
                  eapply MS_source_tau_star_step_sep_obj_clt_preserved in Htaustar; eauto.                  
                  eapply mem_inv_client in Hmatch; eauto.
                  eapply ThreadSimObject.
                  inv H4. econstructor; eauto. eapply ObjectSim.match_rely; eauto.
                  eapply H_rg_oo; eauto.
                  eapply ThreadClientSim_Sta_Go; eauto.
                  eapply MS_source_tau_star_step_sep_obj_clt_preserved in Htaustar; eauto.                  
                  eapply mem_inv_client in Hmatch; eauto.
                }
              }
              { revert Hmatch Htp' Htp'' Htp''' Htp''''. clear. intros.
                apply thdp_sims in Hmatch. 
                destruct Htp''' as [Htp'''|(A'&B'&C'&D')]; 
                  destruct Htp' as [Htp'|(A&B&C&D)]; subst; simpl in *.
                do 4 (eapply thdp_inv_upd; eauto).
                apply tp_inv_src in Hmatch. simpl in *. auto.
                do 3 (eapply thdp_inv_upd; eauto).
                apply tp_inv_src in Hmatch. simpl in *. auto.
                do 3 (eapply thdp_inv_upd; eauto).
                apply tp_inv_src in Hmatch. simpl in *. auto.
                do 2 (eapply thdp_inv_upd; eauto).
                apply tp_inv_src in Hmatch. simpl in *. auto.
              }
              { inv H_tp_upd. simpl.
                revert Hmatch Htp' Htp'' Htp''' Htp''''. clear. intros.
                apply thdp_sims in Hmatch. 
                destruct Htp''' as [Htp'''|(A'&B'&C'&D')]; 
                  destruct Htp' as [Htp'|(A&B&C&D)]; subst; simpl in *.
                do 4 (erewrite thdp_upd_next_tid; eauto). inv Hmatch; auto.
                do 3 (erewrite thdp_upd_next_tid; eauto). inv Hmatch; auto.
                do 3 (erewrite thdp_upd_next_tid; eauto). inv Hmatch; auto.
                do 2 (erewrite thdp_upd_next_tid; eauto). inv Hmatch; auto.
              }
              { inv H_tp_upd. simpl.
                revert Hmatch Htp' Htp'' Htp''' Htp''''. clear. intros.
                apply thdp_sims in Hmatch. 
                destruct Htp''' as [Htp'''|(A'&B'&C'&D')]; 
                  destruct Htp' as [Htp'|(A&B&C&D)]; subst; simpl in *.
                do 4 (erewrite thdp_upd_next_fmap; eauto). inv Hmatch; auto.
                do 3 (erewrite thdp_upd_next_fmap; eauto). inv Hmatch; auto.
                do 3 (erewrite thdp_upd_next_fmap; eauto). inv Hmatch; auto.
                do 2 (erewrite thdp_upd_next_fmap; eauto). inv Hmatch; auto.
              }
              (* tso tau step fm exists.. *)
              exploit FLs_embed_preserved.
              rewrite <- Hflseq. eapply GlobEnv.wd_fl. eapply GE_wd. eauto.
              eapply fls_embed. eauto. eauto. simpl. auto.
              (* inv thdp *)
              {
                eapply glob_step_inv_preserve in Htsostep;eauto.
                eapply MS_tge_flwd;eauto.
                eapply inv_thdp;eauto.
              }
              (* buffered alloc *)
              exploit tsostep_buffered_alloc_in_fl. eauto.
              symmetry in H. eapply ThreadPool.cs_inv in H. eapply ThreadPool.fid_belongsto in H; [|simpl; eauto].
              revert H Hmatch. clear. simpl; intros H Hmatch (tail & Hbuffer & Hbufalloc) t0 b lo hi H0.
              subst buf'. simpl in H0. unfold tupdate in H0. destruct (peq t0 t).
              subst. apply in_app in H0. destruct H0.
              eapply buffered_alloc_local; eauto.
              destruct H as [fn H]. 
              apply Hbufalloc in H0. destruct H0 as [n H0].
              exists fn, n. subst flid. unfold FLists.get_tfl. erewrite <- match_fls_eq in *; eauto. 
              eapply buffered_alloc_local; eauto.
              eapply tp_inv_src. eapply thdp_sims in Hmatch; eauto.
              (* fl_valid_eq *)
              { exploit (@ThreadPool.fid_belongsto SGE).
                eapply ThreadPool.cs_inv. eapply tp_inv_src. eapply thdp_sims. eauto. simpl. eauto. simpl; left; eauto.
                intros [fn Hflid]. simpl in Hflid.
                eapply fl_valid_eq_stable'; eauto.
                eapply Ic_unbuffer_safe. eapply mem_inv_client in Hmatch; eauto.
                erewrite <- match_fls_eq; eauto. eapply GlobEnv.wd_fl. eapply GE_wd. eauto.
                intros. eapply fl_valid_match in Hmatch. simpl in Hmatch. eauto.
                exploit MS_src_tau_star_step_gmem_forward; eauto.
                eapply star_corestep_LocalAlloc in Hstar.
                eapply star_corestep_LocalAlloc in Hatomstar.
                subst flid. erewrite <- match_fls_eq; eauto.
                intros. eapply LocalAlloc_trans. eapply Hstar. eapply Hatomstar. eauto. eauto.
                eapply GE_mod_sim_source_lang_wd. eapply GE_eq. eauto.
                eapply GE_mod_sim_source_lang_wd. eapply GE_eq. eauto.
                subst flid. simpl in *. erewrite match_fls_eq in H_core_step; eauto.
                unfold tsoupd. subst flid.
                erewrite match_fls_eq in Hvalideq; eauto.
              }
              (* sep obj client block *)
              { eapply MS_source_tau_star_step_sep_obj_clt_preserved in Htaustar; eauto. }
              (* obj_fp *)
              simpl. auto.
            }
            { (* sc abort in atom block *)
              exists (FP.union sfp_star
                          (FP.union FP.emp
                                    (FP.union sfp_star' FP.emp))).
              exists {| thread_pool := tp'''; cur_tid := t; gm := sm_ext; atom_bit := I |}.
              assert (tau_star glob_step {| thread_pool := thread_pool; cur_tid := t; gm := gm; atom_bit := O |}
                               (FP.union sfp_star (FP.union FP.emp (FP.union sfp_star' FP.emp)))
                               {| thread_pool := tp'''; cur_tid := t; gm := sm_ext; atom_bit := I |}) as Htaustar.
              { eapply tau_star_star. exact Hglobstar.
                eapply tau_star_cons. exact Hglobent.
                eapply tau_star_star. exact Hglobatomstar.
                eapply tau_star_0. }
              exploit taustar_etrace_star. eauto. intros [ls Htaustar'].
              exfalso. eapply source_safe. eauto. eauto. 
              constructor; simpl in *.
              (* thread not halted *)
              { revert Htp''' Htp''. clear. intros. intro.
                inv Htp'''. inv H0. inv H. GDefLemmas.solv_thread. congruence.
                destruct H0 as (? & ? & ? & ?); subst.
                inv Htp''. inv H. GDefLemmas.solv_thread. congruence. }
              (* abort *)
              { destruct Habort as (Habort & Hnatext & Hnaftext & Hnhalt).
                revert Habort Hnatext Hnaftext Hnhalt Htp''' Htp''. clear. intros.
                destruct Htp''' as [Htp''' | (?&?&?&?)]; subst;
                  inv H; auto; exfalso.
                GDefLemmas.solv_thread. eapply Habort. eauto.
                GDefLemmas.solv_thread. simpl in *. congruence.
                GDefLemmas.solv_thread. eapply Habort. eauto.
                GDefLemmas.solv_thread. simpl in *. congruence.
              }
            }
          }
          (* tm_alloc_not_fl *)
          { exploit thdp_sims. eauto. simpl. intro Hcsinv. apply tp_inv_src in Hcsinv.
            exploit (@ThreadPool.cs_inv SGE). eauto. unfold ThreadPool.get_cs in H. rewrite <- H. eauto.
            intro C. eapply ThreadPool.fid_belongsto in C; [|simpl; left; eauto].
            destruct C as [fn C]. simpl in C. subst flid.
            erewrite match_fls_eq; [|eauto].
            eapply MS_tm_alloc_not_fl in Hmatch. eauto. }
          (* rel_tm_gm_vb *)
          assert (exists fn, FLists.get_tfid (GlobEnv.freelists SGE) t fn = flid) as [fn Hflid].
          { apply thdp_sims in Hmatch. apply tp_inv_src in Hmatch.
            exploit (@ThreadPool.cs_inv SGE). eauto. simpl. unfold ThreadPool.get_cs in H. rewrite <- H; eauto.
            simpl. intro A. exploit (@ThreadPool.fid_belongsto SGE). eauto. simpl. left. eauto.
            destruct 1. eauto. }
          eapply fl_valid_match in Hmatch; simpl in Hmatch.
          unfold rel_tm_gm_vb. intros. unfold fl_valid_eq, GMem.valid_block in Hmatch.
          eapply Hmatch in H3. destruct H3; split; eauto.
          unfold FLists.get_tfl. rewrite <-Hflseq. rewrite Hflid. rewrite Hflseq. eauto.
        }
      }
      (* call *)
      { destruct spc.
        exploit tid_eq; eauto. simpl. intro; subst cur_tid.
        exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
        exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
        instantiate (1:=t) in Htsim. simpl in *. rewrite H_tp_core in Htsim.
        inv Htsim. inv H1.
        { (* client call *)
          contradict HO. inv H0. inv H4. econstructor; eauto.
        }
        { (* object call - impossible case *)
          inv H4. eapply ObjectSim.match_no_extcall in H1; eauto. simpl in *. congruence.
        }
      } 
      (* return *)
      { destruct spc.
        exploit tid_eq; eauto. simpl. intro; subst cur_tid.
        exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
        exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
        instantiate (1:=t) in Htsim. simpl in *. rewrite H_tp_core in Htsim.
        inv Htsim. inv H1.
        (* client return *)
        { contradict HO. inv H0. inv H4. econstructor; eauto. }
        (* object return *)
        {
          (* callee return *)
          inv H4. inv H5. 
          exploit ObjectSim.match_halt; eauto. intro Hhalt. simpl in *. 
          (* caller after external *)
          inv H6. 
          exploit ClientSim.match_after_external. exact H3. exact H4. eauto.
          intros (sc0' & Haftext & Hcmatch_caller'). simpl in *.
          clear H0 H1.
          (* cosntruct glob step *)
          apply helper2. do 2 eexists. split.
          eapply tau_star_cons;[|eapply tau_star_0].
          eapply Return; simpl in *; eauto.
          unfold ThreadPool.get_top. rewrite <- H. simpl. eauto.
          simpl. eauto.
          unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
          unfold ThreadPool.get_top, ThreadPool.get_cs. simpl. rewrite PMap.gss.
          simpl. eauto.
          simpl. eauto.
          econstructor; eauto.
          econstructor; eauto.
          unfold ThreadPool.get_top, ThreadPool.get_cs. simpl. rewrite PMap.gss. eauto.
          simpl. econstructor; eauto. econstructor. eauto.
          simpl.
          intro Hglobtaustep.
          split.
          (* match after tau step *)
          { constructor; try (inv Hmatch; eauto; fail).
            (* safe *)
            intros ls fp s' Hstar'. 
            exploit taustar_etrace_star. exact Hglobtaustep. intros [ls' Hstar'0].
            eapply source_safe; eauto. eapply etrace_star_star; eauto. 
            (* drf *)
            intro.
            exploit taustar_etrace_star. exact Hglobtaustep. intros [ls' Hstar'0].
            eapply source_drf; eauto. destruct H0 as (ls & fp & s' & Hstar' & RACE).
            econstructor. eexists _, s'. split; auto. eapply etrace_star_star; eauto.
            (* thread sims... *)
            { constructor.
              { intro. unfold ThreadPool.get_cs. simpl.
                unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. inv H_tp_pop. simpl in *.
                inv H_tp_upd; simpl in *.
                destruct (peq t t0).
                (* case: t = t0 *)
                { subst t0. simpl in *. repeat rewrite PMap.gss in *. inv H0.
                  constructor. 
                  eapply ThreadSimClient.
                  constructor. inv H_core_upd. simpl. econstructor; eauto. auto.
                }
                (* case: t <> t0 *)
                { do 4 (rewrite PMap.gso; eauto).
                  exploit thdp_sims; eauto. intro Htpsim.
                  exploit thread_simulation; eauto. 
                }
              }
              (* tp inv *)
              exploit (@ThreadPool.pop_inv SGE).
              inv Hmatch; eapply tp_inv_src; eauto. simpl.
              unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
              simpl. intro. eapply thdp_inv_upd; eauto.
              econstructor. unfold ThreadPool.get_cs; simpl. rewrite PMap.gss. eauto.
              econstructor. econstructor. eauto. simpl. eauto.
              (* tp next tid *)
              simpl. inv H_tp_upd. unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. 
              inv H_tp_pop. simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
              (* next fmap *)
              intro. 
              inv H_tp_upd. unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. 
              inv H_tp_pop. simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
            }
            (* inv thdp *)
            {
              eapply glob_step_inv_preserve in Htsostep;eauto.
              eapply MS_tge_flwd;eauto.
              eapply inv_thdp;eauto.
            }
          }
          { (* obj_fp *)
            constructor; auto.
          }
        }
      }
      (* thread halt *)
      { destruct spc.
        exploit tid_eq; eauto. simpl. intro; subst cur_tid.
        exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
        exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
        instantiate (1:=t) in Htsim. simpl in *. rewrite H_tp_core in Htsim.
        inv Htsim. apply helper2.
        inv H1.
        (* client halt *)
        { contradict HO. inv H0. inv H4. econstructor; eauto. }
        (* object halt *)
        { inv H4. inv H5. do 2 eexists. split.
          eapply tau_star_cons. eapply Halt.
          unfold ThreadPool.get_top, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
          erewrite <- ObjectSim.match_halt; eauto.
          unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
          econstructor. unfold ThreadPool.get_cs. simpl. rewrite PMap.gss. eauto. constructor.
          apply tau_star_0.
          intros Hglobtaustep. split.
          { constructor; try (inv Hmatch; eauto; fail).
            (* safe *)
            intros ls fp s' Hstar'. 
            exploit taustar_etrace_star. exact Hglobtaustep. intros [ls' Hstar'0].
            eapply source_safe; eauto. eapply etrace_star_star; eauto. 
            (* drf *)
            intro.
            exploit taustar_etrace_star. exact Hglobtaustep. intros [ls' Hstar'0].
            eapply source_drf; eauto. destruct H2 as (ls & fp & s' & Hstar' & RACE).
            econstructor. eexists _, s'. split; auto. eapply etrace_star_star; eauto.
            (* thread sims... *)
            { constructor.
              { intro. unfold ThreadPool.get_cs. simpl.
                unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. inv H_tp_pop. simpl in *.
                destruct (peq t t0).
                (* case: t = t0 *)
                { subst t0. simpl in *. repeat rewrite PMap.gss in *.
                  constructor. constructor. constructor.
                }
                (* case: t <> t0 *)
                { do 2 (rewrite PMap.gso; eauto).
                  exploit thdp_sims; eauto. intro Htpsim.
                  exploit thread_simulation; eauto. 
                }
              }
              (* tp inv *)
              exploit (@ThreadPool.pop_inv SGE).
              inv Hmatch; eapply tp_inv_src; eauto. simpl.
              unfold ThreadPool.pop, ThreadPool.get_cs in *. rewrite <- H. simpl. eauto.
              simpl. auto.
              (* tp next tid *)
              simpl. unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. 
              inv H_tp_pop. simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
              (* next fmap *)
              intro. 
              unfold TSOThrdPool.pop in *. rewrite H_tp_core in H_tp_pop. inv H_tp_pop.
              simpl. apply thdp_sims in Hmatch; inv Hmatch; simpl in *; auto.
            }
            (* inv thdp *)
            {
              eapply glob_step_inv_preserve in Htsostep;eauto.
              eapply MS_tge_flwd;eauto.
              eapply inv_thdp;eauto.
            }
          }
          simpl. constructor; auto.
        }  
      }
    }
  Qed.
  
  Lemma MS_preserved_after_tau_step_if_not_conflicting_client_fp:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      forall tpc' fpT',
        tso_globstep tpc tau fpT' tpc' ->
        (client_core TGE i_obj (cid tpc) tpc ->
         ~ conflictc (cid tpc) fpT' (tso_buffers (tm tpc))) ->
        exists spc' fpS',
          tau_star glob_step spc fpS' spc' /\ MS SGE TGE i_obj spc' tpc'.
  Proof.
    intros.
    exploit MS_tau_step_fp_cases; eauto.
    intros [ (_ & fpS & spc' & Hsstep & Hfp & MATCH')
           | (_ & fpS & spc' & Hsstep & MATCH' & Hfp) ]; eauto.
    exists spc', fpS. split; auto.
    rewrite <- (FP.fp_union_emp fpS). econstructor; eauto.
    econstructor.
  Qed.

  Lemma fpmatchc_refl:
    forall fp, fpmatchc fp fp.
  Proof. clear. apply FP.subset_refl. Qed.

  Lemma MS_preserved_after_evt_step:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      forall tpc' v fp,
        tso_globstep tpc (evt v) fp tpc' ->
        exists spc',
          glob_step spc (ETrace.evt v) FP.emp spc' /\
          MS SGE TGE i_obj spc' tpc'.
  Proof.
    intros SGE TGE i_obj spc tpc Hmatch tpc' v fp Hevtstep. pose proof Hevtstep as Hevtstep'.
    inv Hevtstep. destruct spc.
    exploit tid_eq; eauto. simpl. intro; subst cur_tid.
    exploit atom_bit_0; eauto. simpl. intro; subst atom_bit.
    exploit thdp_sims; eauto. intro Htsim. eapply thread_simulation in Htsim.
    instantiate (1:=t) in Htsim. simpl in *. rewrite H_tp_core in Htsim.
    inv Htsim. inv H1.
    { (* client print *)
      inv H0. inv H4. pose proof H2 as Hcmatch.
      eapply ClientSim.match_at_external in H2; eauto.
      pose proof Hcmatch as Hcmatch'.
      eapply ClientSim.match_after_external in Hcmatch'; eauto.
      destruct Hcmatch' as (sc' & Haftext & Hcmatch').
      simpl in *. apply helper1. eexists _. split.
      eapply EF_Print; simpl; eauto.
      unfold ThreadPool.get_top. rewrite <- H. simpl. eauto.
      simpl. rewrite <- H2. eauto.
      simpl. eauto. econstructor; eauto. simpl.
      econstructor; eauto. econstructor; eauto. econstructor; eauto.
      intro Hglobstep. 
      unfold ThreadPool.push, ThreadPool.get_cs in *.
      (* match after call step *)
      { simpl.
        constructor; simpl; try (inv Hmatch; auto; fail).
        (* safe *)
        intros ls fp s' Hstar'.
        eapply source_safe; eauto.
        eapply etrace_star_star; eauto. eapply ETrace.star_step. eauto. econstructor.
        (* drf *)
        intro.
        eapply source_drf; eauto. destruct H3 as (ls & fp & s' & Hstar' & RACE).
        econstructor. eexists _, s'. split; auto.
        eapply etrace_star_star; eauto. eapply ETrace.star_step. eauto. econstructor.
        (* thread sims... *)
        { constructor.
          { intro. unfold ThreadPool.get_cs. simpl.
            inv H_tp_upd. inv H_core_update. simpl in *.
            destruct (peq t t0).
            (* case: t = t0 *)
            { subst t0. simpl in *. do 2 rewrite PMap.gss.
              constructor. eapply ThreadSimClient.
              constructor.
              econstructor; eauto.
              rewrite H_tp_core in H3. inv H3. auto.
            }
            (* case: t <> t0 *)
            { do 2 (rewrite PMap.gso; eauto).
              exploit thdp_sims; eauto. intro Htpsim.
              exploit thread_simulation; eauto.
            }
          }
          { eapply thdp_inv_upd.
              apply thdp_sims in Hmatch. apply tp_inv_src in Hmatch. eauto.
              simpl. econstructor; eauto. econstructor; eauto. econstructor; eauto.
            }
            { inv H_tp_upd. simpl in *. apply thdp_sims in Hmatch. eapply valid_tid_eq; eauto. }
            { intro. apply thdp_sims in Hmatch. inv H_tp_upd. simpl in *. 
              (erewrite next_fmap_eq; eauto). 
            }
        }
        (* inv thdp *)
        {
          eapply glob_step_inv_preserve in Hevtstep' ;eauto.
          eapply MS_tge_flwd;eauto.
          eapply inv_thdp;eauto.
        }
      }
    }
    { (* object print, impossible case *)
      inv H4. eapply match_no_extcall in H1; eauto. simpl in *. congruence.
    }
  Qed.

  Lemma MS_tso_client_step_fp_match:
    forall SGE TGE i_obj spc tpc fp,
      MS SGE TGE i_obj spc tpc ->
      tso_client_step_fp TGE i_obj tpc fp ->
      exists spc' fpS,
        glob_step spc ETrace.tau fpS spc' /\
        fpmatchc fpS fp.
  Proof.
    intros SGE TGE i_obj spc tpc fp MATCH Hstep.
    exploit thdp_sims. eauto. intro H.
    exploit thread_simulation. eauto. intro Hsim.
    inv Hstep. simpl in *. rewrite H0 in Hsim. inv Hsim.
    inv H5.
    { inv H4. inv H8. simpl in *. pose proof H2 as Hstep.
      eapply ClientSim.match_tau in H2; eauto.
      destruct H2. simpl in *.
      destruct H2 as (fpS & sc' & sm' & Hsstep & [(_ & Hfp & _ & _ ) | (_ & Hmatch)]).
      { destruct spc. erewrite <- tid_eq in H3; [|eauto]. simpl in H3.
        do 2 eexists. simpl in *. split.
        eapply GlobSemantics.Corestep; eauto. unfold ThreadPool.get_top.
        rewrite <- H3. simpl. eauto.
        simpl. erewrite match_fls_eq. eauto. eauto.
        econstructor. eauto. simpl. econstructor. eauto.
        econstructor. econstructor. eauto. eauto. auto. }
      { destruct spc. erewrite <- tid_eq in H3; [|eauto]. simpl in H3.
        do 2 eexists. simpl in *. split.
        eapply GlobSemantics.Corestep; eauto. unfold ThreadPool.get_top.
        rewrite <- H3. simpl. eauto.
        simpl. erewrite match_fls_eq. eauto. eauto.
        econstructor. eauto. simpl. econstructor. eauto.
        econstructor. econstructor. eauto. eauto. auto. }
      { exfalso. eapply source_safe. eauto. eapply ETrace.star_refl.
        split. 
        (* thread not halted *)
        erewrite <- tid_eq in H3; [|eauto]. revert H3; clear. intros H.
        simpl. intro. inv H0. rewrite H1 in H. inv H. inv H2.
        (* no glob step except for sw *)
        erewrite <- match_fls_eq in H2; eauto. simpl in *.
        assert (Hnatext: at_external (ModSem.lang (GlobEnv.modules SGE ix))
                                       (ModSem.Ge (GlobEnv.modules SGE ix))
                                       sc
                         = None).
        { apply thdp_sims in MATCH. apply thread_simulation with (t0 := cid tpc) in MATCH; simpl in MATCH.
          rewrite <- H3, H0 in MATCH. inv MATCH. 
          erewrite <- ClientSim.match_at_external; eauto.
          eapply tsostep_not_atext; eauto.
        }
        assert (Hnhalt: halt (ModSem.lang (GlobEnv.modules SGE ix)) sc = None).
        { apply thdp_sims in MATCH. apply thread_simulation with (t0 := cid tpc) in MATCH; simpl in MATCH.
          rewrite <- H3, H0 in MATCH. inv MATCH.
          erewrite <- ClientSim.match_halted; eauto.
          eapply tsostep_not_halted; eauto. }
        intros.
        { erewrite <- tid_eq in H3; eauto. inv H7; auto; exfalso.
          { (* tau step *)
            GDefLemmas.solv_thread. simpl in *. eapply H2. eauto. 
          }
          all: GDefLemmas.solv_thread; simpl in *; try congruence;
            rewrite <- H3 in *; simpl in *;
              GDefLemmas.solv_thread; simpl in *; try congruence.
        }
      }
      { (* tm_alloc_not_fl *)
        exploit (@ThreadPool.fid_belongsto SGE).
        eapply ThreadPool.cs_inv. eapply tp_inv_src; eauto.
        unfold ThreadPool.get_cs in H3. eauto. simpl. left. eauto.
        simpl. erewrite match_fls_eq; eauto. intros [fn Hflid]. subst flid.
        eapply MS_tm_alloc_not_fl in MATCH; eauto.
      }
      { (* rel_tm_gm_vb *)
        eapply fl_valid_eq_rel_tm_gm_vb.
        exploit (@ThreadPool.fid_belongsto SGE).
        eapply ThreadPool.cs_inv. eapply tp_inv_src; eauto.
        unfold ThreadPool.get_cs in H3. eauto. simpl. left. eauto.
        simpl. erewrite match_fls_eq; eauto. intros [fn Hflid]. subst flid.
        eapply fl_valid_match. eauto.
      }
    }
    exfalso. inv H8. simpl in *. congruence.
  Qed.


  (** ********************************************************************* *)
  (** Additional invariants for proving no conflicting client footprint     *)
  (** ********************************************************************* *)
  
  Inductive buffer_forward (bi: buffer_item):
    buffer -> buffer ->
    buffer -> buffer -> Prop :=
  | buf_forward_refl: forall head tail,
      buffer_forward bi head tail head tail
  | buf_forward_enq: forall head tail new_bis,
      buffer_forward bi head tail head (tail ++ new_bis)
  | buf_forward_deq: forall bi_head head tail,
      buffer_forward bi (bi_head :: head) tail head tail.

  
  
  (**
     S0 -> S1 -> ... -> Sn -> S
     |     |            |     | 
     T0 -> T1 -> ... -> Tn -> T

     where 
     (1) bi is inserted at T0 -> T1 step, and
     (2) after each Tn step, the buffer item bi is not unbuffered, and
     (3) each Ti -> Ti+1 step's footprint satisfies [no_conflicting_client_fp], and
         i.e. if it's a client step, the footprint does not conflict with buffer of other threads, and
     (4) after each Ti -> Ti+1 step, there's correponding Si ->* Si+1 step, after which Ti+1 and Si+1 match
   *)

  Definition PrevInsertedInv
             (SGE: GlobEnv.t)
             (TGE: TSOGlobEnv.t)
             i_obj
             (spc: ProgConfig) (tpc: TSOProgConfig): Prop :=
    MS SGE TGE i_obj spc tpc
    /\ no_conflicting_client_fp TGE i_obj tpc.

  Inductive bi_not_unbuffered
            (TGE: TSOGlobEnv.t)
            i_obj
            (t: tid)
            (bi: buffer_item)
    : buffer -> buffer -> TSOProgConfig ->
      buffer -> buffer -> TSOProgConfig -> Prop :=
    
  | bi_nub_refl: forall thdp cid tm head tail,
      let tpc := Build_TSOProgConfig TGE thdp cid tm in
      tso_buffers tm t = head ++ bi :: tail ->
      bi_not_unbuffered TGE i_obj t bi
                        head tail tpc
                        head tail tpc
                        
  | bi_nub_step:  forall tpc head tail l fp tpc' head' tail' tpc'' head'' tail'',
      tso_globstep tpc l fp tpc' ->
      tso_buffers (tm tpc) t = head ++ bi :: tail ->
      tso_buffers (tm tpc') t = head' ++ bi :: tail' ->
      buffer_forward bi head tail head' tail' ->
      (client_core TGE i_obj (cid tpc) tpc ->
       ~ conflictc (cid tpc) fp (tso_buffers (tm tpc))) ->
      bi_not_unbuffered TGE i_obj t bi
                        head' tail' tpc' head'' tail'' tpc'' ->
      
      bi_not_unbuffered TGE i_obj t bi
                        head tail tpc head'' tail'' tpc''.
    
  Inductive PreviouslyInserted
            (TGE: TSOGlobEnv.t)
            (i_obj: 'I_(TSOGlobEnv.M TGE))
            (t: tid)
            (bi: buffer_item)
            (tpc0: @TSOProgConfig TGE)
    : buffer -> buffer -> @TSOProgConfig TGE -> Prop :=
  | PrevInserted: forall head head' tail' tau fp tpc1 headn tailn tpcn,
      (* 1 *)
      tso_buffers (tm tpc0) t = head ->
      tso_globstep tpc0 tau fp tpc1 ->
      (client_core TGE i_obj (cid tpc0) tpc0 ->
       ~ conflictc (cid tpc0) fp (tso_buffers (tm tpc0))) ->
      tso_buffers (tm tpc1) t = head ++ head' ++ bi :: tail' ->
      (* 2, 3, 4 *)
      bi_not_unbuffered TGE i_obj t bi 
                        (head ++ head') tail' tpc1 
                        headn tailn tpcn ->
      PreviouslyInserted TGE i_obj t bi tpc0 headn tailn tpcn.
      
  Record BufWD (SGE: GlobEnv.t) (TGE: TSOGlobEnv.t) i_obj (tpc: TSOProgConfig): Prop :=
    {
      (* buffered items are inserted by previous tsostep *)
      prev_inserted:
        forall t bi head tail,
          (tso_buffers (tm tpc) t) = head ++ bi :: tail ->
          exists spc0 tpc0,
            MS SGE TGE i_obj spc0 tpc0 /\
            PreviouslyInserted TGE i_obj t bi
                               tpc0 head tail tpc
    }.

  Lemma buf_emp_BufWD:
    forall SGE TGE i_obj tpc,
      (forall t, tso_buffers (tm tpc) t = nil) ->
      BufWD SGE TGE i_obj tpc.
  Proof. clear . intros. constructor. intros. rewrite H in H0. destruct head; inv H0. Qed.

  (**
     Next, we reorder the Ti execution trace (postpone thread t0 steps) such that
     after thread t0 inserting bi in T0 -> T1 step, no t0 steps during T1 to Tn to T, and
     T is still able to step with footprint fp, which conflicts with bi
     
     S0 -> S1 -> ... -> Sn -> S
     |     |            |     | 
     T0 -> T1 -> ... -> Tn -> T -fp->

     where 
     (1) bi is inserted at T0 -> T1 step, and
     (2) after each Tn step, the buffer item bi is not unbuffered, and
     (3) each Ti -> Ti+1 step's footprint satisfies [no_conflicting_client_fp], and
         i.e. if it's a client step, the footprint does not conflict with buffer of other threads, and
     (4) after each Ti -> Ti+1 step, there's correponding Si ->* Si+1 step, after which Ti+1 and Si+1 match
   *)
  Inductive bi_not_unbuffered'
            (TGE: TSOGlobEnv.t)
            i_obj
            (t: tid)
            (bi: buffer_item)
    : buffer -> buffer -> @TSOProgConfig TGE ->
      buffer -> buffer -> @TSOProgConfig TGE -> Prop :=
    
  | bi_nub_refl': forall thdp cid tm head tail,
      let tpc := Build_TSOProgConfig TGE thdp cid tm in
      tso_buffers tm t = head ++ bi :: tail ->
      bi_not_unbuffered' TGE i_obj t bi
                        head tail tpc
                        head tail tpc
                        
  | bi_nub_step':  forall tpc head tail l fp tpc' head' tail' tpc'' head'' tail'',

      (cid tpc <> t /\ (l = tau \/ exists v, l = evt v)
                     \/ l = sw \/ exists t', l = ub t') ->
      tso_globstep tpc l fp tpc' ->
      tso_buffers (tm tpc) t = head ++ bi :: tail ->
      tso_buffers (tm tpc') t = head' ++ bi :: tail' ->
      buffer_forward bi head tail head' tail' ->
      (client_core TGE i_obj (cid tpc) tpc ->
       ~ conflictc (cid tpc) fp (tso_buffers (tm tpc))) ->
      
      bi_not_unbuffered' TGE i_obj t bi
                        head' tail' tpc' head'' tail'' tpc'' ->
      
      bi_not_unbuffered' TGE i_obj t bi
                         head tail tpc head'' tail'' tpc''.

  

  
  
  Lemma glob_step_valid:
    forall TGE tpc l fp tpc' t,
      @tso_globstep TGE tpc l fp tpc' ->
      thrd_valid tpc' t ->
      thrd_valid tpc t.
  Proof.
    clear. unfold thrd_valid, TSOThrdPool.valid_tid. intros. inv H; simpl; auto.
    inv H_tp_upd; auto.
    unfold TSOThrdPool.push in H_tp_push.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_push; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
    destruct l; inv H1. inv H_tp_upd; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
    destruct l; inv H1. auto.
    inv H_tp_upd; auto.
  Qed.

  Lemma glob_step_halted:
    forall TGE tpc l fp tpc' t,
      @tso_globstep TGE tpc l fp tpc' ->
      thrd_not_halted tpc' t ->
      thrd_not_halted tpc t.
  Proof.
    clear. unfold thrd_not_halted.
    intros TGE tpc l fp tpc' t Hstep A C; apply A; clear A.
    inv C.
    inv Hstep;
      try (destruct (peq t t0); [subst; simpl in *; congruence|simpl in *]);
      try (constructor; auto).
    inv H_tp_upd. simpl. rewrite PMap.gso; auto.
    unfold TSOThrdPool.push in H_tp_push.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_push; simpl.
    rewrite PMap.gso; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop; simpl.
    destruct l; inv H1. inv H_tp_upd; simpl. repeat rewrite PMap.gso; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
    destruct l; inv H1. simpl. rewrite PMap.gso; auto.
    inv H_tp_upd; simpl. rewrite PMap.gso; auto.
  Qed.

  Lemma glob_step_valid':
    forall TGE tpc l fp tpc' t,
      @tso_globstep TGE tpc l fp tpc' ->
      thrd_valid tpc t ->
      thrd_valid tpc' t.
  Proof.
    clear. unfold thrd_valid, TSOThrdPool.valid_tid. intros. inv H; simpl; auto.
    inv H_tp_upd; auto.
    unfold TSOThrdPool.push in H_tp_push.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_push; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
    destruct l; inv H1. inv H_tp_upd; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
    destruct l; inv H1. auto.
    inv H_tp_upd; auto.
  Qed.

  Lemma glob_step_halted':
    forall TGE tpc l fp tpc' t,
      @tso_globstep TGE tpc l fp tpc' ->
      cid tpc <> t ->
      thrd_not_halted tpc t ->
      thrd_not_halted tpc' t.
  Proof.
    clear. unfold thrd_not_halted.
    intros TGE tpc l fp tpc' t Hstep Hcid A C; apply A; clear A.
    inv C.
    inv Hstep; simpl in *; try (constructor; auto).
    inv H_tp_upd. simpl in *. rewrite PMap.gso in H; auto.
    unfold TSOThrdPool.push in H_tp_push.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_push; simpl in *.
    rewrite PMap.gso in H; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop; simpl in *.
    destruct l; inv H1. inv H_tp_upd; simpl in *. do 2 rewrite PMap.gso in H; auto.
    unfold TSOThrdPool.pop in H_tp_pop.
    destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
    destruct l; inv H1. simpl in *. rewrite PMap.gso in H; auto.
    inv H_tp_upd; simpl in *. rewrite PMap.gso in H; auto.
  Qed.


  Lemma bi_not_unbuffered_bi_not_unbuffered':
    forall TGE i_obj t0 bi head0 tail0 tpc0 head tail tpc _tail0 _tail0' _tpc0,
      bi_not_unbuffered TGE i_obj t0 bi
                        head0 tail0 tpc0 head tail tpc ->
      tso_buffers (tm _tpc0) t0 = head0 ++ bi :: _tail0 ->
      tail0 = _tail0 ++ _tail0' ->
      (forall t, t0 <> t -> eq_thrdp_tm TGE t tpc0 _tpc0) ->
      (thrd_valid tpc0 t0 -> thrd_valid _tpc0 t0) ->
      (thrd_not_halted tpc0 t0 -> thrd_not_halted _tpc0 t0) ->
      cid tpc0 = cid _tpc0 ->
      exists _tail _tpc,
        bi_not_unbuffered' TGE i_obj t0 bi
                           head0 _tail0 _tpc0 head _tail _tpc /\
        (forall t, t0 <> t -> eq_thrdp_tm TGE t tpc _tpc) /\
        cid _tpc = cid tpc.
  Proof.
    intros TGE i_obj t0 bi head0 tail0 tpc0 head tail tpc _tail0 _tail0' _tpc0
           H.
    revert _tpc0 _tail0 _tail0'. induction H.
    intros _tpc0 _tail0 _tail0' Hbuffer Htail EQ VALID HALTED EQcid.
    exists _tail0, _tpc0.
    split; [|auto]. destruct _tpc0. eapply bi_nub_refl'. auto. 
    (* inductive case *)
    intros _tpc0 _tail0 _tail0' Hbuffer Htail EQ VALID HALTED EQcid.
    (* case study on tso_globstep *)
    destruct l.
    (* tau step *)
    Lemma tau_step_buffer_append:
      forall TGE tpc fp tpc',
        @tso_globstep TGE tpc tau fp tpc' ->
        forall t, exists tail,
            tso_buffers (tm tpc') t =
            tso_buffers (tm tpc) t ++ tail.
    Proof.
      clear. intros. inv H; simpl in *; try (exists nil; rewrite app_nil_r; auto; fail).
      unfold tupdate. destruct peq.
      { subst. inv H_core_step.
        inv H7; simpl in *.
        { Lemma exec_instr_TSO_buffer_append:
            forall ge f i rs bfm rs' bfm',
              exec_instr_TSO ge f i rs bfm = Next rs' bfm' ->
              exists tail, tbuffer bfm' = tbuffer bfm ++ tail.
          Proof.
            clear.
            intros ge f i rs bfm rs' bfm' H.
            Lemma exec_load_TSO_mem_unchg:
              forall ge chunk bfm a rs r rs' bfm',
                exec_load_TSO ge chunk bfm a rs r = Next rs' bfm' ->
                bfm' = bfm.
            Proof.
              clear. unfold exec_load_TSO. intros ge chunk bfm a rs r rs' bfm'.
              destruct (tsoloadv chunk bfm _); try discriminate.
              intro H; inv H; auto.
            Qed.
            Lemma exec_store_TSO_buffer_append:
              forall ge chunk bfm a rs r lr rs' bfm',
                exec_store_TSO ge chunk bfm a rs r lr = Next rs' bfm' ->
                exists tail, tbuffer bfm' = tbuffer bfm ++ tail.
            Proof.
              clear. unfold exec_store_TSO. intros ge chunk bfm a rs r lr rs' bfm'.
              unfold tsostorev. unfold tsostore.
              destruct eval_addrmode; try discriminate.
              intro H; inv H. simpl. eauto.
            Qed.
            destruct i; inv H;
              unfold tso_goto_label in *; 
              repeat match goal with
                   | H: match ?x with _ => _ end = Next _ _ |- _ =>
                     destruct x; try discriminate
                   | H: Next _ _ = Next _ _ |- _ =>
                     inv H
                   | |- exists _, ?x = ?x ++ _ => exists nil; rewrite app_nil_r; auto
                   | H: exec_load_TSO _ _ _ _ _ _ = Next _ _ |- _ =>
                     apply exec_load_TSO_mem_unchg in H;
                       exists nil; rewrite app_nil_r; congruence
                   | H: exec_store_TSO _ _ _ _ _ _ _ = Next _ _ |- _ =>
                     eapply exec_store_TSO_buffer_append; eauto
                     end;
              simpl; eauto.
          Qed.
          eapply exec_instr_TSO_buffer_append in H5. eauto.
        }
        { inv H3. unfold tsostore in *. inv H6; inv H8.
          simpl. repeat rewrite <- app_assoc. eauto. }
        { exists nil. rewrite app_nil_r. auto. }
        { exists nil. rewrite app_nil_r. auto. }
        { exists nil. rewrite app_nil_r. auto. }        
        { inv H1. revert H3. clear.
          generalize (tso_buffers tm t0) (Mem.nextblock fm'). clear. intros buf b.
          match goal with
            |- context[BufferedAlloc ?x ?y ?z] => generalize (BufferedAlloc x y z); intro bi
          end.
          clear. unfold store_args_fmem.
          generalize 0.
          remember (buffer_insert {| tbuffer := buf; fmemory := fm |} bi) as bfm0.
          unfold buffer_insert in *. simpl in *.
          intros.
          assert (exists tail, tbuffer tsofm' = tbuffer bfm0 ++ tail).
          { clear Heqbfm0. revert bfm0 tys z H3. clear. induction args.
            intros. simpl in H3. destruct tys; inv H3. exists nil. rewrite app_nil_r. auto.
            intros. simpl in H3.
            destruct tys; inv H3.
            destruct t; try eapply IHargs in H0.
            destruct H0. rewrite H. simpl. repeat rewrite <- app_assoc. eauto.
            destruct H0. rewrite H. simpl. repeat rewrite <- app_assoc. eauto.
            destruct a; try discriminate;
              try apply IHargs in H0; destruct H0; rewrite H;
                simpl; repeat rewrite <- app_assoc; eauto.
            destruct H0. rewrite H. simpl. repeat rewrite <- app_assoc. eauto.
            destruct H0. rewrite H. simpl. repeat rewrite <- app_assoc. eauto.
            destruct H0. rewrite H. simpl. repeat rewrite <- app_assoc. eauto.
          }
          destruct H as [tail' Htail'].
          rewrite Htail'. subst bfm0. simpl. rewrite <- app_assoc. eauto.
        }
      }
      exists nil. rewrite app_nil_r; auto.
    Qed.
    Lemma tau_step_buffer_forward_head_tail:
      forall TGE (tpc: @TSOProgConfig TGE) fp tpc' t0 bi head tail head' tail',
        tso_globstep tpc tau fp tpc' ->
        tso_buffers (tm tpc) t0 = head ++ bi :: tail ->
        tso_buffers (tm tpc') t0 = head' ++ bi :: tail' ->
        buffer_forward bi head tail head' tail' ->
        head' = head /\ exists tail'', tail' = tail ++ tail''.
    Proof.
      clear. intros. eapply tau_step_buffer_append in H.
      destruct H as [tail'' Hbuffer'].
      rewrite Hbuffer' in H1. rewrite H0 in H1.
      destruct H2. eauto using app_nil_r.
      split; auto. exists tail''. f_equal. eapply app_inv_head.
      rewrite app_comm_cons in H1. rewrite app_assoc in H1. eauto.
      exfalso. rewrite <- app_comm_cons in H1.
      revert H1. generalize (head ++ bi :: tail) tail''. clear.
      intros. assert (length ((bi_head :: l) ++ tail'') = length l) by congruence.
      rewrite app_length in H. simpl in H. Lia.lia.
    Qed.
    exploit tau_step_buffer_forward_head_tail; eauto.
    intros [A [_tail0'' B]]; subst head'.
    destruct (peq t0 (cid tpc)).
    { (* if t0 step, skip it *)
      specialize (IHbi_not_unbuffered _tpc0 _tail0 (_tail0' ++ _tail0'')).
      eapply IHbi_not_unbuffered; eauto.
      subst tail' tail. rewrite app_assoc; auto.
      Lemma tau_step_eq_thrdp_tm:
        forall TGE tpc fp tpc',
          tso_buffers (tm tpc) (cid tpc) <> nil ->
          tso_globstep tpc tau fp tpc' ->
          (forall t, t <> cid tpc -> eq_thrdp_tm TGE t tpc tpc').
      Proof.
        clear. intros.
        inv H0; unfold eq_thrdp_tm; simpl in *.
        { inv H_tp_upd; simpl. rewrite PMap.gso; auto.
          unfold tupdate. destruct peq; try contradiction.
          repeat (split; auto).
          Lemma tsostep_buff_non_empty_mem_unchg:
            forall ge fl c buf gm fp c' buf' gm',
              tsostep ge fl c (buf, gm) fp c' (buf', gm') ->
              buf <> nil ->
              gm' = gm.
          Proof.
            clear. intros. inv H. inv H9; simpl.
            all: try match goal with
                     | H: embed _ _ _  |- _ => inv H; auto
                     end.
            Lemma exec_instr_TSO_buff_non_empty_mem_unchg:
              forall ge f i rs bfm rs' bfm',
                exec_instr_TSO ge f i rs bfm = Next rs' bfm' ->
                tbuffer bfm <> nil ->
                fmemory bfm' = fmemory bfm.
            Proof.
              clear. intros.
              Lemma exec_store_TSO_mem_unchg:
                forall ge chunk bfm a rs r lr rs' bfm',
                  exec_store_TSO ge chunk bfm a rs r lr = Next rs' bfm' ->
                  fmemory bfm' = fmemory bfm.
              Proof.
                clear. unfold exec_store_TSO, tsostorev, tsostore. intros.
                destruct eval_addrmode; try discriminate.
                inv H. simpl. auto.
              Qed.
              destruct i; simpl in *;
                unfold tso_goto_label in *; 
                repeat match goal with
                       | |- ?x = ?x => auto
                       | H: Stuck = Next _ _ |- _ => discriminate
                       | H: match ?x with _ => _ end = Next _ _ |- _ =>
                         destruct x; try discriminate
                       | H: Next _ _ = Next _ _ |- _ =>
                         inv H
                       | |- exists _, ?x = ?x ++ _ => exists nil; rewrite app_nil_r; auto
                       | H: exec_load_TSO _ _ _ _ _ _ = Next _ _ |- _ =>
                         apply exec_load_TSO_mem_unchg in H; try congruence
                       | H: exec_store_TSO _ _ _ _ _ _ _ = Next _ _ |- _ =>
                         apply exec_store_TSO_mem_unchg in H; try congruence
                       end;
                simpl in *; auto; try contradiction.
            Qed.
            apply exec_instr_TSO_buff_non_empty_mem_unchg in H4; auto.
            simpl in *. rewrite H4. auto.
            simpl in *. inv H3. unfold tsostore in *. inv H5; inv H7. simpl. auto.
            { revert H3. inv H1. clear.
              match goal with
              | |- context[BufferedAlloc ?a ?b ?c] =>
                generalize (BufferedAlloc a b c)
              end.
              unfold store_args_fmem.
              match goal with
              | |- context[store_args_rec_fmem _ ?a ?b ?c ?d] =>
                generalize a b
              end. clear. unfold buffer_insert. simpl.
              intros until b. generalize (buf ++ b :: nil). clear.
              revert z tys fm. induction args; simpl; intros.
              destruct tys; inv H3; auto.
              destruct tys; inv H3.
              destruct t; unfold store_stack_fmem, tsostorev, tsostore, buffer_insert in H0.
              destruct Val.offset_ptr; try discriminate; eauto.
              destruct Val.offset_ptr; try discriminate; eauto.
              destruct a; try discriminate.
              destruct Val.offset_ptr; try discriminate; eauto.
              destruct Val.offset_ptr; try discriminate; eauto.
              destruct Val.offset_ptr; try discriminate; eauto.
              destruct Val.offset_ptr; try discriminate; eauto.
              destruct Val.offset_ptr; try discriminate; eauto.
            }
          Qed.
          apply tsostep_buff_non_empty_mem_unchg in H_core_step; auto.
        }
        { unfold TSOThrdPool.push in H_tp_push.
          destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_push; simpl.
          destruct peq; try congruence.
          rewrite PMap.gso; auto. }
        { unfold TSOThrdPool.pop in H_tp_pop.
          destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
          destruct l; inv H2. inv H_tp_upd; simpl. repeat rewrite PMap.gso; auto. }
        { unfold TSOThrdPool.pop in H_tp_pop.
          destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
          destruct l; inv H2. simpl. rewrite PMap.gso; auto. }
      Qed.
      intros. specialize (EQ _ H5).
      eapply eq_thrdp_tm_trans.
      eapply eq_thrdp_tm_sym. eapply tau_step_eq_thrdp_tm; eauto.
      intro. subst t0. rewrite H0 in H6. destruct head; discriminate.
      congruence. eauto.
      intro. apply VALID. eapply glob_step_valid; eauto.
      intro. apply HALTED. eapply glob_step_halted; eauto.
      Lemma tau_step_cid_eq:
        forall TGE tpc fp tpc',
          @tso_globstep TGE tpc tau fp tpc' ->
          cid tpc' = cid tpc.
      Proof. clear. inversion 1; auto. Qed.
      erewrite tau_step_cid_eq; eauto.
    }
    { (* if not t0 step, do the same step *)
      exploit eq_thrdp_tm_tau_step_sim; try exact H.
      eauto.
      { intros. destruct (peq t' t0).
        subst. rewrite Hbuffer. rewrite H0. rewrite app_comm_cons, app_assoc; eauto.
        exploit EQ. intro. apply n0. eauto. intros (_ & _ & _ & _ & Hbuffers). rewrite Hbuffers.
        exists nil. rewrite app_nil_r. auto. }
      eapply EQ; auto. intros (_tpc1 & Hstep' & EQ').
      Lemma less_buffer_item_not_conflict_preserve:
        forall t fp buffers buffers',
          (forall t' bi, In bi (buffers' t') -> In bi (buffers t')) ->
          ~ conflictc t fp buffers ->
          ~ conflictc t fp buffers'.
      Proof.
        clear. intros t fp buffers buffers' H A C; apply A; clear A.
        inv C. apply H in H1. econstructor; eauto.
      Qed.
      Lemma tau_step_buffer_eq:
        forall TGE tpc0 fp tpc1 t,
          @tso_globstep TGE tpc0 tau fp tpc1 ->
          cid tpc0 <> t ->
          tso_buffers (tm tpc1) t = tso_buffers (tm tpc0) t.
      Proof.
        clear. inversion 1; simpl in *; auto.
        subst. unfold tsoupd. simpl.
        unfold tupdate. destruct peq; auto.
        subst. contradiction.
      Qed.
      exploit tau_step_buffer_eq. exact Hstep'.
      intro. apply n. rewrite EQcid, H5. reflexivity.
      intro Hbuffer'. rewrite Hbuffer in Hbuffer'.
      assert (tail' = tail).
      { exploit tau_step_buffer_eq. exact H.
        intro. apply n. eauto.
        rewrite H0, H1. clear. intro.
        induction head; inv H; auto. }
      subst tail'. rewrite Htail in H5 at 2.
      exploit (IHbi_not_unbuffered _tpc1 _tail0 _tail0' Hbuffer' H5).
      - intros. apply EQ'. auto.
      - intro. eapply glob_step_valid'; eauto. 
        apply VALID. eapply glob_step_valid; eauto.
      - intro. eapply glob_step_halted'; eauto. congruence.
        apply HALTED. eapply glob_step_halted; eauto. 
      - erewrite tau_step_cid_eq; try exact H. rewrite EQcid. symmetry.
        eapply tau_step_cid_eq; try exact Hstep'.
      intros (_tail & _tpc & Hnub' & EQ'').
      exists _tail, _tpc. split; auto.
      eapply bi_nub_step'; try exact Hstep'.
      left. split;[|auto]. intro. apply n. rewrite EQcid. auto.
      auto.
      eauto.
      apply buf_forward_refl; auto.
      intro Hclient. eapply less_buffer_item_not_conflict_preserve.
      intros. instantiate (1:= tso_buffers (tm tpc)). destruct (peq t0 t').
      subst t'. rewrite Hbuffer in H6. rewrite H0. subst tail.
      rewrite app_comm_cons, app_assoc. apply in_app; auto.
      apply EQ in n0. destruct n0 as [_ [_ [_ [_ E]]]]. rewrite E. auto.
      rewrite <- EQcid. apply H3. rewrite EQcid.
      Lemma eq_thrdp_tm_eq_client_core:
        forall TGE i_obj t tpc _tpc,
          eq_thrdp_tm TGE t tpc _tpc ->
          client_core TGE i_obj t tpc ->
          client_core TGE i_obj t _tpc.
      Proof.
        clear. intros TGE i_obj t tpc _tpc H H0.
        inv H0; econstructor; eauto. destruct H. intuition. rewrite <- H3. eauto.
      Qed.
      eapply eq_thrdp_tm_eq_client_core; eauto.
      apply eq_thrdp_tm_sym, EQ. congruence.
      auto.
    } 
    { (* sw step *)
      exploit eq_thrdp_tm_sw_step_sim; try exact H; eauto.
      intros t [A B]. destruct (peq t0 t). subst t. split; auto.
      split; [eapply eq_thrdp_tm_valid| eapply eq_thrdp_tm_halted]; try apply EQ; auto. 
      intros (_tpc1 & EQcid' & Hstep' & EQ').
      Lemma sw_step_buffer_forward_head_tail:
        forall TGE (tpc: @TSOProgConfig TGE) fp tpc' t0 bi head tail head' tail',
          tso_globstep tpc sw fp tpc' ->
          tso_buffers (tm tpc) t0 = head ++ bi :: tail ->
          tso_buffers (tm tpc') t0 = head' ++ bi :: tail' ->
          buffer_forward bi head tail head' tail' ->
          head' = head /\ tail' = tail.
      Proof.
        clear. inversion 1. subst. simpl. intros.
        inv H2; auto.
        split; auto.
        rewrite H0 in H1. eapply app_inv_head in H1. inversion H1. rewrite H3 at 2. auto.
        split; auto. eapply app_inv_tail. rewrite H1 in H0. eauto.
      Qed.
      Lemma sw_step_buffer_eq:
        forall TGE tpc fp tpc',
          @tso_globstep TGE tpc sw fp tpc' ->
          tso_buffers (tm tpc') = tso_buffers (tm tpc).
      Proof. clear. inversion 1. auto. Qed.
      exploit sw_step_buffer_forward_head_tail; try exact H.
      rewrite H0; eauto. rewrite H1; eauto. auto. intros [A B]; subst head' tail'.
      exploit (IHbi_not_unbuffered _tpc1 _tail0 _tail0').
      erewrite sw_step_buffer_eq; try exact Hstep'; auto.
      auto.
      intros. apply EQ'. apply EQ. auto.
      Lemma sw_step_thdp_eq:
        forall TGE tpc fp tpc',
          @tso_globstep TGE tpc sw fp tpc' ->
          thrdpool tpc' = thrdpool tpc.
      Proof. clear. inversion 1. auto. Qed.
      unfold thrd_valid.
      erewrite sw_step_thdp_eq; try exact H.
      intro A. apply VALID in A. erewrite sw_step_thdp_eq. exact A. eauto.
      unfold thrd_not_halted.
      erewrite sw_step_thdp_eq; try exact H.
      intro A. apply HALTED in A. erewrite sw_step_thdp_eq. exact A. eauto.
      congruence.
      intros (_tail & _tpc & Hbnu' & EQ'').
      exists _tail, _tpc. split; auto.
      eapply bi_nub_step'. right. left. eauto. eauto. eauto.
      erewrite sw_step_buffer_eq; eauto.
      eapply buf_forward_refl. intros.
      Lemma emp_fp_not_conflictc:
        forall t B, ~ conflictc t FP.emp B.
      Proof.
        clear. intros t B C. inv C.
        inv H1;
          repeat rewrite Locs.locs_intersect_emp in *;
          repeat rewrite Locs.locs_intersect_emp_sym in *;
          repeat rewrite Locs.locs_union_emp in *;
          repeat rewrite Locs.emp_union_locs in *;
          auto using Locs.locs_emp.
      Qed.
      Lemma sw_step_emp_fp:
        forall TGE tpc fp tpc',
          @tso_globstep TGE tpc sw fp tpc' ->
          fp = FP.emp.
      Proof. clear. inversion 1; auto. Qed.
      apply sw_step_emp_fp in Hstep'. subst. apply emp_fp_not_conflictc.
      auto.
    }
    { (* ub step *)
      Lemma ub_step_emp_fp:
        forall TGE tpc fp tpc' t,
          @tso_globstep TGE tpc (ub t) fp tpc' ->
          fp = FP.emp.
      Proof. clear. inversion 1; auto. Qed.
      exploit ub_step_emp_fp. exact H. intro FP. subst fp.
      Lemma ub_step_buffer_forward_head_tail:
        forall TGE (tpc: @TSOProgConfig TGE) fp tpc' t0 bi head tail head' tail',
          tso_globstep tpc (ub t0) fp tpc' ->
          tso_buffers (tm tpc) t0 = head ++ bi :: tail ->
          tso_buffers (tm tpc') t0 = head' ++ bi :: tail' ->
          buffer_forward bi head tail head' tail' ->
          tail' = tail /\ exists bi', head = bi' :: head'.
      Proof.
        clear. intros. inv H. simpl in *.
        inv H2; (eauto; exfalso; unfold unbuffer in H_unbuf;
                 destruct (tso_buffers tm t0); inv H_unbuf;
                 destruct apply_buffer_item; inv H2; simpl in *;
                 unfold tupdate in H1; destruct peq; auto).
        rewrite <- H0 in H1.
        revert H1. clear. induction b0; inversion 1; subst; auto.
        rewrite app_comm_cons, app_assoc in H1. rewrite <- H0 in H1.
        revert H1. clear. induction b0; inversion 1; auto.
      Qed.
      destruct (peq t0 t).
      (* t = t0 *)
      subst t.
      exploit ub_step_buffer_forward_head_tail; eauto. intros [A [bi' B]]. subst tail'.
      exploit less_buffer_item_not_unbuffered_ub_sim; try exact H.
      Lemma exists_noneq_tid:
        forall t: tid, exists t', t <> t'.
      Proof.
        clear. intros. destruct t.
        exists (t~0)%positive. discriminate.
        exists (t~1)%positive. discriminate.
        exists (1~0)%positive. discriminate.
      Qed.
      pose proof (exists_noneq_tid t0) as Ht. destruct Ht as [t' Ht]. apply EQ in Ht. destruct Ht as (_&_&_&C&_); eauto.
      eauto. eauto. eauto. eauto.
      intros (_tpc1 & Hstep' & Hbuffer').
      exploit (IHbi_not_unbuffered _tpc1 _tail0 _tail0' Hbuffer' Htail).
      Lemma ub_step_eq_thrdp_tm_preserved:
        forall TGE t tpc _tpc head bi tail _tail tpc' _tpc',
          tso_buffers (tm tpc) t = head ++ bi :: tail ->
          tso_buffers (tm _tpc) t = head ++ bi :: _tail ->
          tso_globstep tpc (ub t) FP.emp tpc' ->
          tso_globstep _tpc (ub t) FP.emp _tpc' ->
          (forall t', eq_thrdp_tm TGE t' tpc _tpc ->
                 eq_thrdp_tm TGE t' tpc' _tpc').
      Proof.
        clear. intros.
        inv H1; inv H2; simpl in *.
        unfold eq_thrdp_tm in *; simpl in *.
        assert (exists bi' tail' _tail', tso_buffers tm t = bi' :: tail' /\
                                    tso_buffers tm0 t = bi' :: _tail').
        { rewrite H, H0. clear. destruct head; simpl; eauto. }
        clear bi head tail _tail H H0. destruct H1 as (bi & tail & _tail & H & H0).
        destruct H3 as [A [B [C [D E]]]].
        do 3 (split; auto).
        unfold unbuffer in *. rewrite H in H_unbuf. rewrite H0 in H_unbuf0.
        destruct apply_buffer_item eqn:F; inv H_unbuf.
        destruct (apply_buffer_item bi (memory tm0)) eqn:G; inv H_unbuf0.
        simpl in *. split. congruence.
        unfold tupdate. destruct peq; congruence.
      Qed.
      Lemma ub_step_thrdp_eq:
        forall TGE tpc t tpc',
          @tso_globstep TGE tpc (ub t) FP.emp tpc' ->
          thrdpool tpc' = thrdpool tpc.
      Proof. clear. inversion 1; auto. Qed.
      Lemma ub_step_cid_eq:
        forall TGE tpc t tpc',
          @tso_globstep TGE tpc (ub t) FP.emp tpc' ->
          cid tpc' = cid tpc.
      Proof. clear. inversion 1; auto. Qed.
      { intros. eapply ub_step_eq_thrdp_tm_preserved; try apply EQ; eauto. }
      intro. eapply glob_step_valid'; eauto. apply VALID. eapply glob_step_valid; eauto.
      intro. unfold thrd_not_halted. erewrite ub_step_thrdp_eq; try exact Hstep'.
      apply HALTED. eapply glob_step_halted; eauto.
      erewrite ub_step_cid_eq; try exact H. symmetry. rewrite EQcid. eapply ub_step_cid_eq; eauto.
      intros (_tail & _tpc & Hbnub' & EQ').
      exists _tail, _tpc. split; auto.
      eapply bi_nub_step'; try exact Hstep'. right. right. eauto.
      auto. eauto. subst head. eapply buf_forward_deq.
      intro. apply emp_fp_not_conflictc. auto.
      (* t0 <> t *)
      exploit eq_thrdp_tm_ub_step_sim. exact H. apply EQ. auto.
      intros (_tpc1 & Hstep' & EQ').
      Lemma buffer_forward_split_eq:
        forall head tail head' tail' bi,
          buffer_forward bi head tail head' tail' ->
          head ++ bi :: tail = head' ++ bi :: tail' ->
          head' = head /\ tail' = tail.
      Proof.
        clear. intros head tail head' tail' bi H H'. inv H; auto.
        induction head'; inv H'.
        rewrite <- (app_nil_r tail) in H0. rewrite <- app_assoc, app_nil_l in H0.
        apply app_inv_head in H0. subst. rewrite <- app_assoc. auto.
        apply IHhead' in H0. intuition.
        apply app_inv_tail in H'. rewrite <- H' at 1. auto.
      Qed.
      
      exploit ub_step_buffer_eq; try exact H. exact n. intro A.
      exploit buffer_forward_split_eq. exact H2. rewrite <- H0, <- H1, A.  auto.
      intros [B C]. subst head' tail'. 
      exploit (IHbi_not_unbuffered _tpc1 _tail0 _tail0').
      erewrite ub_step_buffer_eq; try exact Hstep'.
      auto. exact n. auto. intros. apply EQ'. apply EQ. auto.
      intro. eapply glob_step_valid'; eauto. apply VALID. eapply glob_step_valid; eauto.
      intro. unfold thrd_not_halted. erewrite ub_step_thrdp_eq; try exact Hstep'.
      apply HALTED. eapply glob_step_halted; eauto.
      erewrite ub_step_cid_eq; try exact H. symmetry. rewrite EQcid. eapply ub_step_cid_eq; eauto.
      intros (_tail & _tpc & Hbnub' & EQ'').
      exists _tail, _tpc. split; auto.
      eapply bi_nub_step'; try exact Hstep'. right. right. eauto.
      auto. erewrite ub_step_buffer_eq; try exact Hstep'. eauto. eauto.
      constructor. 
      intro. apply emp_fp_not_conflictc. auto.
    }
    { (* print step *)
      Lemma print_step_emp_fp:
        forall TGE tpc v fp tpc',
          @tso_globstep TGE tpc (evt v) fp tpc' ->
          fp = FP.emp.
      Proof. clear. inversion 1; auto. Qed.
      exploit print_step_emp_fp. try exact H. intro; subst fp.
      Lemma print_step_mem_eq:
        forall TGE tpc v tpc',
          @tso_globstep TGE tpc (evt v) FP.emp tpc' ->
          (tm tpc) = (tm tpc').
      Proof. clear. inversion 1; auto. Qed.
      exploit buffer_forward_split_eq. eauto. rewrite <-H0, <-H1.
      erewrite print_step_mem_eq; eauto.
      intros [A B]; subst head' tail'.
      destruct (peq t0 (cid tpc)).
      { (* if t0 step, skip it *)
        specialize (IHbi_not_unbuffered _tpc0 _tail0 _tail0').
        eapply IHbi_not_unbuffered; eauto.
        Lemma print_step_eq_thrdp_tm:
          forall TGE tpc v tpc',
            tso_globstep tpc (evt v) FP.emp tpc' ->
            (forall t, t <> cid tpc -> eq_thrdp_tm TGE t tpc tpc').
        Proof.
          clear. intros TGE tpc v tpc' H t H0.
          inv H. simpl in *. unfold eq_thrdp_tm. simpl.
          inv H_tp_upd. simpl. rewrite PMap.gso; auto.
        Qed.
        intros. eapply eq_thrdp_tm_trans.
        eapply eq_thrdp_tm_sym. eapply print_step_eq_thrdp_tm; eauto. congruence. auto.
        intro. apply VALID. eapply glob_step_valid; eauto.
        intro. apply HALTED. eapply glob_step_halted; eauto.
        Lemma print_step_cid_eq:
          forall TGE tpc v tpc',
            @tso_globstep TGE tpc (evt v) FP.emp tpc' ->
            cid tpc' = cid tpc.
        Proof. clear. inversion 1; auto. Qed.
        erewrite print_step_cid_eq; eauto.
      }
      { (* if not t0 step, do the same step *)
        exploit eq_thrdp_tm_print_step_sim; try exact H.
        eauto. eapply EQ; auto. intros (_tpc1 & Hstep' & EQ').
        exploit (IHbi_not_unbuffered _tpc1 _tail0 _tail0').
        rewrite <- Hbuffer. symmetry; erewrite print_step_mem_eq; eauto.
        auto.
        intros. apply EQ'. apply EQ. auto.
        intro. eapply glob_step_valid'; eauto. 
        apply VALID. eapply glob_step_valid; eauto.
        intro. eapply glob_step_halted'; eauto. congruence.
        apply HALTED. eapply glob_step_halted; eauto. 
        erewrite print_step_cid_eq; try exact H. rewrite EQcid. symmetry.
        eapply print_step_cid_eq; try exact Hstep'.
        intros (_tail & _tpc & Hnub' & EQ'').
        exists _tail, _tpc. split; auto.
        eapply bi_nub_step'; try exact Hstep'.
        left. split;[|eauto]. intro. apply n. rewrite EQcid. auto.
        auto.
        erewrite <- print_step_mem_eq; eauto.
        apply buf_forward_refl; auto.
        intro. apply emp_fp_not_conflictc. auto.
      }
    }
  Qed.

      
  Inductive PreviouslyInserted' 
            (TGE: TSOGlobEnv.t)
            (i_obj: 'I_(TSOGlobEnv.M TGE))
            (t: tid)
            (bi: buffer_item)
            (tpc0: @TSOProgConfig TGE)
    : buffer -> buffer -> @TSOProgConfig TGE -> Prop :=
  | PrevInserted': forall head head' tail' l fp tpc1 headn tailn tpcn,
      (* 1 *)
      tso_buffers (tm tpc0) t = head ->
      tso_globstep tpc0 l fp tpc1 ->
      tso_buffers (tm tpc1) t = head ++ head' ++ bi :: tail' ->
      (client_core TGE i_obj (cid tpc0) tpc0 ->
       ~ conflictc (cid tpc0) fp (tso_buffers (tm tpc0))) ->
      (* 2, 3, 4 *)
      bi_not_unbuffered' TGE i_obj t bi 
                         (head ++ head') tail' tpc1 
                         headn tailn tpcn ->
      PreviouslyInserted' TGE i_obj t bi tpc0 headn tailn tpcn.

  Lemma eq_thrdp_tm_eq_tso_client_step_fp:
    forall TGE i_obj tpc tpc' fp,
      cid tpc = cid tpc' ->
      (TSOThrdPool.content (thrdpool tpc)) !! (cid tpc) =
      (TSOThrdPool.content (thrdpool tpc')) !! (cid tpc') ->
      memory (tm tpc) = memory (tm tpc') ->
      tso_buffers (tm tpc) (cid tpc) = tso_buffers (tm tpc') (cid tpc') ->
      tso_client_step_fp TGE i_obj tpc fp ->
      tso_client_step_fp TGE i_obj tpc' fp.
  Proof.
    clear. intros. inv H3. rewrite H0 in H4.
    econstructor; eauto.
    destruct tpc, tpc'. simpl in *.
    destruct tm, tm0; simpl in *.
    subst. rewrite H2 in H6. eauto.
  Qed.
        
  Lemma PreviouslyInserted_PreviouslyInserted':
    forall TGE i_obj t0 bi tpc0 head tail tpc fp,
      t0 <> cid tpc ->
      PreviouslyInserted TGE i_obj t0 bi tpc0 head tail tpc ->
      tso_client_step_fp TGE i_obj tpc fp ->
      exists _head _tail _tpc,
        PreviouslyInserted' TGE i_obj t0 bi tpc0  _head _tail _tpc /\
        cid _tpc = cid tpc /\
        tso_client_step_fp TGE i_obj _tpc fp.
  Proof.
    intros TGE i_obj t0 bi tpc0 head tail tpc fp
           Htid0 HPrevInserted Hclientfp.
    destruct HPrevInserted.
    exploit bi_not_unbuffered_bi_not_unbuffered'.
    eapply H3. rewrite <- app_assoc. eauto.
    erewrite app_nil_r. auto.
    intros. apply eq_thrdp_tm_refl.
    auto.
    auto.
    auto.
    intros (_tail & _tpc & Hbnub & EQ & EQcid).
    exists headn, _tail, _tpc.
    split. econstructor.
    eauto. eauto. eauto. auto. auto.
    split. auto.
    apply EQ in Htid0. destruct Htid0 as [A [B [C [D E]]]].
    eapply eq_thrdp_tm_eq_tso_client_step_fp.
    symmetry. exact EQcid. congruence. auto. congruence. auto.
  Qed.

  Inductive non_conflicting_steps
            (TGE: TSOGlobEnv.t)
            i_obj
            (t: tid)
    : @TSOProgConfig TGE -> @TSOProgConfig TGE -> Prop :=
    
  | ncss_refl: forall tpc, non_conflicting_steps TGE i_obj t tpc tpc
  | ncss_step: forall tpc l fp tpc' tpc'', 
      (cid tpc <> t /\ (l = tau \/ exists v, l = evt v)
                     \/ l = sw \/ exists t', l = ub t') ->
      tso_globstep tpc l fp tpc' ->
      (client_core TGE i_obj (cid tpc) tpc ->
       ~ conflictc (cid tpc) fp (tso_buffers (tm tpc))) ->
      non_conflicting_steps TGE i_obj t tpc' tpc'' ->
      non_conflicting_steps TGE i_obj t tpc tpc''.

  Lemma bi_not_unbuffered'_non_conflicting_steps:
    forall TGE i_obj t bi head0 tail0 tpc0 headn tailn tpcn,
      bi_not_unbuffered' TGE i_obj t bi head0 tail0 tpc0 headn tailn tpcn ->
      non_conflicting_steps TGE i_obj t tpc0 tpcn.
  Proof.
    clear.
    intros. induction H. constructor.
    econstructor; eauto. 
  Qed.
  
  (**
     Finally, we reorder the Ti execution trace (postpone T0 step) such that

     after thread t0 inserting bi in T0 -> T1 step, no t0 steps during T1 to Tn to T, and
     T is still able to step with footprint fp, which conflicts with bi
     
     S0 -> S1 -> ... -> Sn -> S0' -> S0''   ->   S
     |     |            |     |      |           |
     T0 -> T1 -> ... -> Tn -> T0' -> T0'' -ub->* T -fp->

     where 
     (1) bi is inserted at T0' -> T0'' step, and
     (2) some buffer item of thread t0 unbuffered during T0'' to T
   *)
    

  Lemma app_tail_eq_nil:
    forall A (l tail: list A), l = l ++ tail -> tail = nil.
  Proof. clear. induction l; intros; auto. inv H; auto. Qed.
     
  Lemma more_buffer_item_tau_step:
    forall TGE tpc l fp tpc' tail t,
      @tso_globstep TGE tpc l fp tpc' ->
      tso_buffers (tm tpc') t = tso_buffers (tm tpc) t ++ tail ->
      tail <> nil ->
      l = tau /\ t = cid tpc.
  Proof.
    clear. intros. destruct l.
    { split; auto. destruct (peq t (cid tpc)); auto.
      exploit tau_step_buffer_eq. eauto. eauto. intros. rewrite H2 in H0.
      exfalso. apply H1. eauto using app_tail_eq_nil. }
    { exfalso. inv H; simpl in *. eauto using app_tail_eq_nil. }
    { exfalso. inv H; simpl in *. 
      unfold unbuffer in *. destruct (peq t t0). subst.
      destruct (tso_buffers tm t0). discriminate.
      destruct apply_buffer_item; inv H_unbuf. simpl in *.
      unfold tupdate in *. destruct peq; [|contradiction].
      revert H0. clear. revert b tail. induction b0; try discriminate.
      intros. inv H0. eauto.
      destruct (tso_buffers tm t0). discriminate.
      destruct apply_buffer_item; inv H_unbuf. simpl in *.
      unfold tupdate in *. destruct peq; [contradiction|].
      eauto using app_tail_eq_nil. }
    { exfalso. inv H; simpl in *. eauto using app_tail_eq_nil. }
  Qed.

  Lemma MS_client_core_client_fp':
    forall SGE TGE i_obj spc tpc fp spc',
      MS SGE TGE i_obj spc tpc ->
      client_core TGE i_obj (cid tpc) tpc ->
      glob_step spc ETrace.tau fp spc' ->
      client_fp' (gm spc) fp.
  Proof.
    intros.
    eapply client_fp_client_fp'.
    eapply MS_client_core_step_client_fp; eauto.
  Qed.
  
(*  Inductive insert_buffer_fp: FP.t -> Prop :=
  | insert_write: forall ge chunk a rs,
      insert_buffer_fp (exec_store_fp ge chunk a rs)
  | insert_free: forall fp' b lo hi,
      (forall b' ofs', FP.locs fp' b' ofs' = true -> b' = b) ->
      insert_buffer_fp (FP.union fp' (FMemOpFP.free_fp b lo hi))
  | insert_alloc: forall fp' b lo hi,
      (forall b' ofs', FP.locs fp' b' ofs' = true -> b' = b /\ lo <= ofs' < hi) ->
      insert_buffer_fp (FP.union (tsoalloc_fp b lo hi) fp')
  . 

  Lemma insert_buffer_fp_conflict:
    forall fp0 fp fpS,
      insert_buffer_fp fp0 ->
      FP.conflict fp0 fp ->
      fpmatchc fpS fp ->
      FP.conflict fp0 fpS.
  Proof.
    clear. intros.
  Qed.

  Lemma buffer_append_insert_buffer_fp:
    forall TGE tpc fp tpc' head tail,
      @tso_globstep TGE tpc tau fp tpc' ->
      tso_buffers (tm tpc) (cid tpc) = head ->
      tso_buffers (tm tpc') (cid tpc) = head ++ tail ->
      tail <> nil ->
      insert_buffer_fp fp.
  Proof.
    clear. intros. inv H; simpl in *.
    { (* core step *)
      unfold tupdate in H1. destruct peq; [subst|contradiction].
      revert H2 H_core_step. 
      generalize (TSOGlobEnv.modules TGE (TSOCore.i c))
                 (FLists.get_fl (TSOGlobEnv.freelists TGE) (TSOCore.F c))
                 (TSOCore.c c) (tso_buffers tm t) (memory tm) cc' gm'.
      clear. intros ge fl c buf gm c' gm' Htail Hstep.
      inv Hstep. destruct tsofm' as [buf' fm']. simpl in H9. subst buf'.
      clear H4. inv H7.
      { (* exec_instr *)
        destruct i; simpl in *; inv H3;
          unfold exec_load_TSO, tso_goto_label in *;
          repeat match goal with
                 | |- insert_buffer_fp (exec_store_fp _ _ _ _) =>
                   apply insert_write
                 | H: match ?a with _ => _ end = Next _ _ |- _ =>
                   destruct a eqn:?; inv H
                 | H: ?A <> ?A |- _ => contradiction
                 | H: ?A = ?A ++ tail |- _ =>
                   contradict Htail; rewrite (app_nil_end A) in H at 1;
                     eapply app_inv_head; eauto
                 end.
        (* free *)
        apply insert_free. intros. revert H3.
        
        
      }
      { (* alloc *)
        eapply insert_alloc. intros.
        
      }
      { contradict Htail.
        rewrite (app_nil_end buf) in H at 1. eapply app_inv_head; eauto. }
      { contradict Htail.
        rewrite (app_nil_end buf) in H at 1. eapply app_inv_head; eauto. }
      { contradict Htail.
        rewrite (app_nil_end buf) in H at 1. eapply app_inv_head; eauto. }
      { (* initialize core *)
        eapply insert_alloc. intros.

      }
    }
    all: contradict H2; rewrite (app_nil_end (tso_buffers tm t)) in H1 at 1; eapply app_inv_head; eauto.
  Qed.
 *)
  
  Lemma buffer_append_conflict_bi_fp_conflict:
    forall TGE tpc fp0 tpc' head tail bi fp,
      @tso_globstep TGE tpc tau fp0 tpc' ->
      tso_buffers (tm tpc) (cid tpc) = head ->
      tso_buffers (tm tpc') (cid tpc) = head ++ tail ->
      In bi tail ->
      conflict_bi fp bi ->
      FP.conflict fp0 fp.
  Proof. clear. intros. eapply conflict_bi_conflict_fp; eauto. congruence. Qed.

  Lemma PreviouslyInserted'_conflict_client_core:
    forall SGE TGE i_obj t0 bi tpc0 spc0 head tail tpc fp,
      MS SGE TGE i_obj spc0 tpc0 ->
      PreviouslyInserted' TGE i_obj t0 bi tpc0 head tail tpc ->
      t0 <> cid tpc ->
      tso_client_step_fp TGE i_obj tpc fp ->
      conflict_bi fp bi ->
      client_core TGE i_obj (cid tpc0) tpc0.
  Proof.
    intros SGE TGE i_obj t0 bi.
    intros tpc0 spc0 head tail tpc fp MATCH0 PI0 Hcid Hclientfp Hconflict.
    inv PI0. exploit more_buffer_item_tau_step. eauto. eauto. clear. destruct head'; intro C; inv C.
    intros [Hl Ht0]; subst l t0.
    exploit MS_tau_step_fp_cases. eauto. eauto. auto.
    intros [(Result & _) | (Hobject_core & fpS0 & spc1 & Hsstep0 & MATCH1 & Hobjfp)]. auto.
    exfalso. clear Hobject_core.
    assert (exists spcn, MS SGE TGE i_obj spcn tpc /\
                    GMem.forward (gm spc1) (gm spcn)) as (spcn & MATCHn & Hforward).
    { apply bi_not_unbuffered'_non_conflicting_steps in H3.
      clear Hsstep0 Hobjfp bi spc0 head tail MATCH0 Hcid Hclientfp Hconflict head' tail' H0 H1 H2 fp0 fpS0 fp.
      revert H3 spc1 MATCH1. induction 1.
      eexists. split; eauto using GMem.forward_refl.
      intros. destruct H as [(Hcid & [Hl| [v Hl]]) | [Hl | [t' Hl]]]; subst l.
      { exploit MS_preserved_after_tau_step_if_not_conflicting_client_fp.
        exact MATCH1. exact H0. auto. intros (spc2 & fpS1 & Hsstep1 & MATCH2).
        exploit IHnon_conflicting_steps. exact MATCH2. intros (spcn & MATCHn & Hforward).
        exploit MS_src_tau_star_step_gmem_forward. exact MATCH1. eauto. intro.
        exists spcn. split. auto. eauto using GMem.forward_trans. }
      { exploit MS_preserved_after_evt_step; eauto. intros (spc2 & Hsstep1 & MATCH2).
        exploit IHnon_conflicting_steps; eauto. intros (spcn & MATCHn & Hfoward).
        exists spcn. split; eauto using GMem.forward_trans, MS_src_step_gmem_forward. }
      { exploit sw_step_emp_fp. eauto. intro; subst fp.
        exploit MS_preserved_after_sw; eauto. intros (spc2 & Hsstep1 & MATCH2).
        exploit IHnon_conflicting_steps; eauto. intros (spcn & MATCHn & Hfoward).
        exists spcn. split; eauto using GMem.forward_trans, MS_src_step_gmem_forward. }
      { exploit ub_step_emp_fp. eauto. intro; subst fp.
        exploit MS_preserved_after_unbuffer. eauto. eauto. eauto. }
    }
    exploit MS_tso_client_step_fp_match.
    exact MATCHn. eauto. intros (spc' & fpS & Hsstepn & Hfpmatchc).
    exploit buffer_append_conflict_bi_fp_conflict. exact H0. eauto. eauto.
    apply in_app. right. simpl. left. eauto. eauto. intro.
    exploit fp_subset_conflict_full_conflict. eauto. eauto. 
    apply FP.smile_conflict_compat.
    eapply obj_fp_forward_client_fp'_smile.
    eapply MS_sep_obj_client_blocks. exact MATCH0.
    eauto.
    eapply MS_src_tau_star_step_gmem_forward. exact MATCH0. eauto. eauto.
    eapply MS_client_core_client_fp'; eauto. inv Hclientfp.
    econstructor; eauto.
  Qed.

  Inductive tau_step_followed_by_unbuffer {TGE: TSOGlobEnv.t}
    : TSOProgConfig -> FP.t -> TSOProgConfig -> Prop :=
  | tau_step_with_nonempty_buffer:
      forall tpc fp tpc',
        @tso_globstep TGE tpc tau fp tpc' ->
        tau_step_followed_by_unbuffer tpc fp tpc'
  | tau_step_followed_by_unbuffers:
      forall tpc fp tpc' tpc'',
        tso_buffers (tm tpc) (cid tpc) = nil ->
        @tso_globstep TGE tpc tau fp tpc' ->
        ub_star TGE (cid tpc) tpc' tpc'' ->
        tau_step_followed_by_unbuffer tpc fp tpc''.

  Lemma MS_preserved_after_tau_ub_non_conflicting_client_step:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      forall tpc' fp,
        tau_step_followed_by_unbuffer tpc fp tpc' ->
        client_core TGE i_obj (cid tpc) tpc ->
        ~ conflictc (cid tpc) fp (tso_buffers (tm tpc)) ->
        exists fpS spc',
          glob_step spc ETrace.tau fpS spc' /\
          fpmatchc fpS fp /\
          MS SGE TGE i_obj spc' tpc'.
  Proof.
    intros SGE TGE i_obj spc tpc MATCH tpc' fp H Hclient Hconflict.
    destruct H.
    exploit MS_preserved_after_tau_non_conflicting_client_step; eauto.
    exploit MS_preserved_after_tau_non_conflicting_client_step; eauto.
    intros [fpS [spc' [Hstep [Hfp MATCH']]]].
    eexists _, spc'; split. eauto.
    revert H1 MATCH'. clear H H0 Hclient Hconflict Hstep MATCH.
    induction 1. auto. intro. apply IHub_star. 
    eapply MS_preserved_after_unbuffer. eauto. eauto.
  Qed.
    
  Lemma eq_config_not_unbuffered':
    forall TGE i_obj t0 tpc0 tpc0' bi0 head0 tail0 tpcn headn tailn,
      bi_not_unbuffered' TGE i_obj t0 bi0 head0 tail0 tpc0 headn tailn tpcn ->
      eq_config TGE tpc0 tpc0' ->
      exists tpcn', 
        bi_not_unbuffered' TGE i_obj t0 bi0 head0 tail0 tpc0' headn tailn tpcn' /\
        eq_config TGE tpcn tpcn'.
  Proof.
    clear. intros TGE i_obj t0 tpc0 tpc0' bi0 head0 tail0 tpcn headn tailn Hbnu.
    revert tpc0'. induction Hbnu.
    intros. destruct tpc0'. subst tpc. inv H0; simpl in *.
    eexists. split. eapply bi_nub_refl'. congruence.
    econstructor; eauto.
    intros ? Heq0. exploit eq_config_eq_step. exact Heq0. eauto.
    intros [tpc1' [Hstep' Heq1]].
    specialize (IHHbnu _ Heq1). destruct IHHbnu as [tpcn' [Hbnu' Heqn]].
    exists tpcn'. split; auto.
    econstructor. instantiate (1:= l). erewrite <- eq_cid; eauto.
    eauto. inv Heq0; congruence. inv Heq1. rewrite <- eq_buffer. eauto.
    auto. erewrite <- eq_cid; eauto. erewrite <- eq_buffer; eauto. intro.
    apply H4. eapply eq_config_eq_client_core; eauto. auto using eq_config_sym.
    auto.
  Qed.

  Lemma eq_config_client_step_fp:
    forall TGE i_obj tpc tpc' fp,
      eq_config TGE tpc tpc' ->
      tso_client_step_fp TGE i_obj tpc fp ->
      tso_client_step_fp TGE i_obj tpc' fp.
  Proof.
    clear. intros TGE i_obj tpc tpc' fp EQ CLIENTFP.
    inv CLIENTFP. inv EQ. destruct tpc, tpc'; simpl in *. subst.
    exploit gmem_buffer_eq_corestep_eq. eauto. eauto.
    intros (gm' & Hstep & _).
    econstructor; simpl; eauto.
    rewrite <- eq_buffer. eauto.
  Qed.

  Lemma tau_ub_evt_reorder:
    forall TGE (tpc0 tpc1 tpc2 tpc3: @TSOProgConfig TGE)
      (FLWD: FLists.wd (TSOGlobEnv.freelists TGE))
      (INVTHDP1: inv TGE tpc0.(thrdpool))
      fp0 v,
      tau_step_followed_by_unbuffer tpc0 fp0 tpc1 ->
      tso_globstep tpc1 sw FP.emp tpc2 ->
      tso_globstep tpc2 (evt v) FP.emp tpc3 ->
      cid tpc0 <> cid tpc2 ->
      exists _tpc2 _tpc2' _tpc0 _tpc0',
        tso_globstep tpc0 sw FP.emp _tpc2 /\
        cid _tpc2 = cid tpc2 /\
        tso_globstep _tpc2 (evt v) FP.emp _tpc2' /\
        tso_globstep _tpc2' sw FP.emp _tpc0 /\
        cid _tpc0 = cid tpc0 /\
        tau_step_followed_by_unbuffer _tpc0 fp0 _tpc0' /\
        eq_config_but_cid TGE tpc3 _tpc0'.
  Proof.
    clear. intros TGE tpc0 tpc1 tpc2 tpc3 FLWD INVTHDP1 fp0 v Htau_ub Hsw Hevt Hcid.
    destruct Htau_ub.
    { exploit diff_thrd_normal_step_reorder'.
      eauto. eauto. 
      instantiate (1:= tau). simpl. auto. eauto.
      erewrite tau_step_cid_eq. eauto. eauto. auto.
      instantiate (1:= evt v). simpl. auto. eauto.
      apply smile_emp_fp.
      intros (_tpc2 & _tpc2' & _tpc1 & _tpc1' & Hswto2 & Hcid2 & Hevt2 & Hswto1 & Hcid1 & Htau1 & Heq).
      exists _tpc2, _tpc2', _tpc1, _tpc1'. repeat (split; auto). apply tau_step_with_nonempty_buffer. auto. }
    { exploit ub_star_evt_reorder.
      eauto. eauto. eauto. intros (_tpc2 & tpc2' & _tpcub & Hsw' & Hcid2 & Hevt' & Hubstar' & Heq').
      exploit diff_thrd_normal_step_reorder'.
      eauto. eauto.
      instantiate (1:= tau). simpl. auto. eauto.
      rewrite <- Hcid2 in Hcid. erewrite tau_step_cid_eq; try exact Hcid. eauto. auto.
      instantiate (1:= evt v). simpl. auto. eauto.
      apply smile_emp_fp.
      intros (? & ? & ? & ? & Hsw'' & Hcid'' & Hevt'' & Hsw''' & Hcid''' & Htau1'' & Heq'').
      exists x, x0, x1.
      exploit eq_config_but_cid_ub_star. exact Heq''. eauto. intros (? & Hubstar'' & Heq''').
      eexists. do 2 (split; auto). congruence. split; auto. split; auto. split; auto.
      split. eapply tau_step_followed_by_unbuffers.
      rewrite Hcid'''. erewrite sw_step_buffer_eq; try exact Hsw'''.
      inv Hevt''. simpl in *. subst. eapply sw_step_buffer_eq in Hsw''. simpl in *. rewrite Hsw''. auto.
      eauto. rewrite Hcid'''. eauto. eauto using eq_config_but_cid_trans. }
  Qed.

  Lemma tau_ub_step_non_emp_fp_sw:
    forall TGE tpc fp tpc',
      fp <> FP.emp ->
      TSOThrdPool.valid_tid (thrdpool tpc') (cid tpc') ->
      @tau_step_followed_by_unbuffer TGE tpc fp tpc' ->
      tso_globstep tpc' sw FP.emp tpc'.
  Proof.
    clear. intros.
    inv H1.
    inv H2; simpl in *; try congruence.
    econstructor; eauto.
    intro. inv H1. inv H_tp_upd. simpl in *.
    rewrite PMap.gss in H2. inv H2.
    destruct tpc'. simpl in *.
    econstructor; eauto.
    apply ub_star_thdp_cid_unchg in H4. simpl in *.
    inv H3; simpl in *; auto. destruct H4; subst.
    intro. inv H1. inv H_tp_upd. simpl in *.
    rewrite PMap.gss in H3. inv H3.
  Qed.
  
  
  Lemma tau_ub_unbuffer_reorder:
    forall TGE tpc0 fp0 tpc1 t tpc2
      (FLISTWD:   FLists.wd (TSOGlobEnv.freelists TGE))
      (INVTHDP1: inv TGE tpc0.(thrdpool))
      (LALLOC:thread_buffered_alloc_local (TSOGlobEnv.freelists TGE)(tm tpc0)),
      FLs_embed (TSOGlobEnv.freelists TGE) (tm tpc0) ->
      tau_step_followed_by_unbuffer tpc0 fp0 tpc1 ->
      tso_globstep tpc1 (ub t) FP.emp tpc2 ->
      ~ conflictc (cid tpc0) fp0 (tso_buffers (tm tpc0)) ->
      exists _tpc0 _tpc1,
        ub_star TGE t tpc0 _tpc0 /\
        tau_step_followed_by_unbuffer _tpc0 fp0 _tpc1 /\
        eq_config_but_cid TGE _tpc1 tpc2.
  Proof.
    clear. intros TGE tpc0 fp0 tpc1 t tpc2 FLISTWD INVTHDP1 LALLOC
                  Hfls Htau_ub Hub Hconflict0.
    destruct (peq t (cid tpc0)).
    (* ub same thread *)
    { subst t. destruct Htau_ub.
      (* tau case *)
      { destruct (tso_buffers (tm tpc) (cid tpc)) eqn:Hbuffer0.
        { exists tpc, tpc2. split. constructor. split.
          eapply tau_step_followed_by_unbuffers; eauto.
          eapply ub_star_cons. eauto. apply ub_star_refl.
          apply eq_config_but_cid_refl. }
        { exploit same_thrd_normal_unbuffer_step_reorder; try exact H. 
          auto. rewrite Hbuffer0. discriminate. simpl. auto. eauto.
          intros (_tpc0 & Hub' & Htau').
          exists _tpc0, tpc2. split.
          eapply ub_star_cons. eauto. apply ub_star_refl.
          split.
          apply tau_step_with_nonempty_buffer. auto.
          apply eq_config_but_cid_refl. }
      }
      (* tau with ub case *)
      { exists tpc, tpc2. split. constructor. split; [|auto using eq_config_but_cid_refl].
        eapply tau_step_followed_by_unbuffers. auto. eauto.
        revert H1 Hub. clear. induction 1.
        intros. eapply ub_star_cons. eauto. apply ub_star_refl.
        intros. eapply ub_star_cons; eauto. }
    }
    (* ub different thread *)
    { destruct Htau_ub.
      (* tau case *)
      { exploit diff_thrd_normal_unbuffer_step_reorder'; try exact H.
        auto. auto.  auto.
        {
          instantiate(1:=t).
          eapply thread_buffered_alloc_local_buffer_local_alloc with(t:=t) in LALLOC;eauto.
          eapply buffer_local_alloc_preserve;eauto.
        }
        auto.
        simpl; auto. eauto. eauto.
        intros (_tpc0 & _tpc2 & Hub' & Hstep' & Heq2).
        exists _tpc0, _tpc2.
        split. econstructor; eauto. constructor.
        split. apply tau_step_with_nonempty_buffer. auto.
        apply eq_config_eq_config_but_cid; auto using eq_config_sym. }
      (* tau and ub case *)
      { exploit ub_star_ub_step_reorder. exact H1. exact Hub. auto.
        intros. eapply non_conflicting_tau_step_buffer_fp_smile; eauto.
        intros (_tpc2 & _tpc3 & Hub' & Hubstar' & Heq').
        exploit diff_thrd_normal_unbuffer_step_reorder'; try exact H; eauto.
        {
          eapply thread_buffered_alloc_local_buffer_local_alloc with(t:=t) in LALLOC;eauto.
          eapply buffer_local_alloc_preserve;eauto.
        }
        simpl. auto.
        intros (_tpc0 & _tpc1 & Hub'' & Htau' & Heq'').
        exploit eq_config_eq_ub_star. exact Heq''. exact Hubstar'.
        intros (_tpc2' & Hubstar'' & Heq''').
        exists _tpc0, _tpc2'. split. econstructor; eauto. constructor.
        split. eapply tau_step_followed_by_unbuffers.
        erewrite ub_step_buffer_eq. erewrite ub_step_cid_eq. eauto. eauto. eauto.
        erewrite ub_step_cid_eq. eauto. eauto.
        eauto. 
        erewrite ub_step_cid_eq. eauto. eauto.
        eapply eq_config_eq_config_but_cid.
        eapply eq_config_trans. apply eq_config_sym. eauto. apply eq_config_sym. eauto.
      }
    }
  Qed.
            
  Lemma PreviouslyInserted'_adjacent_conflicting_step:
    forall SGE TGE i_obj t0 bi tpc0 spc0 head tail tpc fp,
      MS SGE TGE i_obj spc0 tpc0 ->
      PreviouslyInserted' TGE i_obj t0 bi tpc0 head tail tpc ->
      t0 <> cid tpc ->
      tso_client_step_fp TGE i_obj tpc fp ->
      conflict_bi fp bi -> 
      exists spc0' tpc0' fp0 tpc0'' tpc',
        MS SGE TGE i_obj spc0' tpc0' /\
        t0 = cid tpc0' /\
        client_core TGE i_obj (cid tpc0') tpc0' /\
        ~ conflictc (cid tpc0') fp0 (tso_buffers (tm tpc0')) /\
        tau_step_followed_by_unbuffer tpc0' fp0 tpc0'' /\
        tso_globstep tpc0'' sw FP.emp tpc' /\
        cid tpc' = cid tpc /\
        tso_client_step_fp TGE i_obj tpc' fp /\
(*        insert_buffer_fp fp0 /\ *)
        FP.conflict fp0 fp.
  Proof.
    intros SGE TGE i_obj t0 bi tpc0 spc0 head tail tpc fp MATCH0 PI0 Hcidn Hfp Hconflict.
    exploit PreviouslyInserted'_conflict_client_core; eauto.
    destruct PI0 as [? ? ? ? ? ? ? ? ? Hbuffer0 Hstep0 Hbuffer1 Hconflict0 H].
    exploit buffer_insert_cid_label; try exact Hstep0.
    rewrite Hbuffer0. eauto. destruct head'; intro C; inv C.
    intros [Ht0 Hl]; subst l.
(*    exploit buffer_append_insert_buffer_fp.
    exact Hstep0. rewrite <- Ht0. exact Hbuffer0. rewrite <- Ht0. eauto. 
    destruct head'; simpl; intro C; inv C. *)
    exploit conflict_bi_conflict_fp; eauto. 
    subst t0. rewrite Hbuffer0. eauto. apply in_app_iff. right. simpl. auto.
    clear Hconflict. intros Hconflict Hclient0.
    specialize (Hconflict0 Hclient0).
    exploit (@tau_step_with_nonempty_buffer TGE). exact Hstep0.
    clear Hstep0. clear Hbuffer0 Hbuffer1.
    exploit bi_not_unbuffered'_non_conflicting_steps. eauto.
    clear bi head head' tail' headn tailn H.
    intros H Htau_ub.
    exploit tau_ub_step_non_emp_fp_sw; try exact Htau_ub.
    exploit FP.emp_never_conflict. eauto. intuition.
    { revert MATCH0 Htau_ub. clear. intros.
      exploit tid_eq. eauto. intro.
      apply thdp_sims in MATCH0.
      assert (TSOThrdPool.valid_tid (thrdpool tpc0) (cid tpc0)).
      { unfold TSOThrdPool.valid_tid. 
        erewrite <- valid_tid_eq; eauto. rewrite <- H.
        assert (exists tpc', tso_globstep tpc0 tau fp0 tpc') by (inv Htau_ub; eauto).
        clear tpc1 Htau_ub. destruct H0 as [tpc1 Htau].
        assert (exists tcs, (TSOThrdPool.content (thrdpool tpc0)) !! (cid tpc0) = Some tcs)
          as [tcs Htp] by (inv Htau; eauto).
        clear Htau. rewrite <- H in Htp.
        exploit thread_simulation. eauto. rewrite Htp. intro A; inv A.
        apply tp_inv_src in MATCH0.
        destruct (plt (cur_tid spc0) (ThreadPool.next_tid (thread_pool spc0))); auto.
        apply ThreadPool.tp_finite in n; auto.
        unfold ThreadPool.get_cs in H0. congruence.
      }
      Lemma tso_globstep_valid_tid:
        forall TGE tpc l fp tpc' t,
          @tso_globstep TGE tpc l fp tpc' ->
          TSOThrdPool.valid_tid (thrdpool tpc) t <->
          TSOThrdPool.valid_tid (thrdpool tpc') t.
      Proof.
        clear. inversion 1; simpl in *; subst; try tauto.
        inv H_tp_upd; simpl; tauto.
        unfold TSOThrdPool.push in H_tp_push.
        destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_push. tauto.
        inv H_tp_upd. simpl in *.
        unfold TSOThrdPool.pop in H_tp_pop. 
        destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
        destruct l; inv H2. simpl. tauto.
        unfold TSOThrdPool.pop in H_tp_pop. 
        destruct ((TSOThrdPool.content thdp) !! t0); inv H_tp_pop.
        destruct l; inv H1. simpl. tauto.
        inv H_tp_upd; simpl; tauto.
      Qed.
      inv Htau_ub.
      rewrite <- tso_globstep_valid_tid; eauto.
      erewrite tau_step_cid_eq; eauto.
      apply ub_star_thdp_cid_unchg in H3. destruct H3. rewrite H3, H4.
      rewrite <- tso_globstep_valid_tid; eauto.
      erewrite tau_step_cid_eq; eauto.
    }
    intro Hsw.
    assert (exists tpc00, tau_step_followed_by_unbuffer tpc0 fp0 tpc00 /\
                           eq_config_but_cid TGE tpc1 tpc00)
      as (tpc00 & Htau_ub' & Heq2).
    { eexists. split; eauto. apply eq_config_but_cid_refl. }
    clear Htau_ub Hsw.
    rename Htau_ub' into Htau_ub.
    rename tpc1 into tpc2.
    rename tpc00 into tpc1.
    
    assert (exists spc0' tpc0' tpc0'' tpc',
               MS SGE TGE i_obj spc0' tpc0' /\
               t0 = cid tpc0' /\
               client_core TGE i_obj (cid tpc0') tpc0' /\
               ~ conflictc (cid tpc0') fp0 (tso_buffers (tm tpc0')) /\
               tau_step_followed_by_unbuffer tpc0' fp0 tpc0'' /\
               tso_globstep tpc0'' sw FP.emp tpc' /\
               eq_config TGE tpcn tpc')
      as (spc0' & tpc0' & tpc0'' & tpc' & MATCH0' & Ht0' &
          Hclient0' & Hconflict0' & Hstep0' & Hsw' & Heq).
    {
      assert (switchable tpcn (cid tpcn)) as Hswable.
      { revert MATCH0 H Htau_ub Heq2 Hfp. clear. intros.
        unfold switchable. split.
        assert ((TSOThrdPool.content (thrdpool tpcn)) !! (cid tpcn) <> None).
        { inv Hfp. rewrite H0. discriminate. }
        clear Hfp.
        assert ((TSOThrdPool.content (thrdpool tpc2)) !! (cid tpcn) <> None
                /\ (thrd_valid tpc2 (cid tpcn) -> thrd_valid tpcn (cid tpcn))).
        { revert H H0. clear. generalize (cid tpcn). induction 1; auto.
          split.
          apply IHnon_conflicting_steps in H3. clear IHnon_conflicting_steps H2 H1 H.
          destruct H3 as [H3 _].
          Lemma glob_step_cs_not_none':
            forall TGE tpc l fp tpc' t,
              @tso_globstep TGE tpc l fp tpc' ->
              (TSOThrdPool.content (thrdpool tpc')) !! t <> None ->
              (TSOThrdPool.content (thrdpool tpc)) !! t <> None.
          Proof.
            clear. intros. inv H; simpl in *; auto.
            inv H_tp_upd; simpl in *.
            destruct (peq t t0). subst; congruence.
            rewrite PMap.gso in H0; auto.
            unfold TSOThrdPool.push in H_tp_push.
            destruct (peq t t0). subst. congruence.
            rewrite H_tp_core in H_tp_push. inv H_tp_push. simpl in *.
            rewrite PMap.gso in H0; auto.
            unfold TSOThrdPool.pop in H_tp_pop. rewrite H_tp_core in H_tp_pop. inv H_tp_pop.
            destruct (peq t t0). subst. congruence.
            inv H_tp_upd. simpl in *. do 2 rewrite PMap.gso in H0; auto.
            unfold TSOThrdPool.pop in H_tp_pop. rewrite H_tp_core in H_tp_pop. inv H_tp_pop.
            destruct (peq t t0). subst. congruence.
            simpl in *. rewrite PMap.gso in H0; auto.
            inv H_tp_upd; simpl in *.
            destruct (peq t t0). subst; congruence.
            rewrite PMap.gso in H0; auto.
          Qed.
          eapply glob_step_cs_not_none'; eauto.
          intro. eapply glob_step_valid' in H0; eauto. intuition.
        }
        clear H0. destruct H1. apply H1. clear H1 H.
        cut (thrd_valid tpc1 (cid tpcn)). intro.
        inv Heq2. unfold thrd_valid in *. congruence.
        erewrite eq_thrdpool' in H0; eauto. clear Heq2.
        destruct Htau_ub.
        Lemma MS_tp_not_none_valid:
          forall SGE TGE i_obj spc tpc t,
            MS SGE TGE i_obj spc tpc ->
            (TSOThrdPool.content (thrdpool tpc)) !! t <> None ->
            thrd_valid tpc t.
        Proof.
          clear. intros. apply thdp_sims in H.
          exploit valid_tid_eq; eauto.
          exploit thread_simulation; eauto.
          instantiate (1:= t). intros. inv H1. rewrite <- H5 in H0. contradiction.
          unfold thrd_valid, TSOThrdPool.valid_tid. rewrite <- H2.
          destruct (plt t (ThreadPool.next_tid (thread_pool spc))); auto.
          eapply ThreadPool.tp_finite in n. unfold ThreadPool.get_cs in *. congruence.
          inv H; auto.
        Qed.
        eapply glob_step_valid'; eauto.
        eapply MS_tp_not_none_valid. eauto.
        eapply glob_step_cs_not_none'; eauto.
        apply ub_star_thdp_cid_unchg in H2. destruct H2.
        rewrite H2 in H0.
        unfold thrd_valid. rewrite H2.
        eapply glob_step_valid'; eauto.
        eapply MS_tp_not_none_valid. eauto. 
        eapply glob_step_cs_not_none'; eauto.
        
        unfold thrd_not_halted. intro. inv H0. inv Hfp. congruence.
      }
      clear fp Hfp Hconflict.
      revert tpc0 spc0 fp0 tpc1 MATCH0 Htau_ub Heq2 Ht0 Hclient0 Hconflict0.
      induction H.
      { intros.
        Lemma switchable_sw_step:
          forall TGE tpc t,
            switchable tpc t ->
            exists tpc', @tso_globstep TGE tpc sw FP.emp tpc' /\
                    eq_config_but_cid TGE tpc tpc' /\
                    cid tpc' = t.
        Proof.
          clear. intros. destruct tpc. eexists. split.
          econstructor; destruct H; eauto.
          split; auto. constructor; auto using GMem.eq_refl.
        Qed.
        Lemma switchable_eq_config_but_cid_switchable:
          forall TGE tpc t tpc',
            switchable tpc t ->
            eq_config_but_cid TGE tpc tpc' ->
            switchable tpc' t.
        Proof.
          clear. unfold switchable. intros. inv H0. destruct H. split.
          unfold thrd_valid in *. congruence.
          unfold thrd_not_halted in *. congruence.
        Qed.
        eapply switchable_eq_config_but_cid_switchable in Hswable; eauto.
        exploit switchable_sw_step. eauto. intros (_tpc' & Hsw & Heq2' & Hcid').
        exists spc0, tpc0, tpc1, _tpc'. do 4 (split; auto).
        split. auto. split. auto.
        Lemma eq_config_but_cid_eq_cid_eq_config:
          forall TGE tpc tpc',
            eq_config_but_cid TGE tpc tpc' ->
            cid tpc = cid tpc' ->
            eq_config TGE tpc tpc'.
        Proof. clear. intros. inv H. constructor; auto. Qed.
        apply eq_config_but_cid_eq_cid_eq_config; auto.
        eapply eq_config_but_cid_trans; eauto. 
      }
      { specialize (IHnon_conflicting_steps Hcidn Hswable).
        intros tpc0 spc0 fp0 tpc1 MATCH0 Htau_ub Heq2 Ht0 Hclient0 Hconflict0.
        rename tpc into tpc2. rename l into l2. rename fp into fp2. rename tpc' into tpc3.
        rename H into Hlabel. rename H0 into Hstep'. rename H1 into Hconflict'. clear H2.
        exploit MS_preserved_after_tau_ub_non_conflicting_client_step; eauto.
        intros (fpS1 & spc1 & Hsstep0 & Hmatchfp1 & MATCH1).
        destruct Hlabel as [[Hcid2 [Htau | [v Hevt]]] | [Hsw | Hub]].
        (* tau step *)
        { subst l2. clear Hswable.
          assert (Hswable2: switchable tpc1 (cid tpc2)).
          { revert Hstep' Heq2 MATCH1. clear. intros.
            assert (exists c cs, (TSOThrdPool.content (thrdpool tpc2)) !! (cid tpc2) = Some (c :: cs)).
            { inv Hstep'; simpl in *; eauto. } 
            clear Hstep'. destruct H as [c [cs Hthdp]].
            erewrite eq_thrdpool' in Hthdp; eauto.
            exploit thdp_sims. eauto. intro.
            exploit valid_tid_eq. eauto. intro.
            exploit thread_simulation. eauto. intro.
            inv H1. exfalso. rewrite Hthdp in H4. discriminate. 
            split. unfold thrd_valid, TSOThrdPool.valid_tid. rewrite <- H0.
            destruct (plt (cid tpc2) (ThreadPool.next_tid (thread_pool spc1))); auto.
            eapply ThreadPool.tp_finite in n. unfold ThreadPool.get_cs in H2. congruence.
            eapply tp_inv_src. eauto.
            unfold thrd_not_halted. intro. inv H1. congruence.
          }
          assert (exists _tpc2, tso_globstep tpc1 sw FP.emp _tpc2 /\
                           eq_config TGE tpc2 _tpc2) as [_tpc2 [Hsw1 Heq2']].
          { Lemma eq_config_but_cid_switchable_sw_eq_config:
              forall TGE tpc tpc',
                eq_config_but_cid TGE tpc tpc' ->
                switchable tpc (cid tpc') ->
                exists tpc'', tso_globstep tpc sw FP.emp tpc'' /\
                         eq_config TGE tpc' tpc''.
            Proof.
              clear. intros. destruct tpc, tpc'. simpl in *.
              eapply switchable_sw_step in H0.
              destruct H0 as (tpc'' & Hsw & Heq & Hcid). exists tpc''. split; auto.
              inv Hsw; inv H. simpl in *.
              constructor; simpl; auto using GMem.eq_sym.
            Qed.
            eapply eq_config_but_cid_switchable_sw_eq_config;
              eauto using eq_config_but_cid_sym.
          }
          exploit MS_preserved_after_sw; eauto.
          intros (spc2 & Hssw & MATCH2).
          assert (Hsmile: FP.smile fp0 fp2).
          { clear IHnon_conflicting_steps.
            exploit eq_config_eq_step. exact Heq2'. exact Hstep'. intros (_tpc3 & Hstep2' & Heq).
            assert (client_core TGE i_obj (cid _tpc2) _tpc2 -> ~ conflictc (cid _tpc2) fp2 (tso_buffers (tm _tpc2))).
            { erewrite <- eq_cid; eauto. erewrite <- eq_buffer; eauto. intro. apply Hconflict'.
              inv H; econstructor; eauto. erewrite eq_thrdpool; eauto. }
            revert MATCH0 Hsstep0 Htau_ub Hclient0 MATCH1 Hssw Hsw1 MATCH2 Hstep2' H.
            assert (cid tpc0 <> cid _tpc2).
            { subst t0. apply eq_cid in Heq2'. congruence. }
            revert H. clear t0 tpc'' Hcidn tpc2 tpc3 Hcid2 Hconflict' Hstep' Heq2 Ht0 Hswable2 Heq2' Heq.
            intros. rename _tpc2 into tpc2. rename _tpc3 into tpc3. rename H0 into Hconflict2.
           
            exploit MS_tau_step_fp_cases. exact MATCH2. eauto. eauto.
            intros [ (_ & fpS2 & spc3 & Hsstep2 & HFP2 & MATCH3)
                   | (_ & fpS2 & spc3 & Hsstep2 & MATCH3 & HFP2 )].
            (* client case *)
            { apply FP.smile_conflict_compat. intro.
              exploit adjacent_sc_conflicting_step_race.
              {
                eapply GE_mod_sim_source_lang_wd. eapply GE_eq. eauto.
              }
              eapply GE_wd. exact MATCH0.
              eapply tp_inv_src. eapply thdp_sims. exact MATCH0.
              eapply source_safe. eauto.
              eauto. eauto. eauto.
              erewrite tid_eq; try exact MATCH0. erewrite tid_eq; try exact MATCH2. auto.
              eapply fp_subset_conflict_full_conflict.
              eapply FP.conflict_sym, fp_subset_conflict_full_conflict.
              eapply FP.conflict_sym. eauto. eauto. eauto.
              intro. eapply source_drf. exact MATCH0. auto. }
            (* object case *)
            { eapply adjacent_client_fp_obj_fp_smile.
              eapply MS_sep_obj_client_blocks. exact MATCH0.
              eapply MS_client_core_step_client_fp in Hsstep0; try exact MATCH0; eauto.
              Lemma fpmatchc_client_fp_preserve:
                forall fpS fpT gm1 gm2,
                  fpmatchc fpS fpT ->
                  client_fp gm1 gm2 fpS ->
                  client_fp gm1 gm2 fpT.
              Proof.
                clear. intros. inv H0.
                { apply client_emp_fp. eapply FP.fp_eq, FP.subset_eq; eauto using FP.subset_emp. }
                { eapply client_valid_block_fp. intros. eapply H_client_valid_block_fp.
                  unfold FP.locs in *. eapply FP.subset_ge_cmps_subset; eauto. }
                { eapply client_alloc_fp. intros; eapply H_client_alloc_fp.
                  unfold FP.locs in *. eapply FP.subset_ge_cmps_subset; eauto. }
              Qed.
              eapply fpmatchc_client_fp_preserve. eauto. eauto.
              eapply MS_src_step_gmem_forward. exact MATCH0. eauto.
              eapply MS_client_core_step_obj_mem_eq. eauto. eauto. eauto.
              inv Hssw. simpl in *. eauto. }
          }
          exploit eq_config_eq_step. exact Heq2'. exact Hstep'.
          intros (_tpc3 & Hstep'' & Heq3).
          clear MATCH1 Hsstep0 spc1 Hssw MATCH2 spc2 Heq2 Hstep'.
          destruct Htau_ub.
          (* tau case *)
          { (* reorder tau and tau... *)
            exploit diff_thrd_normal_step_reorder'.
            eapply MS_tge_flwd;eauto. eapply inv_thdp;eauto.
            instantiate (1:= tau). simpl. auto. exact H.
            instantiate (1:= _tpc2). erewrite tau_step_cid_eq; [|eauto].
            rewrite <- Ht0. intro. apply Hcid2. rewrite H0. apply eq_cid. auto.
            assumption.
            instantiate (1:= tau). simpl. auto. exact Hstep''.
            assumption.
            intros (_tpc2' & _tpc3' & _tpc0' & _tpc1' &
                    Hswto2 & Hcid2' & Htau2' & Hswto1 & Hcid1' & Htau1' & Heq3').
            (* construct MS on new tpc0 *)
            exploit MS_preserved_after_sw. exact MATCH0. exact Hswto2.
            intros (_spc2' & _ & MATCH2).
            exploit MS_preserved_after_tau_step_if_not_conflicting_client_fp.
            exact MATCH2. exact Htau2'.
            { rewrite Hcid2'. erewrite <- eq_cid; [| exact Heq2']. intro Hclient2.
              eapply less_buffer_item_not_conflict_preserve; try eapply Hconflict'.
              intros. exploit tau_step_buffer_append. exact H. intros [tail Hbuffer2'].
              erewrite sw_step_buffer_eq in H0; try exact Hswto2.
              erewrite eq_buffer; try exact Heq2'.
              erewrite sw_step_buffer_eq. rewrite Hbuffer2'. apply in_app. auto. eauto.
              eapply eq_config_eq_client_core. apply eq_config_sym. eauto.
              revert Hcid2 Hswto2 H Ht0 Hsw1 Hclient2. clear. intros.
              exploit step_diff_tid_thrdp_eq. rewrite <- Ht0. eauto. eauto. 
              erewrite <- sw_step_thdp_eq; eauto. intro.
              inv Hclient2. erewrite sw_step_thdp_eq in H1; eauto.
              econstructor; eauto. rewrite H0. eauto.
            }
            intros (_spc3' & _ & _ & MATCH3).
            clear MATCH2 _spc2'.
            exploit MS_preserved_after_sw. exact MATCH3. exact Hswto1.
            intros (_spc0' & _ & MATCH0').
            clear MATCH3 _spc3'.
            (* construct tau_ub *)
            exploit (@tau_step_with_nonempty_buffer TGE). exact Htau1'.
            intro Htau_ub'.
            (* apply induction hypo *)
            eapply IHnon_conflicting_steps.
            exact MATCH0'.
            exact Htau_ub'. 
            eapply eq_config_but_cid_trans. apply eq_config_eq_config_but_cid.
            exact Heq3. exact Heq3'.
            congruence.
            { rewrite Hcid1'. subst t0.
              revert Hclient0 Hswto1 Htau2' Hswto2 Heq2' Hcid2 Hcid2'. clear.
              intros. inv Hclient0.
              erewrite <- sw_step_thdp_eq in H; eauto.

              erewrite <- step_diff_tid_thrdp_eq in H; try exact Htau2'.
              erewrite <- sw_step_thdp_eq in H; eauto.
              econstructor; eauto.
              intro. apply Hcid2. rewrite <- H1, Hcid2'. apply eq_cid; auto. }
            { rewrite Hcid1'.
              erewrite sw_step_buffer_eq; try exact Hswto1.
              erewrite <- sw_step_buffer_eq in Hconflict0; try exact Hswto2.
              revert Hsmile Htau2' Hconflict0. clear. intros.
              eapply glob_step_fp_smile_conflictc_preserve; eauto.
              auto using smile_sym. }
          }
          (* tau followed by ub star ... *)
          { (* reorder tau_ub and tau ... *)
            exploit diff_thrd_normal_step_unbuffer_normal_step_reorder'.
            eapply MS_tge_flwd;eauto. eapply  fls_embed;eauto.
            eapply inv_thdp;eauto.
            exact H.
            instantiate (1:= tau). simpl. auto. exact H0. exact H1.
            instantiate (1:= _tpc2). apply eq_cid in Heq2'. congruence.
            assumption. 
            instantiate (1:= tau). simpl. auto. exact Hstep''. assumption.
            intros (_tpc2' & _tpc3' & _tpc0' & _tpc1' & _tpc1'' &
                    Hswto2 & Hcid2' & Htau2' & Hswto1 & Hcid1' & Htau1' & Hub1' & Heq3').
            (* construct MS on new tpc0 *)
            exploit MS_preserved_after_sw. exact MATCH0. exact Hswto2.
            intros (_spc2' & _ & MATCH2).
            exploit MS_preserved_after_tau_step_if_not_conflicting_client_fp.
            exact MATCH2. exact Htau2'.
            { rewrite Hcid2'. erewrite <- eq_cid; [| exact Heq2']. intro Hclient2.
              eapply less_buffer_item_not_conflict_preserve; try eapply Hconflict'.
              intros. exploit tau_step_buffer_append. exact H0. intros [tail Hbuffer2'].
              erewrite sw_step_buffer_eq in H2; try exact Hswto2.
              erewrite eq_buffer; try exact Heq2'.
              erewrite sw_step_buffer_eq; [|eauto].
              destruct (peq t' t0).
              subst. rewrite H in H2. inv H2.
              Lemma ub_star_buffer_eq:
                forall TGE t tpc tpc',
                  ub_star TGE t tpc tpc' ->
                  forall t', t' <> t -> tso_buffers (tm tpc') t' = tso_buffers (tm tpc) t'.
              Proof. clear. induction 1. eauto. intros. rewrite IHub_star; eauto using ub_step_buffer_eq. Qed.
              Lemma ub_star_thdp_eq:
                forall TGE t tpc tpc',
                  ub_star TGE t tpc tpc' ->
                  thrdpool tpc = thrdpool tpc'.
              Proof. clear. induction 1. eauto. inv H. simpl in *. congruence. Qed. 
              erewrite ub_star_buffer_eq; try exact H1.
              rewrite Hbuffer2'. apply in_app. auto. subst t0. eauto. 
              eapply eq_config_eq_client_core. apply eq_config_sym. eauto.
              revert Hcid2 Hswto2 H0 H1 Ht0 Hsw1 Hclient2. clear. intros.
              exploit step_diff_tid_thrdp_eq. rewrite <- Ht0. eauto. eauto.
              erewrite ub_star_thdp_eq; [| exact H1]. 
              erewrite <- sw_step_thdp_eq; eauto. intro.
              inv Hclient2. econstructor; eauto. rewrite H. erewrite <- sw_step_thdp_eq; eauto. 
            }
            intros (_spc3' & _ & _ & MATCH3).
            exploit MS_preserved_after_sw. exact MATCH3. exact Hswto1.
            intros (_spc0' & _ & MATCH0').
            clear MATCH3 _spc3'.
            (* construct tau_ub *)
            exploit (@tau_step_followed_by_unbuffers TGE).
            { instantiate (1:= _tpc0'). rewrite <- H. rewrite Hcid1'.
              erewrite sw_step_buffer_eq; try exact Hswto1.
              erewrite tau_step_buffer_eq.
              erewrite sw_step_buffer_eq. eauto. eauto. eauto.
              apply eq_cid in Heq2'. congruence.
            }
            exact Htau1'. rewrite Hcid1'. exact Hub1'.
            intro Htau_ub'.
            (* apply induction hypo *)
            eapply IHnon_conflicting_steps.
            exact MATCH0'.
            exact Htau_ub'. 
            eapply eq_config_but_cid_trans. eapply eq_config_eq_config_but_cid.
            exact Heq3. assumption. congruence.
            { rewrite Hcid1'. subst t0.
              revert Hclient0 Hswto1 Htau2' Hswto2 Heq2' Hcid2 Hcid2'. clear.
              intros. inv Hclient0.
              erewrite <- sw_step_thdp_eq in H; eauto.
              erewrite <- step_diff_tid_thrdp_eq in H; try exact Htau2'.
              erewrite <- sw_step_thdp_eq in H; eauto.
              econstructor; eauto.
              intro. apply Hcid2. rewrite <- H1, Hcid2'. apply eq_cid; auto. }
            { rewrite Hcid1'.
              erewrite sw_step_buffer_eq; try exact Hswto1.
              erewrite <- sw_step_buffer_eq in Hconflict0; try exact Hswto2.
              revert Hsmile Htau2' Hconflict0. clear. intros.
              eapply glob_step_fp_smile_conflictc_preserve; eauto.
              auto using smile_sym. }
          }
        }
        (* evt step *)
        { subst l2. clear Hswable.
          assert (Hswable2: switchable tpc1 (cid tpc2)).
          { revert Hstep' Heq2 MATCH1. clear. intros.
            assert (exists c cs, (TSOThrdPool.content (thrdpool tpc2)) !! (cid tpc2) = Some (c :: cs)).
            { inv Hstep'; simpl in *; eauto. } 
            clear Hstep'. destruct H as [c [cs Hthdp]].
            erewrite eq_thrdpool' in Hthdp; eauto.
            exploit thdp_sims. eauto. intro.
            exploit valid_tid_eq. eauto. intro.
            exploit thread_simulation. eauto. intro.
            inv H1. exfalso. rewrite Hthdp in H4. discriminate. 
            split. unfold thrd_valid, TSOThrdPool.valid_tid. rewrite <- H0.
            destruct (plt (cid tpc2) (ThreadPool.next_tid (thread_pool spc1))); auto.
            eapply ThreadPool.tp_finite in n. unfold ThreadPool.get_cs in H2. congruence.
            eapply tp_inv_src. eauto.
            unfold thrd_not_halted. intro. inv H1. congruence. }
          assert (exists _tpc2, tso_globstep tpc1 sw FP.emp _tpc2 /\
                           eq_config TGE tpc2 _tpc2) as [_tpc2 [Hsw1 Heq2']].
          { eapply eq_config_but_cid_switchable_sw_eq_config;
              eauto using eq_config_but_cid_sym. }
          exploit MS_preserved_after_sw; eauto.
          intros (spc2 & Hssw & MATCH2).
          
          exploit evt_step_emp_fp. exact Hstep'. intro. subst fp2.
          exploit eq_config_eq_step. exact Heq2'. exact Hstep'.
          intros (_tpc3 & Hstep'' & Heq3).
          clear MATCH1 Hsstep0 spc1 Hssw MATCH2 spc2 Heq2 Hstep'.
          exploit tau_ub_evt_reorder.
          eapply MS_tge_flwd;eauto. eapply inv_thdp;eauto.
          exact Htau_ub. exact Hsw1. exact Hstep''.
          apply eq_cid in Heq2'. congruence.
          intros (_tpc2' & _tpc3' & _tpc0' & _tpc1' & 
                  Hswto2 & Hcid2' & Hevt2' & Hswto1 & Hcid1' & Htau_ub1' & Heq3').
          exploit MS_preserved_after_sw.
          exact MATCH0. exact Hswto2. intros (_spc2' & _ & MATCH2').
          exploit MS_preserved_after_evt_step.
          exact MATCH2'. exact Hevt2'. intros (_spc2'' & _ & MATCH2'').
          clear _spc2' MATCH2'.
          exploit MS_preserved_after_sw.
          exact MATCH2''. exact Hswto1. intros (_spc0' & _ & MATCH0').
          clear _spc2'' MATCH2''.
          eapply IHnon_conflicting_steps.
          exact MATCH0'. exact Htau_ub1'.
          eapply eq_config_but_cid_trans.
          eapply eq_config_eq_config_but_cid; eauto. auto.
          congruence.
          { rewrite Hcid1'. subst t0.
            revert Hclient0 Hswto1 Hevt2' Hswto2 Heq2' Hcid2 Hcid2'. clear.
            intros. inv Hclient0.
            erewrite <- sw_step_thdp_eq in H; eauto.
            erewrite <- step_diff_tid_thrdp_eq in H; try exact Hevt2'.
            erewrite <- sw_step_thdp_eq in H; eauto.
            econstructor; eauto.
            intro. apply Hcid2. rewrite <- H1, Hcid2'. apply eq_cid; auto. }
          { rewrite Hcid1'.
            erewrite sw_step_buffer_eq; try exact Hswto1.
            erewrite <- sw_step_buffer_eq in Hconflict0; try exact Hswto2.
            revert Hconflict0 Hevt2'. clear. intros. inv Hevt2'. auto. }
        }
        (* sw case *)
        { subst l2. exploit sw_step_emp_fp. eauto. intro; subst fp2.
          eapply IHnon_conflicting_steps.
          exact MATCH0. exact Htau_ub.
          eapply eq_config_but_cid_trans.
          apply eq_config_but_cid_sym.
          apply sw_step_eq_config_but_cid. eauto.
          exact Heq2. exact Ht0. exact Hclient0. exact Hconflict0. }
        (* ub step case *)
        { destruct Hub as [t' Hlabel]; subst l2.
          clear spc1 MATCH1 Hsstep0 Hswable.
          assert (exists _tpc3, tso_globstep tpc1 (ub t') FP.emp _tpc3 /\
                           eq_config_but_cid TGE tpc3 _tpc3)
          as [_tpc3 [Hstep'' Heq3]].
          { revert Heq2 Hstep'. clear. intros.
            destruct tpc1.
            inv Heq2. inv Hstep'. simpl in *. subst. 
            destruct tm, tm0, tm'. simpl in *.
            exploit gmem_eq_ub_gmem_eq.
            eauto. simpl in *. eauto.
            intros (gm2' & Hunbuffer & Heqm'). 
            eexists. split. econstructor; eauto. subst. eauto.
            simpl. econstructor; eauto. }
          clear Hstep'.
          assert (exists _tpc0 _tpc1,
                     ub_star TGE t' tpc0 _tpc0 /\
                     tau_step_followed_by_unbuffer _tpc0 fp0 _tpc1 /\
                     eq_config_but_cid TGE _tpc1 _tpc3)
            as (_tpc0 & _tpc1 & Hubstar & Htau_ub' & Heq3').
          {
            clear IHnon_conflicting_steps.
            clear Hconflict'. 
            eapply tau_ub_unbuffer_reorder.
            eapply MS_tge_flwd;eauto. eapply inv_thdp;eauto.
            eapply buffered_alloc_local;eauto.
            eapply fls_embed. eauto. 
            eauto. eauto. auto.           
          }
          exploit MS_preserved_after_ub_star.
          exact MATCH0. exact Hubstar. intros MATCH0'.
          eapply IHnon_conflicting_steps.
          exact MATCH0'. exact Htau_ub'.
          eapply eq_config_but_cid_trans; eauto using eq_config_but_cid_sym.
          subst t0. apply ub_star_thdp_cid_unchg in Hubstar. intuition.
          { apply ub_star_thdp_cid_unchg in Hubstar. destruct Hubstar.
            inv Hclient0. econstructor; eauto. rewrite H, H0. eauto. }
          { exploit ub_star_thdp_cid_unchg; try exact Hubstar.
            intros [_ Hcid0']. rewrite Hcid0'.
            eapply less_buffer_item_not_conflict_preserve; try exact Hconflict0.
            generalize Hubstar. clear. induction 1; intros; auto.
            apply IHHubstar in H0. destruct (peq t' t'0).
            subst. apply ub_step_buffer_pop in H. destruct H. rewrite H. simpl. auto.
            eapply ub_step_buffer_eq in H; eauto. congruence.
          }
        }
      }
    }
    exists spc0', tpc0', fp0, tpc0'', tpc'.
    repeat (split; auto).
    apply eq_cid. auto using eq_config_sym.
    eapply eq_config_client_step_fp; eauto.
  Qed.

  
  Lemma conflicting_adjacent_steps_race:
    forall SGE TGE i_obj t0 spc0 tpc0 fp0 tpc0' tpc fp,
      MS SGE TGE i_obj spc0 tpc0 ->
      t0 = cid tpc0 ->
      client_core TGE i_obj (cid tpc0) tpc0 ->
      ~ conflictc (cid tpc0) fp0 (tso_buffers (tm tpc0)) ->
      tau_step_followed_by_unbuffer tpc0 fp0 tpc0' ->
      tso_globstep tpc0' sw FP.emp tpc ->
      t0 <> cid tpc ->
      tso_client_step_fp TGE i_obj tpc fp ->
      FP.conflict fp0 fp -> False.
  Proof.
    intros SGE TGE i_obj t0 spc0 tpc0 fp0 tpc0' tpc fp
           MATCH0 Hcid0 Hclient0 Hconflict0 Htau_ub Hsw Hcid Hclientfp Hconflict.
    exploit MS_preserved_after_tau_ub_non_conflicting_client_step.
    exact MATCH0. exact Htau_ub. exact Hclient0. exact Hconflict0.
    intros (fpS1 & spc1 & Hsstep0 & Hfp & MATCH1).
    exploit MS_preserved_after_sw.
    exact MATCH1. exact Hsw.
    intros (spc2 & Hssw & MATCH2).
    exploit MS_tso_client_step_fp_match. exact MATCH2. exact Hclientfp.
    intros (spc3 & fpS2 & Hsstep2 & FPMATCH).
    exploit fp_subset_conflict_full_conflict; eauto. 
    intro Hsconflict.
    exploit adjacent_sc_conflicting_step_race.
    eapply GE_mod_sim_source_lang_wd. eapply GE_eq; eauto.
    eapply GE_wd; eauto.
    eapply tp_inv_src. eapply thdp_sims. exact MATCH0.
    eapply source_safe. eauto.
    eauto. eauto. eauto.
    erewrite tid_eq;[|eauto].
    erewrite tid_eq;[|eauto].
    congruence.
    eapply FP.conflict_sym, fp_subset_conflict_full_conflict.
    apply FP.conflict_sym. eauto. eauto.
    intro C. eapply source_drf. exact MATCH0. auto.
  Qed.
  
  Theorem PreviouslyInserted_no_conflicting_client_fp:
    forall SGE TGE i_obj t' bi spc0 tpc0 head tail tpc,
      MS SGE TGE i_obj spc0 tpc0 ->
      PreviouslyInserted TGE i_obj t' bi tpc0 head tail tpc ->
      t' <> cid tpc ->
      forall tC tcs fp tc' b' tm',
        nat_of_ord (TSOCore.i tC) <> i_obj ->
        (TSOThrdPool.content (thrdpool tpc)) !! (cid tpc) = Some (tC :: tcs) ->
        tsostep (TSOGlobEnv.modules TGE (TSOCore.i tC)) (FLists.get_fl (TSOGlobEnv.freelists TGE) (TSOCore.F tC)) 
                (TSOCore.c tC) (tso_buffers (tm tpc) (cid tpc), memory (tm tpc)) fp tc' (b', tm') ->
        ~ conflict_bi fp bi.
  Proof.
    intros SGE TGE i_obj t' bi spc0 tpc0 head tail tpc
           MATCH0 PrevInserted Htid tC tcs fp tc' b' tm'
           Hmid Htcore Hstep Hconflict.
    exploit PreviouslyInserted_PreviouslyInserted'; eauto.
    econstructor; eauto.
    intros (_head & _tail & _tpc & HPrevInserted' & Htid' & Hclientfp).
    clear PrevInserted Htcore Hstep tC tcs tc' b' tm' Hmid.
    assert (t' <> cid _tpc) as Htid''.
    { intro. subst. auto. }
    clear Htid Htid' head tail tpc.
    exploit PreviouslyInserted'_adjacent_conflicting_step; eauto.
    clear spc0 tpc0 bi Hconflict HPrevInserted' _head _tail MATCH0.
    rename t' into t0.
    intros (spc0 & tpc0 & fp0 & tpc0' & tpc0'' &
            Hinv & Htid0 & Hclient0 & Hconflict0 & Hstep0 & Hswstep & Hcid'' &
            Hfp & Hconflict).
    exploit conflicting_adjacent_steps_race; eauto. congruence.
  Qed.

  (** Lemma 15 in draft ... *)  
  Theorem MS_BufWD_no_conflicting_client_fp:
    forall SGE TGE i_obj tpc,
      BufWD SGE TGE i_obj tpc ->
      no_conflicting_client_fp TGE i_obj tpc.
  Proof.
    intros SGE TGE i_obj tpc H.
    unfold no_conflicting_client_fp.
    intros fp Hclientfp C. destruct C. apply in_split in H1.
    destruct H1 as [head [tail Hbi]].
    eapply prev_inserted in Hbi; try exact H.
    destruct Hbi as [spc0 [tpc0 [MATCH0 Hbi]]].
    destruct Hclientfp.
    eapply PreviouslyInserted_no_conflicting_client_fp; eauto.
  Qed.

  Corollary BufWD_client_core_not_conflictc:
    forall SGE TGE i_obj tpc fp tpc',
      BufWD SGE TGE i_obj tpc ->
      client_core TGE i_obj (cid tpc) tpc ->
      tso_globstep tpc tau fp tpc' ->
      ~ conflictc (cid tpc) fp (tso_buffers (tm tpc)).
  Proof.
    intros. apply MS_BufWD_no_conflicting_client_fp in H.
    inv H1; auto using emp_fp_not_conflictc. simpl in *.
    apply H. econstructor; eauto.
    inv H0. simpl in *. rewrite H_tp_core in H1. inv H1. auto.
  Qed.


  (** BufWD is actually an invariant *)
  Lemma BufWD_preserved_if_post_states_MS:
    forall SGE TGE i_obj spc tpc,
      MS SGE TGE i_obj spc tpc ->
      BufWD SGE TGE i_obj tpc ->
      forall l fp tpc',
        tso_globstep tpc l fp tpc' ->
        BufWD SGE TGE i_obj tpc'.
  Proof.
    intros SGE TGE i_obj spc tpc MATCH H l fp tpc' Hstep.
    constructor. intros t bi head tail Hbuffer.
    (* case study on Htstep... *)
    
    destruct l.
    (* tau step *)
    { exploit tau_step_buffer_append. exact Hstep.
      rewrite Hbuffer. intros [tail' Hbuffer'].
      assert ((exists head',
                  head = tso_buffers (tm tpc) t ++ head' /\
                  tail' = head' ++ bi :: tail)
              \/
              (exists tail0,
                  tso_buffers (tm tpc) t = head ++ bi :: tail0 /\
                  tail0 ++ tail' = tail)).
      { revert Hbuffer'. generalize (tso_buffers (tm tpc) t).
        clear. intro head'.
        Lemma list_head_tail_split_cases:
          forall A bi (head tail head' tail': list A),
            head ++ bi :: tail = head' ++ tail' ->
            (exists head'0, head = head' ++ head'0 /\ tail' = head'0 ++ bi :: tail) \/
            (exists tail0, head' = head ++ bi :: tail0 /\ tail0 ++ tail' = tail).
        Proof.
          clear. intros A bi.
          induction head.
          intros. destruct head'; simpl in *. eauto.
          inversion H. subst. eauto.
          intros. destruct head'; simpl in *.
          destruct tail'; inv H. eauto.
          inv H.
          eapply IHhead in H2. clear IHhead.
          destruct H2 as [(head0' & Hhead & Htail) | (tail0 & Hhead & Htail)].
          subst. eauto. subst. eauto.
        Qed.
        apply list_head_tail_split_cases.
      }
      destruct H0 as [Hnew | Hold].
      destruct Hnew as [head' [Hhead Htail]]. subst head tail'. clear Hbuffer'.
      exists spc, tpc. split; auto.
      econstructor. eauto. eauto. intros.
      eapply BufWD_client_core_not_conflictc; eauto.
      rewrite app_assoc. eauto.
      destruct tpc'. eapply bi_nub_refl. auto.
      destruct Hold as [tail0 [Hbuffer0 Htail]]. subst tail.
      pose proof H as BUFWD.
      eapply prev_inserted in H; eauto.
      destruct H as (spc0 & tpc0 & MATCH0 & PI0).
      exists spc0, tpc0. split. auto.
      destruct PI0.
      econstructor. eauto. eauto. eauto. eauto.
      Lemma bi_nub_insert_buffer_bi_nub:
        forall TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn l fp tpc tail,
          bi_not_unbuffered TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn ->
          tso_globstep tpcn l fp tpc ->
          tso_buffers (tm tpc) t = tso_buffers (tm tpcn) t ++ tail ->
          (client_core TGE i_obj (cid tpcn) tpcn ->
           ~ conflictc (cid tpcn) fp (tso_buffers (tm tpcn))) ->
          bi_not_unbuffered TGE i_obj t bi head1 tail1 tpc1 headn (tailn ++ tail) tpc.
      Proof.
        clear.
        intros TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn l fp tpc tail
               BNU Hstep Hbuffer Hconflict.
        induction BNU.
        { subst tpc0. simpl in *. econstructor. exact Hstep. auto.
          rewrite H in Hbuffer. rewrite Hbuffer. rewrite <- app_assoc.
          f_equal. rewrite app_comm_cons. eauto.
          econstructor.
          simpl. auto. destruct tpc; apply bi_nub_refl. 
          rewrite H in Hbuffer. simpl in *. rewrite Hbuffer.
          rewrite <- app_assoc. f_equal. }
        { econstructor; eauto. }
      Qed.
      Lemma bi_nub_sw_bi_nub:
        forall TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn tpc,
          bi_not_unbuffered TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn ->
          tso_globstep tpcn sw FP.emp tpc ->
          bi_not_unbuffered TGE i_obj t bi head1 tail1 tpc1 headn tailn tpc.
      Proof.
        clear.
        intros TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn tpc BNU Hstep.
        induction BNU.
        { subst tpc0. simpl in *. econstructor. exact Hstep. auto.
          erewrite sw_step_buffer_eq; eauto. simpl. eauto.
          constructor.
          simpl. intros. apply emp_fp_not_conflictc.
          destruct tpc; apply bi_nub_refl.
          apply sw_step_buffer_eq in Hstep. simpl in *. congruence. }
        { econstructor; eauto. }
      Qed.
      Lemma bi_nub_evt_bi_nub:
        forall TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn v tpc,
          bi_not_unbuffered TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn ->
          tso_globstep tpcn (evt v) FP.emp tpc ->
          bi_not_unbuffered TGE i_obj t bi head1 tail1 tpc1 headn tailn tpc.
      Proof.
        clear.
        intros TGE i_obj t bi head1 tail1 tpc1 headn tailn tpcn v tpc 
               BNU Hstep.
        induction BNU.
        { subst tpc0. simpl in *. econstructor. exact Hstep. auto.
          inv Hstep. simpl. eauto. constructor.
          intros. apply emp_fp_not_conflictc.
          destruct tpc; apply bi_nub_refl.
          inv Hstep; simpl; auto. }
        { econstructor; eauto. }
      Qed.
      eapply bi_nub_insert_buffer_bi_nub.
      eauto. eauto. congruence.
      intro. eapply BufWD_client_core_not_conflictc; eauto.
    }
    (* sw step *)
    { inversion Hstep; subst. simpl in *.
      eapply prev_inserted in H; simpl; eauto.
      destruct H as (spc0 & tpc0 & MATCH0 & PI0).
      exists spc0, tpc0. split. auto.
      destruct PI0. econstructor. eauto. eauto. eauto. eauto.
      eapply bi_nub_sw_bi_nub. eauto. eauto. }
    (* ub step *)
    { destruct (peq t t0).
      { subst t.
        inversion Hstep; subst; simpl in *.
        assert (exists bi0, tso_buffers tm t0 = bi0 :: (head ++ bi :: tail))
          as [bi0 Hbuffer0].
        { unfold unbuffer in H_unbuf.
          destruct (tso_buffers tm t0) as [|bi0 tail0]. discriminate.
          destruct (apply_buffer_item bi0 (memory tm)); inv H_unbuf.
          exists bi0. f_equal. simpl in *.
          unfold tupdate in Hbuffer. destruct peq; auto. congruence. }
        exploit prev_inserted.
        eauto. simpl. rewrite Hbuffer0. rewrite app_comm_cons. eauto.
        intros (spc0 & tpc0 & MATCH0 & PI0).
        inversion PI0. subst. simpl in *.  exists spc0, tpc0. split. auto.
        econstructor. eauto. eauto. eauto. eauto.
        revert Hstep H4. clear.
        match goal with
        | |- context[tso_globstep ?a _ _ ?b] => generalize a b
        end.
        generalize (tso_buffers (TSOGlobSem.tm tpc0) t0 ++ head').
        clear. intros head1 tpc tpc' Hstep H. rename tail' into tail1.
        revert tpc' Hstep. remember (bi0 :: head) as head0.
        revert bi0 head Heqhead0. induction H.
        intros. subst. subst tpc. destruct tpc'.
        inversion Hstep; subst; simpl in *.
        assert (tso_buffers tm0 t0 = head0 ++ bi :: tail).
        { unfold unbuffer in H_unbuf. rewrite H in H_unbuf.
          destruct apply_buffer_item; inv H_unbuf. simpl.
          unfold tupdate. destruct peq. eauto. contradiction. }
        eapply bi_nub_step. eauto. simpl. eauto. simpl. eauto.
        eapply buf_forward_deq.
        intro. apply emp_fp_not_conflictc.
        eapply bi_nub_refl. auto.
        intros. exploit IHbi_not_unbuffered; eauto.
        intro. econstructor; eauto.
      }
      { exploit ub_step_emp_fp. eauto. intro; subst fp.
        erewrite ub_step_buffer_eq in Hbuffer; eauto.
        exploit prev_inserted. eauto. eauto. intros (spc0 & tpc0 & MATCH0 & PI0).
        inversion PI0; subst; simpl in *.
        exists spc0, tpc0. split. auto.
        econstructor. eauto. eauto. eauto. eauto.
        revert H4 n Hstep. clear. generalize (tso_buffers (tm tpc0) t ++ head').
        intro head1. rename tail' into tail1. clear.
        intro H. revert t0 tpc'. induction H.
        intros. exploit ub_step_buffer_eq. eauto. eauto. intro Hbuffer'.
        intros. econstructor. eauto. eauto. rewrite Hbuffer'. eauto. constructor.
        intros. apply emp_fp_not_conflictc.
        destruct tpc'; eapply bi_nub_refl. simpl in *; congruence.
        intros. econstructor; eauto.
      }
    }
    (* evt step *)
    { inversion Hstep; subst. simpl in *.
      eapply prev_inserted in H; simpl; eauto.
      destruct H as (spc0 & tpc0 & MATCH0 & PI0).
      exists spc0, tpc0. split. auto.
      destruct PI0. econstructor. eauto. eauto. eauto. eauto.
      eapply bi_nub_evt_bi_nub. eauto. eauto. }
  Qed.

  

  (* BufWD preserved w.r.t. glob step *)
  Lemma step_BufWD_preserved:
    forall SGE TGE i_obj spc ls sfp spc' tpc l fp tpc',
      @tso_globstep TGE tpc l fp tpc' ->
      ETrace.star glob_step spc ls sfp spc' ->
      MS SGE TGE i_obj spc tpc ->
      BufWD SGE TGE i_obj tpc ->
      MS SGE TGE i_obj spc' tpc' ->
      BufWD SGE TGE i_obj tpc'.
  Proof.
    intros. eapply BufWD_preserved_if_post_states_MS.
    exact H1. exact H2. exact H. 
  Qed.

End Invs.