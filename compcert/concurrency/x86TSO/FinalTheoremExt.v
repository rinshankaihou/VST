Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.ssrnat.

Require Import Coqlib Axioms Errors.

Require Import InteractionSemantics GAST GlobSemantics Blockset ReachClose DRF SeqCorrect.

Require Import Soundness.

Require Import LangProps SpecLangIDtrans CompCorrect.

Import Compositionality.

Require Import Languages SCSemLemmas.

(** * Final Theorem of the extended framework *)

Require code.

Section ClightSC_Compilation_correctness.
  (* M Clight modules, 1 object spec module, and N threads *)
  Variable (cl_units: @cunits NL L).
  Variable (compiled_units: @cunits NL L).
  Variable (spec_unit: @cunit NL L).
  (* construct source compilation units *)
  Let scunits:= spec_unit :: cl_units.
  Let tcunits:= spec_unit :: compiled_units.
  Variable e: @entries.
  (* construct compilers using compcert and id *)
  Definition cl_comps : @gcomp NL L :=
    List.repeat (Build_seq_comp_i NL L id0 id1 clight_trans)
                (List.length cl_units).
  Definition id_comp: @seq_comp_i NL L :=
    (Build_seq_comp_i NL L id2 id2 id_trans_speclang).
      
  (** Hypothesis 1: modules are reach-closed *)
  Hypothesis Hrc : rc_cunits scunits.
  (** Hypothesis 2: compilation units are compiled by [comps] *)
  Hypotheses (Hcomp_clight: cunits_transf cl_comps cl_units compiled_units).
  Hypotheses (Hcomp_spec: cunit_transf id_comp spec_unit spec_unit).
  (** Hypothesis 3: whole source program is safe and data-race-free *)
  Hypothesis (Hdrf: drf (scunits, e)).
  Hypothesis (Hsafe: safe_prog (scunits, e)).
  
  Definition comps: @gcomp NL L := id_comp :: cl_comps.

  Lemma Hwd_src: wd_langs scunits.
  Proof.
    clear Hdrf Hsafe Hrc.
    induction scunits. 
    intros cu C. inversion C.
    unfold wd_langs. intros. inv H; auto.
    destruct cu; simpl. destruct (eq_ord lid); subst.
    rewrite L_sound_1. apply ClightWD.Clight_wd2.
    inv H.
    rewrite L_sound_2. apply AsmWD.Asm_wd.
    rewrite L_sound_3. apply SpecLangWDDET.SpecLang_wd.
  Qed.
    
  Lemma Hwd_tgt: wd_langs tcunits.
  Proof.
    clear Hdrf Hsafe Hrc.
    induction tcunits.
    intros cu C. inversion C.
    unfold wd_langs. intros. inv H; auto.
    destruct cu; simpl. destruct (eq_ord lid); subst.
    rewrite L_sound_1. apply ClightWD.Clight_wd2.
    inv H.
    rewrite L_sound_2. apply AsmWD.Asm_wd.
    rewrite L_sound_3. apply SpecLangWDDET.SpecLang_wd.    
  Qed.
  
  Lemma Hdet_tgt: det_langs tcunits.
  Proof.
    subst scunits tcunits. unfold cl_comps, id_comp in *.
    clear Hrc e Hdrf Hsafe.
    revert compiled_units Hcomp_clight Hcomp_spec.
    induction cl_units; intros.
    inv Hcomp_clight. simpl.
    intros cu H. simpl in H. destruct H; inv H.
    inv Hcomp_spec; simpl in *. inv H. apply SpecLangWDDET.SpecLang_det.
    inv Hcomp_clight. simpl in *. intros cu IN. inv IN.
    inv Hcomp_spec; simpl in *. inv H. apply SpecLangWDDET.SpecLang_det.
    inv H. inv H4. inv H. apply AsmDET.Asm_det.
    eapply IHc; eauto. right. auto.
  Qed.

  Lemma Hcomp: cunits_transf comps scunits tcunits.
  Proof.
    clear Hsafe Hrc Hdrf. subst scunits tcunits. unfold comps, cl_comps, id_comp in *.
    revert compiled_units Hcomp_clight Hcomp_spec.
    induction cl_units; intros; inv Hcomp_clight.
    simpl. constructor; auto. constructor.
    constructor; auto.
    exploit IHc; eauto. intro H. inv H.
    constructor; auto.
  Qed.    
  
  (* compilers are correct w.r.t. [seqcorrect] *)
  (* proved by compcert correctness and id_trans correctness *)
  Lemma Hcorrect: seqs_correct comps.
  Proof.
    unfold comps. clear. unfold cl_comps, id_comp.
    generalize (length cl_units). clear.
    induction n; simpl.
    constructor. simpl. apply SpecLangIDtrans.id_trans_correct.
    constructor; auto.
    inv IHn. constructor; simpl; auto.
    constructor; simpl. apply compcert_correct. auto. 
  Qed.
  
  
  Theorem refinement_sc:
    prog_refine (scunits, e) (tcunits, e).
  Proof.
    eapply framework_sound.
    apply Hwd_src.
    apply Hwd_tgt.
    apply Hdet_tgt.
    apply Hrc.
    apply Hcomp.
    apply Hcorrect.
    apply Hdrf.
    apply Hsafe.
  Qed.


  
  Require Import GlobDefs TSOGlobSem TSOGlobUSim TSOCompInvs TSOCompositionality RGRels ClientSim ObjectSim.
  Require Import code InvRG LockProof LockSim.
  Variable (client_units: list AsmTSO.comp_unit).
  (** client code are identical *)
  Hypothesis (H_client_code: client_id compiled_units client_units).

  (** object  module *)
  Variable (impl_unit: AsmTSO.comp_unit).
  (** object  R/G/O *)
  Variable (Io: ASM_local.genv -> stInv).
  Variable (Ro Go: ASM_local.genv -> tid -> stRel).
  (** object  R/G/O properties *)  
  Hypothesis (Io_Sta_Go: forall ge t, Sta (Io ge) (Go ge t)).
  Hypothesis (Go_Implies_Ro: forall ge t t', t <> t' -> Implies (Go ge t) (Ro ge t')).  
  Hypothesis (UBSta_Io: forall ge, UBSta (Io ge)).
  Hypothesis (UBImplies_Ro: forall ge t, UBImplies (Io ge) (Ro ge t)).
  Hypothesis (HRP: RespectPerm Io Ro Go).
  (** object simulation *)
  Hypothesis (H_obj_sim: objcu_sim Ro Go Io spec_unit impl_unit).

  Theorem refinement_tso_asm_sc:
    safe_prog (tcunits, e) ->
    drf (tcunits, e) ->
    tso_refine_sc
      (tcunits, e)
      (impl_unit :: client_units,e).
  Proof.
    intros Htgtsafe Htgtdrf.
    apply tso_globusim_refinement.
    eapply compositionality; eauto.
  Qed.

  Let pSrc := (scunits, e).
  Let pSrc' := (tcunits, e).
  Let pTgt := (impl_unit :: client_units, e).
  
  Theorem refinement_tso_clight:
    forall mu
      sgm sge spc t
      sgm' sge' spc'
      tgm tge tpc,
      (** initial states related *)
      init_config pSrc sgm sge spc t ->
      InitRel mu sge sge' sgm sgm' ->
      init_config pSrc' sgm' sge' spc' t ->
      tso_sc_initRel sge' tge sgm' tgm ->
      tso_initconfig pTgt tgm tge tpc t ->
      (** event trace refinement for behaviors that do not silently diverge *)
      (forall B: ETrace.behav,
          tsoEtr tpc B ->
          notsd B ->
          ETrace.Etr glob_step GlobSemantics.abort GlobDefs.final_state spc B).
  Proof.
    intros.
    exploit tso_globusim_refinement; eauto.
    eapply compositionality; eauto.
    intro. inv H6.
    pose proof refinement_sc as Hasm_cl. inv Hasm_cl.
    eapply H6; eauto. 
    eapply H7; eauto.
    eapply drf_preservation; eauto.
    apply Hwd_src. eapply Hwd_tgt. eapply Hdet_tgt. eapply Hcomp. eapply Hcorrect.
    eapply safety_preservation; eauto.
    apply Hwd_src. eapply Hwd_tgt. eapply Hdet_tgt. eapply Hcomp. eapply Hcorrect.    
  Qed.
  
End ClightSC_Compilation_correctness.

Check refinement_tso_clight.
(** Theorem 15 in Sec. 7. *)

(** [rc_cunits] : 
    source modules are reach-closed *)

(** [cunits_transf (cl_comps cl_units) cl_units compiled_units] :
    [compiled_units] are x86 assembly units that compiled from [cl_units] by CompCert passes *)

(** [cunit_transf id_comp spec_unit spec_unit]:
    [spec_unit] is identically translated *)

(** [drf (spec_unit ++ cl_units :: nil, e)]:
    source program is data-race free *)

(** [safe_prog (spec_unit ++ cl_units :: nil, e)]:
    source program is safe *)

(** [client_id compiled_units client_units]:
    [client_units] are x86TSO units that is identical to [compiled_units] *)

(** [forall (impl_unit : AsmTSO.comp_unit) (Io : ASM_local.genv -> stInv) (Ro Go : ASM_local.genv -> tid -> stRel),
       (forall (ge : ASM_local.genv) (t : tid), Sta Ic (Go ge t)) ->
       (forall t : tid, Sta Ic (Gc t)) ->
       (forall (ge : ASM_local.genv) (t : tid), Sta (Io ge) (Go ge t)) ->
       (forall (ge : ASM_local.genv) (t : tid), Sta (Io ge) (Gc t)) ->
       (forall (ge : ASM_local.genv) (t t' : tid), Implies (Go ge t) (Rc t')) ->
       (forall (ge : ASM_local.genv) (t t' : tid), t <> t' -> Implies (Go ge t) (Ro ge t')) ->
       (forall (ge : ASM_local.genv) (t t' : tid), t <> t' -> Implies (Gc t) (Ro ge t')) ->
       (forall ge : ASM_local.genv, UBSta (Io ge)) ->
       (forall (ge : ASM_local.genv) (t : tid), UBImplies (Io ge) (Ro ge t)) ->
       objcu_sim Ro Go Io spec_unit impl_unit]
       :         
       object correctness (4. in Thm. 15) *)

(** [init_config (cl_units ++ spec_unit :: nil, e) sgm sge spc ts]
    [init_config (compiled_units ++ spec_unit :; nil, e) sgm' sge' spc' ts']
    [tso_initconfig (client_units ++ impl_unit :: nil, e) tgm tge tpc tt]:
    forall initial states of source program and target program *)

(** [InitRel mu sge sge' sgm sgm']
    [tso_sc_initRel sge' tge sgm' tgm]:
    initial states are properly related by some [mu] *)

(** [forall B : ETrace.behav, tsoEtr tpc B -> notsd B -> ETrace.Etr glob_step GlobSemantics.abort GlobDefs.final_state spc B]:
    for any bahavior [B] of tso program ([tsoEtr tpc B]),
    if [B] will not silently diverge ([notsd B]),
    then the clight source program with lock spec has the same behavior [B] 
    ([ETrace.Etr glob_step GlobSemantics.abort GlobDefs.final_state spc]) *)


Check refinement_tso_asm_sc.
(** Lemma 16 in Sec. 7, object module replaced by lock impl. *)

(** [client_id compiled_units client_units]:
    [client_units] are x86TSO units that is identical to [compiled_units] *)

(** [forall (impl_unit : AsmTSO.comp_unit) (Io : ASM_local.genv -> stInv) (Ro Go : ASM_local.genv -> tid -> stRel),
       (forall (ge : ASM_local.genv) (t : tid), Sta Ic (Go ge t)) ->
       (forall t : tid, Sta Ic (Gc t)) ->
       (forall (ge : ASM_local.genv) (t : tid), Sta (Io ge) (Go ge t)) ->
       (forall (ge : ASM_local.genv) (t : tid), Sta (Io ge) (Gc t)) ->
       (forall (ge : ASM_local.genv) (t t' : tid), Implies (Go ge t) (Rc t')) ->
       (forall (ge : ASM_local.genv) (t t' : tid), t <> t' -> Implies (Go ge t) (Ro ge t')) ->
       (forall (ge : ASM_local.genv) (t t' : tid), t <> t' -> Implies (Gc t) (Ro ge t')) ->
       (forall ge : ASM_local.genv, UBSta (Io ge)) ->
       (forall (ge : ASM_local.genv) (t : tid), UBImplies (Io ge) (Ro ge t)) ->
       objcu_sim Ro Go Io spec_unit impl_unit]
       :
       object correctness (2. in Lem. 16 *)

(** [safe_prog (spec_unit :: compiled_units, e)]
    SC program is safe *)

(** [drf (spec_unit :: compiled_units, e)]
    SC program is DRF *)

(** [tso_refine_sc (spec_unit :: compiled_units, e) (impl_unit :: client_units, e)]
    then the x86-TSO program refines the SC program *)
