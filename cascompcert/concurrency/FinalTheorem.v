Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.ssrnat.

Require Import Coqlib Axioms Errors.

Require Import InteractionSemantics GAST GlobSemantics Blockset ReachClose DRF SeqCorrect.

Require Import Soundness.

Require Import LangProps ClightLang AsmIDTransCorrect CompCorrect.

Import Compositionality.

(** * Final Theorem of SC compilation *)
(** This file defines the final theorem of the ClightSC compiler. *)
(** Which says 
    if we have [n] cminor modules [c_1],...,[c_n] and a module [obj] for object implementations,
    and the linked program 
    [P_s = Let (c_1, ..., c_n, obj) In (f_1 || ... || f_m)] is safe and drf,
    then if we compile each [c_i] separately using compcert to [t_i],
    the target program 
    [P_t = Let (t_1, ..., t_n, obj) In (f_1 || ... || f_m)] refines [P_s].
*)

(** ** Case 1: Object is implemented in x86-SC assembly *)
(** Two languages: Clight and x86 ASM  *)
Definition NL := 2%nat.

Program Definition id0 : 'I_NL := @Ordinal NL 0 _.
Program Definition id1 : 'I_NL := @Ordinal NL 1 _.

Program Definition L (i: 'I_NL): Language :=
  if eqn i 0 then Clight_IS_2
  else AsmLang.

Lemma L_sound_1: L id0 = Clight_IS_2.
Proof. auto. Qed.
Lemma L_sound_2: L id1 = AsmLang.
Proof. auto. Qed.
Lemma eq_ord: forall i:'I_NL,
    i = id0 \/ i = id1.
Proof.
  unfold id0, id1.
  intro. destruct i.
  destruct m.
  left. cut (i = id0_obligation_1). intro; subst; auto.
  apply proof_irr.
  destruct m.
  right. cut (i = id1_obligation_1). intro; subst; auto.
  apply proof_irr.
  inversion i.
Qed.

Section ClightSC_Compilation_correctness.
  (* M0 Cminor modules, M1 ASM modules and N threads *)
  Variable (clight_units: @cunits NL L).
  Variable (compiled_units: @cunits NL L).
  Variable (asm_units: @cunits NL L).
  (* construct source compilation units *)
  Let scunits:= clight_units ++ asm_units.
  Let tcunits:= compiled_units ++ asm_units.
  Variable e: @entries.
  (* construct compilers using compcert and id *)
  Definition cm_comps : @gcomp NL L :=
    List.repeat (Build_seq_comp_i NL L id0 id1 clight_trans)
                (List.length clight_units).

  Definition asm_comps: @gcomp NL L :=
    List.repeat (Build_seq_comp_i NL L id1 id1 id_trans_asm)
                (List.length asm_units).
  (** Hypothesis 1: modules are reach-closed *)
  Hypothesis Hrc : rc_cunits scunits.
  (** Hypothesis 2: compilation units are compiled by [comps] *)
  Hypotheses (Hcomp_cminor: cunits_transf cm_comps clight_units compiled_units).
  Hypotheses (Hcomp_asm: cunits_transf asm_comps asm_units asm_units).
  (** Hypothesis 3: whole source program is safe and data-race-free *)
  Hypothesis (Hdrf: drf (scunits, e)).
  Hypothesis (Hsafe: safe_prog (scunits, e)).
  
  Definition comps: @gcomp NL L := cm_comps ++ asm_comps.

  Lemma Hwd_src: wd_langs scunits.
  Proof.
    clear Hdrf Hsafe Hrc.
    induction scunits. 
    intros cu C. inversion C.
    unfold wd_langs. intros. inv H; auto.
    destruct cu; simpl. destruct (eq_ord lid); subst.
    rewrite L_sound_1. apply ClightWD.Clight_wd2.
    rewrite L_sound_2. apply AsmWD.Asm_wd.
  Qed.
    
  Lemma Hwd_tgt: wd_langs tcunits.
  Proof.
    clear Hdrf Hsafe Hrc.
    induction tcunits.
    intros cu C. inversion C.
    unfold wd_langs. intros. inv H; auto.
    destruct cu; simpl. destruct (eq_ord lid); subst.
    rewrite L_sound_1. apply ClightWD.Clight_wd2.
    rewrite L_sound_2. apply AsmWD.Asm_wd.
  Qed.
  
  Lemma Hdet_tgt: det_langs tcunits.
  Proof.
    subst scunits tcunits. unfold cm_comps, asm_comps in *.
    clear Hrc e Hdrf Hsafe.
    revert compiled_units asm_units Hcomp_cminor Hcomp_asm.
    induction clight_units; intros.
    inv Hcomp_cminor. simpl.
    induction asm_units; intros cu C; inv C.
    destruct cu; simpl in *. destruct (eq_ord lid); subst.
    inv Hcomp_asm. inv H2. inv H. inv H1.
    rewrite L_sound_2. apply AsmDET.Asm_det.
    inv Hcomp_asm. apply IHc; auto.
    inv Hcomp_cminor. simpl. intros cu IN. inv IN.
    inv H4. simpl. inv H. rewrite L_sound_2. apply AsmDET.Asm_det.
    eapply IHc; eauto.
  Qed.

  Lemma Hcomp: cunits_transf comps scunits tcunits.
  Proof.
    clear Hsafe Hrc Hdrf. subst scunits tcunits. unfold comps, cm_comps, asm_comps in *.
    revert compiled_units Hcomp_cminor Hcomp_asm.
    induction clight_units; intros; inv Hcomp_cminor.
    simpl. auto. constructor; auto. 
  Qed.    
  
  (* compilers are correct w.r.t. [seqcorrect] *)
  (* proved by compcert correctness and id_trans correctness *)
  Lemma Hcorrect: seqs_correct comps.
  Proof.
    unfold comps. clear. unfold cm_comps, asm_comps.
    generalize (length clight_units) (length asm_units). clear.
    induction n. simpl. induction n. simpl. constructor.
    simpl. constructor; auto. simpl. apply id_trans_asm_correct.
    simpl. constructor. simpl. apply compcert_correct. apply IHn.
  Qed.
  
  Theorem refinement:
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
End ClightSC_Compilation_correctness.


Check refinement.
(** [rc_cunits] : 
    source modules are reach-closed *)
(** [cunits_transf (cm_comps clight_units) clight_units compiled_units] :
    [compiled_units] are x86 assembly units that compiled from [clight_units] by CompCert passes *)
(** [cunits_transf (asm_comps asm_units) asm_units asm_units]:
    [asm_units] are identically translated *)
(** [drf (clight_units ++ asm_units, e)]:
    source program is data-race free *)
(** [safe_prog (clight_units ++ asm_unit, e)]:
    source program is safe *)
(** [prog_refine (clight_units ++ asm_units, e) (compiled_units ++ asm_units, e)]:
    there is event trace refinement between source and target programs *)


(** ** Case 2: Object is implemented in CImp language (Thm. 14) *)
Require Import Languages SpecLangIDtrans.

Section ClightSC_Compilation_Correctness_with_Object.
  (** M Clight modules, 1 object spec module, and N threads *)
  Variable (M: nat).
  Variable (cl_units: @cunits NL L).
  Variable (compiled_units: @cunits NL L).
  Variable (spec_unit: @cunit NL L).
  (** construct source compilation units *)
  Let scunits:= spec_unit :: cl_units.
  Let tcunits:= spec_unit :: compiled_units.
  Variable e: @entries.
  (** construct compilers using compcert and id *)
  Definition cl_comps : @gcomp NL L :=
    List.repeat (Build_seq_comp_i NL L id0 id1 clight_trans) M.
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

  (** construct compilers *)
  Definition comps': @gcomp NL L := id_comp :: cl_comps.

  Lemma Hwd_src': wd_langs scunits.
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
    
  Lemma Hwd_tgt': wd_langs tcunits.
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
  
  Lemma Hdet_tgt': det_langs tcunits.
  Proof.
    subst scunits tcunits. unfold cl_comps, id_comp in *.
    clear Hrc e Hdrf Hsafe.
    revert M compiled_units Hcomp_clight Hcomp_spec.
    induction cl_units; intros.
    inv Hcomp_clight. simpl.
    intros cu H. simpl in H. destruct H; inv H.
    inv Hcomp_spec; simpl in *. inv H. apply SpecLangWDDET.SpecLang_det.
    inv Hcomp_clight. simpl in *. intros cu IN. inv IN.
    inv Hcomp_spec; simpl in *.
    destruct M; inv H. inv H0. apply SpecLangWDDET.SpecLang_det.
    destruct M; inv H. inv H2. inv H. inv H0.
    apply AsmDET.Asm_det.
    eapply IHc; eauto. right. auto.
  Qed.

  Lemma Hcomp': cunits_transf comps' scunits tcunits.
  Proof.
    clear Hsafe Hrc Hdrf. subst scunits tcunits. unfold comps', cl_comps, id_comp in *.
    revert M compiled_units Hcomp_clight Hcomp_spec.
    induction cl_units; intros; inv Hcomp_clight.
    simpl. constructor; auto. constructor.
    constructor; auto.
    destruct M; inv H. 
    exploit IHc; eauto. intro H. inv H.
    constructor; auto.
  Qed.    
  
  (** compilers are correct w.r.t. [seqcorrect] *)
  (** proved by compcert correctness and CImp id_trans correctness *)
  Lemma Hcorrect': seqs_correct comps'.
  Proof.
    unfold comps'. clear. unfold cl_comps, id_comp.
    induction M; simpl.
    constructor. simpl. apply SpecLangIDtrans.id_trans_correct.
    constructor; auto.
    inv IHn. constructor; simpl; auto.
    constructor; simpl. apply compcert_correct. auto. 
  Qed.

  (** The refinement theorem *)
  Theorem refinement_sc:
    prog_refine (scunits, e) (tcunits, e).
  Proof.
    eapply framework_sound.
    apply Hwd_src'.
    apply Hwd_tgt'.
    apply Hdet_tgt'.
    apply Hrc.
    apply Hcomp'.
    apply Hcorrect'.
    apply Hdrf.
    apply Hsafe.
  Qed.
  
End ClightSC_Compilation_Correctness_with_Object.

Lemma seq_comp_i_eq:
  forall NL L id1 id2 comp comp',
    @Build_seq_comp_i NL L id1 id2 comp =
    @Build_seq_comp_i NL L id1 id2 comp' ->
    comp = comp'.
Proof. intros. inv H. repeat apply existTeq in H1. auto. Qed.




(** ** Theorem 14 in paper *)
(** i.e. CompCert along with identity transformation of CImp
    are correct as a whole for compiling concurrent programs.
    Note here we made number of Clight modules [M] explicit 
    for the convenience of defining separated compilation of each module *)

Definition CompCert_CImpID (M: nat) : gcomp := id_comp :: cl_comps M.

Theorem GCorrect_compcert_CImpID:
  forall M, gcorrect (CompCert_CImpID M).
Proof.
  assert (CompCert_CImpID = comps') as COMP by auto. rewrite COMP.
  intros M scunits tcunits entries TRANS SAFE DRF RC.
  assert (exists obj scunits', scunits = obj :: scunits') as (obj & scunits' & Hscunits).
  { inv TRANS. eauto. }
  subst scunits. 
  assert (exists tcunits', tcunits = obj :: tcunits') as (tcunits' & Htcunits).
  { inv TRANS. inv H4. inversion H. subst.
    apply seq_comp_i_eq in H. subst. unfold id_trans_speclang in H2.
    monadInv H2. eauto. }
  subst tcunits.
  inv TRANS.
  eapply refinement_sc; eauto.
Qed.
