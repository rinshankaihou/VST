Require Import Setoid List.
Require Import mathcomp.ssreflect.fintype.
(* CompCert modules *)
Require Import Coqlib Errors Values AST.

Require Import Blockset InteractionSemantics GAST GlobDefs GlobSemantics DRF ReachClose Init.
Require Import NPEquiv GlobUSimRefine SimDRF Flipping Compositionality SeqCorrect.

(** ** Framework Final Theorem *)

(** This file defines the final theorem [framework_final_theorem] of our framework (Thm. 12), 
    in which languages are parameterized. *)

(** The main result is that if we have a [safe] and [DRF] source program
    [P_s] = [Let (c_1,...,c_n) In f_1 || ... || f_n], 
    each of its modules [c_i] is reach-closed and 
    correctly compiled to a target module [t_i], 
    and all the target languages are deterministic,
    then the target program
    [Let (c_1,...,c_n) In f_1 || ... || f_n] refines [P_s]. *)


(** Block set and block injection definitions, 
    for the definition of simulation and refinement *)

Definition blocks := Bset.t.
Definition bs_emp := Bset.emp.
Definition block_subset := Bset.subset.
Definition block_inj := Bset.inj.
Definition binj_emp := Bset.inj_emp.
Definition binj_id := Bset.inj_id.
Definition block_inj_subset := Bset.inj_subset.
Definition blocks_inject := Bset.inject.

Definition seqs_correct {NL: nat} {L: @langs NL} (scomps: @gcomp NL L) : Prop :=
  Forall (fun scomp => seq_correct scomp.(comp)) scomps.

Lemma seqs_correct_ldsims:
  forall NL L comps scunits tcunits,
  @seqs_correct NL L comps ->
  cunits_transf comps scunits tcunits ->
  ldsims scunits tcunits.
Proof.
  intros NL L.
  induction comps; intros.
  { inversion H0. constructor. }
  { inversion H0; subst. inversion H; subst.
    constructor.
    generalize H3 H4. clear. intros.
    inversion H3. subst. simpl in *.
    apply H4. auto.
    apply IHcomps; auto. }
Qed.

Lemma seqs_correct_fn_preserved:
  forall NL L comps scunits tcunits,
  @seqs_correct NL L comps ->
  cunits_transf comps scunits tcunits ->
  fn_preserved scunits tcunits.
Proof.
  intros NL L; induction comps; intros.
  { inversion H0. constructor. }
  { inversion H0; subst. inversion H; subst.
    constructor.
    generalize H3 H4. clear. intros.
    inversion H3. subst. simpl in *.
    apply H4. auto.
    apply IHcomps; auto. }
Qed.

  

Section Soundness.
  (** NL languages *)
  Context {NL: nat}.
  (** Languages *)
  Variable (L: @langs NL).
  
  (** Compilation units of source/target program*)
  Variable (scunits tcunits: @cunits NL L).
  
  (** Thread entries *)
  Variable (e: entries).
  
  (** The collection of compilers *)
  Variable (comps: @gcomp NL L).

  Theorem framework_sound:
    (** languages are well-defined *)
    wd_langs scunits ->
    wd_langs tcunits ->
    (** target languages are deterministic *)
    det_langs tcunits ->
    (** all compilation units are reach-closed *)
    rc_cunits scunits ->
    (** compilation units are compiled by [comps] *)
    cunits_transf comps scunits tcunits ->
    (** compilers are correct w.r.t. the global root and global injection on root*)
    seqs_correct comps ->
    (** whole source program is data-race-free *)
    drf (scunits, e) ->
    (** whole source program is safe *)
    safe_prog (scunits, e) ->
    (** main result: target program refines the source *)
    prog_refine (scunits, e) (tcunits, e).
  Proof.
    intros Hwd_src Hwd_tgt Hdet_tgt Hrc Hcomp Hcorrect Hdrf Hsafe.
    pose proof (@compositionality NL L) as HSim.
    specialize (HSim _ _ e Hwd_src Hwd_tgt Hrc).
    pose proof (Safe_NPSafe _ _ _ _ Hwd_src Hsafe) as Hnpsafe.
    cut (ldsims scunits tcunits). intro. specialize (HSim H). clear H.
    apply flipping in HSim; auto.
    constructor. intros. 
    eapply RefineEquiv.init_pair_config_refine;eauto.
    eapply init_pair_lemma in H1 as ?;try apply H0;eauto.
    clear H1.
    remember {|thread_pool := thread_pool tpc;
               cur_tid := ts;
               gm := gm tpc;
               atom_bit := atom_bit tpc |} as tpc'.
    clear tpc Heqtpc'. rename tpc' into tpc. rename H2 into H1.
    assert(NPSemantics.np_safe_config spc). inversion Hnpsafe;eauto.

    eapply DRF_NP_Refine_Config;try apply H0;try apply H1;eauto;simpl;eauto.
    intros.
    assert(ts = cur_tid tpc). inversion H1;auto. subst.
    assert(cur_tid tpc = cur_tid spc). inversion H0;auto.
    rewrite H4 in H0.
    eapply init_free in H1 as ?;eauto.
    eapply init_pair_lemma in H0;try apply H5;eauto.
    eapply USim_Safe_Config in H5;try apply H0;eauto.
    
    eapply NPDRF_DRF_Config; eauto;simpl;auto.
    intros.
    assert(ts = cur_tid tpc). inversion H1;auto. subst.
    assert(cur_tid tpc = cur_tid spc). inversion H0;auto.
    rewrite H4 in H0.
    eapply init_free in H1 as ?;eauto.
    eapply init_pair_lemma in H0;try apply H5;eauto.
    eapply USim_Safe_Config in H5;try apply H0;eauto.
    
    intros.
    assert(ts = cur_tid tpc). inversion H1;auto. subst.
    assert(cur_tid tpc = cur_tid spc). inversion H0;auto.
    rewrite H4 in H0.
    eapply init_free in H1 as ?;eauto.
    eapply init_pair_lemma in H0 as ?;try apply H5;eauto.
    eapply USim_NPDRF_Config in H5;try apply H0;eauto.
    assert( NPDRF.npdrf (scunits,e)).
    unfold NPDRF.npdrf. intro. unfold drf in Hdrf. contradict Hdrf.
    apply SmileReorder.NPRace_Race;auto.
    eapply NPDRF_config in H6;eauto.
    apply init_property_1_alt in H6;auto.
     
    apply USim_Refine in HSim as HRefine.
    inversion HRefine; eauto.
    eapply seqs_correct_fn_preserved; eauto. 
    eapply seqs_correct_ldsims; eauto. 
  Qed.

End Soundness.

(** ** Framework final theorem *)

(** Correctness of concurrent compiler correctness:
    for any compilation units [scunits] and [tcunits],
    if the [tcunits] are compiled from [scunits] by [comps],
    and the whole source program [(scunits, entries)] is safe,
    and the whole source program is data-race-free ([drf]), 
    and all source compilation units are reach-closed ([rc_cunits]), 
    then target program refines the source ([prog_refine]) 
 *)
Definition gcorrect {NL L} (comps: @gcomp NL L) : Prop :=
  forall scunits tcunits entries,
    cunits_transf comps scunits tcunits ->
    safe_prog (scunits, entries) ->
    drf (scunits, entries) ->
    rc_cunits scunits ->
    prog_refine (scunits, entries) (tcunits, entries).

(** Source and target langages of compilers are well-defined ([wd]) *)
Definition wd_comps_langs {NL L} (comps: @gcomp NL L) : Prop :=
  forall comp, In comp comps -> wd (L (slid comp)) /\ wd (L (tlid comp)).
(** Target languages of compilers are deterministic ([lang_det]) *)
Definition det_comps_tgt_langs {NL L} (comps: @gcomp NL L) : Prop :=
  forall comp, In comp comps -> lang_det (L (tlid comp)).

(** Framework final theorem:
    for any sequential compilers [comps], 
    if 
- [wd_comps_langs comps]: source and target languages of compilers are well defined,
- [det_comps_tgt_langs comps]: target languages are deterministic,
- [seqs_correct]: sequential compilers are correct w.r.t. our correctness creteria,
    then [gcorrect comps]: the sequential compilers are correct as a whole for compiling concurrent programs *)

Theorem framework_final_theorem:
  forall NL L (comps: @gcomp NL L),
  wd_comps_langs comps ->
  det_comps_tgt_langs comps ->
  seqs_correct comps ->
  gcorrect comps.
Proof.
  unfold gcorrect.
  intros NL L comps Hwd Hdet Hcorrect scunits tcunits entries Hcomp Hsafe Hdrf Hrc.
  eapply framework_sound; eauto.
  { revert Hcomp Hwd; clear. intro H. induction H.
    intros. intros cu C. inv C.
    intros. intros cu A. destruct A.
    inv H. simpl in *. exploit Hwd. left. eauto. tauto.
    exploit IHcunits_transf. intros cu' B. apply Hwd. right. auto. eauto. auto. }
  { revert Hcomp Hwd; clear. intro H. induction H.
    intros. intros cu C. inv C.
    intros. intros cu A. destruct A.
    inv H. simpl in *. exploit Hwd. left. eauto. tauto.
    exploit IHcunits_transf. intros cu' B. apply Hwd. right. auto. eauto. auto. }
  { revert Hcomp Hdet; clear. intro H. induction H.
    intros. intros cu C. inv C.
    intros. intros cu A. destruct A.
    inv H. simpl.
    replace tlid with (GAST.tlid {| slid := slid; tlid := tlid; comp := comp0 |}) by auto.
    eapply Hdet. left. auto. 
    eapply IHcunits_transf.
    intros cu' B. apply Hdet. right. auto. auto. }
Qed.

(* Print Assumptions framework_final_theorem. *)
