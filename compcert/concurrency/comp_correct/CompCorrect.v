Require Import Coqlib Maps Errors Globalenvs AST.

Require Import InteractionSemantics Blockset SeqCorrect IS_local LDSim_local Localize .

Require Import LDSimDefs_local CminorLang AsmLang Cminor_local CminorSel_local RTL_local LTL_local Linear_local Mach_local ASM_local Op_fp.

Require Import CminorLocalize AsmLocalize CUAST LDSim_local_transitive AsmIDTransCorrect.

Require
  selection selection_proof
  rtlgen rtlgen_proof
  tailcall tailcall_proof
  renumber renumber_proof
  allocation alloc_proof
  tunneling tunneling_proof
  linearize linearize_proof
  cleanuplabels cleanuplabels_proof
  stacking stacking_proof
  asmgen asmgen_proof.
  
(** This file contains the proof of CompCert satisfying our [SeqCorrect] condition *)


(** * CompCert backend Correctness *)
Hint Resolve nodup_gd_init_genv_ident_exists.

Lemma transf_partial_cunit_init_genv_preserved':
  forall F1 V1 F2 V2 cu1 cu2 transf_fun transf_var,
    transform_partial_cunit2 F1 V1 F2 V2 transf_fun transf_var cu1 = OK cu2 ->
    forall G1 ge1, ge1 = G1 /\ globalenv_generic cu1 ge1 ->
              exists G2 ge2, (ge2 = G2 /\ globalenv_generic cu2 ge2) /\
                        Genv.genv_next ge2 = Genv.genv_next ge1.
Proof.
  intros. destruct H0. exploit transform_partial_cunit_init_genv_preserved; eauto.
  intros [ge2 [GE GENVNEXT]]. eauto.
Qed.
Hint Resolve transf_partial_cunit_init_genv_preserved'.

Lemma transf_partial_fundef_correct:
  forall F1 F2 transf,
    @transf_func_correct F1 F2 (fun _ f => transf_partial_fundef transf f).
Proof.
  intros. unfold transf_partial_fundef. intro. intros.
  destruct f1; monadInv H; auto.
Qed.

Definition cminor_trans: @seq_comp CminorLang AsmLang :=
  fun scu : cminor_comp_unit =>
    assertion (nodup_gd_ident (cu_defs scu));
      assertion (nodup_ef (cu_defs scu));
      do cu_cminorsel <- selection.transf_program scu;
      assertion (nodup_gd_ident (cu_defs cu_cminorsel));
      do cu_rtl <- rtlgen.transf_program cu_cminorsel;
      assertion (nodup_gd_ident (cu_defs cu_rtl));
      do cu_rtl1 <- tailcall.transf_program cu_rtl;
      assertion (nodup_gd_ident (cu_defs cu_rtl1));
      do cu_rtl2 <- renumber.transf_program cu_rtl1;
      assertion (nodup_gd_ident (cu_defs cu_rtl2));
      do cu_ltl <- allocation.transf_program cu_rtl2;
      assertion (nodup_gd_ident (cu_defs cu_ltl));
      do cu_ltl2 <- tunneling.transf_program cu_ltl;
      assertion (nodup_gd_ident (cu_defs cu_ltl2));
      do cu_linear <- linearize.transf_program cu_ltl2;
      assertion (nodup_gd_ident (cu_defs cu_linear));
      do cu_linear2 <- cleanuplabels.transf_program cu_linear;
      assertion (nodup_gd_ident (cu_defs cu_linear2));
      do cu_mach <- stacking.transf_program cu_linear2;
      assertion (nodup_gd_ident (cu_defs cu_mach));
      do cu_asm <- asmgen.transf_program cu_mach;
      assertion (nodup_gd_ident (cu_defs cu_asm));
      assertion (nodup_ef (cu_defs cu_asm));
      OK cu_asm.

Ltac UG := unfold
             Cminor.fundef, Cminor_local.init_mem, Cminor_local.init_genv, Cminor.genv,
           CminorSel.fundef, CminorSel_local.init_mem, CminorSel_local.init_genv, CminorSel.genv,
           RTL.fundef, RTL_local.init_mem, RTL_local.init_genv, RTL.genv,
           LTL.fundef, LTL_local.init_mem, LTL_local.init_genv, LTL.genv,
           Linear.fundef, Linear_local.init_mem, Linear_local.init_genv, Linear.genv,
           Mach.fundef, Mach_local.init_mem, Mach_local.init_genv, Mach.genv,
           ASM_local.fundef, ASM_local.init_mem, ASM_local.init_genv, ASM_local.genv in *.
Ltac GG x :=
  UG;
  match goal with
  | H: transform_partial_cunit _ _ _ _ x = OK _ |- _ =>
    let HX:= fresh in
    pose proof H as HX; eapply transform_partial_cunit_init_genv_preserved in HX; eauto;
    destruct HX as [?ge [? ?]]
  end.
Ltac MM x :=
  UG;
  match goal with
  | H0: transform_partial_cunit _ _ _ _ x = OK ?y,
        H: globalenv_generic x ?ge1,
           H1: globalenv_generic ?y ?ge2
    |- init_mem_generic _ ?m =>
    exploit (init_mem_preserved' _ _ _ _ x y ge1 ge2 m H0); try exact H; try exact H1;
    simpl in *; UG; try congruence; eauto; clear H0 H1; intro
  end.
Ltac FF :=
  UG;
  match goal with
  | H: transform_partial_cunit _ _ _ _ ?x = OK ?y |- _ =>
    eapply transform_partial_cunit2_internal_fn_preserved in H;
    try apply transf_partial_fundef_correct
  end.
      

Theorem cminor_trans_correct: seq_correct cminor_trans.
Proof.
  unfold seq_correct, cminor_trans. intros.
  monadInv H. monadInv EQ.
  unfold
    rtlgen.transf_program,
  tailcall.transf_program,
  renumber.transf_program,
  allocation.transf_program,
  tunneling.transf_program,
  linearize.transf_program,
  cleanuplabels.transf_program,
  stacking.transf_program,
  asmgen.transf_program
    in *.
  split.
  { (* ldsim *)
    eapply localize. exact cminor_localize. exact asm_lift.
    intros. inv H0. destruct H. eapply nodup_gd_init_genv_ident_exists; eauto.
    intros. inv H0. destruct H. eapply nodup_gd_init_genv_ident_exists; eauto.
    split; auto. split; auto.
    (** Cminor -> CminorSel *)
    eapply ldsim_local_transitive with (L2:= CminorSel_IS) ; simpl. instantiate (1:=x).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x. GG x0. GG x1. GG x2. GG x3. GG x4. GG x5. GG x6.
    MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. MM x1. MM x0. MM x.
    intros ? ? ? ? ? ? ? . exploit selection_proof.transf_local_ldsim; eauto.
    unfold selection.transf_program. rewrite EQ9. simpl. eauto.
    (** CminorSel -> RTL *)
    eapply ldsim_local_transitive with (L2:= RTL_IS); simpl.
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x0. GG x1. GG x2. GG x3. GG x4. GG x5. GG x6.
    MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. MM x1. MM x0. 
    intros ? ? ? ? ? ? ? . exploit rtlgen_proof.transf_local_ldsim; eauto.
    (** Tailcall *)
    eapply ldsim_local_transitive with (L2:= RTL_IS); simpl. instantiate (1:= x1).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x1. GG x2. GG x3. GG x4. GG x5. GG x6.
    MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. MM x1.
    intros ? ? ? ? ? ? ? . exploit tailcall_proof.transf_local_ldsim; eauto.
    (** Renumber *)
    eapply ldsim_local_transitive with (L2:= RTL_IS); simpl. instantiate (1:=x2).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x2. GG x3. GG x4. GG x5. GG x6.
    MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. 
    intros ? ? ? ? ? ? ? . inv H; inv H0.
    exploit renumber_proof.TRANSF_local_ldsim.
    exact H3. exact H2. auto. 
    auto using renumber_proof.transf_program_match. auto.
    (** RTL -> LTL *)
    eapply ldsim_local_transitive with (L2:= LTL_IS); simpl. 
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x3. GG x4. GG x5. GG x6. MM x7. MM x6. MM x5. MM x4. MM x3. 
    intros ? ? ? ? ? ? ? . exploit alloc_proof.transf_local_ldsim; eauto.
    (** Tunneling *)
    eapply ldsim_local_transitive with (L2:= LTL_IS); simpl. instantiate (1:= x4).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x4. GG x5. GG x6. MM x7. MM x6. MM x5. MM x4. 
    intros ? ? ? ? ? ? ? . exploit tunneling_proof.transf_local_ldsim; eauto.
    (** LTL -> Linear *)
    eapply ldsim_local_transitive with (L2:= Linear_IS); simpl.
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x5. GG x6. MM x7. MM x6. MM x5. 
    intros ? ? ? ? ? ? ? . exploit linearize_proof.transf_local_ldsim; eauto.
    (** Cleanuplabels *)
    eapply ldsim_local_transitive with (L2:= Linear_IS); simpl. instantiate (1:= x6).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x6. MM x7. MM x6. 
    intros ? ? ? ? ? ? ? . exploit cleanuplabels_proof.transf_local_ldsim; eauto.
    (** Linear -> Mach *)
    eapply ldsim_local_transitive with (L2:= Mach_IS asmgen_proof0.return_address_offset); simpl.
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    MM x7. 
    intros ? ? ? ? ? ? ? . exploit stacking_proof.transf_local_ldsim; eauto.
    exact asmgen_proof.return_address_exists.
    (** Mach -> x86_32 *)
    intros ? ? ? ? ? ? ? . exploit asmgen_proof.transf_local_ldsim; eauto.
  }
  { (* fn preserved *)
    FF. FF. FF. FF. FF. FF. FF. FF. FF. FF. 
    unfold InteractionSemantics.internal_fn. simpl. congruence.
    unfold Tailcall.transf_fundef. unfold transf_fundef.
    clear. intro. intros. monadInv H. destruct f1; auto.
    unfold Renumber.transf_fundef.
    intro. intros. monadInv H. destruct f1; simpl; auto.
    unfold Tunneling.tunnel_fundef.
    intro. intros. monadInv H. destruct f1; simpl; auto.
    unfold CleanupLabels.transf_fundef.
    intro. intros. monadInv H. destruct f1; simpl; auto.
  }
Qed.

(* Coq bug ? *)
(* Print Assumptions alloc_proof.transf_local_ldsim. *)

(* Print Assumptions linearize_proof.transf_local_ldsim. *)

(* Print Assumptions stacking_proof.transf_local_ldsim. *)
(* where did we use Events.inline_assembly_sem ? *)

(* can we eliminate helpers.i64ext_inject? *)

(* Print Assumptions asmgen_proof.transf_local_ldsim. *)

Theorem id_trans_asm_correct: seq_correct id_trans_asm.
Proof. apply AsmIDTransCorrect.id_trans_asm_correct. Qed.


Require Import Csharpminor_local.
Require ClightLang Clight_local.
Require
  ClightLocalize
  cshmgen cshmgen_proof
  cminorgen cminorgen_proof.
  
(** * CompCert Correctness *)


Definition clight_trans: @seq_comp ClightLang.Clight_IS_2 AsmLang :=
  fun scu : ClightLang.clight_comp_unit =>
    assertion (nodup_gd_ident (ClightLang.cu_defs scu));
      assertion (ClightLocalize.nodup_ef (ClightLang.cu_defs scu));
      do cu_cshm <- cshmgen.transl_program scu;
      assertion (nodup_gd_ident (cu_defs cu_cshm));
      do cu_cminor <- cminorgen.transl_program cu_cshm;
      assertion (nodup_gd_ident (cu_defs cu_cminor));
      do cu_cminorsel <- selection.transf_program cu_cminor;
      assertion (nodup_gd_ident (cu_defs cu_cminorsel));
      do cu_rtl <- rtlgen.transf_program cu_cminorsel;
      assertion (nodup_gd_ident (cu_defs cu_rtl));
      do cu_rtl1 <- tailcall.transf_program cu_rtl;
      assertion (nodup_gd_ident (cu_defs cu_rtl1));
      do cu_rtl2 <- renumber.transf_program cu_rtl1;
      assertion (nodup_gd_ident (cu_defs cu_rtl2));
      do cu_ltl <- allocation.transf_program cu_rtl2;
      assertion (nodup_gd_ident (cu_defs cu_ltl));
      do cu_ltl2 <- tunneling.transf_program cu_ltl;
      assertion (nodup_gd_ident (cu_defs cu_ltl2));
      do cu_linear <- linearize.transf_program cu_ltl2;
      assertion (nodup_gd_ident (cu_defs cu_linear));
      do cu_linear2 <- cleanuplabels.transf_program cu_linear;
      assertion (nodup_gd_ident (cu_defs cu_linear2));
      do cu_mach <- stacking.transf_program cu_linear2;
      assertion (nodup_gd_ident (cu_defs cu_mach));
      do cu_asm <- asmgen.transf_program cu_mach;
      assertion (nodup_gd_ident (cu_defs cu_asm));
      assertion (nodup_ef (cu_defs cu_asm));
      OK cu_asm.

Theorem compcert_correct: seq_correct clight_trans.
Proof.
  unfold seq_correct, clight_trans. intros.
  monadInv H. monadInv EQ0.
  unfold
    cshmgen.transl_program,
  cminorgen.transl_program,
  rtlgen.transf_program,
  tailcall.transf_program,
  renumber.transf_program,
  allocation.transf_program,
  tunneling.transf_program,
  linearize.transf_program,
  cleanuplabels.transf_program,
  stacking.transf_program,
  asmgen.transf_program
    in *.
  split.
  { (* ldsim *)
    eapply localize. exact ClightLocalize.clight_localize. exact asm_lift.
    intros. inv H0. destruct H. eapply nodup_gd_init_genv_ident_exists; try eassumption. simpl. eauto.
    intros. inv H0. destruct H. eapply nodup_gd_init_genv_ident_exists; eauto.
    split; auto. split; auto.
    (** Clight -> C#minor *)
    eapply ldsim_local_transitive with (L2:= Csharpminor_IS) ; simpl. instantiate (1:=x).
    UG. unfold Clight_local.init_genv. simpl in *. intros. destruct H.
    exploit transform_partial_cunit_init_genv_preserved. exact EQ. exact H0.
    unfold init_genv. intros [ge2 [Hgenv Hnext]]. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst. unfold init_mem.
    GG x. GG x0. GG x1. GG x2. GG x3. GG x4. GG x5. GG x6. GG x7. GG x8.
    MM x9. MM x8. MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. MM x1. MM x0. MM x.
    intros ? ? ? ? ? ? ? . exploit cshmgen_proof.TRANSF_local_ldsim; eauto.
    simpl in *. destruct H0. eauto.
    simpl in *. eapply cshmgen_proof.transl_program_match. eauto.
    simpl in *. inv H. eauto.
    simpl in *. inv H. inv H0. simpl. auto.
    (** C#minor -> Cminor *)
    eapply ldsim_local_transitive with (L2:= Cminor_IS) ; simpl. instantiate (1:=x0).
    unfold Csharpminor_local.init_genv, Cminor_local.init_genv. simpl in *. intros. destruct H.
    exploit transform_partial_cunit_init_genv_preserved. exact EQ1. exact H0.
    unfold init_genv. intros [ge2 [Hgenv Hnext]]. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst. 
    GG x0. GG x1. GG x2. GG x3. GG x4. GG x5. GG x6. GG x7. GG x8.
    MM x9. MM x8. MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. MM x1. MM x0. 
    intros ? ? ? ? ? ? ? . exploit cminorgen_proof.TRANSF_local_ldsim.
    simpl in *. eapply cminorgen_proof.transf_program_match. eauto.
    simpl in *. inv H. eauto.
    simpl in *. inv H. inv H0. eauto.
    simpl in *. inv H. inv H0. eauto.
    simpl in *. inv H. inv H0. auto.
    (** Cminor -> CminorSel *)
    eapply ldsim_local_transitive with (L2:= CminorSel_IS) ; simpl. instantiate (1:=x1).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x1. GG x2. GG x3. GG x4. GG x5. GG x6. GG x7. GG x8.
    MM x9. MM x8. MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. MM x1. 
    intros ? ? ? ? ? ? ? . exploit selection_proof.transf_local_ldsim; eauto.
    unfold selection.transf_program. rewrite EQ11. simpl. eauto.
    (** CminorSel -> RTL *)
    eapply ldsim_local_transitive with (L2:= RTL_IS); simpl.
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x2. GG x3. GG x4. GG x5. GG x6. GG x7. GG x8.
    MM x9. MM x8. MM x7. MM x6. MM x5. MM x4. MM x3. MM x2. 
    intros ? ? ? ? ? ? ? . exploit rtlgen_proof.transf_local_ldsim; eauto.
    (** Tailcall *)
    eapply ldsim_local_transitive with (L2:= RTL_IS); simpl. instantiate (1:= x3).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x3. GG x4. GG x5. GG x6. GG x7. GG x8.
    MM x9. MM x8. MM x7. MM x6. MM x5. MM x4. MM x3. 
    intros ? ? ? ? ? ? ? . exploit tailcall_proof.transf_local_ldsim; eauto.
    (** Renumber *)
    eapply ldsim_local_transitive with (L2:= RTL_IS); simpl. instantiate (1:=x4).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x4. GG x5. GG x6. GG x7. GG x8.
    MM x9. MM x8. MM x7. MM x6. MM x5. MM x4. 
    intros ? ? ? ? ? ? ? . inv H; inv H0.
    exploit renumber_proof.TRANSF_local_ldsim.
    exact H3. exact H2. auto. 
    auto using renumber_proof.transf_program_match. auto.
    (** RTL -> LTL *)
    eapply ldsim_local_transitive with (L2:= LTL_IS); simpl. 
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x5. GG x6. GG x7. GG x8. MM x9. MM x8. MM x7. MM x6. MM x5. 
    intros ? ? ? ? ? ? ? . exploit alloc_proof.transf_local_ldsim; eauto.
    (** Tunneling *)
    eapply ldsim_local_transitive with (L2:= LTL_IS); simpl. instantiate (1:= x6).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x6. GG x7. GG x8. MM x9. MM x8. MM x7. MM x6. 
    intros ? ? ? ? ? ? ? . exploit tunneling_proof.transf_local_ldsim; eauto.    
    (** LTL -> Linear *)
    eapply ldsim_local_transitive with (L2:= Linear_IS); simpl.
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x7. GG x8. MM x9. MM x8. MM x7. 
    intros ? ? ? ? ? ? ? . exploit linearize_proof.transf_local_ldsim; eauto.
    (** Cleanuplabels *)
    eapply ldsim_local_transitive with (L2:= Linear_IS); simpl. instantiate (1:= x8).
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    GG x8. MM x9. MM x8. 
    intros ? ? ? ? ? ? ? . exploit cleanuplabels_proof.transf_local_ldsim; eauto.
    (** Linear -> Mach *)
    eapply ldsim_local_transitive with (L2:= Mach_IS asmgen_proof0.return_address_offset); simpl.
    UG. eauto.
    intros. inversion H0. rewrite dom_match. auto.
    UG; intros. destruct H, H0. subst.
    MM x9. 
    intros ? ? ? ? ? ? ? . exploit stacking_proof.transf_local_ldsim; eauto.
    exact asmgen_proof.return_address_exists.
    (** Mach -> x86_32 *)
    intros ? ? ? ? ? ? ? . exploit asmgen_proof.transf_local_ldsim; eauto.
  }
  { (* fn preserved *)
    FF. FF. FF. FF. FF. FF. FF. FF. FF. FF. FF.
    unfold InteractionSemantics.internal_fn. simpl.
    rewrite <- EQ10; clear EQ10.
    rewrite <- EQ9; clear EQ9.
    rewrite <- EQ8; clear EQ8.
    rewrite <- EQ7; clear EQ7.
    rewrite <- EQ6; clear EQ6.
    rewrite <- EQ5; clear EQ5.
    rewrite <- EQ4; clear EQ4.
    rewrite <- EQ3; clear EQ3.
    rewrite <- EQ2; clear EQ2.
    rewrite <- EQ12; clear EQ12.
    rewrite <- EQ1; clear EQ1.
    revert EQ; simpl; clear. intro.
    { monadInv EQ.
      unfold ClightLang.internal_fn. unfold cshmgen.clight_cu_to_cu in EQ0. simpl in EQ0.
      revert EQ0. generalize (ClightLang.cu_defs su).
      unfold internal_fn. simpl.
      intros. f_equal.
      revert EQ0. generalize (ClightLang.cu_comp_env su). intro. clear su.
      revert x0. induction l; intros.
      monadInv EQ0. auto.
      simpl in *. destruct a as [id0 g0].
      destruct g0. destruct (Cshmgen.transl_fundef c id0 f) eqn:EQ. monadInv EQ0. 
      erewrite IHl; eauto. simpl.
      apply Axioms.functional_extensionality. intro. destruct ident_eq; auto.
      subst. destruct f; simpl in EQ; try monadInv EQ; auto.
      destruct signature_eq; monadInv EQ; auto.
      monadInv EQ0.
      monadInv EQ0. simpl. erewrite IHl; eauto.
    }    
    unfold Tailcall.transf_fundef. unfold transf_fundef.
    clear. intro. intros. monadInv H. destruct f1; auto.
    unfold Renumber.transf_fundef.
    intro. intros. monadInv H. destruct f1; simpl; auto.
    unfold Tunneling.tunnel_fundef.
    intro. intros. monadInv H. destruct f1; simpl; auto.
    unfold CleanupLabels.transf_fundef.
    intro. intros. monadInv H. destruct f1; simpl; auto.
  }
Qed.

