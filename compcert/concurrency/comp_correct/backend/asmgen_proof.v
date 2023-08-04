(* Extended the original CompCert's correctness proof for supporting concurrency. *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86-64 generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

Require Import Blockset Footprint InteractionSemantics IS_local CUAST
        Mach_local ASM_local Op_fp asmgen asmgen_proof0 asmgen_proof1.

Require Import loadframe InjRels MemClosures_local LDSim_local val_casted.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

Require Import LDSimDefs LDSimDefs_local.

(** TODO: move to ? *)
Lemma val_inject_strict_id_eq:
  forall j bs v v',
    inject_incr j inject_id ->
    G_arg bs v ->
    Val.inject j v v' ->
    v' = v.
Proof. clear. intros. inv H1; auto. apply H in H2. inv H2. rewrite Ptrofs.add_zero. auto. contradiction. Qed.

Lemma val_inject_list_strict_id_eq:
  forall j bs vl vl',
    inject_incr j inject_id ->
    G_args bs vl ->
    Val.inject_list j vl vl' ->
    vl' = vl.
Proof. clear. induction 3; auto. inv H0. f_equal. apply val_inject_strict_id_eq with j bs; auto. auto. Qed.

Definition match_cu (cu: Mach_comp_unit) (tcu: Asm_comp_unit) :=
  match_comp_unit_gen (fun f tf => transf_fundef f = OK tf) eq cu tcu.

Lemma transf_program_match:
  forall cu tcu, transf_program cu = OK tcu -> match_cu cu tcu.
Proof.
  intros. eapply match_transform_partial_cunit; eauto.
Qed.

Definition funsig (f: ASM_local.fundef) : signature :=
  match f with
  | Internal fd => fn_sig fd
  | External ef => ef_sig ef
  end.

Lemma sig_preserved':
  forall f tf, transf_function f = OK tf -> fn_sig tf = Mach.fn_sig f.
Proof.
  intros f tf. unfold transf_function, transl_function.
  intro TRANS. monadInv TRANS. monadInv EQ. destruct zlt in EQ0; [discriminate|]. clear g.
  inv EQ0. simpl. auto.
Qed.

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> funsig tf = Mach.funsig f.
Proof.
  clear.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros H; monadInv H; auto.
  simpl. apply sig_preserved'; auto.
Qed.


Section PRESERVATION.

Let Mach_IS := Mach_IS return_address_offset.

Variable scu: Mach_IS.(comp_unit).
Variable tcu: Asm_IS.(comp_unit).

Hypothesis TRANSF: match_cu scu tcu.


Variables sge sG: Mach.genv.
Variables tge tG: ASM_local.genv.

Hypothesis GE_INIT: Mach_IS.(init_genv_local) scu sge sG.
Hypothesis TGE_INIT: Asm_IS.(init_genv_local) tcu tge tG.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof.
  inv GE_INIT; inv TGE_INIT. exploit match_cu_match_genv; eauto.
  intro. inv H; auto.
Qed.

Lemma senv_preserved:
  Senv.equiv sge tge.
Proof. inv GE_INIT. inv TGE_INIT. eapply match_cu_senv_preserved; eauto. Qed.

Lemma ge_match: ge_match_strict sge tge.
Proof. inv GE_INIT. inv TGE_INIT. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr sge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold Genv.find_funct_ptr, Genv.find_def; intros.
  exploit match_cu_match_genv; eauto.
  inv GE_INIT; auto. inv TGE_INIT; auto.
  intros [_ _ MATCH]. specialize (MATCH b).
  inv MATCH. rewrite <- H1 in H. discriminate.
  rewrite <- H0 in H. inv H. 
  inv H2. inv H4; eauto. discriminate.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct sge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  destruct v; simpl; intros; try discriminate.
  destruct Ptrofs.eq_dec; [|discriminate].
  apply function_ptr_translated; auto.
Qed.

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr sge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit function_ptr_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ. auto.
Qed.

Lemma ef_transl:
  forall fb ef,
    Genv.find_funct_ptr sge fb = Some (External ef) ->
    Genv.find_funct_ptr tge fb = Some (External ef).
Proof.
  intros. exploit function_ptr_translated; eauto.
  intros [tf' [A B]]. monadInv B. auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z (fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); monadInv EQ0.
  omega.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs lf m fp rs' m',
  transl_code_at_pc sge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m fp c' rs' m' ->
  plus (step tge) (Core_State rs lf) m fp (Core_State rs' lf) m'.
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m fp rs' m',
  transl_code_at_pc sge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m fp tc' rs' m' ->
  transl_code_at_pc sge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros.
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_shrxlimm_label:
  forall n k c, mk_shrxlimm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H. destruct (Int.eq n Int.zero); TailNoLabel.
Qed.
Hint Resolve mk_shrxlimm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c ->
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel.
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_storebyte_label:
  forall addr r k c, mk_storebyte addr r k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_storebyte; intros. TailNoLabel.
Qed.
Hint Resolve mk_storebyte_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty; try discriminate; destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd RAX); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (Archi.ptr64 || low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct (Float.eq_dec n Float.zero); TailNoLabel.
  destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
  destruct (normalize_addrmode_64 x) as [am' [delta|]]; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto.
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ0; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr sge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m
  /\ transl_code_at_pc sge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply asmgen_proof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
 *)

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach_local.core) : nat :=
  match s with
  | Mach_local.Core_Returnstate _ _ _ => 1%nat
  | _ => 0%nat
  end.


Ltac svalid :=
  match goal with
  | H: ge_init_inj ?mu ?sge ?tge |- context[Injections.SharedSrc ?mu]
    => erewrite mu_shared_src; eauto; unfold Mem.valid_block; intros;
      apply Plt_Ple_trans with (Genv.genv_next sge); eauto with coqlib
  | H: ge_init_inj ?mu ?sge ?tge |- context[Injections.SharedTgt ?mu]
    => erewrite mu_shared_tgt; eauto; unfold Mem.valid_block; intros;
      apply Plt_Ple_trans with (Genv.genv_next tge); eauto with coqlib
  end.

Inductive MATCH_STATE: bool -> nat -> Injections.Mu -> FP.t -> FP.t ->
                       Mach_local.core * mem -> ASM_local.core * mem -> Prop :=
| MATCH_STATE_intro:
    forall mu s fb sp c ep ms m m' rs f tf tc sp0 args0 tyl0 sigres0 fp fp'
      (STACKS: match_stack sge s)
      (FIND: Genv.find_funct_ptr sge fb = Some (Internal f))
      (MEXT: Mem.extends m m')
      (AT: transl_code_at_pc sge (rs PC) fb f c ep tf tc)
      (AG: agree ms sp rs)
      (AXP: ep = true -> rs#RAX = parent_sp0 sp0 s)
      (** NEW *)
      (BOUND: Ple (Genv.genv_next sge) (Mem.nextblock m))
      (BOUND': Ple (Genv.genv_next tge) (Mem.nextblock m'))
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE true 0%nat mu fp fp'
                  (Mach_local.Core_State s fb sp c ms (mk_load_frame sp0 args0 tyl0 sigres0), m)
                  (ASM_local.Core_State rs (ASM_local.mk_load_frame sp0 sigres0), m')
                  
| MATCH_STATE_call:
    forall mu s fb ms m m' rs sp0 args0 tyl0 sigres0 fp fp'
      (STACKS: match_stack sge s)
      (MEXT: Mem.extends m m')
      (AG: agree ms (parent_sp0 sp0 s) rs)
      (ATPC: rs PC = Vptr fb Ptrofs.zero)
      (ATLR: rs RA = parent_ra s)
      (** NEW *)
      (BOUND: Ple (Genv.genv_next sge) (Mem.nextblock m))
      (BOUND': Ple (Genv.genv_next tge) (Mem.nextblock m'))
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE true 0%nat mu fp fp'
                  (Mach_local.Core_Callstate s fb ms (mk_load_frame sp0 args0 tyl0 sigres0), m)
                  (ASM_local.Core_State rs (ASM_local.mk_load_frame sp0 sigres0), m')

| MATCH_STATE_return:
    forall mu s ms m m' rs sp0 args0 tyl0 sigres0 fp fp'
      (STACKS: match_stack sge s)
      (MEXT: Mem.extends m m')
      (AG: agree ms (parent_sp0 sp0 s) rs)
      (ATPC: rs PC = parent_ra s)
      (** NEW *)
      (BOUND: Ple (Genv.genv_next sge) (Mem.nextblock m))
      (BOUND': Ple (Genv.genv_next tge) (Mem.nextblock m'))
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE true 1%nat mu fp fp'
                  (Mach_local.Core_Returnstate s ms (mk_load_frame sp0 args0 tyl0 sigres0), m)
                  (ASM_local.Core_State rs (ASM_local.mk_load_frame sp0 sigres0), m')

| MATCH_STATE_callout:
    forall b mu s fb ef args args' ms m m' rs sp0 args0 tyl0 sigres0 fp fp'
      (STACKS: match_stack sge s)
      (MEXT: Mem.extends m m')
      (AG: agree ms (parent_sp0 sp0 s) rs)
      (ATPC: rs PC = Vptr fb Ptrofs.zero)
      (ATLR: rs RA = parent_ra s)
      (BOUND: Ple (Genv.genv_next sge) (Mem.nextblock m))
      (BOUND': Ple (Genv.genv_next tge) (Mem.nextblock m'))
      (** NEW *)
      (*      (EXTFUN: Genv.find_funct_ptr tge fb = Some (External callee)) *)
      (ARGS: Val.lessdef_list args args')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE b 0%nat mu fp fp'
                  (Mach_local.Core_CallstateOut s fb ef args ms (mk_load_frame sp0 args0 tyl0 sigres0), m)
                  (ASM_local.Core_CallstateOut ef args' rs (ASM_local.mk_load_frame sp0 sigres0), m')
                  
| MATCH_STATE_callin:
    forall mu fb0 m m' args0 tyl0 sigres0 
      (MEXT: Mem.extends m m')
      (** NEW *)
      (BOUND: Ple (Genv.genv_next sge) (Mem.nextblock m))
      (BOUND': Ple (Genv.genv_next tge) (Mem.nextblock m'))
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: unmapped_closed mu m m')
    ,
      MATCH_STATE true 0%nat mu empfp empfp
                  (Mach_local.Core_CallstateIn fb0 args0 tyl0 sigres0, m)
                  (ASM_local.Core_CallstateIn fb0 args0 tyl0 sigres0, m')
.

(** TODO: move to InjRels.v? *)



Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2
    mu sp0 args0 tyl0 sigres0 fp0 fp0' fp
    (AGMU: proper_mu sge tge inject_id mu)
    (RCPRESV: unmapped_closed mu m2 m2')
    (FPMATCH: Injections.FPMatch' mu fp0 fp0')
    (BOUND: Ple (Genv.genv_next sge) (Mem.nextblock m2))
    (BOUND': Ple (Genv.genv_next tge) (Mem.nextblock m2'))
,
    match_stack sge s ->
    Mem.extends m2 m2' ->
    Genv.find_funct_ptr sge fb = Some (Internal f) ->
    transl_code_at_pc sge (rs1 PC) fb f (i :: c) ep tf tc ->
    (forall k c (TR: transl_instr f i ep k = OK c),
        exists rs2 fp',
          exec_straight tge tf c rs1 m1' fp' k rs2 m2'
          /\ agree ms2 sp rs2
          /\ (it1_is_parent ep i = true -> rs2#RAX = parent_sp0 sp0 s)
          /\ (Injections.FPMatch' mu fp fp')) ->
    exists fp' st' m2'',
      plus (step tge) (Core_State rs1 (ASM_local.mk_load_frame sp0 sigres0)) m1' fp' st' m2'' /\
      Injections.FPMatch' mu (FP.union fp0 fp) (FP.union fp0' fp') /\
      MATCH_STATE true 0%nat mu (FP.union fp0 fp) (FP.union fp0' fp')
                  (Mach_local.Core_State s fb sp c ms2 (mk_load_frame sp0 args0 tyl0 sigres0), m2)
                  (st', m2'').
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [fp' [A [B [C D]]]]].
  exists fp', (Core_State rs2 (ASM_local.mk_load_frame sp0 sigres0)), m2'; split.
  eapply exec_straight_exec; eauto.
  split.
  apply Injections.fp_match_union'; auto.
  econstructor; eauto. eapply exec_straight_at; eauto.
  apply Injections.fp_match_union'; auto.
Qed.
(** TODO: move to ? *)
Lemma store_args_extends:
  forall m1 m1' sp args tyl m2,
    Mem.extends m1 m1' ->
    store_args m1 sp args tyl = Some m2 ->
    exists m2', store_args m1' sp args tyl = Some m2' /\
           Mem.extends m2 m2'.
Proof.
  clear.
  unfold store_args. intros until 1. generalize 0. revert args m1 m1' tyl m2 H.
  induction args; intros.
  simpl in H0. destruct tyl; [inv H0;simpl|discriminate]. eexists; eauto.
  destruct tyl; [discriminate|].
  destruct t; simpl in H0;
    match goal with
    | H: match (store_stack ?a ?b ?c ?d ?e) with _ => _ end = _ |- _ =>
      destruct (store_stack a b c d e) eqn:?EQ; inv H; simpl; unfold store_stack, Mach.store_stack in EQ |- *;
        (eapply Mem.storev_extends in EQ; eauto); destruct EQ as [?m [?B ?C]]; rewrite B;
          try (eapply IHargs; eauto; fail)
    | _ => idtac
    end.
  destruct a; inv H0.
  destruct (store_stack m1 _ _ _ _) eqn:?EQ; try discriminate; simpl; unfold store_stack, Mach.store_stack in EQ |- *;
    (eapply Mem.storev_extends in EQ; eauto); destruct EQ as [?A [?B ?C]]; rewrite B.
  destruct (store_stack m _ _ _ _) eqn:?EQ; try discriminate; simpl; unfold store_stack, Mach.store_stack in EQ |- *;
    (eapply Mem.storev_extends in EQ; eauto); destruct EQ as [?A [?B ?C]].
  simpl in B0. rewrite B0. eapply IHargs; eauto.
Qed.

Lemma store_args_nextblock:
  forall m m' sp args tyl,
    store_args m sp args tyl = Some m' ->
    Mem.nextblock m' = Mem.nextblock m.
Proof.
  clear. unfold store_args. intros until args. generalize 0. revert m m' sp. induction args.
  simpl. destruct tyl; inversion 1; auto.
  simpl. destruct tyl; [discriminate|].
  destruct t; intro H; simpl in H;
    match goal with
    | H: match (store_stack ?a ?b ?c ?d ?e) with _ => _ end = _ |- _ =>
      destruct (store_stack a b c d e) eqn:?EQ; inv H; simpl; unfold store_stack, Mach.store_stack in EQ |- *;
        exploit IHargs; eauto; intro NEXT; rewrite NEXT; simpl in EQ; eapply Mem.nextblock_store; eauto
    | _ => idtac
    end.
  destruct a; inv H.
  destruct (store_stack m _ _ _ _) eqn:?EQ; inv H1; simpl; unfold store_stack, Mach.store_stack in EQ |- *.
  destruct (store_stack m0 _ _ _ _) eqn:?EQ; inv H0; simpl; unfold store_stack, Mach.store_stack in EQ0 |- *.
  simpl in EQ, EQ0.
  exploit IHargs; eauto; intro NEXT; rewrite NEXT.
  erewrite Mem.nextblock_store. erewrite Mem.nextblock_store. eauto. eauto. eauto. 
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c'
    mu sp0 args0 tyl0 sigres0 fp0 fp0' fp
    (AGMU: proper_mu sge tge inject_id mu)
    (RCPRESV: unmapped_closed mu m2 m2')
    (FPMATCH: Injections.FPMatch' mu fp0 fp0')
    (BOUND: Ple (Genv.genv_next sge) (Mem.nextblock m2))
    (BOUND': Ple (Genv.genv_next tge) (Mem.nextblock m2'))
,
    match_stack sge s ->
    Mem.extends m2 m2' ->
    Genv.find_funct_ptr sge fb = Some (Internal f) ->
    Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
    transl_code_at_pc sge (rs1 PC) fb f (i :: c) ep tf tc ->
    it1_is_parent ep i = false ->
    (forall k c (TR: transl_instr f i ep k = OK c),
        exists jmp, exists k', exists rs2, exists fp',
              exec_straight tge tf c rs1 m1' fp' (jmp :: k') rs2 m2'
              /\ agree ms2 sp rs2
              /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2'
              /\ exec_instr_fp tge tf jmp rs2 m2' = empfp
              /\ (Injections.FPMatch' mu fp fp')) ->
    exists fp' st' m2'',
      plus (step tge) (Core_State rs1 (ASM_local.mk_load_frame sp0 sigres0)) m1' fp' st' m2'' /\
      Injections.FPMatch' mu (FP.union fp0 fp) (FP.union fp0' fp') /\
      MATCH_STATE true 0%nat mu (FP.union fp0 fp) (FP.union fp0' fp')
                  (Mach_local.Core_State s fb sp c' ms2 (mk_load_frame sp0 args0 tyl0 sigres0), m2)
                  (st', m2'').
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [fp' [A [B [C [D E]]]]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists fp', (Core_State rs3 (ASM_local.mk_load_frame sp0 sigres0)), m2'; split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  rewrite FP.fp_union_emp; auto.
  split. apply Injections.fp_match_union'; auto.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
  apply Injections.fp_match_union'; auto.
Qed.

Theorem TRANSF_local_ldsim:
  @local_ldsim Mach_IS Asm_IS sG tG sge tge.
Proof.
  eapply (@Local_ldsim Mach_IS Asm_IS _ _ _ _ nat Nat.lt MATCH_STATE).
    
  constructor.
  (* index wf *)
  - apply Nat.lt_wf_0.
  (* wd_mu *)
  - intros. inv H; eapply proper_mu_inject; eauto.
  (* inj ge *)
  - intros. inv H; eapply proper_mu_ge_init_inj; eauto.
  (* ge match *)
  - apply ge_match.
  (* initial call *)
  - assert (HSG: sG = sge) by (inv GE_INIT; auto).
    assert (HTG: tG = tge) by (inv TGE_INIT; auto).
    intros mu fid args args' score GE_INIT_INJ INJID GARGS ARGREL INITCORE.
    assert (ARGINJ: Val.inject_list (Bset.inj_to_meminj (Injections.inj mu)) args args') by auto.
(*     { generalize ARGREL; clear. induction 1; eauto. constructor; auto. inv H; eauto. } *)
    unfold init_core_local in *. simpl in *.
    unfold Mach_local.init_core, init_core in *.
    rewrite HTG, symbols_preserved.
    rewrite HSG in INITCORE.
    destruct (Genv.find_symbol sge fid) eqn: FIND; try discriminate.
    destruct (Genv.find_funct_ptr sge b) eqn: FINDB; try discriminate.
    exploit function_ptr_translated; eauto. intros (tf & FINDB' & TRANSL).
    rewrite FINDB'.
    destruct f; try discriminate.
    assert (exists tfd, tf = Internal tfd)  as [tfd INTERNAL] by (monadInv TRANSL; eauto). subst tf.
    unfold Mach_local.fundef_init, fundef_init in *.
    erewrite sig_preserved';[|monadInv TRANSL; eauto].
    destruct (wd_args args (sig_args (Mach.funsig (Internal f)))) eqn: WDARGS; [|discriminate].
    erewrite wd_args_inject; eauto.
    eexists. split. eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists 0%nat.
    inversion INITCORE; clear INITCORE.
    assert (args' = args) as EQARG.
    { inv MEMINITINJ. eapply val_inject_list_strict_id_eq; eassumption. }
    subst args'.
    econstructor; eauto.
    (** TODO: need to require no new blocks in local freelist in RELY *)
    (** TODO: Mem.extends -> HLRely -> Mem.extends *)
    assert (Mem.extends sm0 tm0).
    { generalize MEMINITINJ GE_INIT_INJ S_EQ. clear; intros.
      inv MEMINITINJ.
      (** TODO: move to ? *)
      eapply inject_implies_extends; eauto.
      intros. unfold Mem.valid_block in H; rewrite <- dom_eq_src in H. eapply Bset.inj_dom in H; eauto.
      destruct H as [b' A]. unfold Bset.inj_to_meminj. rewrite A. eauto.
      inv GE_INIT_INJ.
      rewrite mu_shared_src in dom_eq_src.
      rewrite mu_shared_tgt in dom_eq_tgt.
      rewrite S_EQ in dom_eq_src.
      assert (forall b, Plt b (Mem.nextblock sm0) <-> Plt b (Mem.nextblock tm0)).
      { intro. rewrite <- dom_eq_src, <- dom_eq_tgt. tauto. }
      destruct (Pos.lt_total (Mem.nextblock sm0) (Mem.nextblock tm0)) as [LT | [EQ | LT]]; auto;
        generalize H LT; clear; intros; exfalso;
          apply H in LT; eapply Pos.lt_irrefl; eauto.
    }
    
    eapply extends_rely_extends; eauto.
    inv MEMINITINJ; eauto.
    inv MEMINITINJ; eauto.
    constructor; auto.
    
    erewrite dom_match. inv HRELY. inv H. eauto. auto.
    erewrite dom_match. inv LRELY. inv H. eauto. auto.    
    inversion GE_INIT_INJ; inversion MEMINITINJ. constructor; auto.
    unfold sep_inject. intros. 
    unfold Bset.inj_to_meminj in H. destruct (Injections.inj mu b0) eqn:?; [|inv H].
    eapply Bset.inj_range' in Heqo;[|inv mu_inject; eauto]. inv H. inv H1.
    rewrite mu_shared_tgt, <- S_EQ, <- mu_shared_src in Heqo.
    eapply Bset.inj_dom in Heqo; eauto. destruct Heqo.
    destruct Bset.inj_to_meminj as [[b' ofs]|] eqn:C. apply inj_inject_id in C. inv C; auto.
    unfold Bset.inj_to_meminj in C. rewrite H in C. discriminate.

    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY; auto.
    
  (* tau step *)
  - intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MATCH STEP.
    generalize i Hfp Lfp Lcore Lm MATCH; clear i Hfp Lfp Lcore Lm MATCH.
    induction STEP; intros i Hfp Lfp Lcore Lm MATCH; inv MATCH;
      assert (HSG: sG = sge) by (inv GE_INIT; auto);
      assert (HTG: tG = tge) by (inv TGE_INIT; auto).  
    
    + (* Mlabel *)
      right. exists 0%nat. simpl. rewrite HTG.
      eapply exec_straight_steps; eauto; intros.
      monadInv TR. eexists; eexists; split.
      apply exec_straight_one. simpl; eauto. auto. auto.
      split. apply agree_nextinstr; auto.
      split. simpl; congruence.
      simpl. apply fp_match_id; inv AGMU; auto.

    + (* Mgetstack *)
      unfold load_stack in H.
      exploit Mem.loadv_extends; eauto. intros [v' [A B]].
      rewrite (sp_val _ _ _ AG) in A. rewrite HTG.
      right; exists 0%nat. eapply exec_straight_steps; eauto. intros. simpl in TR.
      exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
      eexists rs', _; split. eauto.
      split. eapply agree_set_mreg; eauto. congruence.
      split. simpl; congruence.
      unfold load_stack_fp. inv AG. apply fp_match_id; inv AGMU; auto.

    + (* Msetstack *)
      unfold store_stack in H.
      assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
      exploit Mem.storev_extends; eauto. intros [m2' [A B]]. rewrite HTG.
      right; exists 0%nat; eapply exec_straight_steps.
      auto. 

      unfold Mach.store_stack, Mem.storev in H, A. destruct (Val.offset_ptr sp ofs) eqn:ADDR; try discriminate.
      destruct AGMU.
      eapply store_val_inject_unmapped_closed_preserved; eauto.
      svalid. svalid. reflexivity. rewrite Z.add_0_r. eauto. 

      auto. 
      unfold Mach.store_stack, Mem.storev in H.
      destruct (Val.offset_ptr sp ofs) in H; try discriminate.
      erewrite Mem.nextblock_store. eauto. eauto.
      unfold Mem.storev in A; destruct (Val.offset_ptr sp ofs) in A; try discriminate.
      erewrite Mem.nextblock_store. eauto. eauto.
      auto. auto. eauto. eauto.
      
      rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
      exploit storeind_correct; eauto. intros [rs' [P Q]].
      eexists rs', _; split. eauto.
      split. eapply agree_undef_regs; eauto.
      simpl; intros.
      split. rewrite Q; auto with asmgen.
      Local Transparent destroyed_by_setstack.
      destruct ty; simpl; intuition congruence.
      unfold store_stack_fp. inv AG. apply fp_match_id; inv AGMU; auto.

    + (* Mgetparam *)
      assert (f0 = f) by congruence; subst f0.
      unfold load_stack in *.
      exploit Mem.loadv_extends. eauto. eexact H0. auto.
      intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
      exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
      exploit Mem.loadv_extends. eauto. eexact H2. auto.
      intros [v' [C D]].
      Opaque loadind. rewrite HTG.
      right; exists 0%nat; eapply exec_straight_steps; eauto; intros.
      assert (DIFF: negb (mreg_eq dst AX) = true -> IR RAX <> preg_of dst).
      intros. change (IR RAX) with (preg_of AX). red; intros.
      unfold proj_sumbool in H1. destruct (mreg_eq dst AX); try discriminate.
      elim n. eapply preg_of_injective; eauto.
      destruct ep; simpl in TR.
      (* RAX contains parent *)
      exploit loadind_correct. eexact TR.
      instantiate (2 := rs0). rewrite AXP; eauto.
      intros [rs1 [P [Q R]]].
      eexists rs1, _; split. eauto.
      split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
      split.
      simpl; intros. rewrite R; auto.
      rewrite AXP;[|auto]. rewrite FP.union_comm_eq; apply Injections.fp_match_union_S'.
      unfold load_stack_fp. apply fp_match_id; inv AGMU; auto.
      (* RAX does not contain parent *)
      monadInv TR.
      exploit loadind_correct. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
      exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto.
      intros [rs2 [S [T U]]].
      eexists rs2, _; split. eapply exec_straight_trans; eauto.
      split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
      split. simpl; intros. rewrite U; auto.
      inv AG; rewrite Q; unfold load_stack_fp.
      apply Injections.fp_match_union'; apply fp_match_id; inv AGMU; auto. 

    + (* Mop *)
      assert (eval_operation tge sp op rs##args m = Some v).
      rewrite <- H, HSG. apply eval_operation_preserved. exact symbols_preserved.
      assert (eval_operation_fp tge sp op rs##args m = Some fp).
      rewrite <- H0, HSG. apply eval_operation_fp_preserved. exact symbols_preserved.
      exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H1.
      intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
      exploit eval_operation_lessdef_fp. eapply preg_vals; eauto. eauto. eexact H1. eexact H2.
      intros [fp' [A' B']]. 
      rewrite HTG. 
      right; exists 0%nat; eapply exec_straight_steps; eauto; intros. simpl in TR.
      exploit transl_op_correct; eauto. rewrite <- (sp_val _ _ _ AG). eauto.
      intros [rs2 [P [Q R]]].
      assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
      exists rs2, fp'; split. eauto.
      split. eapply agree_set_undef_mreg; eauto.
      split. simpl; congruence.
      inv AGMU; eapply fp_inject_fp_match; eauto. 

    + (* Mload *)
      assert (eval_addressing tge sp addr rs##args = Some a).
      rewrite <- H, HSG. apply eval_addressing_preserved. exact symbols_preserved.
      exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
      intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
      exploit Mem.loadv_extends; eauto. intros [v' [C D]].
      rewrite HTG. 
      right; exists 0%nat; eapply exec_straight_steps; eauto; intros. simpl in TR.
      exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
      eexists rs2, _; split. eauto.
      split. eapply agree_set_undef_mreg; eauto. congruence.
      split. simpl; congruence.
      { destruct a; inv B; inv H0. apply fp_match_id; inv AGMU; auto. }

    + (* Mstore *)
      assert (eval_addressing tge sp addr rs##args = Some a).
      rewrite <- H, HSG. apply eval_addressing_preserved. exact symbols_preserved.
      exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
      intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
      assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
      exploit Mem.storev_extends; eauto. intros [m2' [C D]].
      rewrite HTG.
      right; exists 0%nat; eapply exec_straight_steps.
      auto.

      unfold Mem.storev in H0, C. destruct a eqn:ADDR; try discriminate. inv B.
      destruct AGMU.
      eapply store_val_inject_unmapped_closed_preserved; eauto.
      svalid. svalid. reflexivity. rewrite Z.add_0_r. eauto. 

      auto. 
      unfold Mem.storev in H0. destruct a; try discriminate.
      erewrite Mem.nextblock_store. eauto. eauto.
      unfold Mem.storev in C. destruct a'; try discriminate.
      erewrite Mem.nextblock_store. eauto. eauto.
      auto. auto. eauto. eauto.
      
      intros. simpl in TR.
      exploit transl_store_correct; eauto. intros [rs2 [P Q]].
      eexists rs2, _; split. eauto.
      split. eapply agree_undef_regs; eauto.
      split. simpl; congruence.
      { destruct a; inv B; inv H0. apply fp_match_id; inv AGMU; auto. }

    + (* Mgoto *)
      assert (f0 = f) by congruence. subst f0.
      revert HSG HTG. inv AT. monadInv H4. intros.
      exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
      right; exists 0%nat.
      exists empfp, (Core_State rs' (ASM_local.mk_load_frame sp1 sigres0)), Lm; split.
      apply plus_one. econstructor; eauto.
      rewrite HTG. eapply functions_transl; eauto.
      eapply find_instr_tail; eauto.
      simpl; eauto. auto.
      split. apply Injections.fp_match_union'; auto. apply fp_match_id; inv AGMU; auto.
      econstructor; eauto.
      eapply agree_exten; eauto with asmgen.
      congruence.
      apply Injections.fp_match_union'; auto. apply fp_match_id; inv AGMU; auto.

    + (* Mcond true *)
      assert (f0 = f) by congruence. subst f0.
      
      exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
      exploit eval_condition_lessdef_fp. eapply preg_vals; eauto. eauto. eauto. eauto. intros [fp' [EC' FPINJ']].
      rewrite HTG.
      right; exists 0%nat; eapply exec_straight_steps_goto; eauto.
      intros. simpl in TR.
      pose proof (transl_cond_correct tge tf cond args _ _ rs0 Lm TR).
      unfold PregEq.t in *. rewrite EC in H3.
      destruct H3 as [rs' [fp'' [A [B [B' C]]]]].
      rewrite EC' in B'. inversion B'. subst fp''.
      eapply fp_inject_fp_match in FPINJ'; try (inv AGMU; eauto; fail).
      destruct (testcond_for_condition cond); simpl in *.
      (* simple jcc *)
      exists (Pjcc c1 lbl); exists k; exists rs'; exists fp'. 
      split. eexact A.
      split. eapply agree_exten; eauto.
      split. simpl. rewrite B. auto.
      split. simpl. auto.
      auto.
      
      (* jcc; jcc *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
        destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct b1.
      (* first jcc jumps *)
      exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'; exists fp'.
      split. eexact A.
      split. eapply agree_exten; eauto.
      split. simpl. rewrite TC1. auto.
      split. simpl. auto.
      auto.
      (* second jcc jumps *)
      exists (Pjcc c2 lbl); exists k; exists (nextinstr rs'); exists fp'.
      split. rewrite <- (FP.fp_union_emp fp'). eapply exec_straight_trans. eexact A.
      eapply exec_straight_one. simpl. rewrite TC1. auto. auto. auto.
      split. eapply agree_exten; eauto.
      intros; Simplifs.
      split. simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
      destruct b2; auto || discriminate.
      split. auto. auto.
      (* jcc2 *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
        destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct (andb_prop _ _ H4). subst.
      exists (Pjcc2 c1 c2 lbl); exists k; exists rs'; exists fp'.
      split. eexact A.
      split. eapply agree_exten; eauto.
      split. simpl. rewrite TC1; rewrite TC2; auto.
      split. auto. auto.

    + (* Mcond false *)
      exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
      exploit eval_condition_lessdef_fp. eapply preg_vals; eauto. eauto. eauto. eauto.
      intros [fp' [EC' FPINJ']].
      rewrite HTG.
      right; exists 0%nat ; eapply exec_straight_steps; eauto. intros. simpl in TR.
      destruct (transl_cond_correct tge tf cond args _ _ rs0 Lm TR)
               as [rs' [fp'' A]].
      unfold PregEq.t in *. rewrite EC in A. destruct A as [A [B [B' C]]].
      rewrite EC' in B'.
      inversion B'. subst fp''. clear B'.
      eapply fp_inject_fp_match in FPINJ'; try (inv AGMU; eauto; fail).      
      destruct (testcond_for_condition cond); simpl in *.
      (* simple jcc *)
      do 2 econstructor; split.
      eapply exec_straight_trans. eexact A.
      apply exec_straight_one. simpl. rewrite B. eauto. auto. auto.
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      split. simpl; congruence.
      simpl. rewrite FP.fp_union_emp; auto.
      (* jcc ; jcc *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
        destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct (orb_false_elim _ _ H2); subst.
      do 2 econstructor; split.
      eapply exec_straight_trans. eexact A.
      eapply exec_straight_two. simpl. rewrite TC1. eauto. auto. 
      simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto. auto.
      split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
      split. simpl; congruence.
      simpl. rewrite FP.fp_union_emp; auto.
      (* jcc2 *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
        destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      exists (nextinstr rs'), fp'; split.
      rewrite <- (FP.fp_union_emp fp').
      eapply exec_straight_trans. eexact A.
      apply exec_straight_one. simpl.
      rewrite TC1; rewrite TC2.
      destruct b1. simpl in *. subst b2. auto. auto. auto.
      auto.
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      split. rewrite H2; congruence.
      auto.
      
    + (* Mjumptable *)
      assert (f0 = f) by congruence. subst f0.
      revert HSG HTG. inv AT. monadInv H6. 
      exploit functions_transl; eauto. intro FN.
      generalize (transf_function_no_overflow _ _ H5); intro NOOV.
      set (rs1 := rs0 #RAX <- Vundef #RDX <- Vundef).
      exploit (find_label_goto_label f tf lbl rs1); eauto. 
      intros [tc' [rs' [A [B C]]]].
      exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
      intros. rewrite HTG. right. exists 0%nat.
      do 3 eexists; split.
      apply plus_one. econstructor; eauto.
      eapply find_instr_tail; eauto.
      simpl. rewrite <- H9.  unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
      split. simpl. do 2 rewrite FP.fp_union_emp; auto.
      econstructor; eauto.
      Transparent destroyed_by_jumptable.
      apply agree_undef_regs with rs0; auto. 
      simpl; intros. destruct H8. rewrite C by auto with asmgen. unfold rs1; Simplifs.
      congruence.
      simpl. do 2 rewrite FP.fp_union_emp; auto.
      
    + (* dummy step *)
      right. exists 0%nat. rewrite FP.emp_union_fp.
      (*exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
      generalize EQ; intros EQ'. monadInv EQ'.
      destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); inv EQ1.
      monadInv EQ0. rewrite transl_code'_transl_code in EQ1.*)
      exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
      intros [m1' [C D]].

      exploit store_args_extends. exact D. exact H2. intros [Lm' [STOREARGS' EXTENDS']].
      rewrite HTG.
      do 2 eexists; exists Lm'. split.
      apply plus_one. simpl. econstructor; eauto.
      split. rewrite FP.emp_union_fp. unfold MemOpFP.alloc_fp.
      erewrite Mem.mext_next; eauto.
      eapply Injections.fp_match_union'; eapply fp_match_id; inv AGMU; auto.
      
      econstructor; eauto.
      constructor. constructor; simpl; trivial. discriminate.
      apply store_args_nextblock in H2. rewrite H2.
      erewrite Mem.nextblock_alloc; eauto. apply Ple_trans with (Mem.nextblock m); eauto with coqlib.
      apply store_args_nextblock in STOREARGS'. rewrite STOREARGS'.
      erewrite Mem.nextblock_alloc; eauto. apply Ple_trans with (Mem.nextblock Lm); eauto with coqlib.
      
      inv AGMU.
      eapply unchanged_on_unmapped_closed_preserved; eauto.
      svalid. svalid.
      apply Mem.unchanged_on_trans with m'. eapply Mem.alloc_unchanged_on. eauto. 
      eapply Mem.unchanged_on_implies. eapply store_args_unchanged_on; eauto.
      erewrite mu_shared_src; eauto. intros; intro; subst. apply Mem.fresh_block_alloc in H0. apply H0.
      unfold Mem.valid_block. apply Plt_Ple_trans with (Genv.genv_next sge); eauto with coqlib.
      apply Mem.unchanged_on_trans with m1'. eapply Mem.alloc_unchanged_on. eauto. 
      eapply Mem.unchanged_on_implies. eapply store_args_unchanged_on; eauto.
      erewrite mu_shared_tgt; eauto. intros; intro; subst. apply Mem.fresh_block_alloc in C. apply C.
      unfold Mem.valid_block. apply Plt_Ple_trans with (Genv.genv_next tge); eauto with coqlib.
      
      rewrite FP.emp_union_fp. unfold MemOpFP.alloc_fp.
      erewrite Mem.mext_next; eauto.
      eapply Injections.fp_match_union'; eapply fp_match_id; inv AGMU; auto.
      
    + (* Mcall *)
      assert (f0 = f) by congruence.  subst f0.
      revert HSG HTG. inv AT. 
      assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto.
      destruct ros as [rf|fid]; simpl in H; monadInv H6.
      ++ (* Indirect call *)
        assert (rs rf = Vptr f' Ptrofs.zero).
        destruct (rs rf); try discriminate.
        revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
        assert (rs0 x0 = Vptr f' Ptrofs.zero).
        exploit ireg_val; eauto. rewrite H6; intros LD; inv LD; auto.
        generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
        assert (TCA: transl_code_at_pc sge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
        econstructor; eauto.
        exploit return_address_offset_correct; eauto. intros; subst ra.
        rewrite HTG. right. exists 0%nat. eexists _,_,_. split.
        apply plus_one. eapply exec_step_internal. eauto.
        eapply functions_transl; eauto. eapply find_instr_tail; eauto.
        simpl. eauto. eauto.
        split. simpl. do 2 rewrite FP.fp_union_emp. auto.
        econstructor; eauto.
        econstructor; eauto.
        eapply agree_sp_def; eauto.
        simpl. eapply agree_exten; eauto. intros. Simplifs.
        Simplifs. rewrite <- H3. auto.
        do 2 rewrite FP.fp_union_emp. auto.
      ++ (* Direct call *)
        generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
        assert (TCA: transl_code_at_pc sge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
        econstructor; eauto.
        exploit return_address_offset_correct; eauto. intros; subst ra.
        right. rewrite HTG. exists 0%nat. eexists _,_,_. split.
        apply plus_one. eapply exec_step_internal. eauto.
        eapply functions_transl; eauto. eapply find_instr_tail; eauto.
        simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite <- HSG. rewrite H. eauto.
        simpl. eauto. repeat rewrite FP.fp_union_emp.
        split. auto.
        econstructor; eauto.
        econstructor; eauto.
        eapply agree_sp_def; eauto.
        simpl. eapply agree_exten; eauto. intros. Simplifs.
        Simplifs. rewrite <- H3. auto.

    + (* Call out *)
      assert (f0 = f) by congruence.  subst f0.
      revert HSG HTG. inv AT. 
      assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto.
      destruct ros as [rf|fid]; simpl in H; monadInv H8.
      ++ (* Indirect call *)
        assert (rs rf = Vptr f' Ptrofs.zero).
        destruct (rs rf); try discriminate.
        revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
        assert (rs0 x0 = Vptr f' Ptrofs.zero).
        exploit ireg_val; eauto. rewrite H8; intros LD; inv LD; auto.
        generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
        assert (TCA: transl_code_at_pc sge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
        econstructor; eauto.
        exploit return_address_offset_correct; eauto. intros; subst ra.

        exploit extcall_arguments_match.
        instantiate (1:=(rs0 # RA <- (Val.offset_ptr (rs0 PC) Ptrofs.one)) # PC <- (rs0 x0)).
        apply agree_set_other; auto. apply agree_set_other; eauto. eauto. eauto.
        exploit extcall_arguments_fp_match.
        instantiate (1:=(rs0 # RA <- (Val.offset_ptr (rs0 PC) Ptrofs.one)) # PC <- (rs0 x0)).
        apply agree_set_other; auto. apply agree_set_other; eauto. eauto. eauto.        
        intros ARGFP' [args' [ARGS' ARGREL]].
        
        rewrite HTG. right. exists 0%nat. eexists _,_,_. split.
        eapply plus_two. eapply exec_step_internal. eauto.
        eapply functions_transl; eauto. eapply find_instr_tail; eauto.
        simpl. eauto. simpl. eauto.
        eapply exec_step_to_external. eauto.
        apply ef_transl. rewrite <- HSG. eauto. eauto. eauto. rewrite FP.emp_union_fp; eauto.
        match goal with |- ?P /\ _ => assert P end.
        apply Injections.fp_match_union'; auto. apply fp_match_id; inv AGMU; auto.
        split. auto.
        econstructor; eauto.
        econstructor; eauto.
        eapply agree_sp_def; eauto.
        simpl. eapply agree_exten; eauto. intros. Simplifs.
        Simplifs. rewrite <- H5. auto.

      ++ (* Direct call *)
        generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
        assert (TCA: transl_code_at_pc sge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
        econstructor; eauto.
        exploit return_address_offset_correct; eauto. intros; subst ra.

        exploit extcall_arguments_match.
        instantiate (1:=(rs0 # RA <- (Val.offset_ptr (rs0 PC) Ptrofs.one)) # PC <- (Vptr f' Ptrofs.zero)).
        apply agree_set_other; auto. apply agree_set_other; eauto. eauto. eauto.
        exploit extcall_arguments_fp_match.
        instantiate (1:=(rs0 # RA <- (Val.offset_ptr (rs0 PC) Ptrofs.one)) # PC <- (Vptr f' Ptrofs.zero)).
        apply agree_set_other; auto. apply agree_set_other; eauto. eauto. eauto.        
        intros ARGFP' [args' [ARGS' ARGREL]].
        
        right. rewrite HTG. exists 0%nat. eexists _,_,_. split.
        eapply plus_two. eapply exec_step_internal. eauto.
        eapply functions_transl; eauto. eapply find_instr_tail; eauto.
        simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite <- HSG. rewrite H. eauto.
        simpl. eauto.
        eapply exec_step_to_external; eauto.
        Simplifs. apply ef_transl. rewrite <- HSG. auto. 
        rewrite FP.emp_union_fp. eauto.
        match goal with |- ?P /\ _ => assert P end.
        apply Injections.fp_match_union'; auto. apply fp_match_id; inv AGMU; auto.
        split. auto.
        econstructor; eauto.
        econstructor; eauto.
        eapply agree_sp_def; eauto.
        simpl. eapply agree_exten; eauto. intros. Simplifs.
        Simplifs. rewrite <- H5. auto.

    + (* Mtailcall *)
      assert (f0 = f) by congruence.  subst f0.
      revert HSG HTG. inv AT.
      assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto.
      rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
      exploit Mem.loadv_extends. eauto. eexact H1. auto. intros [parent' [A B]].
      exploit Mem.loadv_extends. eauto. eexact H3. auto. intros [ra' [C D]].
      exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
      exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
      exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]]. revert HSG HTG.
      destruct ros as [rf|fid]; simpl in H; monadInv H7.
    ++ (* Indirect call *)
      assert (rs rf = Vptr f' Ptrofs.zero).
      destruct (rs rf); try discriminate.
      revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
      assert (rs0 x0 = Vptr f' Ptrofs.zero).
      exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
      generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
      right. rewrite HTG. exists 0%nat. eexists _,_,_. split.
      eapply plus_left. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. simpl in A,C. unfold Mptr. destruct Archi.ptr64 eqn:Cont; inversion Cont; clear Cont.
      rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto. simpl. rewrite <- (sp_val _ _ _ AG). eauto.
      apply star_one. eapply exec_step_internal.
      transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H2. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. eauto. simpl. eauto. eauto.
      repeat rewrite FP.fp_union_emp.
      rewrite <- (sp_val _ _ _ AG). unfold load_stack_fp. unfold Mptr.
      destruct Archi.ptr64 eqn:Cont; inversion Cont; clear Cont. simpl. 
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'. auto.
      apply Injections.fp_match_union'.
      rewrite FP.union_comm_eq. apply Injections.fp_match_union'; apply fp_match_id; inv AGMU; auto.
      apply fp_match_id; inv AGMU; auto.
      split. auto.
      
      econstructor; eauto.
      apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
      eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
      Simplifs. rewrite Pregmap.gso; auto.
      generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
      apply Mem.nextblock_free in H5. rewrite H5. auto.
      apply Mem.nextblock_free in E. rewrite E. auto.

      inv AGMU. eapply free_inject_unmapped_closed_preserved; try exact E; eauto.
      svalid. svalid. reflexivity. omega. omega.
      
    ++ (* Direct call *)
      generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
      right. rewrite HTG. exists 0%nat. eexists _,_,_. split.
      eapply plus_left. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. replace (chunk_of_type Tint) with Mptr in * by (unfold Mptr; destruct Archi.ptr64 eqn:Cont; auto; inv Cont).
      rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
      simpl. rewrite <- (sp_val _ _ _ AG). erewrite (FP.union_comm_eq (FMemOpFP.loadv_fp _ _) _). eauto.
      apply star_one. eapply exec_step_internal.
      transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H2. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. eauto. simpl. eauto. rewrite FP.fp_union_emp. eauto.
      rewrite <- (sp_val _ _ _ AG). unfold load_stack_fp. unfold Mptr.
      destruct Archi.ptr64 eqn:Cont; inversion Cont; clear Cont. simpl.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'. auto.
      apply Injections.fp_match_union'.
      rewrite FP.union_comm_eq. apply Injections.fp_match_union'; apply fp_match_id; inv AGMU; auto.
      apply fp_match_id; inv AGMU; auto.
      split. auto.
      econstructor; eauto.
      apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
      eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
      rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite <- HSG, H. auto.
      apply Mem.nextblock_free in H5. rewrite H5. auto.
      apply Mem.nextblock_free in E. rewrite E. auto.
      
      inv AGMU. eapply free_inject_unmapped_closed_preserved; try exact E; eauto.
      svalid. svalid. reflexivity. omega. omega.

    + (* Mtailcall external *)
      assert (f0 = f) by congruence.  subst f0.
      revert HSG HTG. inv AT.
      assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto.
      rewrite (sp_val _ _ _ AG) in *. unfold load_stack, Mach.load_stack in *.
      exploit Mem.loadv_extends. eauto. eexact H1. auto. intros [parent' [A B]].
      exploit Mem.loadv_extends. eauto. eexact H3. auto. intros [ra' [C D]].
      exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
      exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
      exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]]. revert HSG HTG.
      destruct ros as [rf|fid]; simpl in H; monadInv H11.
    ++ (* Indirect call *)
      assert (rs rf = Vptr f' Ptrofs.zero).
      destruct (rs rf); try discriminate.
      revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
      assert (rs0 x0 = Vptr f' Ptrofs.zero).
      exploit ireg_val; eauto. rewrite H11; intros LD; inv LD; auto.
      generalize (code_tail_next_int _ _ _ _ NOOV H12). intro CT1.
      assert (AG':agree rs (parent_sp0 sp0 s)
                        (nextinstr (rs0 # RSP <- (parent_sp0 sp0 s)) # RA <- (parent_ra s)) # PC
                        <- (nextinstr (rs0 # RSP <- (parent_sp0 sp0 s)) # RA <- (parent_ra s) x0)).
      { apply agree_set_other; auto. apply agree_set_other; auto. apply agree_set_other; auto.
        eapply agree_change_sp; eauto. eapply parent_sp_def; eauto. }
      exploit extcall_arguments_match.
      exact AG'. exact F. eapply tailcall_possible_extcall_arguments; eauto. intros (args' & ARGS' & INJARGS).
      exploit extcall_arguments_fp_match.
      exact AG'. eapply tailcall_possible_extcall_arguments_fp; eauto. intro ARGSFP.
      
      right. rewrite HTG. exists 0%nat. eexists _,_,_. split.
      eapply plus_left. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. simpl in A,C. unfold Mptr. destruct Archi.ptr64 eqn:Cont; inversion Cont; clear Cont.
      rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto. simpl. rewrite <- (sp_val _ _ _ AG). eauto.
      eapply star_two. eapply exec_step_internal. 
      transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H2. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. eauto. simpl. eauto.
      eapply exec_step_to_external.
      transitivity (rs0 x0);[|eauto]. rewrite Pregmap.gss. Simplifs. rewrite Pregmap.gso. auto.
      generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
      eapply ef_transl. rewrite <-HSG. eauto.
      eauto. eauto. rewrite FP.emp_union_fp. eauto. eauto.
      
      simpl. rewrite <- (sp_val _ _ _ AG). unfold load_stack_fp. unfold Mptr.
      destruct Archi.ptr64 eqn:Cont; inversion Cont; clear Cont. simpl. 
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'. auto.
      apply Injections.fp_match_union'. apply Injections.fp_match_union'. 
      rewrite FP.union_comm_eq. apply Injections.fp_match_union'; apply fp_match_id; inv AGMU; auto.
      apply fp_match_id; inv AGMU; auto.       apply fp_match_id; inv AGMU; auto.
      split. auto.
      
      econstructor; eauto.
      Simplifs. rewrite Pregmap.gso; auto.
      generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
      apply Mem.nextblock_free in H5. rewrite H5. auto.
      apply Mem.nextblock_free in E. rewrite E. auto.

      inv AGMU. eapply free_inject_unmapped_closed_preserved; try exact E; eauto.
      svalid. svalid. reflexivity. omega. omega.
      
    ++ (* Direct call *)
      generalize (code_tail_next_int _ _ _ _ NOOV H12). intro CT1.
      assert (AG':agree rs (parent_sp0 sp0 s)
        (nextinstr (rs0 # RSP <- (parent_sp0 sp0 s)) # RA <- (parent_ra s)) 
        # PC <- (Genv.symbol_address tge fid Ptrofs.zero)).
      { apply agree_set_other; auto. apply agree_set_other; auto. apply agree_set_other; auto.
        eapply agree_change_sp; eauto. eapply parent_sp_def; eauto. }
      exploit extcall_arguments_match.
      exact AG'. exact F. eapply tailcall_possible_extcall_arguments; eauto. intros (args' & ARGS' & INJARGS).
      exploit extcall_arguments_fp_match.
      exact AG'. eapply tailcall_possible_extcall_arguments_fp; eauto. intro ARGSFP.
      right. rewrite HTG. exists 0%nat. eexists _,_,_. split.
      eapply plus_left. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. replace (chunk_of_type Tint) with Mptr in * by (unfold Mptr; destruct Archi.ptr64 eqn:Cont; auto; inv Cont).
      rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
      simpl. rewrite <- (sp_val _ _ _ AG). erewrite (FP.union_comm_eq (FMemOpFP.loadv_fp _ _) _). eauto.
      eapply star_two. eapply exec_step_internal.
      transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H2. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. eauto. simpl. eauto.
      eapply exec_step_to_external.
      transitivity (Genv.symbol_address tge fid Ptrofs.zero); auto.
      unfold Genv.symbol_address. rewrite symbols_preserved. rewrite <- HSG, H. eauto.
      eapply ef_transl. rewrite <- HSG. eauto.
      eauto. eauto. rewrite FP.emp_union_fp. eauto. eauto.
      rewrite <- (sp_val _ _ _ AG). unfold load_stack_fp. unfold Mptr.
      destruct Archi.ptr64 eqn:Cont; inversion Cont; clear Cont. simpl.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'. auto.
      apply Injections.fp_match_union'. apply Injections.fp_match_union'.
      rewrite FP.union_comm_eq. apply Injections.fp_match_union'; apply fp_match_id; inv AGMU; auto.
      apply fp_match_id; inv AGMU; auto. apply fp_match_id; inv AGMU; auto.
      split. auto.
      econstructor; eauto.
      Simplifs. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite <- HSG, H. auto.
      apply Mem.nextblock_free in H5. rewrite H5. auto.
      apply Mem.nextblock_free in E. rewrite E. auto.

      inv AGMU. eapply free_inject_unmapped_closed_preserved; try exact E; eauto.
      svalid. svalid. reflexivity. omega. omega.

    + (* Mbuiltin *)
      revert HSG HTG. inv AT. monadInv H6.
      exploit functions_transl; eauto. intro FN.
      generalize (transf_function_no_overflow _ _ H5); intro NOOV.
      exploit builtin_args_match; eauto. intros [vargs' [P Q]].
      exploit builtin_args_match_fp; eauto. intros P'.
      exploit external_call_mem_extends; eauto.
      intros [vres' [Lm' [A [B _]]]].
      exploit helpers.i64ext_effects; try exact A; eauto. intros [X _]; subst Lm'.
      right. rewrite HSG in A,P,P'. rewrite HTG. do 4 eexists. split. apply plus_one. 
      eapply exec_step_builtin; eauto. eapply find_instr_tail; eauto.
      inv AG; auto.
      erewrite <- sp_val by eauto. eapply eval_builtin_args_preserved with (ge1 := sge); eauto. exact symbols_preserved.
      erewrite <- sp_val by eauto. eapply MemOpFP.eval_builtin_args_fp_preserved with (ge1 := sge); eauto.
      exact symbols_preserved. 
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      match goal with |- ?P /\ _ => assert P end. apply Injections.fp_match_union'; auto. apply fp_match_id; inv AGMU; auto.
      split. auto. econstructor; eauto.
      instantiate (2 := tf); instantiate (1 := x).
      unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
      rewrite undef_regs_other. rewrite set_res_other. rewrite undef_regs_other_2.
      rewrite <- H3. simpl. econstructor; eauto.
      eapply code_tail_next_int; eauto.
      rewrite preg_notin_charact. intros. auto with asmgen.
      auto with asmgen.
      simpl; intros. intuition congruence.
      apply agree_nextinstr_nf. eapply agree_set_res; auto.
      eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
      congruence.
      
    + (* Mreturn *)
      assert (f0 = f) by congruence. subst f0.
      revert HSG HTG. inv AT.
      assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto.
      rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
      exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]].
      exploit lessdef_parent_sp; eauto. intro. subst parent'. clear B.
      exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [ra' [C D]].
      exploit lessdef_parent_ra; eauto. intro. subst ra'. clear D.
      exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
      monadInv H6.
      exploit code_tail_next_int; eauto. intro CT1.
      right. rewrite HTG. exists 1%nat. eexists _,_,_. split.
      eapply plus_left. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      replace (chunk_of_type Tptr) with Mptr in * by (unfold Mptr; destruct Archi.ptr64 eqn:Contra; auto; inv Contra).
      simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
      simpl. rewrite <- (sp_val _ _ _ AG). eauto.
      apply star_one. eapply exec_step_internal.
      transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H1. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. eauto. simpl. eauto. rewrite FP.fp_union_emp. eauto.
      rewrite <- (sp_val _ _ _ AG). unfold load_stack_fp. unfold Mptr.
      destruct Archi.ptr64 eqn:Cont; inversion Cont; clear Cont. simpl.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'. auto.
      apply Injections.fp_match_union'. 
      rewrite FP.union_comm_eq. apply Injections.fp_match_union'; apply fp_match_id; inv AGMU; auto.
      apply fp_match_id; inv AGMU; auto. 
      split. auto.
      constructor; auto.
      apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
      eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
      apply Mem.nextblock_free in H4. rewrite H4. auto.
      apply Mem.nextblock_free in E. rewrite E. auto.

      inv AGMU. eapply free_inject_unmapped_closed_preserved; try exact E; eauto.
      svalid. svalid. reflexivity. omega. omega.
      
    + (* internal function *)
      exploit functions_translated. rewrite <-HSG, Genv.find_funct_find_funct_ptr. eauto.
      intros [tf [A B]]. revert HSG HTG. monadInv B.
      generalize EQ; intros EQ'. monadInv EQ'.
      destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); inv EQ1.
      monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
      unfold store_stack, Mach.store_stack in *.
      exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
      intros [m1' [C D]].
      exploit Mem.storev_extends. eexact D. eexact H2. eauto. eauto.
      intros [m2' [F G]].
      exploit Mem.storev_extends. eexact G. eexact H4. eauto. eauto.
      intros [m3' [P Q]].
      right; exists 0%nat. eexists _,_,_; split.
      apply plus_one. econstructor; eauto.
      rewrite Genv.find_funct_find_funct_ptr in A. rewrite HTG. eauto.
      simpl. rewrite Ptrofs.unsigned_zero. simpl. eauto.
      simpl. rewrite C. simpl in F, P. 
      replace (chunk_of_type Tptr) with Mptr in F, P by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
      rewrite (sp_val _ _ _ AG) in F. rewrite F.
      rewrite ATLR. rewrite P. eauto.
      simpl. rewrite C.
      unfold store_stack_fp. simpl.
      replace (chunk_of_type Tptr) with Mptr by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'. auto.
      rewrite <- FP.fp_union_assoc. apply Injections.fp_match_union'.
      unfold MemOpFP.alloc_fp. erewrite Mem.mext_next; eauto. apply fp_match_id; inv AGMU; auto.
      apply Injections.fp_match_union'; apply fp_match_id; inv AGMU; auto.
      split; auto.
      econstructor; eauto.
      rewrite <- HSG. eauto.
      unfold nextinstr. rewrite Pregmap.gss. repeat rewrite Pregmap.gso; auto with asmgen.
      rewrite ATPC. simpl. constructor; eauto. rewrite <- HSG. eauto.
      unfold fn_code. eapply code_tail_next_int. simpl in g. omega.
      constructor.
      apply agree_nextinstr. eapply agree_change_sp; eauto.
      Transparent destroyed_at_function_entry.
      apply agree_undef_regs with rs0; eauto.
      simpl; intros. apply Pregmap.gso; auto with asmgen. tauto.
      congruence.
      intros. Simplifs. eapply agree_sp; eauto.

      erewrite Mem.nextblock_store; simpl in H4; try exact H4.
      erewrite Mem.nextblock_store; simpl in H2; try exact H2.
      erewrite Mem.nextblock_alloc; try exact H0. apply Ple_trans with (Mem.nextblock m); eauto with coqlib.
      erewrite Mem.nextblock_store; simpl in P; try exact P.
      erewrite Mem.nextblock_store; simpl in F; try exact F.
      erewrite Mem.nextblock_alloc; try exact C. apply Ple_trans with (Mem.nextblock Lm); eauto with coqlib.

      inv AGMU. simpl in H2, H4, F, P.
      assert (~ Injections.SharedSrc mu stk).
      { erewrite mu_shared_src; eauto. intros; intro; subst. apply Mem.fresh_block_alloc in H0. apply H0.
        unfold Mem.valid_block. eapply Plt_Ple_trans; eauto. }
      assert (~ Injections.SharedTgt mu stk).
      { erewrite mu_shared_tgt; eauto. intros; intro; subst. apply Mem.fresh_block_alloc in C. apply C.
        unfold Mem.valid_block. eapply Plt_Ple_trans; eauto. }
      eapply unchanged_on_unmapped_closed_preserved; eauto.
      svalid. svalid.
      apply Mem.unchanged_on_trans with m1. eapply Mem.alloc_unchanged_on. eauto.
      apply Mem.unchanged_on_trans with m2; eapply Mem.store_unchanged_on; eauto.
      apply Mem.unchanged_on_trans with m1'. eapply Mem.alloc_unchanged_on. eauto.
      apply Mem.unchanged_on_trans with m2'; eapply Mem.store_unchanged_on; eauto. 

    + (* i64ext *)
      exploit functions_translated. instantiate (2:= Vptr fb Ptrofs.zero). simpl.
      destruct Ptrofs.eq_dec; [|congruence]. rewrite <- HSG; eauto. intros [tf [A B]].
      simpl in B. revert HSG HTG. inv B. 
      exploit external_call_mem_extends; eauto.
      intros [res' [m2' [P [Q _]]]].
      exploit helpers.i64ext_effects; eauto. intros [X _]; subst m2'.
      right. rewrite HTG. rewrite HSG in P. do 4 eexists. split.
      apply plus_one. eapply exec_step_i64ext; eauto; try rewrite HTG; eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      repeat rewrite FP.fp_union_emp. split; auto.
      econstructor; eauto.
      unfold loc_external_result.
      apply agree_set_other; auto. apply agree_set_pair; auto.
      
    + (* return *)
      inv STACKS. simpl in *.
      left. exists 0%nat. split. unfold Nat.lt. omega.
      econstructor; eauto. rewrite ATPC; eauto. congruence.
      rewrite FP.fp_union_emp; auto.
      
  - (* at external *)
    intros. exists 0%nat. exists argSrc.
    simpl in *. unfold at_external, Mach_local.at_external in *.
    destruct Hcore; try discriminate.
    destruct f0; try discriminate.
    destruct (invert_symbol_from_string sG name) eqn:FINDFID; try discriminate.
    eapply match_genvs_invert_symbol_from_string_preserved in FINDFID.
    inv H. rewrite FINDFID.
    destruct peq; try discriminate. destruct peq; try discriminate. simpl in *.
    inv H0. 
    split.
    f_equal. f_equal.
    { generalize ARGS H2; clear. revert args'. induction argSrc; simpl; intros.
      inv ARGS; auto. inv H2. inv ARGS. f_equal.
      destruct a; simpl in H1; try contradiction; inv H2; auto. auto. }
    split.
    { generalize H2 AGMU. clear.
      clear. induction argSrc; constructor.
      destruct a; econstructor. inv H2. simpl in H1. eapply Bset.inj_dom in H1. destruct H1.
      unfold Bset.inj_to_meminj. rewrite H. f_equal. f_equal. inv AGMU. exploit proper_mu_inject_incr.
      unfold Bset.inj_to_meminj. rewrite H. eauto. intro. inv H0; auto.
      inv AGMU. eauto. rewrite Ptrofs.add_zero. auto.
      inv H2. apply IHargSrc; auto. }
    split.
    { inv AGMU. eapply unmapped_closed_reach_closed_preserved_by_extends; eauto.
      svalid. svalid. }
    split. auto.
    split.
    { unfold LDefs.Inv. (** TODO: Mem.extends' -> Mem.inject' *)
      inv AGMU. eapply extends_reach_closed_implies_inject; eauto.
      svalid. svalid.
    }
    constructor; auto. apply fp_match_id; inv AGMU; auto.
    destruct GE_INIT. destruct TGE_INIT. rewrite <-e, <-e0.
    eapply match_cu_match_genv; eauto.
    { clear. intros. inv H. destruct f1; monadInv H0; auto. auto. }

  - (* after external *)
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MATCH GRES AFTEXT ORESREL.
    simpl in *. unfold Mach_local.after_external, after_external in *.
    destruct Hcore; try discriminate.
    destruct f; try discriminate.
    inv MATCH.
    assert (Hcore' =
            match oresSrc with
            | Some v => (Core_Returnstate stack (Mach.set_pair (loc_result sg) v rs) (mk_load_frame sp0 args0 tyl0 sigres0))
            | None => (Core_Returnstate stack (Mach.set_pair (loc_result sg) Vundef rs) (mk_load_frame sp0 args0 tyl0 sigres0))
            end).
    { destruct oresSrc; destruct (sig_res sg); inv AFTEXT; auto.
      destruct val_has_type_func; inv H0; auto. }
    exists (match oresTgt with
       | Some v => Core_State (set_pair (loc_external_result sg) v rs0) #PC <- (rs0 RA)
                             (ASM_local.mk_load_frame sp0 sigres0)
       | None => Core_State (set_pair (loc_external_result sg) Vundef rs0) #PC <- (rs0 RA)
                           (ASM_local.mk_load_frame sp0 sigres0)
       end).
    split.
    destruct oresSrc eqn:RES, oresTgt eqn:RES', (sig_res sg) eqn:SG; try discriminate; try contradiction; auto.
    destruct v,t; inv ORESREL; try discriminate; try contradiction; simpl in *; eauto.

    intros. exists 1%nat.
    assert (Mem.extends Hm' Lm').
    { inv AGMU; eapply extends_rely_extends; eauto. }
    assert (unmapped_closed mu Hm' Lm').
    { eapply reach_closed_unmapped_closed. inv H0. inv H3. auto. }
    destruct oresSrc, oresTgt; try contradiction; rewrite H.
    econstructor; eauto.
    apply agree_set_other; auto. apply agree_set_pair; auto. inv ORESREL; auto.
    inv AGMU. apply proper_mu_inject_incr in H3. inv H3. rewrite Ptrofs.add_zero. auto.
    inv H0. inv H3. inv H. apply Ple_trans with (Mem.nextblock Hm); auto.
    inv H0. inv H4. inv H. apply Ple_trans with (Mem.nextblock Lm); auto.    
    econstructor; eauto.
    apply agree_set_other; auto. apply agree_set_pair; auto. 
    inv H0. inv H3. inv H. apply Ple_trans with (Mem.nextblock Hm); auto.
    inv H0. inv H4. inv H. apply Ple_trans with (Mem.nextblock Lm); auto.

  - (* halted *)
    intros. simpl in *. unfold Mach_local.halted, halted in *.
    destruct Hcore; try discriminate.
    destruct stack; try discriminate.
    destruct loader; try discriminate; simpl in *.
    inv H0. inv H. simpl in ATPC. rewrite ATPC. unfold Vnullptr, Vzero.
    destruct Archi.ptr64 eqn:ARCHI; [inv ARCHI|]. simpl.
    assert (LDefs.Inv mu Hm Lm).
    { inv AGMU. eapply extends_reach_closed_implies_inject; eauto.
      svalid. svalid. }
    assert (reach_closed Lm (Injections.SharedTgt mu)).
    { eapply unmapped_closed_reach_closed_preserved_by_injection'; eauto.
      inv AGMU; auto. }
    
    destruct loc_result eqn:RESLOC; (eexists; split; [eauto|split; eauto]).
    
    generalize (agree_mregs _ _ _ AG r); intro.
    destruct (rs r) eqn:VAL; inv H3; try constructor; try contradiction.
    econstructor. simpl in H2. eapply Bset.inj_dom in H2. destruct H2.
    inv AGMU. exploit proper_mu_inject_incr. 1,2: unfold Bset.inj_to_meminj. rewrite H2. eauto.
    intro. rewrite H2. inv H3; eauto.
    inv AGMU; eauto.
    rewrite Ptrofs.add_zero; auto.

    generalize (agree_mregs _ _ _ AG rhi) (agree_mregs _ _ _ AG rlo). intros.
    destruct (rs rhi) eqn:VHI, (rs rlo) eqn:VLO; try contradiction.
    inv H3; inv H4. constructor.
Qed.

End PRESERVATION.


Theorem transf_local_ldsim:
  forall scu tcu,
    asmgen.transf_program scu = OK tcu ->
    forall sge sG tge tG,
      init_genv_local (Mach_IS return_address_offset) scu sge sG ->
      init_genv_local Asm_IS tcu tge tG ->
      Genv.genv_next sge = Genv.genv_next tge ->
      local_ldsim sG tG sge tge.
Proof.
  intros. eapply TRANSF_local_ldsim; eauto.
  apply transf_program_match. auto.
Qed.