From mathcomp.ssreflect Require Import fintype ssrnat.            
Require Import Coqlib Maps Axioms.  
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
 
Require Import Asm. 

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory TSOMem. 
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe. 
 
Require CminorLang. 
Require SpecLang. 
Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.

Require Import Coq.Lists.Streams.

Require Import RGRels.
Require Import LibTactics.

Require Import code.
Require Import ObjectSim.
Require Import InvRG.

(*+ Some Tactics +*)
Ltac ptr_elim :=
  match goal with
  | H1 : ?rs ?PC = Vptr _ _,
         H1' : ?rs ?PC = Vptr _ _,
               H2 : Genv.find_funct_ptr _ _ = Some _,
                    H2' : Genv.find_funct_ptr _ _ = Some _,
                          H3 : find_instr _ _ = Some _,
                               H3' : find_instr _ _ = Some _ |- _ =>
    rewrite H1 in H1'; inversion H1'; subst;
    rewrite H2 in H2'; inversion H2'; subst;
    rewrite H3 in H3'; inversion H3'; subst
  end.

Ltac external_call_elim :=
  match goal with
  | H1 : ?rs ?PC = Vptr _ _,
         H1' : ?rs ?PC = Vptr _ _,
               H2 : Genv.find_funct_ptr _ _ = Some _,
                    H2' : Genv.find_funct_ptr _ _ = Some (External _) |- _ =>
    rewrite H1 in H1'; inversion H1'; subst;
    rewrite H2 in H2'; inversion H2'; subst
  end.

Ltac split_and H :=
  match type of H  with
  | _ /\ _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    split_and H1; split_and H2
  | exists _, _ =>
    let t := fresh in
    let H' := fresh in
    destruct H as [t H'];
    split_and H'
  | _ => idtac
  end.

Ltac solve_ptr_ofs_range :=
  match goal with
  | |- context [Ptrofs.max_unsigned] =>
    unfold Ptrofs.max_unsigned;
    unfold Ptrofs.modulus;
    unfold Ptrofs.wordsize;
    unfold Wordsize_Ptrofs.wordsize;
    destruct Archi.ptr64 eqn:?; tryfalse;
    simpl; omega
  end.

Ltac clear_trivial_eq :=
  match goal with
  | H : ?A = ?A |- _ =>
    clear H; clear_trivial_eq
  | |- _ => idtac
  end.

Ltac elim_next_intr :=
  match goal with
  | H : ?rs PC = Vptr _ _ |- nextinstr_nf _ _ = Vptr _ _ =>
    unfold nextinstr_nf; unfold nextinstr; simpl;
    try rewrite Pregmap.gss; repeat (rewrite Pregmap.gso; try (intro; tryfalse)) ;
    try rewrite H; eauto
  end.

Ltac elim_next_intr' :=
  match goal with
  | H : ?rs PC = Vptr _ _ |- nextinstr _ _ = Vptr _ _ =>
    unfold nextinstr; simpl;
    try rewrite Pregmap.gss; repeat (rewrite Pregmap.gso; try (intro; tryfalse)) ;
    try rewrite H; eauto
  end.

Ltac find_label :=
  match goal with
  | H : context [peq ?A ?A] |- _ =>
    destruct (peq A A) eqn : Ht; tryfalse
  | H : context [peq ?A ?B] |- _ =>
    let Ht := fresh in
    destruct (peq A B) eqn : Ht; [tryfalse | find_label]
  | _ => idtac
  end.

Ltac trivial_inversion :=
  match goal with
  | H : ?A _ = ?A _ |- _ =>
    inversion H; subst; trivial_inversion
  | H : ?A _ _ = ?A _ _ |- _ =>
    inversion H; subst; trivial_inversion
  | H : ?A _ _ _ = ?A _ _ _ |- _ =>
    inversion H; subst; trivial_inversion
  | H : ?A _ _ _ _ = ?A _ _ _ _ |- _ =>
    inversion H; subst; trivial_inversion
  | H : ?A _ _ _ _ _ = ?A _ _ _ _ _ |- _ =>
    inversion H; subst; trivial_inversion
  | H : ?A _ _ _ _ _ _ = ?A _ _ _ _ _ _ |- _ =>
    inversion H; subst; trivial_inversion
  | _ => idtac
  end.

Ltac ret_zero_ptr_false :=
  match goal with
  | H1 : ?rs PC = Vptr _ _,
         H2 : ?rs PC = Vzero |- _ =>
    rewrite H1 in H2; inversion H2; tryfalse; ret_zero_ptr_false
  end.

Ltac elim_ZMap :=
  match goal with
  | |- context[ZMap.get ?p (ZMap.set ?p _ _)] =>
    rewrite ZMap.gss; eauto
  | |- context[ZMap.get ?p1 (ZMap.set ?p2 _ _)] =>
    rewrite ZMap.gso; try solve [intro; tryfalse]; elim_ZMap
  end.

Ltac exec_instr_tso :=
  match goal with
  | H : exec_instr_TSO _ _ _ _ _ = _ |- _ =>
    simpl in H; inversion H; subst; clear_trivial_eq
  end.

Ltac Pregmap_elim :=
  match goal with
  | |- context [_ # ?i <- _ ?i] =>
    rewrite Pregmap.gss; Pregmap_elim
  | |- context [_ # ?j <- _ ?i] =>
    rewrite Pregmap.gso; [Pregmap_elim | intro; tryfalse]
  | _ => idtac
  end.

Ltac trivial_not_abort :=
  econstructor; eauto; econstructor; eauto; simpl; eauto.

Ltac spec_p_exec :=
  eapply InteractionSemantics.star_step; eauto;
  [
    try econstructor; eauto;
    try econstructor; eauto;
    try econstructor; eauto | ].