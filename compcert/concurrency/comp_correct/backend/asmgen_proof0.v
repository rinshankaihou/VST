(* Extended the original CompCert's correctness proof for supporting concurrency. *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for Asm generation: machine-independent framework *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.

Require Import Mach_local ASM_local MemOpFP asmgen Asmgenproof0.

(** * Processor registers and register states *)

Hint Extern 2 (_ <> _) => congruence: asmgen.

Hint Resolve preg_of_not_SP preg_of_not_PC: asmgen.

(** * Agreement between Mach registers and processor registers *)

(** Preservation of register agreement under various assignments. *)

(** Connection between Mach and Asm calling conventions for external
    functions.  *)

Lemma extcall_arg_fp_match:
  forall ms sp rs l fp,
  agree ms sp rs ->
  Mach_local.extcall_arg_fp sp l fp ->
  ASM_local.extcall_arg_fp rs l fp.
Proof.
  intros. inv H0. constructor.
  inv H. econstructor; eauto.
Qed.

Lemma extcall_arg_pair_fp_match:
  forall ms sp rs p fp,
  agree ms sp rs ->
  Mach_local.extcall_arg_pair_fp sp p fp ->
  ASM_local.extcall_arg_pair_fp rs p fp.
Proof.
  intros. inv H0.
  constructor. eapply extcall_arg_fp_match; eauto.
  econstructor; eauto; eapply extcall_arg_fp_match; eauto.
Qed.

Lemma extcall_args_fp_match:
  forall ms sp rs, agree ms sp rs -> 
              forall ll fp,
                Mach_local.load_arguments_fp sp ll fp ->
                load_arguments_fp rs ll fp.
Proof.
  induction 2. constructor.
  subst. econstructor; eauto.
  eapply extcall_arg_pair_fp_match; eauto.
Qed.

Lemma extcall_arguments_fp_match:
  forall ms sp rs sg fp,
  agree ms sp rs -> 
  Mach_local.extcall_arguments_fp sp sg fp ->
  ASM_local.extcall_arguments_fp rs sg fp.
Proof.
  unfold Mach_local.extcall_arguments_fp, ASM_local.extcall_arguments_fp; intros.
  eapply extcall_args_fp_match; eauto.
Qed.

(** Translation of arguments and results to builtins. *)
Remark builtin_arg_match_fp:
  forall ge (rs: regset) sp a fp,
  eval_builtin_arg_fp ge (fun r => rs (preg_of r)) sp a fp ->
  eval_builtin_arg_fp ge rs sp (map_builtin_arg preg_of a) fp.
Proof.
  induction 1; simpl; econstructor; eauto.
Qed.

Lemma builtin_args_match_fp:
  forall ge ms sp rs, agree ms sp rs -> 
  forall al fp, eval_builtin_args_fp ge ms sp al fp ->
           eval_builtin_args_fp ge rs sp (map (map_builtin_arg preg_of) al) fp.
Proof.
  induction 2; intros; simpl; econstructor; eauto.
  apply builtin_arg_match_fp. eapply eval_builtin_arg_fp_lessdef; eauto.
Qed.

(** * Correspondence between Mach code and Asm code *)

Lemma find_instr_in:
  forall c pos i,
  find_instr pos c = Some i -> In i c.
Proof.
  induction c; simpl. intros; discriminate.
  intros until i. case (zeq pos 0); intros.
  left; congruence. right; eauto.
Qed.

(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

Inductive code_tail: Z -> code -> code -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos i c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + 1) (i :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1. omega. omega.
Qed.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. omegaContradiction.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by omega.
  eauto.
Qed.

Remark code_tail_bounds_1:
  forall fn ofs c,
  code_tail ofs fn c -> 0 <= ofs <= list_length_z fn.
Proof.
  induction 1; intros; simpl.
  generalize (list_length_z_pos c). omega.
  rewrite list_length_z_cons. omega.
Qed.

Remark code_tail_bounds_2:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < list_length_z fn.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl.
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). omega.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). omega.
  eauto.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> code_tail (ofs + 1) fn c').
  induction 1; intros.
  subst c. constructor. constructor.
  constructor. eauto.
  eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  list_length_z fn <= Ptrofs.max_unsigned ->
  code_tail (Ptrofs.unsigned ofs) fn (i :: c) ->
  code_tail (Ptrofs.unsigned (Ptrofs.add ofs Ptrofs.one)) fn c.
Proof.
  intros. rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_one.
  rewrite Ptrofs.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds_2 _ _ _ _ H0). omega.
Qed.

(** [transl_code_at_pc pc fb f c ep tf tc] holds if the code pointer [pc] points
  within the Asm code generated by translating Mach function [f],
  and [tc] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc (ge: Mach.genv):
    val -> block -> Mach.function -> Mach.code -> bool -> ASM_local.function -> ASM_local.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c ep tf tc,
    Genv.find_funct_ptr ge b = Some(Internal f) ->
    transf_function f = Errors.OK tf ->
    transl_code f c ep = OK tc ->
    code_tail (Ptrofs.unsigned ofs) (fn_code tf) tc ->
    transl_code_at_pc ge (Vptr b ofs) b f c ep tf tc.

(** Equivalence between [transl_code] and [transl_code']. *)

Local Open Scope error_monad_scope.

Lemma transl_code_rec_transl_code:
  forall f il ep k,
  transl_code_rec f il ep k = (do c <- transl_code f il ep; k c).
Proof.
  induction il; simpl; intros.
  auto.
  rewrite IHil.
  destruct (transl_code f il (it1_is_parent ep a)); simpl; auto.
Qed.

Lemma transl_code'_transl_code:
  forall f il ep,
  transl_code' f il ep = transl_code f il ep.
Proof.
  intros. unfold transl_code'. rewrite transl_code_rec_transl_code.
  destruct (transl_code f il ep); auto.
Qed.

(** Predictor for return addresses in generated Asm code.

  The [return_address_offset] predicate defined here is used in the
  semantics for Mach to determine the return addresses that are
  stored in activation records. *)

(** Consider a Mach function [f] and a sequence [c] of Mach instructions
  representing the Mach code that remains to be executed after a
  function call returns.  The predicate [return_address_offset f c ofs]
  holds if [ofs] is the integer offset of the PPC instruction
  following the call in the Asm code obtained by translating the
  code of [f]. Graphically:
<<
     Mach function f    |--------- Mcall ---------|
         Mach code c    |                |--------|
                        |                 \        \
                        |                  \        \
                        |                   \        \
     Asm code           |                    |--------|
     Asm function       |------------- Pcall ---------|

                        <-------- ofs ------->
>>
*)

Definition return_address_offset (f: Mach.function) (c: Mach.code) (ofs: ptrofs) : Prop :=
  forall tf tc,
  transf_function f = OK tf ->
  transl_code f c false = OK tc ->
  code_tail (Ptrofs.unsigned ofs) (fn_code tf) tc.

(** We now show that such an offset always exists if the Mach code [c]
  is a suffix of [f.(fn_code)].  This holds because the translation
  from Mach to PPC is compositional: each Mach instruction becomes
  zero, one or several PPC instructions, but the order of instructions
  is preserved. *)

Lemma is_tail_code_tail:
  forall c1 c2, is_tail c1 c2 -> exists ofs, code_tail ofs c2 c1.
Proof.
  induction 1. exists 0; constructor.
  destruct IHis_tail as [ofs CT]. exists (ofs + 1); constructor; auto.
Qed.

Section RETADDR_EXISTS.

Hypothesis transl_instr_tail:
  forall f i ep k c, transl_instr f i ep k = OK c -> is_tail k c.
Hypothesis transf_function_inv:
  forall f tf, transf_function f = OK tf ->
  exists tc, exists ep, transl_code f (Mach.fn_code f) ep = OK tc /\ is_tail tc (fn_code tf).
Hypothesis transf_function_len:
  forall f tf, transf_function f = OK tf -> list_length_z (fn_code tf) <= Ptrofs.max_unsigned.

Lemma transl_code_tail:
  forall f c1 c2, is_tail c1 c2 ->
  forall tc2 ep2, transl_code f c2 ep2 = OK tc2 ->
  exists tc1, exists ep1, transl_code f c1 ep1 = OK tc1 /\ is_tail tc1 tc2.
Proof.
  induction 1; simpl; intros.
  exists tc2; exists ep2; split; auto with coqlib.
  monadInv H0. exploit IHis_tail; eauto. intros [tc1 [ep1 [A B]]].
  exists tc1; exists ep1; split. auto.
  apply is_tail_trans with x. auto. eapply transl_instr_tail; eauto.
Qed.

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. destruct (transf_function f) as [tf|] eqn:TF.
+ exploit transf_function_inv; eauto. intros (tc1 & ep1 & TR1 & TL1).
  exploit transl_code_tail; eauto. intros (tc2 & ep2 & TR2 & TL2).
Opaque transl_instr.
  monadInv TR2.
  assert (TL3: is_tail x (fn_code tf)).
  { apply is_tail_trans with tc1; auto.
    apply is_tail_trans with tc2; auto.
    eapply transl_instr_tail; eauto. }
  exploit is_tail_code_tail. eexact TL3. intros [ofs CT].
  exists (Ptrofs.repr ofs). red; intros.
  rewrite Ptrofs.unsigned_repr. congruence.
  exploit code_tail_bounds_1; eauto.
  apply transf_function_len in TF. omega.
+ exists Ptrofs.zero; red; intros. congruence.
Qed.

End RETADDR_EXISTS.

Remark code_tail_no_bigger:
  forall pos c1 c2, code_tail pos c1 c2 -> (length c2 <= length c1)%nat.
Proof.
  induction 1; simpl; omega.
Qed.

Remark code_tail_unique:
  forall fn c pos pos',
  code_tail pos fn c -> code_tail pos' fn c -> pos = pos'.
Proof.
  induction fn; intros until pos'; intros ITA CT; inv ITA; inv CT; auto.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  f_equal. eauto.
Qed.

Lemma return_address_offset_correct:
  forall ge b ofs fb f c tf tc ofs',
  transl_code_at_pc ge (Vptr b ofs) fb f c false tf tc ->
  return_address_offset f c ofs' ->
  ofs' = ofs.
Proof.
  intros. inv H. red in H0.
  exploit code_tail_unique. eexact H12. eapply H0; eauto. intro.
  rewrite <- (Ptrofs.repr_unsigned ofs).
  rewrite <- (Ptrofs.repr_unsigned ofs').
  congruence.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some c' else find_label lbl c'
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos'
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + list_length_z c.
Proof.
  induction c.
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (is_label lbl a).
  intro EQ; injection EQ; intro; subst c'.
  exists (pos + 1). split. auto. split.
  replace (pos + 1 - pos) with (0 + 1) by omega. constructor. constructor.
  rewrite list_length_z_cons. generalize (list_length_z_pos c). omega.
  intros. generalize (IHc (pos + 1) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by omega.
  constructor. auto.
  rewrite list_length_z_cons. omega.
Qed.

(** Helper lemmas to reason about
- the "code is tail of" property
- correct translation of labels. *)

Definition tail_nolabel (k c: code) : Prop :=
  is_tail k c /\ forall lbl, find_label lbl c = find_label lbl k.

Lemma tail_nolabel_refl:
  forall c, tail_nolabel c c.
Proof.
  intros; split. apply is_tail_refl. auto.
Qed.

Lemma tail_nolabel_trans:
  forall c1 c2 c3, tail_nolabel c2 c3 -> tail_nolabel c1 c2 -> tail_nolabel c1 c3.
Proof.
  intros. destruct H; destruct H0; split.
  eapply is_tail_trans; eauto.
  intros. rewrite H1; auto.
Qed.

Definition nolabel (i: instruction) :=
  match i with Plabel _ => False | _ => True end.

Hint Extern 1 (nolabel _) => exact I : labels.

Lemma tail_nolabel_cons:
  forall i c k,
  nolabel i -> tail_nolabel k c -> tail_nolabel k (i :: c).
Proof.
  intros. destruct H0. split.
  constructor; auto.
  intros. simpl. rewrite <- H1. destruct i; reflexivity || contradiction.
Qed.

Hint Resolve tail_nolabel_refl: labels.

Ltac TailNoLabel :=
  eauto with labels;
  match goal with
  | [ |- tail_nolabel _ (_ :: _) ] => apply tail_nolabel_cons; [auto; exact I | TailNoLabel]
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: assertion_failed = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H; TailNoLabel
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H;  TailNoLabel
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; TailNoLabel
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; TailNoLabel
  | _ => idtac
  end.

(** * Execution of straight-line code *)

Section STRAIGHTLINE.

Variable ge: genv.
Variable fn: function.

(** Straight-line code is composed of processor instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

(** TODO: instrument exec_straight with footprint *)
Require Import Blockset Footprint InteractionSemantics.

Inductive exec_straight: code -> regset -> mem -> FP.t ->
                         code -> regset -> mem -> Prop :=
| exec_straight_one:
    forall i1 c rs1 m1 fp rs2 m2,
      exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
      exec_instr_fp ge fn i1 rs1 m1 = fp ->
      rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
      exec_straight (i1 :: c) rs1 m1 fp c rs2 m2
| exec_straight_step:
    forall i c rs1 m1 fp1 rs2 m2 fp2 c' rs3 m3 fp,
      exec_instr ge fn i rs1 m1 = Next rs2 m2 ->
      exec_instr_fp ge fn i rs1 m1 = fp1 ->      
      rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
      exec_straight c rs2 m2 fp2 c' rs3 m3 ->
      FP.union fp1 fp2 = fp ->
      exec_straight (i :: c) rs1 m1 fp c' rs3 m3.

Lemma exec_straight_trans:
  forall c1 rs1 m1 fp1 c2 rs2 m2 fp2 c3 rs3 m3,
  exec_straight c1 rs1 m1 fp1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 fp2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 (FP.union fp1 fp2) c3 rs3 m3.
Proof.
  intros until 1. revert fp2 c3 rs3 m3. induction H; intros.
  apply exec_straight_step with fp rs2 m2 fp2; auto.
  subst fp. rewrite <- FP.fp_union_assoc.
  apply exec_straight_step with fp1 rs2 m2 (FP.union fp2 fp0) ; auto.
Qed.

Lemma exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 fp1 rs3 m3 fp2,
    exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
    exec_instr_fp ge fn i1 rs1 m1 = fp1 ->
    exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
    exec_instr_fp ge fn i2 rs2 m2 = fp2 ->    
    rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
    rs3#PC = Val.offset_ptr rs2#PC Ptrofs.one ->
    exec_straight (i1 :: i2 :: c) rs1 m1 (FP.union fp1 fp2) c rs3 m3.
Proof.
  intros. apply exec_straight_step with fp1 rs2 m2 fp2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 fp1 rs3 m3 fp2 rs4 m4 fp3,
  exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
  exec_instr_fp ge fn i1 rs1 m1 = fp1 ->
  exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
  exec_instr_fp ge fn i2 rs2 m2 = fp2 ->
  exec_instr ge fn i3 rs3 m3 = Next rs4 m4 ->
  exec_instr_fp ge fn i3 rs3 m3 = fp3 ->
  rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
  rs3#PC = Val.offset_ptr rs2#PC Ptrofs.one ->
  rs4#PC = Val.offset_ptr rs3#PC Ptrofs.one ->
  exec_straight (i1 :: i2 :: i3 :: c) rs1 m1 (FP.union fp1 (FP.union fp2 fp3)) c rs4 m4.
Proof.
  intros. apply exec_straight_step with fp1 rs2 m2 (FP.union fp2 fp3); auto.
  eapply exec_straight_two; eauto.
Qed.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct Asm executions. *)

Lemma exec_straight_steps_1:
  forall c rs m fp c' rs' m' lf,
    exec_straight c rs m fp c' rs' m' ->
    list_length_z (fn_code fn) <= Ptrofs.max_unsigned ->
    forall b ofs,
      rs#PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal fn) ->
      code_tail (Ptrofs.unsigned ofs) (fn_code fn) c ->
      plus (ASM_local.step ge) (Core_State rs lf) m fp (Core_State rs' lf) m'.
Proof.
  induction 1; intros. 
  apply plus_one.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  eapply plus_left'.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  apply IHexec_straight with b (Ptrofs.add ofs Ptrofs.one).
  auto. rewrite H1. rewrite H5. reflexivity.
  auto.
  apply code_tail_next_int with i; auto.
  traceEq.
Qed.

Lemma exec_straight_steps_2:
  forall c rs m fp c' rs' m',
    exec_straight c rs m fp c' rs' m' ->
    list_length_z (fn_code fn) <= Ptrofs.max_unsigned ->
    forall b ofs,
      rs#PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal fn) ->
      code_tail (Ptrofs.unsigned ofs) (fn_code fn) c ->
      exists ofs',
        rs'#PC = Vptr b ofs'
        /\ code_tail (Ptrofs.unsigned ofs') (fn_code fn) c'.
Proof.
  induction 1; intros.
  exists (Ptrofs.add ofs Ptrofs.one). split.
  rewrite H1. rewrite H3. auto.
  apply code_tail_next_int with i1; auto.
  apply IHexec_straight with (Ptrofs.add ofs Ptrofs.one).
  auto. rewrite H1. rewrite H5. reflexivity. auto.
  apply code_tail_next_int with i; auto.
Qed.

End STRAIGHTLINE.

(** * Properties of the Mach call stack *)

Section MATCH_STACK.

Variable ge: Mach.genv.

(** TODO: This invariant might be too weak, since we have a loadframe *)
Inductive match_stack: list Mach.stackframe -> Prop :=
  | match_stack_nil:
      match_stack nil
  | match_stack_cons: forall fb sp ra c s f tf tc,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      transl_code_at_pc ge ra fb f c false tf tc ->
      sp <> Vundef ->
      match_stack s ->
      match_stack (Stackframe fb sp ra c :: s).

Lemma parent_sp_def: forall s sp0, match_stack s -> parent_sp0 sp0 s <> Vundef.
Proof.
  induction 1; simpl. 
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  auto.
Qed.

Lemma parent_ra_def: forall s, match_stack s -> parent_ra s <> Vundef.
Proof. 
  induction 1; simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  inv H0. congruence.
Qed.

Lemma lessdef_parent_sp:
  forall s sp0 v,
  match_stack s -> Val.lessdef (parent_sp0 sp0 s) v -> v = parent_sp0 sp0 s.
Proof.
  intros. inv H0. auto. exploit parent_sp_def; eauto. tauto.
Qed.

Lemma lessdef_parent_ra:
  forall s v,
  match_stack s -> Val.lessdef (parent_ra s) v -> v = parent_ra s.
Proof.
  intros. inv H0. auto. exploit parent_ra_def; eauto. tauto.
Qed.

End MATCH_STACK.

