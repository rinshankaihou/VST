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

(** Correctness proof for code linearization *)

Require Import FSets.
Require Import Coqlib Maps Ordered Errors Lattice Kildall Integers.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations LTL Linear.
Require Import Linearize.


Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        Op_fp LTL_local Linear_local linearize.

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.

Module NodesetFacts := FSetFacts.Facts(Nodeset).



Definition match_cu (scu: LTL_comp_unit) (tcu: Linear_comp_unit) :=
  match_comp_unit_gen (fun f tf => transf_fundef f = OK tf) eq scu tcu.

Lemma transf_program_match:
  forall scu tcu, transf_program scu = OK tcu -> match_cu scu tcu.
Proof.
  intros. eapply match_transform_partial_cunit; eauto.
Qed.

Section LINEARIZATION.

Variable scu: LTL_comp_unit.
Variable tcu: Linear_comp_unit.

Hypothesis TRANSF: match_cu scu tcu.

Variable sge sG: LTL.genv.
Variable tge tG: Linear.genv.

Hypothesis GE_INIT: LTL_IS.(init_genv_local) scu sge sG.
Hypothesis TGE_INIT: Linear_IS.(init_genv_local) tcu tge tG.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof.
  inv GE_INIT; inv TGE_INIT. exploit match_cu_match_genv; eauto.
  intro. inv H; auto.
Qed.

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

Lemma senv_preserved:
  Senv.equiv sge tge.
Proof. inv GE_INIT. inv TGE_INIT. eapply match_cu_senv_preserved; eauto. Qed.

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  Linear.funsig tf = LTL.funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H. monadInv EQ. reflexivity.
  inv H. reflexivity.
Qed.

Lemma stacksize_preserved:
  forall f tf,
  transf_function f = OK tf ->
  Linear.fn_stacksize tf = LTL.fn_stacksize f.
Proof.
  intros. monadInv H. auto.
Qed.

Lemma ge_match: ge_match_strict sge tge.
Proof. inv GE_INIT. inv TGE_INIT. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma find_function_translated:
  forall ros ls f,
  LTL.find_function sge ros ls = Some f ->
  exists tf,
  find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold LTL.find_function; intros; destruct ros; simpl.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol sge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(** * Correctness of reachability analysis *)

(** The entry point of the function is reachable. *)

Lemma reachable_entrypoint:
  forall f, (reachable f)!!(f.(fn_entrypoint)) = true.
Proof.
  intros. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux; intros reach A.
  assert (LBoolean.ge reach!!(f.(fn_entrypoint)) true).
  eapply DS.fixpoint_entry. eexact A. auto.
  unfold LBoolean.ge in H. tauto.
  intros. apply PMap.gi.
Qed.

(** The successors of a reachable instruction are reachable. *)

Lemma reachable_successors:
  forall f pc pc' b,
  f.(LTL.fn_code)!pc = Some b -> In pc' (successors_block b) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution; eauto. intros; apply DS.L.eq_refl.
  elim H3; intro. congruence. auto.
  intros. apply PMap.gi.
Qed.

(** * Properties of node enumeration *)

(** An enumeration of CFG nodes is correct if the following conditions hold:
- All nodes for reachable basic blocks must be in the list.
- The list is without repetition (so that no code duplication occurs).

We prove that the result of the [enumerate] function satisfies both
conditions. *)

Lemma nodeset_of_list_correct:
  forall l s s',
  nodeset_of_list l s = OK s' ->
  list_norepet l
  /\ (forall pc, Nodeset.In pc s' <-> Nodeset.In pc s \/ In pc l)
  /\ (forall pc, In pc l -> ~Nodeset.In pc s).
Proof.
  induction l; simpl; intros.
  inv H. split. constructor. split. intro; tauto. intros; tauto.
  generalize H; clear H; caseEq (Nodeset.mem a s); intros.
  inv H0.
  exploit IHl; eauto. intros [A [B C]].
  split. constructor; auto. red; intro. elim (C a H1). apply Nodeset.add_1. hnf. auto.
  split. intros. rewrite B. rewrite NodesetFacts.add_iff.
  unfold Nodeset.E.eq. unfold OrderedPositive.eq. tauto.
  intros. destruct H1. subst pc. rewrite NodesetFacts.not_mem_iff. auto.
  generalize (C pc H1). rewrite NodesetFacts.add_iff. tauto.
Qed.

Lemma check_reachable_correct:
  forall f reach s pc i,
  check_reachable f reach s = true ->
  f.(LTL.fn_code)!pc = Some i ->
  reach!!pc = true ->
  Nodeset.In pc s.
Proof.
  intros f reach s.
  assert (forall l ok,
    List.fold_left (fun a p => check_reachable_aux reach s a (fst p) (snd p)) l ok = true ->
    ok = true /\
    (forall pc i,
     In (pc, i) l ->
     reach!!pc = true ->
     Nodeset.In pc s)).
  induction l; simpl; intros.
  split. auto. intros. destruct H0.
  destruct a as [pc1 i1]. simpl in H.
  exploit IHl; eauto. intros [A B].
  unfold check_reachable_aux in A.
  split. destruct (reach!!pc1). elim (andb_prop _ _ A). auto. auto.
  intros. destruct H0. inv H0. rewrite H1 in A. destruct (andb_prop _ _ A).
  apply Nodeset.mem_2; auto.
  eauto.

  intros pc i. unfold check_reachable. rewrite PTree.fold_spec. intros.
  exploit H; eauto. intros [A B]. eapply B; eauto.
  apply PTree.elements_correct. eauto.
Qed.

Lemma enumerate_complete:
  forall f enum pc i,
  enumerate f = OK enum ->
  f.(LTL.fn_code)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc enum.
Proof.
  intros until i. unfold enumerate.
  set (reach := reachable f).
  intros. monadInv H.
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit check_reachable_correct; eauto. intro.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]].
  rewrite B in H2. destruct H2. elim (Nodeset.empty_1 H2). auto.
Qed.

Lemma enumerate_norepet:
  forall f enum,
  enumerate f = OK enum ->
  list_norepet enum.
Proof.
  intros until enum. unfold enumerate.
  set (reach := reachable f).
  intros. monadInv H.
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]]. auto.
Qed.

(** * Properties related to labels *)

(** If labels are globally unique and the Linear code [c] contains
  a subsequence [Llabel lbl :: c1], then [find_label lbl c] returns [c1].
*)

Fixpoint unique_labels (c: code) : Prop :=
  match c with
  | nil => True
  | Llabel lbl :: c => ~(In (Llabel lbl) c) /\ unique_labels c
  | i :: c => unique_labels c
  end.

Lemma find_label_unique:
  forall lbl c1 c2 c3,
  is_tail (Llabel lbl :: c1) c2 ->
  unique_labels c2 ->
  find_label lbl c2 = Some c3 ->
  c1 = c3.
Proof.
  induction c2.
  simpl; intros; discriminate.
  intros c3 TAIL UNIQ. simpl.
  generalize (is_label_correct lbl a). case (is_label lbl a); intro ISLBL.
  subst a. intro. inversion TAIL. congruence.
  elim UNIQ; intros. elim H4. apply is_tail_in with c1; auto.
  inversion TAIL. congruence. apply IHc2. auto.
  destruct a; simpl in UNIQ; tauto.
Qed.

(** Correctness of the [starts_with] test. *)

Lemma starts_with_correct:
  forall lbl c1 c2 c3 s f sp ls lf m,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  find_label lbl c2 = Some c3 ->
  plus (step tge) (Core_State s f sp c1 ls lf) m
       empfp (Core_State s f sp c3 ls lf) m.
Proof.
  induction c1.
  simpl; intros; discriminate.
  simpl starts_with. destruct a; try (intros; discriminate).
  intros. rewrite <- (FP.emp_union_fp empfp).
  apply plus_left with empfp (Core_State s f sp c1 ls lf) m empfp.
  simpl. constructor.
  destruct (peq lbl l).
  subst l. replace c3 with c1. constructor.
  apply find_label_unique with lbl c2; auto.
  apply plus_star.
  apply IHc1 with c2; auto. eapply is_tail_cons_left; eauto.
  auto.
Qed.

(** Connection between [find_label] and linearization. *)

Lemma find_label_add_branch:
  forall lbl k s,
  find_label lbl (add_branch s k) = find_label lbl k.
Proof.
  intros. unfold add_branch. destruct (starts_with s k); auto.
Qed.

Lemma find_label_lin_block:
  forall lbl k b,
  find_label lbl (linearize_block b k) = find_label lbl k.
Proof.
  intros lbl k. generalize (find_label_add_branch lbl k); intro.
  induction b; simpl; auto. destruct a; simpl; auto.
  case (starts_with s1 k); simpl; auto.
Qed.

Remark linearize_body_cons:
  forall f pc enum,
  linearize_body f (pc :: enum) =
  match f.(LTL.fn_code)!pc with
  | None => linearize_body f enum
  | Some b => Llabel pc :: linearize_block b (linearize_body f enum)
  end.
Proof.
  intros. unfold linearize_body. rewrite list_fold_right_eq.
  unfold linearize_node. destruct (LTL.fn_code f)!pc; auto.
Qed.

Lemma find_label_lin_rec:
  forall f enum pc b,
  In pc enum ->
  f.(LTL.fn_code)!pc = Some b ->
  exists k, find_label pc (linearize_body f enum) = Some (linearize_block b k).
Proof.
  induction enum; intros.
  elim H.
  rewrite linearize_body_cons.
  destruct (peq a pc).
  subst a. exists (linearize_body f enum).
  rewrite H0. simpl. rewrite peq_true. auto.
  assert (In pc enum). simpl in H. tauto.
  destruct (IHenum pc b H1 H0) as [k FIND].
  exists k. destruct (LTL.fn_code f)!a.
  simpl. rewrite peq_false. rewrite find_label_lin_block. auto. auto.
  auto.
Qed.

Lemma find_label_lin:
  forall f tf pc b,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  find_label pc (fn_code tf) = Some (linearize_block b k).
Proof.
  intros. monadInv H. simpl.
  rewrite find_label_add_branch. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed.

Lemma find_label_lin_inv:
  forall f tf pc b k,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  find_label pc (fn_code tf) = Some k ->
  exists k', k = linearize_block b k'.
Proof.
  intros. exploit find_label_lin; eauto. intros [k' FIND].
  exists k'. congruence.
Qed.

(** Unique label property for linearized code. *)

Lemma label_in_add_branch:
  forall lbl s k,
  In (Llabel lbl) (add_branch s k) -> In (Llabel lbl) k.
Proof.
  intros until k; unfold add_branch.
  destruct (starts_with s k); simpl; intuition congruence.
Qed.

Lemma label_in_lin_block:
  forall lbl k b,
  In (Llabel lbl) (linearize_block b k) -> In (Llabel lbl) k.
Proof.
  induction b; simpl; intros. auto.
  destruct a; simpl in H; try (intuition congruence).
  apply label_in_add_branch with s; intuition congruence.
  destruct (starts_with s1 k); simpl in H.
  apply label_in_add_branch with s1; intuition congruence.
  apply label_in_add_branch with s2; intuition congruence.
Qed.

Lemma label_in_lin_rec:
  forall f lbl enum,
  In (Llabel lbl) (linearize_body f enum) -> In lbl enum.
Proof.
  induction enum.
  simpl; auto.
  rewrite linearize_body_cons. destruct (LTL.fn_code f)!a.
  simpl. intros [A|B]. left; congruence.
  right. apply IHenum. eapply label_in_lin_block; eauto.
  intro; right; auto.
Qed.

Lemma unique_labels_add_branch:
  forall lbl k,
  unique_labels k -> unique_labels (add_branch lbl k).
Proof.
  intros; unfold add_branch.
  destruct (starts_with lbl k); simpl; intuition.
Qed.

Lemma unique_labels_lin_block:
  forall k b,
  unique_labels k -> unique_labels (linearize_block b k).
Proof.
  induction b; intros; simpl. auto.
  destruct a; auto; try (apply unique_labels_add_branch; auto).
  case (starts_with s1 k); simpl; apply unique_labels_add_branch; auto.
Qed.

Lemma unique_labels_lin_rec:
  forall f enum,
  list_norepet enum ->
  unique_labels (linearize_body f enum).
Proof.
  induction enum.
  simpl; auto.
  rewrite linearize_body_cons.
  intro. destruct (LTL.fn_code f)!a.
  simpl. split. red. intro. inversion H. elim H3.
  apply label_in_lin_rec with f.
  apply label_in_lin_block with b. auto.
  apply unique_labels_lin_block. apply IHenum. inversion H; auto.
  apply IHenum. inversion H; auto.
Qed.

Lemma unique_labels_transf_function:
  forall f tf,
  transf_function f = OK tf ->
  unique_labels (fn_code tf).
Proof.
  intros. monadInv H. simpl.
  apply unique_labels_add_branch.
  apply unique_labels_lin_rec. eapply enumerate_norepet; eauto.
Qed.

(** Correctness of [add_branch]. *)

Lemma is_tail_find_label:
  forall lbl c2 c1,
  find_label lbl c1 = Some c2 -> is_tail c2 c1.
Proof.
  induction c1; simpl.
  intros; discriminate.
  case (is_label lbl a). intro. injection H; intro. subst c2.
  constructor. constructor.
  intro. constructor. auto.
Qed.

Lemma is_tail_add_branch:
  forall lbl c1 c2, is_tail (add_branch lbl c1) c2 -> is_tail c1 c2.
Proof.
  intros until c2. unfold add_branch. destruct (starts_with lbl c1).
  auto. eauto with coqlib.
Qed.

Lemma is_tail_lin_block:
  forall b c1 c2,
  is_tail (linearize_block b c1) c2 -> is_tail c1 c2.
Proof.
  induction b; simpl; intros.
  auto.
  destruct a; eauto with coqlib.
  eapply is_tail_add_branch; eauto.
  destruct (starts_with s1 c1); eapply is_tail_add_branch; eauto with coqlib.
Qed.

Lemma add_branch_correct:
  forall lbl c k s f tf sp ls lf m,
  transf_function f = OK tf ->
  is_tail k tf.(fn_code) ->
  find_label lbl tf.(fn_code) = Some c ->
  plus (step tge) (Core_State s tf sp (add_branch lbl k) ls lf) m
             empfp (Core_State s tf sp c ls lf) m.
Proof.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.
  eapply starts_with_correct; eauto.
  eapply unique_labels_transf_function; eauto.
  apply plus_one. apply exec_Lgoto. auto.
Qed.

(** * Correctness of linearization *)

(** The proof of semantic preservation is a simulation argument of the "star" kind:
<<
           st1 --------------- st2
            |                   |
           t|                  t| + or ( 0 \/ |st1'| < |st1| )
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant (horizontal lines above) is the [match_states]
  predicate defined below.  It captures the fact that the flow
  of data is the same in the source and linearized codes.
  Moreover, whenever the source state is at node [pc] in its
  control-flow graph, the transformed state is at a code
  sequence [c] that starts with the label [pc]. *)
Definition locset_lessdef (ls ls': locset) : Prop :=
  forall l, Val.lessdef (ls l) (ls' l).

Lemma locset_lessdef_regs:
  forall ls ls' args,
    locset_lessdef ls ls' ->
    Val.lessdef_list (reglist ls args) (reglist ls' args).
Proof. clear. induction args; auto. intros. constructor; auto. Qed.

Lemma locset_lessdef_args:
  forall ls ls' args,
    locset_lessdef ls ls' ->
    Val.lessdef_list (map (fun p : rpair loc => Locmap.getpair p ls) args)
                     (map (fun p : rpair loc => Locmap.getpair p ls') args).
Proof. clear. induction args; auto. intros. constructor; auto.
       unfold Locmap.getpair. destruct a; auto.
       apply Val.longofwords_lessdef; auto. Qed.

Lemma undef_locset_lessdef:
  forall ls ls' rl,
    locset_lessdef ls ls' ->
    locset_lessdef (undef_regs rl ls) (undef_regs rl ls').
Proof.
  clear. induction rl; intros; auto.
  apply IHrl in H. simpl.
  intro l. specialize (H l). 
  destruct (Loc.diff_dec (R a) l).
  repeat rewrite Locmap.gso; auto.
  destruct l. destruct (Loc.eq (R a) (R r)).
  rewrite e in *.
  repeat rewrite Locmap.gss; auto.
  exfalso. apply n. simpl. intro. subst. auto.
  exfalso. apply n. simpl. auto.
Qed.

Lemma set_locset_lessdef:
  forall ls ls' v v' l, 
    locset_lessdef ls ls' ->
    Val.lessdef v v' ->
    locset_lessdef (Locmap.set l v ls) (Locmap.set l v' ls').
Proof.
  clear. intros. intro l0.
  unfold Locmap.set. destruct Loc.eq.
  subst. destruct l0; auto. apply Val.load_result_lessdef; auto.
  destruct Loc.diff_dec; auto.
Qed.

Lemma return_locset_lessdef:
  forall ls ls0 ls' ls0',
    locset_lessdef ls ls' ->
    locset_lessdef ls0 ls0' ->
    locset_lessdef (return_regs ls0 ls) (return_regs ls0' ls').
Proof.
  clear. intros. intro l0.
  unfold return_regs. destruct l0; auto.
  destruct (Conventions1.is_callee_save r); auto.
Qed.

Lemma call_locset_lessdef:
  forall ls ls',
    locset_lessdef ls ls' ->
    locset_lessdef (call_regs ls) (call_regs ls').
Proof.
  clear. intros. unfold call_regs.
  intro l. destruct l; auto. destruct sl; auto.
Qed.

Lemma setres_locset_lessdef:
  forall res ls ls' vres vres',
    locset_lessdef ls ls' ->
    Val.lessdef vres vres' ->
    locset_lessdef (Locmap.setres res vres ls)
                   (Locmap.setres res vres' ls').
Proof.
  clear. induction res; simpl; intros; intro l; auto.
  - apply set_locset_lessdef; auto. 
  - apply IHres2. apply IHres1. auto.
    apply Val.hiword_lessdef; auto. apply Val.loword_lessdef; auto.
Qed.

Lemma setpair_locset_lessdef:
  forall ls ls' res res' loc,
    locset_lessdef ls ls' ->
    Val.lessdef res res' ->
    locset_lessdef (Locmap.setpair loc res ls) (Locmap.setpair loc res' ls').
Proof.
  clear. destruct loc; intros; simpl; repeat apply set_locset_lessdef; auto.
  apply Val.hiword_lessdef; auto. apply Val.loword_lessdef; auto.
Qed.
    
Ltac resolv_ls :=
  match goal with
  | |- locset_lessdef (Locmap.set _ _ _) (Locmap.set _ _ _) =>
    apply set_locset_lessdef; auto; resolv_ls
  | |- locset_lessdef (undef_regs _ _) (undef_regs _ _) =>
    apply undef_locset_lessdef; auto; resolv_ls
  | |- locset_lessdef (return_regs _ _) (return_regs _ _) =>
    apply return_locset_lessdef; auto; resolv_ls
  | |- locset_lessdef (call_regs _ _) (return_regs _ _) =>
    apply call_locset_lessdef; auto; resolv_ls
  | |- locset_lessdef (Locmap.setres _ _ _) (Locmap.setres _ _ _) =>
    apply setres_locset_lessdef; auto; resolv_ls
  | |- locset_lessdef (Locmap.setpair _ _ _) (Locmap.setpair _ _ _) =>
    apply setpair_locset_lessdef; auto; resolv_ls                                         
  | _ => idtac
  end.

Lemma find_function_lessdef:
  forall ros ls tfd ls',
    find_function tge ros ls = Some tfd ->
    locset_lessdef ls ls' ->
    find_function tge ros ls' = Some tfd.
Proof.
  clear. unfold find_function; intros.
  destruct ros; auto.
  unfold Genv.find_funct in *.
  specialize (H0 (R m)). inv H0; auto. rewrite <- H2 in H. discriminate.
Qed.



Inductive match_stackframes: LTL.stackframe -> Linear.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp bb ls ls' tf c
      (LSLD: locset_lessdef ls ls'),
      transf_function f = OK tf ->
      (forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true) ->
      is_tail c tf.(fn_code) ->
      match_stackframes
        (LTL.Stackframe f sp ls bb)
        (Linear.Stackframe tf sp ls' (linearize_block bb c)).

Inductive MATCH_STATE:
  bool -> nat -> Injections.Mu -> FP.t -> FP.t ->
  LTL_local.core * mem -> Linear_local.core * mem -> Prop :=
| match_states_add_branch:
    forall mu fp fp' s f sp pc ls sigres0 m tf ts c ls' ls0 fd0 m'
      (STACKS: list_forall2 match_stackframes s ts)
      (TRF: transf_function f = OK tf)
      (REACH: (reachable f)!!pc = true)
      (TAIL: is_tail c tf.(fn_code))
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (LSLD: locset_lessdef ls ls')
      (SIGRES: sig_res (fn_sig fd0) = sigres0)
      (MEXT: Mem.extends m m')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp'),
      MATCH_STATE true 0%nat mu fp fp'
                  (LTL_local.Core_State s f sp pc ls sigres0, m)
                  (Linear_local.Core_State ts tf sp (add_branch pc c) ls' (mk_load_frame ls0 fd0), m')
| match_states_cond_taken:
    forall mu fp fp' condfp s f sp pc ls sigres0 m tf ts cond args c ls' ls0 fd0 m'
      (STACKS: list_forall2 match_stackframes s ts)
      (TRF: transf_function f = OK tf)
      (REACH: (reachable f)!!pc = true)
      (JUMP: eval_condition cond (reglist ls args) m = Some true)
      (JUMP_fp: Op_fp.eval_condition_fp cond (reglist ls args) m = Some condfp)
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (LSLD: locset_lessdef ls ls')
      (SIGRES: sig_res (fn_sig fd0) = sigres0)
      (MEXT: Mem.extends m m')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE true 0%nat mu (FP.union fp condfp) fp'
                  (LTL_local.Core_State s f sp pc (undef_regs (destroyed_by_cond cond) ls) sigres0, m)
                  (Linear_local.Core_State ts tf sp (Lcond cond args pc :: c) ls' (mk_load_frame ls0 fd0), m')
| match_states_jumptable:
    forall mu fp fp' s f sp pc ls sigres0 m tf ts arg tbl c n ls' ls0 fd0 m'
      (STACKS: list_forall2 match_stackframes s ts)
      (TRF: transf_function f = OK tf)
      (REACH: (reachable f)!!pc = true)
      (ARG: ls (R arg) = Vint n)
      (JUMP: list_nth_z tbl (Int.unsigned n) = Some pc)
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (LSLD: locset_lessdef ls ls')
      (SIGRES: sig_res (fn_sig fd0) = sigres0)
      (MEXT: Mem.extends m m')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp') 
    ,
      MATCH_STATE true 0%nat mu fp fp'
                  (LTL_local.Core_State s f sp pc (undef_regs destroyed_by_jumptable ls) sigres0, m)
                  (Linear_local.Core_State ts tf sp (Ljumptable arg tbl :: c) ls' (mk_load_frame ls0 fd0), m')
| match_states_block:
    forall mu fp fp' s f sp bb ls sigres0 m tf ts c ls' ls0 fd0 m'
      (STACKS: list_forall2 match_stackframes s ts)
      (TRF: transf_function f = OK tf)
      (REACH: forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true)
      (TAIL: is_tail c tf.(fn_code))
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (LSLD: locset_lessdef ls ls')
      (SIGRES: sig_res (fn_sig fd0) = sigres0)
      (MEXT: Mem.extends m m')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp') 
    ,
      MATCH_STATE true 1%nat mu fp fp'
                  (LTL_local.Core_Block s f sp bb ls sigres0, m)
                  (Linear_local.Core_State ts tf sp (linearize_block bb c) ls' (mk_load_frame ls0 fd0), m')
| match_states_call_init:
    forall mu f args ls0 sigres0 m fd0 m' 
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (SIGRES: sig_res (fn_sig fd0) = sigres0)
      (HLS: ls0 = set_arguments (Conventions1.loc_arguments (fn_sig fd0)) args (Locmap.init Vundef))
      (MEXT: Mem.extends m m')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
    ,
      transf_fundef f = OK (Internal fd0) ->
      MATCH_STATE true 0%nat mu empfp empfp
                  (LTL_local.Core_Callstate nil f ls0 sigres0, m)
                  (Linear_local.Core_CallstateIn nil (Internal fd0) ls0 (mk_load_frame ls0 fd0), m')
                   
| match_states_call:
    forall b mu fp fp' s f ls sigres0 m tf ts ls' ls0 fd0 m'
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (LSLD: locset_lessdef ls ls')
      (SIGRES: sig_res (fn_sig fd0) = sigres0)
      (MEXT: Mem.extends m m')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      MATCH_STATE b 0%nat mu fp fp'
                  (LTL_local.Core_Callstate s f ls sigres0, m)
                  (Linear_local.Core_Callstate ts tf ls' (mk_load_frame ls0 fd0), m')
                   
| match_states_return:
    forall mu fp fp' s ls sigres0 m ts ls' ls0 fd0 m'
      (** NEW *)
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)      
      (LSLD: locset_lessdef ls ls')
      (SIGRES: sig_res (fn_sig fd0) = sigres0)
      (MEXT: Mem.extends m m')
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      list_forall2 match_stackframes s ts ->
      MATCH_STATE true 0%nat mu fp fp'
                  (LTL_local.Core_Returnstate s ls sigres0, m)
                  (Linear_local.Core_Returnstate ts ls' (mk_load_frame ls0 fd0), m').


Theorem TRANSF_local_ldsim:
  @local_ldsim LTL_IS Linear_IS sG tG sge tge.
Proof.
  eapply (@Local_ldsim LTL_IS Linear_IS _ _ _ _ nat Nat.lt MATCH_STATE).
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
  - intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    (* this should be a property derived from TRANSF? *)
    (* by properties of init_core_local ? *)
    assert (HSG: sG = sge) by (inv GE_INIT; auto).
    assert (HTG: tG = tge) by (inv TGE_INIT; auto).    
    unfold init_core_local in *. simpl in *.
    unfold LTL_local.init_core, init_core in *.
    unfold generic_init_core in INITCORE |- * .
    rewrite HTG, symbols_preserved.
    rewrite HSG in INITCORE.
    destruct (Genv.find_symbol sge fid) eqn: FIND; try discriminate.
    destruct (Genv.find_funct_ptr sge b) eqn: FINDB; try discriminate.
    exploit function_ptr_translated; eauto. intros (tf & FINDB' & TRANSL).
    rewrite FINDB'. 
    unfold LTL_local.fundef_init in INITCORE.
    destruct f; try discriminate.
    assert (exists tfd, tf = Internal tfd)  as [tfd INTERNAL] by (monadInv TRANSL; eauto). subst tf.
    unfold fundef_init.
    erewrite sig_preserved;[|eauto].
    destruct (wd_args args (sig_args (LTL.funsig (Internal f)))) eqn: WDARGS; [|discriminate].
    erewrite wd_args_inject; eauto.
    eexists. split. eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists 0%nat.
    inversion INITCORE; clear INITCORE. simpl. 
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. induction args; intros args' REL G MEMREL; inv REL.
      auto. inv G. f_equal. inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. }
    subst args'.
    exploit sig_preserved; eauto. simpl. intro SG. 
    econstructor; eauto.
    inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_src; auto.
    inv MEMINITINJ. inv LRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto.    
    rewrite SG. auto.
    rewrite SG. eauto.
    { inv MEMINITINJ. inv HRELY. inv LRELY.
      eapply inject_implies_extends; eauto.
      intros b0 A. unfold Mem.valid_block in A; rewrite EQNEXT, <- dom_eq_src in A. eapply Bset.inj_dom in A; eauto.
      destruct A as [b' A]. unfold Bset.inj_to_meminj. rewrite A. eauto.
      inv GE_INIT_INJ.
      rewrite mu_shared_src in dom_eq_src.
      rewrite mu_shared_tgt in dom_eq_tgt.
      rewrite S_EQ in dom_eq_src.
      assert (forall b, Plt b (Mem.nextblock sm0) <-> Plt b (Mem.nextblock tm0)).
      { intro. rewrite <- dom_eq_src, <- dom_eq_tgt. tauto. }
      rewrite EQNEXT, EQNEXT0.
      destruct (Pos.lt_total (Mem.nextblock sm0) (Mem.nextblock tm0)) as [LT | [EQ | LT]]; auto;
        (generalize H3 LT; clear; intros; exfalso; apply H3 in LT; eapply Pos.lt_irrefl; eauto). }

    inv MEMINITINJ; econstructor; eauto.
    simpl. intro.
    intros ? ? ? ? ? . exploit inj_inject_id. exact H. intro. inv H0.
    intro A. inv A. auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
    
  - (* tau step *)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP.
    simpl in STEP. 
    assert (HSG: sG = sge) by (inv GE_INIT; auto);
      assert (HTG: tG = tge) by (inv TGE_INIT; auto).  
    revert i mu Hfp Lfp Lcore Lm MS HSG HTG. induction STEP; intros until 1; try (inv MS).
    
    + (* start of block, at an [add_branch] *)
      exploit find_label_lin; eauto. intros [k F]. intros.
      right. eexists 1%nat, _, _, _.  split. rewrite HTG.
      simpl. eapply add_branch_correct; eauto.
      split. do 2 rewrite FP.fp_union_emp; auto.
      econstructor; eauto.
      intros; eapply reachable_successors; eauto.
      eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.
      do 2 rewrite FP.fp_union_emp; auto.
      
    + (* start of block, target of an [Lcond] *)
      assert (A: Val.lessdef_list (reglist ls args) (reglist ls' args)).
      { revert LSLD; clear. induction args; auto. intros. 
        constructor; auto. }
      exploit find_label_lin; eauto. intros [k F].
      exploit Op_fp.eval_condition_lessdef_fp; try eassumption. intros (condfp' & JUMP_fp' & INJFP).
      right. rewrite HTG. eexists 1%nat, _, _, _. split. 
      apply plus_one. eapply exec_Lcond_true; eauto.
      eapply eval_condition_lessdef; eauto.
      match goal with |- ?P /\ _ => assert P end.
      rewrite FP.fp_union_emp. apply Injections.fp_match_union'; auto. inv AGMU; eapply fp_inject_fp_match; eauto.
      split; auto.
      econstructor; eauto.
      intros; eapply reachable_successors; eauto.
      eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.
      
    + (* start of block, target of an [Ljumptable] *)
      exploit find_label_lin; eauto. intros [k F].
      right; eexists 1%nat, _, _, _. split.
      apply plus_one. eapply exec_Ljumptable; eauto.
      exploit LSLD. rewrite ARG. intro B. inv B; auto.
      do 2 rewrite FP.fp_union_emp. split; auto.
      econstructor; eauto.
      intros; eapply reachable_successors; eauto.
      eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.
      resolv_ls.
      
    + (* Lop *)
      right. simpl. rewrite HTG. rewrite HSG in H, H0.
      assert (A: Val.lessdef_list (reglist rs args) (reglist ls' args)).
      { revert LSLD; clear. induction args; auto. intros. 
        constructor; auto. }
      exploit eval_operation_lessdef_fp; try eassumption. intros (fp' & B & B').
      exploit eval_operation_lessdef; try eassumption. intros (v' & C & C').
      eexists 1%nat, _, _, _. split. 
      apply plus_one. econstructor; eauto.
      erewrite <- eval_operation_preserved in C; eauto. exact symbols_preserved.
      erewrite <- eval_operation_fp_preserved in B; eauto. exact symbols_preserved.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'; auto. inv AGMU; eapply fp_inject_fp_match; eauto.
      split; auto.
      econstructor; eauto.
      resolv_ls.

    + (* Lload *)
      exploit locset_lessdef_regs; eauto. instantiate (1:= args). intro A.
      exploit eval_addressing_lessdef; try eassumption. intros (a' & B & B').
      destruct a; simpl in H0; try discriminate. inv B'.
      exploit Mem.load_extends; eauto. intros (v' & C & C').
      right. rewrite HTG. eexists 1%nat, _, _, _. split.
      apply plus_one. econstructor; try eassumption.
      rewrite <- B. apply eval_addressing_preserved. rewrite HSG. exact symbols_preserved.
      eauto. eauto. eauto.
       match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'; auto. inv AGMU; eapply fp_match_id; eauto.
      split. auto.
      econstructor; eauto.
      resolv_ls.
      
    + (* Lgetstack *)
      right. rewrite HTG. eexists 1%nat, _, _, _. split.
      simpl. apply plus_one. econstructor; eauto.
      repeat rewrite (FP.fp_union_emp).
      split; auto.
      econstructor; eauto.
      resolv_ls.

    + (* Lsetstack *)
      right. rewrite HTG. eexists 1%nat, _, _, _. split.
      apply plus_one. econstructor; eauto.
      repeat rewrite FP.fp_union_emp.
      split; auto.
      econstructor; eauto.
      resolv_ls.
      
    + (* Lstore *)
      exploit locset_lessdef_regs; eauto. instantiate (1:= args). intro A.
      exploit eval_addressing_lessdef; try eassumption. intros (a' & B & B').
      destruct a; simpl in H0; try discriminate. inv B'.
      exploit Mem.store_within_extends; eauto. intros (Lm' & C & C').
      right. rewrite HTG. eexists 1%nat, _, _, _. split.
      apply plus_one. econstructor; try eassumption.
      rewrite <- B. apply eval_addressing_preserved. rewrite HSG. exact symbols_preserved.
      eauto. eauto. eauto.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'; auto. inv AGMU; eapply fp_match_id; eauto.
      split. auto.
      econstructor; eauto. resolv_ls.
      intros. apply SVALID in H2. eapply Mem.store_valid_block_1; eauto.
      intros. apply TVALID in H2. eapply Mem.store_valid_block_1; eauto.
      resolv_ls.
      inv AGMU. eapply MemClosures_local.store_val_inject_unmapped_closed_preserved; eauto.
      unfold inject_id. eauto. rewrite Z.add_0_r. eauto.

    + (* Lcall *)
      intros.
      exploit find_function_translated; eauto. rewrite HSG in *. eauto. intros [tfd [A B]].
      right. eexists 0%nat, _, _, _. split.
      
      apply plus_one. econstructor; eauto. rewrite HTG. eapply find_function_lessdef; eauto.
      symmetry; eapply sig_preserved; eauto.
      repeat rewrite (FP.fp_union_emp).
      split; auto.
      econstructor; eauto. constructor; auto. econstructor; eauto.

    + (* Ltailcall *)
      intros. exploit find_function_translated; eauto. rewrite <- HSG. eauto. intros [tfd [A B]].
      exploit Mem.free_parallel_extends; eauto. intros [Lm' [C D]].
      right. eexists 0%nat, _, _, _. split.
      apply plus_one. econstructor; eauto.
      rewrite HTG. eapply find_function_lessdef; eauto.
      resolv_ls.
      { inv STACKS. simpl. intro. auto. simpl. inv H. auto. }
      symmetry; eapply sig_preserved; eauto.
      rewrite (stacksize_preserved _ _ TRF); eauto.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'; auto.
      rewrite (stacksize_preserved _ _ TRF); eauto.
      inv AGMU; eapply fp_match_id; eauto.
      split. auto.
      econstructor; eauto. 
      intros ? S. apply SVALID in S. eapply Mem.valid_block_free_1; eauto.
      intros ? T. apply TVALID in T. eapply Mem.valid_block_free_1; eauto.
      resolv_ls.
      { inv STACKS. simpl. intro. auto. simpl. inv H1. auto. }
      inv AGMU. eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto.
      unfold inject_id. eauto. omega. omega.

    + (* Lbuiltin *)
      right. exploit eval_builtin_args_lessdef; eauto. intros [vl' [A B]].
      exploit external_call_mem_extends; eauto. intros [vres' [Lm' [C [D _]]]].
      exploit helpers.i64ext_effects; eauto. intros [X _ ]. subst Lm'.
      eexists 1%nat, _, _, _. split.
      apply plus_one. eapply exec_Lbuiltin; eauto.
      eapply eval_builtin_args_preserved with (ge1 := sG); eauto. rewrite HSG, HTG. exact symbols_preserved.
      eapply MemOpFP.eval_builtin_args_fp_preserved with (ge1 := sG); eauto. rewrite HSG, HTG. exact symbols_preserved.
      eapply MemOpFP.eval_builtin_args_fp_lessdef; eauto.
      eapply external_call_symbols_preserved; eauto. rewrite HTG, HSG. apply senv_preserved. 
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'; auto. eapply fp_match_id; inv AGMU; eauto.
      split; auto. econstructor; eauto. resolv_ls.
      
    + (* Lbranch *)
      assert ((reachable f)!!pc = true). apply REACH; simpl; auto.
      intros.
      left; exists 0%nat; split. auto. rewrite FP.fp_union_emp. econstructor; eauto. 

    + (* Lcond *)
      assert (REACH1: (reachable f)!!pc1 = true) by (apply REACH; simpl; auto).
      assert (REACH2: (reachable f)!!pc2 = true) by (apply REACH; simpl; auto).
      exploit eval_condition_lessdef; try eassumption. eapply locset_lessdef_regs; eauto. intro A.
      exploit eval_condition_lessdef_fp; try eassumption. eapply locset_lessdef_regs; eauto. intros (fp' & B & B').
      assert (C: eval_condition_fp (negate_condition cond) (reglist ls' args) Lm = Some fp').
      { eapply eval_condition_fp_negate; eauto. }
      exploit fp_inject_fp_match; try exact B'; try (inv AGMU; eauto; fail). clear B'. intro B'.
      simpl linearize_block.
      destruct (starts_with pc1 c).
      (* branch if cond is false *)
      assert (DC: destroyed_by_cond (negate_condition cond) = destroyed_by_cond cond).
      destruct cond; reflexivity.
      destruct b.
      (* cond is true: no branch *)
      right. eexists 0%nat, _, _, _. split.
      apply plus_one. eapply exec_Lcond_false.
      rewrite eval_negate_condition. rewrite A. auto. eauto. eauto.
      rewrite DC. split. apply Injections.fp_match_union'; auto.
      econstructor; eauto. apply Injections.fp_match_union'; auto.
      (* cond is false: branch is taken *)
      left. eexists 0%nat. split. auto.
      rewrite <- DC. econstructor; eauto.
      rewrite eval_negate_condition. rewrite H. auto.
      apply eval_condition_fp_negate; auto.
      (* branch if cond is true *)
      destruct b.
      (* cond is true: branch is taken *)
      left. eexists 0%nat. split; auto. econstructor; eauto.
      (* cond is false: no branch *)
      right. eexists 0%nat, _, _, _. split.
      apply plus_one. eapply exec_Lcond_false. eauto. eauto. eauto.
      split.  apply Injections.fp_match_union'; auto.
      econstructor; eauto.  apply Injections.fp_match_union'; auto.

    + (* Ljumptable *)
      assert (REACH': (reachable f)!!pc = true).
      apply REACH. simpl. eapply list_nth_z_in; eauto.
      left. eexists 0%nat. split. auto. rewrite FP.fp_union_emp. econstructor; eauto.

    + (* Lreturn *)
      exploit Mem.free_parallel_extends; eauto. 
      rewrite <- (stacksize_preserved _ _ TRF). intros [Lm' [A B]].
      right. eexists 0%nat, _, _, _. split.
      simpl. apply plus_one. econstructor; eauto.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'; auto. inv AGMU; eapply fp_match_id; eauto.
      split; auto. econstructor; eauto.
      intros ? S. apply SVALID in S. eapply Mem.valid_block_free_1; eauto.
      intros ? T. apply TVALID in T. eapply Mem.valid_block_free_1; eauto.
      resolv_ls.
      { inv STACKS. simpl. intro. auto. simpl. inv H1. auto. }
      inv AGMU. eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto.
      unfold inject_id; eauto. omega. 
      rewrite (stacksize_preserved _ _ TRF). omega.

    + (* initial call *)
      assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
      apply reachable_entrypoint.
      monadInv H8. 
      exploit Mem.alloc_extends; eauto. instantiate (1:= 0); omega. instantiate (1:= LTL.fn_stacksize f); omega.
      rewrite <- (stacksize_preserved _ _ EQ). intros [Lm' [A B]].
      right. eexists 0%nat, _, _, _. split.
      eapply plus_two. econstructor. econstructor; eauto.
      rewrite FP.emp_union_fp. eauto.
      repeat rewrite (FP.emp_union_fp).
      match goal with |- ?P /\ _ => assert P end.
      unfold MemOpFP.alloc_fp. inv MEXT. rewrite mext_next. 
      inv AGMU; eapply fp_match_id; eauto.
      split; auto.
      generalize EQ. intros EQ'. monadInv EQ'.
      econstructor; eauto; simpl.
      constructor.
      eapply is_tail_add_branch. constructor.
      intros ? S. apply SVALID in S. eapply Mem.valid_block_alloc; eauto.
      intros ? T. apply TVALID in T. eapply Mem.valid_block_alloc; eauto.
      resolv_ls. intro l; auto.
      eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; inv AGMU; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
      
    + (* internal functions *)
      assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
      apply reachable_entrypoint.
      monadInv H15.
      exploit Mem.alloc_extends; eauto. instantiate (1:= 0); omega. instantiate (1:= LTL.fn_stacksize f); omega.
      rewrite <- (stacksize_preserved _ _ EQ). intros [Lm' [A B]].
      right. eexists 0%nat, _, _, _. split.
      apply plus_one. eapply exec_function_internal; eauto.
      rewrite (stacksize_preserved _ _ EQ). eauto.
      match goal with |- ?P /\ _ => assert P end.
      apply Injections.fp_match_union'; auto. unfold MemOpFP.alloc_fp. inv MEXT. rewrite mext_next. 
      inv AGMU; eapply fp_match_id; eauto.
      split; auto.
      generalize EQ; intro EQ'; monadInv EQ'. simpl.
      econstructor; eauto. simpl. eapply is_tail_add_branch. constructor.
      intros ? S. apply SVALID in S. eapply Mem.valid_block_alloc; eauto.
      intros ? T. apply TVALID in T. eapply Mem.valid_block_alloc; eauto.
      resolv_ls. apply call_locset_lessdef; auto.
      eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; inv AGMU; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
      eapply Mem.alloc_unchanged_on; eauto.

    + (* external function *) monadInv H9.
    + monadInv H16. exploit external_call_mem_extends; eauto.
      eapply locset_lessdef_args; eauto. intros [vres' [Lm' [EXT [VLD _]]]].
      exploit helpers.i64ext_effects; eauto. intros [X Y]; subst Lm' t.
      right. eexists 0%nat, _, _, _. split. 
      apply plus_one. eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto. rewrite HSG, HTG; apply senv_preserved.
      repeat rewrite FP.fp_union_emp. split; auto.
      econstructor; eauto. resolv_ls.

    + (* return *)
      inv H5. inv H1.
      right. eexists 1%nat, _, _, _. split.
      apply plus_one. econstructor.
      repeat rewrite FP.fp_union_emp. split; auto.
      econstructor; eauto.
      
  - (* at_external *)
    
    simpl in *. unfold LTL_local.at_external, at_external.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MS ATEXT RC GARG.
    assert (HSG: sG = sge) by (inv GE_INIT; auto).
    assert (HTG: tG = tge) by (inv TGE_INIT; auto).
    destruct Hcore; try discriminate.
    destruct f0; try discriminate.
    destruct e; try discriminate.
    rewrite HSG in ATEXT.
    destruct (invert_symbol_from_string sge name) eqn:SYMBNAME; try discriminate.
    revert HSG HTG; inv MS. monadInv H5. monadInv H12.
    intros.
    erewrite match_genvs_invert_symbol_from_string_preserved; eauto.
    destruct peq; try discriminate.
    destruct peq; try discriminate.
    simpl in *. revert HSG HTG; inv ATEXT.
    intros.
    eexists 0%nat, _.
    split. eauto.
    split. 
    { unfold LDSimDefs.arg_rel. revert AGMU LSLD GARG; clear.
      generalize (Conventions1.loc_arguments sg). clear.
      induction l; intros. auto. simpl. inv GARG.
      constructor; auto. clear H2 IHl.
      unfold Locmap.getpair in *. destruct a; simpl in *.

      specialize (LSLD r); inv LSLD; auto.
      destruct (ls r); auto. econstructor. simpl in H1.
      inv AGMU. unfold Bset.inj_to_meminj.
      eapply Bset.inj_dom in H1; eauto. destruct H1 as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. rewrite INJ. inv A. eauto. rewrite Ptrofs.add_zero; auto.

      pose proof (LSLD rhi) as HI.
      pose proof (LSLD rlo) as LO.
      exploit Val.longofwords_lessdef. exact HI. exact LO. intro.
      clear HI LO LSLD. revert H H1 AGMU.
      generalize (Val.longofwords (ls rhi) (ls rlo))
                 (Val.longofwords (ls' rhi) (ls' rlo)). clear.
      intros. inv H; auto. destruct v0; auto. econstructor.
      inv AGMU. unfold Bset.inj_to_meminj.
      eapply Bset.inj_dom in H1; eauto. destruct H1 as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. rewrite INJ. inv A. eauto. rewrite Ptrofs.add_zero; auto. }
    split.
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends;
      inv AGMU; eauto.
    split; auto.
    split.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    econstructor; eauto.
    apply Injections.fp_match_emp'.
    rewrite HTG. eapply match_cu_match_genv; eauto.
    inv GE_INIT; eauto. inv TGE_INIT; eauto.
    intros. inv H; auto. destruct f1; monadInv H0; auto.

  - (* after_external *)
    simpl. unfold LTL_local.after_external, after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    assert (HSG: sG = sge) by (inv GE_INIT; auto). assert (HTG: tG = tge) by (inv TGE_INIT; auto). revert HSG HTG.
    destruct Hcore; try discriminate.
    destruct f; try discriminate.
    destruct e; try discriminate.
    inv MS. monadInv H12. intros.
    assert (Hcore' = LTL_local.Core_Returnstate stack
                                                (Locmap.setpair (Conventions1.loc_result sg)
                                                                (match oresSrc with
                                                                 | Some v => v
                                                                 | None => Vundef
                                                                 end) ls)
                                                (sig_res (fn_sig fd0))).
    { destruct oresSrc, (sig_res sg); inv AFTEXT; auto.
      destruct (val_has_type_func v t); inv H0. auto. }
    assert (match oresSrc, (sig_res sg) with
            | None, None => True
            | Some v, Some ty => Val.has_type v ty
            | _, _ => False
            end) as HRES.
    { destruct oresSrc, (sig_res sg); inv AFTEXT; auto.
      destruct (val_has_type_func v t) eqn:A; inv H1. apply val_has_type_funcP; auto. }
    clear AFTEXT. rename H into AFTEXT.
    exists (Core_Returnstate ts (Locmap.setpair (Conventions1.loc_result sg)
                                           (match oresTgt with Some v => v | None => Vundef end) ls')
                        (mk_load_frame ls1 fd0)).
    split.
    { destruct oresSrc, oresTgt, (sig_res sg); try contradiction; auto.
      inv RESREL; destruct t; try contradiction; simpl in *; auto.
      rewrite HRES. auto. }
    intros Hm' Lm' HLRELY.
    destruct HLRELY as [HRELY LRELY INV].
    exists 0%nat. subst. econstructor; eauto.
    intros ? S. apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT; auto.
    intros ? T. apply TVALID in T. unfold Mem.valid_block in *. inv LRELY. rewrite EQNEXT; auto.
    destruct (Conventions1.loc_result sg); simpl; resolv_ls.
    destruct oresSrc, oresTgt; inv RESREL; auto.
    inv AGMU. apply proper_mu_inject_incr in H. inv H. rewrite Ptrofs.add_zero; auto.
    destruct oresSrc, oresTgt; inv RESREL; auto.
    destruct oresSrc, oresTgt; inv RESREL; auto.
    inv AGMU; eapply extends_rely_extends; eauto. econstructor; eauto.
    inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
                                           
  - (* halt *)
    simpl.  unfold LTL_local.halted, halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES.
    destruct Hcore; try discriminate. destruct stack; try discriminate.
    inv HALT. inv MS. inv H5. eexists. split; eauto.
    split. 
    { erewrite (Conventions1.loc_result_exten _ (fn_sig fd0)) in GRES|-*; eauto.
      revert AGMU GRES LSLD. generalize (Conventions1.loc_result (fn_sig fd0)). clear. intros.
      destruct r; simpl in *. 
    
      specialize (LSLD (R r)); inv LSLD; try constructor.
      destruct (ls (R r)); econstructor. simpl in GRES.
      inv AGMU. unfold Bset.inj_to_meminj.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. rewrite INJ. inv A. eauto. rewrite Ptrofs.add_zero; auto.

      pose proof (LSLD (R rhi)) as HI.
      pose proof (LSLD (R rlo)) as LO.
      exploit Val.longofwords_lessdef. exact HI. exact LO. intro.
      clear HI LO LSLD. revert GRES H AGMU.
      generalize (Val.longofwords (ls (R rhi)) (ls (R rlo)))
                 (Val.longofwords (ls' (R rhi)) (ls' (R rlo))). clear.
      intros. inv H; destruct v0; econstructor.
      inv AGMU. unfold Bset.inj_to_meminj.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. rewrite INJ. inv A. eauto. rewrite Ptrofs.add_zero; auto. }
    split.
    inv AGMU; eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto.
    split; auto.
    inv AGMU; eapply extends_reach_closed_implies_inject; eauto.
Qed.

End LINEARIZATION.


Theorem transf_local_ldsim:
  forall scu tcu,
    linearize.transf_program scu = OK tcu ->
    forall sge sG tge tG,
      init_genv_local LTL_IS scu sge sG ->
      init_genv_local Linear_IS tcu tge tG ->
      Genv.genv_next sge = Genv.genv_next tge ->
      local_ldsim sG tG sge tge.
Proof.
  intros. eapply TRANSF_local_ldsim; eauto.
  apply transf_program_match. auto.
Qed.