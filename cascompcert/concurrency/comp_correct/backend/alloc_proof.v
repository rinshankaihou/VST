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


(** Correctness proof for the [Allocation] pass (validated translation from
  RTL to LTL). *)

Require Import FSets.
Require Import Coqlib Ordered Maps Errors Integers Floats.
Require Import AST Linking Lattice Kildall.
Require Import Values Memory Globalenvs Events Smallstep.
Require Archi.
Require Import Op Registers RTL Locations Conventions RTLtyping LTL.
Require Import Allocation.


Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        Op_fp RTL_local RTLtyping_local LTL_local allocation.

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.

Definition match_cu (scu: RTL_comp_unit) (tcu: LTL_comp_unit) :=
  match_comp_unit_gen (fun f tf => transf_fundef f = OK tf) eq scu tcu.

Lemma transf_program_match:
  forall scu tcu, transf_program scu = OK tcu -> match_cu scu tcu.
Proof.
  intros. eapply match_transform_partial_cunit; eauto.
Qed.

(** * Soundness of structural checks *)


Definition expand_move (m: move) : instruction :=
  match m with
  | (R src, R dst) => Lop Omove (src::nil) dst
  | (S sl ofs ty, R dst) => Lgetstack sl ofs ty dst
  | (R src, S sl ofs ty) => Lsetstack src sl ofs ty
  | (S _ _ _, S _ _ _) => Lreturn    (**r should never happen *)
  end.

Definition expand_moves (mv: moves) (k: bblock) : bblock :=
  List.map expand_move mv ++ k.

Definition wf_move (m: move) : Prop :=
  match m with
  | (S _ _ _, S _ _ _) => False
  | _ => True
  end.

Definition wf_moves (mv: moves) : Prop :=
  List.Forall wf_move mv.

Inductive expand_block_shape: block_shape -> RTL.instruction -> LTL.bblock -> Prop :=
  | ebs_nop: forall mv s k,
      wf_moves mv ->
      expand_block_shape (BSnop mv s)
                         (Inop s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_move: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSmove src dst mv s)
                         (Iop Omove (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_makelong: forall src1 src2 dst mv s k,
      wf_moves mv -> Archi.splitlong = true ->
      expand_block_shape (BSmakelong src1 src2 dst mv s)
                         (Iop Omakelong (src1 :: src2 :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_lowlong: forall src dst mv s k,
      wf_moves mv -> Archi.splitlong = true ->
      expand_block_shape (BSlowlong src dst mv s)
                         (Iop Olowlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_highlong: forall src dst mv s k,
      wf_moves mv -> Archi.splitlong = true ->
      expand_block_shape (BShighlong src dst mv s)
                         (Iop Ohighlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_op: forall op args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSop op args res mv1 args' res' mv2 s)
                         (Iop op args res s)
                         (expand_moves mv1
                           (Lop op args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_op_dead: forall op args res mv s k,
      wf_moves mv ->
      expand_block_shape (BSopdead op args res mv s)
                         (Iop op args res s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_load: forall chunk addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSload chunk addr args dst mv1 args' dst' mv2 s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv1
                           (Lload chunk addr args' dst' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2: forall addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s k,
      wf_moves mv1 -> wf_moves mv2 -> wf_moves mv3 ->
      Archi.splitlong = true -> offset_addressing addr 4 = Some addr2 ->
      expand_block_shape (BSload2 addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args1' dst1' ::
                           expand_moves mv2
                             (Lload Mint32 addr2 args2' dst2' ::
                              expand_moves mv3 (Lbranch s :: k))))
  | ebs_load2_1: forall addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      Archi.splitlong = true -> 
      expand_block_shape (BSload2_1 addr args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2_2: forall addr addr2 args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      Archi.splitlong = true -> offset_addressing addr 4 = Some addr2 ->
      expand_block_shape (BSload2_2 addr addr2 args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr2 args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load_dead: forall chunk addr args dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSloaddead chunk addr args dst mv s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_store: forall chunk addr args src mv1 args' src' s k,
      wf_moves mv1 ->
      expand_block_shape (BSstore chunk addr args src mv1 args' src' s)
                         (Istore chunk addr args src s)
                         (expand_moves mv1
                           (Lstore chunk addr args' src' :: Lbranch s :: k))
  | ebs_store2: forall addr addr2 args src mv1 args1' src1' mv2 args2' src2' s k,
      wf_moves mv1 -> wf_moves mv2 ->
      Archi.splitlong = true -> offset_addressing addr 4 = Some addr2 ->
      expand_block_shape (BSstore2 addr addr2 args src mv1 args1' src1' mv2 args2' src2' s)
                         (Istore Mint64 addr args src s)
                         (expand_moves mv1
                           (Lstore Mint32 addr args1' src1' ::
                            expand_moves mv2
                             (Lstore Mint32 addr2 args2' src2' ::
                              Lbranch s :: k)))
  | ebs_call: forall sg ros args res mv1 ros' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BScall sg ros args res mv1 ros' mv2 s)
                         (Icall sg ros args res s)
                         (expand_moves mv1
                           (Lcall sg ros' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_tailcall: forall sg ros args mv ros' k,
      wf_moves mv ->
      expand_block_shape (BStailcall sg ros args mv ros')
                         (Itailcall sg ros args)
                         (expand_moves mv (Ltailcall sg ros' :: k))
  | ebs_builtin: forall ef args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSbuiltin ef args res mv1 args' res' mv2 s)
                         (Ibuiltin ef args res s)
                         (expand_moves mv1
                           (Lbuiltin ef args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_cond: forall cond args mv args' s1 s2 k,
      wf_moves mv ->
      expand_block_shape (BScond cond args mv args' s1 s2)
                         (Icond cond args s1 s2)
                         (expand_moves mv (Lcond cond args' s1 s2 :: k))
  | ebs_jumptable: forall arg mv arg' tbl k,
      wf_moves mv ->
      expand_block_shape (BSjumptable arg mv arg' tbl)
                         (Ijumptable arg tbl)
                         (expand_moves mv (Ljumptable arg' tbl :: k))
  | ebs_return: forall optarg mv k,
      wf_moves mv ->
      expand_block_shape (BSreturn optarg mv)
                         (Ireturn optarg)
                         (expand_moves mv (Lreturn :: k)).

Ltac MonadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some _ |- _ ] =>
        destruct x; [MonadInv|discriminate]
  | [ H: match negb (proj_sumbool ?x) with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match negb ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with (_, _) => _ end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; MonadInv
  | [ H: Some _ = Some _ |- _ ] =>
        inv H; MonadInv
  | [ H: None = Some _ |- _ ] =>
        discriminate
  | _ =>
        idtac
  end.

Remark expand_moves_cons:
  forall m accu b,
  expand_moves (rev (m :: accu)) b = expand_moves (rev accu) (expand_move m :: b).
Proof.
  unfold expand_moves; intros. simpl. rewrite map_app. rewrite app_ass. auto.
Qed.

Lemma extract_moves_sound:
  forall b mv b',
  extract_moves nil b = (mv, b') ->
  wf_moves mv /\ b = expand_moves mv b'.
Proof.
  assert (BASE:
      forall accu b,
      wf_moves accu ->
      wf_moves (List.rev accu) /\ expand_moves (List.rev accu) b = expand_moves (List.rev accu) b).
   { intros; split; auto. unfold wf_moves in *; rewrite Forall_forall in *.
     intros. apply H. rewrite <- in_rev in H0; auto. }

  assert (IND: forall b accu mv b',
          extract_moves accu b = (mv, b') ->
          wf_moves accu ->
          wf_moves mv /\ expand_moves (List.rev accu) b = expand_moves mv b').
  { induction b; simpl; intros.
  - inv H. auto.
  - destruct a; try (inv H; apply BASE; auto; fail).
  + destruct (is_move_operation op args) as [arg|] eqn:E.
    exploit is_move_operation_correct; eauto. intros [A B]; subst.
    (* reg-reg move *)
    exploit IHb; eauto. constructor; auto. exact I. rewrite expand_moves_cons; auto.
    inv H; apply BASE; auto.
  + (* stack-reg move *)
    exploit IHb; eauto. constructor; auto. exact I. rewrite expand_moves_cons; auto.
  + (* reg-stack move *)
    exploit IHb; eauto. constructor; auto. exact I. rewrite expand_moves_cons; auto.
  }
  intros. exploit IND; eauto. constructor. 
Qed.

Lemma check_succ_sound:
  forall s b, check_succ s b = true -> exists k, b = Lbranch s :: k.
Proof.
  intros. destruct b; simpl in H; try discriminate.
  destruct i; try discriminate.
  destruct (peq s s0); simpl in H; inv H. exists b; auto.
Qed.

Ltac UseParsingLemmas :=
  match goal with
  | [ H: extract_moves nil _ = (_, _) |- _ ] =>
      destruct (extract_moves_sound _ _ _ H); clear H; subst; UseParsingLemmas
  | [ H: check_succ _ _ = true |- _ ] =>
      try (discriminate H);
      destruct (check_succ_sound _ _ H); clear H; subst; UseParsingLemmas
  | _ => idtac
  end.

Lemma pair_instr_block_sound:
  forall i b bsh,
  pair_instr_block i b = Some bsh -> expand_block_shape bsh i b.
Proof.
  assert (OP: forall op args res s b bsh,
    pair_Iop_block op args res s b = Some bsh -> expand_block_shape bsh (Iop op args res s) b).
  {
    unfold pair_Iop_block; intros. MonadInv. destruct b0. 
    MonadInv; UseParsingLemmas.
    destruct i; MonadInv; UseParsingLemmas.
    eapply ebs_op; eauto.
    inv H0. eapply ebs_op_dead; eauto. }

  intros; destruct i; simpl in H; MonadInv; UseParsingLemmas.
- (* nop *)
  econstructor; eauto.
- (* op *)
  destruct (classify_operation o l).
+ (* move *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
+ (* makelong *)
  destruct Archi.splitlong eqn:SL; eauto.
  MonadInv; UseParsingLemmas. econstructor; eauto.
+ (* lowlong *)
  destruct Archi.splitlong eqn:SL; eauto.
  MonadInv; UseParsingLemmas. econstructor; eauto.
+ (* highlong *)
  destruct Archi.splitlong eqn:SL; eauto.
  MonadInv; UseParsingLemmas. econstructor; eauto.
+ (* other ops *)
  eauto.
- (* load *)
  destruct b0 as [ | [] b0]; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64 && Archi.splitlong) eqn:A; MonadInv; UseParsingLemmas.
  destruct b as [ | [] b]; MonadInv; UseParsingLemmas.
  InvBooleans. subst m. eapply ebs_load2; eauto.
  InvBooleans. subst m. 
  destruct (eq_addressing a addr). 
  inv H; inv H2. eapply ebs_load2_1; eauto.
  destruct (option_eq eq_addressing (offset_addressing a 4) (Some addr)).
  inv H; inv H2. eapply ebs_load2_2; eauto.
  discriminate.
  eapply ebs_load; eauto.
  inv H. eapply ebs_load_dead; eauto.
- (* store *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64 && Archi.splitlong) eqn:A; MonadInv; UseParsingLemmas.
  destruct b as [ | [] b]; MonadInv; UseParsingLemmas.
  InvBooleans. subst m. eapply ebs_store2; eauto.
  eapply ebs_store; eauto.
- (* call *)
  destruct b0 as [|[] ]; MonadInv; UseParsingLemmas. econstructor; eauto.
- (* tailcall *)
  destruct b0 as [|[] ]; MonadInv; UseParsingLemmas. econstructor; eauto.
- (* builtin *)
  destruct b1 as [|[] ]; MonadInv; UseParsingLemmas. econstructor; eauto.
- (* cond *)
  destruct b0 as [|[]]; MonadInv; UseParsingLemmas. econstructor; eauto.
- (* jumptable *)
  destruct b0 as [|[]]; MonadInv; UseParsingLemmas. econstructor; eauto.
- (* return *)
  destruct b0 as [|[]]; MonadInv; UseParsingLemmas. econstructor; eauto.
Qed.

Lemma matching_instr_block:
  forall f1 f2 pc bsh i,
  (pair_codes f1 f2)!pc = Some bsh ->
  (RTL.fn_code f1)!pc = Some i ->
  exists b, (LTL.fn_code f2)!pc = Some b /\ expand_block_shape bsh i b.
Proof.
  intros. unfold pair_codes in H. rewrite PTree.gcombine in H; auto. rewrite H0 in H.
  destruct (LTL.fn_code f2)!pc as [b|].
  exists b; split; auto. apply pair_instr_block_sound; auto.
  discriminate.
Qed.

(** * Properties of equations *)

Module ESF := FSetFacts.Facts(EqSet).
Module ESP := FSetProperties.Properties(EqSet).
Module ESD := FSetDecide.Decide(EqSet).

Definition sel_val (k: equation_kind) (v: val) : val :=
  match k with
  | Full => v
  | Low => Val.loword v
  | High => Val.hiword v
  end.

(** A set of equations [e] is satisfied in a RTL pseudoreg state [rs]
  and an LTL location state [ls] if, for every equation [r = l [k]] in [e],
  [sel_val k (rs#r)] (the [k] fragment of [r]'s value in the RTL code)
  is less defined than [ls l] (the value of [l] in the LTL code). *)

Definition satisf (rs: regset) (ls: locset) (e: eqs) : Prop :=
  forall q, EqSet.In q e -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).

Lemma empty_eqs_satisf:
  forall rs ls, satisf rs ls empty_eqs.
Proof.
  unfold empty_eqs; intros; red; intros. ESD.fsetdec.
Qed.

Lemma satisf_incr:
  forall rs ls (e1 e2: eqs),
  satisf rs ls e2 -> EqSet.Subset e1 e2 -> satisf rs ls e1.
Proof.
  unfold satisf; intros. apply H. ESD.fsetdec.
Qed.

Lemma satisf_undef_reg:
  forall rs ls e r,
  satisf rs ls e ->
  satisf (rs#r <- Vundef) ls e.
Proof.
  intros; red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r); auto.
  destruct (ekind q); simpl; auto.
Qed.

Lemma add_equation_lessdef:
  forall rs ls q e,
  satisf rs ls (add_equation q e) -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).
Proof.
  intros. apply H. unfold add_equation. simpl. apply EqSet.add_1. auto.
Qed.

Lemma add_equation_satisf:
  forall rs ls q e,
  satisf rs ls (add_equation q e) -> satisf rs ls e.
Proof.
  intros. eapply satisf_incr; eauto. unfold add_equation. simpl. ESD.fsetdec.
Qed.

Lemma add_equations_satisf:
  forall rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  auto.
  eapply add_equation_satisf; eauto.
Qed.

Lemma add_equations_lessdef:
  forall rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list (rs##rl) (reglist ls ml).
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  constructor.
  constructor; eauto.
  apply add_equation_lessdef with (e := e) (q := Eq Full a (R m)).
  eapply add_equations_satisf; eauto.
Qed.

Lemma add_equations_args_satisf:
  forall rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); intros.
- inv H; auto.
- eapply add_equation_satisf; eauto.
- eapply add_equation_satisf. eapply add_equation_satisf. eauto.
- congruence.
- congruence.
Qed.

Lemma val_longofwords_eq:
  forall v,
  Val.has_type v Tlong -> Archi.splitlong = true ->
  Val.longofwords (Val.hiword v) (Val.loword v) = v.
Proof.
  intros. red in H. destruct v; try contradiction.
- reflexivity.
- simpl. rewrite Int64.ofwords_recompose. auto.
- rewrite Archi.splitlong_ptr32 in H by auto. congruence.
Qed.

Lemma add_equations_args_lessdef:
  forall rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf rs ls e' ->
  Val.has_type_list (rs##rl) tyl ->
  Val.lessdef_list (rs##rl) (map (fun p => Locmap.getpair p ls) ll).
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); simpl; intros.
- inv H; auto.
- destruct H1. constructor; auto.
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto.
  rewrite <- (val_longofwords_eq (rs#r1)) by auto. apply Val.longofwords_lessdef.
  eapply add_equation_lessdef with (q := Eq High r1 l1).
  eapply add_equation_satisf. eapply add_equations_args_satisf; eauto.
  eapply add_equation_lessdef with (q := Eq Low r1 l2).
  eapply add_equations_args_satisf; eauto.
- discriminate.
- discriminate.
Qed.

Lemma add_equation_ros_satisf:
  forall rs ls ros mos e e',
  add_equation_ros ros mos e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  unfold add_equation_ros; intros. destruct ros; destruct mos; MonadInv.
  eapply add_equation_satisf; eauto.
  auto.
Qed.

Lemma remove_equation_satisf:
  forall rs ls q e,
  satisf rs ls e -> satisf rs ls (remove_equation q e).
Proof.
  intros. eapply satisf_incr; eauto. unfold remove_equation; simpl. ESD.fsetdec.
Qed.

Lemma remove_equation_res_satisf:
  forall rs ls r l e e',
  remove_equations_res r l e = Some e' ->
  satisf rs ls e -> satisf rs ls e'.
Proof.
  intros. functional inversion H.
  apply remove_equation_satisf; auto.
  apply remove_equation_satisf. apply remove_equation_satisf; auto.
Qed.

Remark select_reg_l_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q1 q2 ->
  select_reg_l r q1 = true -> select_reg_l r q2 = true.
Proof.
  unfold select_reg_l; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]].
  red in A. zify; omega.
  rewrite <- A; auto.
Qed.

Remark select_reg_h_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q2 q1 ->
  select_reg_h r q1 = true -> select_reg_h r q2 = true.
Proof.
  unfold select_reg_h; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]].
  red in A. zify; omega.
  rewrite A; auto.
Qed.

Remark select_reg_charact:
  forall r q, select_reg_l r q = true /\ select_reg_h r q = true <-> ereg q = r.
Proof.
  unfold select_reg_l, select_reg_h; intros; split.
  rewrite ! Pos.leb_le. unfold reg; zify; omega.
  intros. rewrite H. rewrite ! Pos.leb_refl; auto.
Qed.

Lemma reg_unconstrained_sound:
  forall r e q,
  reg_unconstrained r e = true ->
  EqSet.In q e ->
  ereg q <> r.
Proof.
  unfold reg_unconstrained; intros. red; intros.
  apply select_reg_charact in H1.
  assert (EqSet.mem_between (select_reg_l r) (select_reg_h r) e = true).
  {
    apply EqSet.mem_between_2 with q; auto.
    exact (select_reg_l_monotone r).
    exact (select_reg_h_monotone r).
    tauto.
    tauto.
  }
  rewrite H2 in H; discriminate.
Qed.

Lemma reg_unconstrained_satisf:
  forall r e rs ls v,
  reg_unconstrained r e = true ->
  satisf rs ls e ->
  satisf (rs#r <- v) ls e.
Proof.
  red; intros. rewrite PMap.gso. auto. eapply reg_unconstrained_sound; eauto.
Qed.

Remark select_loc_l_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q1 q2 ->
  select_loc_l l q1 = true -> select_loc_l l q2 = true.
Proof.
  unfold select_loc_l; intros. set (lb := OrderedLoc.diff_low_bound l) in *.
  destruct H.
  red in H. subst q2; auto.
  assert (eloc q1 = eloc q2 \/ OrderedLoc.lt (eloc q1) (eloc q2)).
    red in H. tauto.
  destruct H1. rewrite <- H1; auto.
  destruct (OrderedLoc.compare (eloc q2) lb); auto.
  assert (OrderedLoc.lt (eloc q1) lb) by (eapply OrderedLoc.lt_trans; eauto).
  destruct (OrderedLoc.compare (eloc q1) lb).
  auto.
  eelim OrderedLoc.lt_not_eq; eauto.
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
Qed.

Remark select_loc_h_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q2 q1 ->
  select_loc_h l q1 = true -> select_loc_h l q2 = true.
Proof.
  unfold select_loc_h; intros. set (lb := OrderedLoc.diff_high_bound l) in *.
  destruct H.
  red in H. subst q2; auto.
  assert (eloc q2 = eloc q1 \/ OrderedLoc.lt (eloc q2) (eloc q1)).
    red in H. tauto.
  destruct H1. rewrite H1; auto.
  destruct (OrderedLoc.compare (eloc q2) lb); auto.
  assert (OrderedLoc.lt lb (eloc q1)) by (eapply OrderedLoc.lt_trans; eauto).
  destruct (OrderedLoc.compare (eloc q1) lb).
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
  eelim OrderedLoc.lt_not_eq. eexact H2. apply OrderedLoc.eq_sym; auto.
  auto.
Qed.

Remark select_loc_charact:
  forall l q,
  select_loc_l l q = false \/ select_loc_h l q = false <-> Loc.diff l (eloc q).
Proof.
  unfold select_loc_l, select_loc_h; intros; split; intros.
  apply OrderedLoc.outside_interval_diff.
  destruct H.
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)); assumption || discriminate.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)); assumption || discriminate.
  exploit OrderedLoc.diff_outside_interval. eauto.
  intros [A | A].
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)).
  auto.
  eelim OrderedLoc.lt_not_eq; eauto.
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)).
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  eelim OrderedLoc.lt_not_eq; eauto. apply OrderedLoc.eq_sym; auto.
  auto.
Qed.

Lemma loc_unconstrained_sound:
  forall l e q,
  loc_unconstrained l e = true ->
  EqSet.In q e ->
  Loc.diff l (eloc q).
Proof.
  unfold loc_unconstrained; intros.
  destruct (select_loc_l l q) eqn:SL.
  destruct (select_loc_h l q) eqn:SH.
  assert (EqSet2.mem_between (select_loc_l l) (select_loc_h l) (eqs2 e) = true).
  {
    apply EqSet2.mem_between_2 with q; auto.
    exact (select_loc_l_monotone l).
    exact (select_loc_h_monotone l).
    apply eqs_same. auto.
  }
  rewrite H1 in H; discriminate.
  apply select_loc_charact; auto.
  apply select_loc_charact; auto.
Qed.

Lemma loc_unconstrained_satisf:
  forall rs ls k r mr e v,
  let l := R mr in
  satisf rs ls (remove_equation (Eq k r l) e) ->
  loc_unconstrained (R mr) (remove_equation (Eq k r l) e) = true ->
  Val.lessdef (sel_val k rs#r) v ->
  satisf rs (Locmap.set l v ls) e.
Proof.
  intros; red; intros.
  destruct (OrderedEquation.eq_dec q (Eq k r l)).
  subst q; simpl. unfold l; rewrite Locmap.gss. auto.
  assert (EqSet.In q (remove_equation (Eq k r l) e)).
    simpl. ESD.fsetdec.
  rewrite Locmap.gso. apply H; auto. eapply loc_unconstrained_sound; eauto.
Qed.

Lemma reg_loc_unconstrained_sound:
  forall r l e q,
  reg_loc_unconstrained r l e = true ->
  EqSet.In q e ->
  ereg q <> r /\ Loc.diff l (eloc q).
Proof.
  intros. destruct (andb_prop _ _ H).
  split. eapply reg_unconstrained_sound; eauto. eapply loc_unconstrained_sound; eauto.
Qed.

Lemma parallel_assignment_satisf:
  forall k r mr e rs ls v v',
  let l := R mr in
  Val.lessdef (sel_val k v) v' ->
  reg_loc_unconstrained r (R mr) (remove_equation (Eq k r l) e) = true ->
  satisf rs ls (remove_equation (Eq k r l) e) ->
  satisf (rs#r <- v) (Locmap.set l v' ls) e.
Proof.
  intros; red; intros.
  destruct (OrderedEquation.eq_dec q (Eq k r l)).
  subst q; simpl. unfold l; rewrite Regmap.gss; rewrite Locmap.gss; auto.
  assert (EqSet.In q (remove_equation {| ekind := k; ereg := r; eloc := l |} e)).
    simpl. ESD.fsetdec.
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto. rewrite Locmap.gso; auto.
Qed.

Lemma parallel_assignment_satisf_2:
  forall rs ls res res' e e' v v',
  remove_equations_res res res' e = Some e' ->
  satisf rs ls e' ->
  reg_unconstrained res e' = true ->
  forallb (fun l => loc_unconstrained l e') (map R (regs_of_rpair res')) = true ->
  Val.lessdef v v' ->
  satisf (rs#res <- v) (Locmap.setpair res' v' ls) e.
Proof.
  intros. functional inversion H.
- (* One location *)
  subst. simpl in H2. InvBooleans. simpl. 
  apply parallel_assignment_satisf with Full; auto.
  unfold reg_loc_unconstrained. rewrite H1, H4. auto.
- (* Two 32-bit halves *)
  subst.
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := R mr2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := R mr1 |} e)) in *.
  simpl in H2. InvBooleans. simpl.
  red; intros.
  destruct (OrderedEquation.eq_dec q (Eq Low res (R mr2))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gss. 
  apply Val.loword_lessdef; auto.
  destruct (OrderedEquation.eq_dec q (Eq High res (R mr1))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gso by auto. rewrite Locmap.gss. 
  apply Val.hiword_lessdef; auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec.
  rewrite Regmap.gso. rewrite ! Locmap.gso. auto.
  eapply loc_unconstrained_sound; eauto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
Qed.

Remark in_elements_between_1:
  forall r1 s q,
  EqSet.In q (EqSet.elements_between (select_reg_l r1) (select_reg_h r1) s) <-> EqSet.In q s /\ ereg q = r1.
Proof.
  intros. rewrite EqSet.elements_between_iff, select_reg_charact. tauto.
  exact (select_reg_l_monotone r1). exact (select_reg_h_monotone r1).
Qed.

Lemma in_subst_reg:
  forall r1 r2 q (e: eqs),
  EqSet.In q e ->
  ereg q = r1 /\ EqSet.In (Eq (ekind q) r2 (eloc q)) (subst_reg r1 r2 e)
  \/ ereg q <> r1 /\ EqSet.In q (subst_reg r1 r2 e).
Proof.
  intros r1 r2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e => add_equation (Eq (ekind q) r2 (eloc q)) (remove_equation q e)).
  generalize (in_elements_between_1 r1 e0).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  intros IN_ELT.
  set (P := fun e1 e2 =>
         EqSet.In q e1 ->
         EqSet.In (Eq (ekind q) r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3.
      + subst x. ESD.fsetdec.
      + rewrite ESF.add_iff. rewrite ESF.remove_iff.
        destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto.
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - simpl. red in H2. rewrite H2 in H4. ESD.fsetdec. 
  }
  destruct (ESP.In_dec q elt).
  left. split. apply IN_ELT. auto. apply H. auto.
  right. split. red; intros. elim n. rewrite IN_ELT. auto. apply H0. auto.
Qed.

Lemma subst_reg_satisf:
  forall src dst rs ls e,
  satisf rs ls (subst_reg dst src e) ->
  satisf (rs#dst <- (rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg dst src q e H0) as [[A B] | [A B]].
  subst dst. rewrite Regmap.gss. exploit H; eauto.
  rewrite Regmap.gso; auto.
Qed.

Lemma in_subst_reg_kind:
  forall r1 k1 r2 k2 q (e: eqs),
  EqSet.In q e ->
  (ereg q, ekind q) = (r1, k1) /\ EqSet.In (Eq k2 r2 (eloc q)) (subst_reg_kind r1 k1 r2 k2 e)
  \/ EqSet.In q (subst_reg_kind r1 k1 r2 k2 e).
Proof.
  intros r1 k1 r2 k2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e =>
      if IndexedEqKind.eq (ekind q) k1
      then add_equation (Eq k2 r2 (eloc q)) (remove_equation q e)
      else e).
  generalize (in_elements_between_1 r1 e0).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  intros IN_ELT.
  set (P := fun e1 e2 =>
         EqSet.In q e1 -> ekind q = k1 ->
         EqSet.In (Eq k2 r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    intros; apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3.
      + subst x. unfold f. destruct (IndexedEqKind.eq (ekind q) k1).
        simpl. ESD.fsetdec. contradiction.
      + unfold f. destruct (IndexedEqKind.eq (ekind x) k1).
        simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff.
        destruct (OrderedEquation.eq_dec x {| ekind := k2; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto.
        auto.
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 \/ ekind q <> k1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - unfold f. red in H2. rewrite H2 in H4.
      destruct (IndexedEqKind.eq (ekind x) k1).
      simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right. split. apply H3. tauto. intuition congruence.
      apply H3. intuition auto.
  }
  destruct (ESP.In_dec q elt).
  destruct (IndexedEqKind.eq (ekind q) k1).
  left. split. f_equal. apply IN_ELT. auto. auto. apply H. auto. auto.
  right. apply H0. auto.
  right. apply H0. auto.
Qed.

Lemma subst_reg_kind_satisf_makelong:
  forall src1 src2 dst rs ls e,
  let e1 := subst_reg_kind dst High src1 Full e in
  let e2 := subst_reg_kind dst Low src2 Full e1 in
  reg_unconstrained dst e2 = true ->
  satisf rs ls e2 ->
  satisf (rs#dst <- (Val.longofwords rs#src1 rs#src2)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst High src1 Full q e H1) as [[A B] | B]; fold e1 in B.
  destruct (in_subst_reg_kind dst Low src2 Full _ e1 B) as [[C D] | D]; fold e2 in D.
  simpl in C; simpl in D. inv C.
  inversion A. rewrite H3; rewrite H4. rewrite Regmap.gss.
  apply Val.lessdef_trans with (rs#src1).
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto.
  rewrite Int64.hi_ofwords. auto.
  exploit H0. eexact D. simpl. auto.
  destruct (in_subst_reg_kind dst Low src2 Full q e1 B) as [[C D] | D]; fold e2 in D.
  inversion C. rewrite H3; rewrite H4. rewrite Regmap.gss.
  apply Val.lessdef_trans with (rs#src2).
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto.
  rewrite Int64.lo_ofwords. auto.
  exploit H0. eexact D. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Lemma subst_reg_kind_satisf_lowlong:
  forall src dst rs ls e,
  let e1 := subst_reg_kind dst Full src Low e in
  reg_unconstrained dst e1 = true ->
  satisf rs ls e1 ->
  satisf (rs#dst <- (Val.loword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src Low q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss.
  exploit H0. eexact B. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Lemma subst_reg_kind_satisf_highlong:
  forall src dst rs ls e,
  let e1 := subst_reg_kind dst Full src High e in
  reg_unconstrained dst e1 = true ->
  satisf rs ls e1 ->
  satisf (rs#dst <- (Val.hiword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src High q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss.
  exploit H0. eexact B. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Module ESF2 := FSetFacts.Facts(EqSet2).
Module ESP2 := FSetProperties.Properties(EqSet2).
Module ESD2 := FSetDecide.Decide(EqSet2).

Lemma partial_fold_ind:
  forall (A: Type) (P: EqSet2.t -> A -> Prop) f init final s,
  EqSet2.fold
         (fun q opte =>
            match opte with
            | None => None
            | Some e => f q e
            end)
         s (Some init) = Some final ->
  (forall s', EqSet2.Empty s' -> P s' init) ->
  (forall x a' a'' s' s'',
      EqSet2.In x s -> ~EqSet2.In x s' -> ESP2.Add x s' s'' ->
      f x a' = Some a'' -> P s' a' -> P s'' a'') ->
  P s final.
Proof.
  intros. 
  set (g := fun q opte => match opte with Some e => f q e | None => None end) in *.
  set (Q := fun s1 opte => match opte with None => True | Some e => P s1 e end).
  change (Q s (Some final)).
  rewrite <- H. apply ESP2.fold_rec; unfold Q, g; intros.
  - auto.
  - destruct a as [e|]; auto. destruct (f x e) as [e'|] eqn:F; auto. eapply H1; eauto.
Qed.

Lemma in_subst_loc:
  forall l1 l2 q (e e': eqs),
  EqSet.In q e ->
  subst_loc l1 l2 e = Some e' ->
  (eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e') \/ (Loc.diff l1 (eloc q) /\ EqSet.In q e').
Proof.
  unfold subst_loc; intros l1 l2 q e0 e0' IN SUBST.
  set (elt := EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e0)) in *.
  set (f := fun q0 e =>
             if Loc.eq l1 (eloc q0) then
                Some (add_equation
                     {| ekind := ekind q0; ereg := ereg q0; eloc := l2 |}
                     (remove_equation q0 e))
             else None).
  set (P := fun e1 e2 => EqSet2.In q e1 -> eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e2).
  assert (A: P elt e0').
  { eapply partial_fold_ind with (f := f) (s := elt) (final := e0'). eexact SUBST.
  - unfold P; intros. ESD2.fsetdec.
  - unfold P, f; intros. destruct (Loc.eq l1 (eloc x)); inversion H2; subst a''; clear H2.
    simpl. rewrite ESF.add_iff, ESF.remove_iff.
    apply H1 in H4; destruct H4.
    subst x; rewrite e; auto.
    apply H3 in H2; destruct H2. split. congruence. 
    destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := ereg q; eloc := l2 |}); auto.
    subst x; auto.
  }
  set (Q := fun e1 e2 => ~EqSet2.In q e1 -> EqSet.In q e2).
  assert (B: Q elt e0').
  { eapply partial_fold_ind with (f := f) (s := elt) (final := e0'). eexact SUBST.
  - unfold Q; intros. auto.
  - unfold Q, f; intros. destruct (Loc.eq l1 (eloc x)); inversion H2; subst a''; clear H2.
    simpl. rewrite ESF.add_iff, ESF.remove_iff.
    red in H1. rewrite H1 in H4. intuition auto. }
  destruct (ESP2.In_dec q elt).
  left. apply A; auto.
  right. split; auto.
  rewrite <- select_loc_charact.
  destruct (select_loc_l l1 q) eqn: LL; auto.
  destruct (select_loc_h l1 q) eqn: LH; auto.
  elim n. eapply EqSet2.elements_between_iff.
  exact (select_loc_l_monotone l1).
  exact (select_loc_h_monotone l1).
  split. apply eqs_same; auto. auto.
Qed.

Lemma loc_type_compat_charact:
  forall env l e q,
  loc_type_compat env l e = true ->
  EqSet.In q e ->
  subtype (sel_type (ekind q) (env (ereg q))) (Loc.type l) = true \/ Loc.diff l (eloc q).
Proof.
  unfold loc_type_compat; intros.
  rewrite EqSet2.for_all_between_iff in H.
  destruct (select_loc_l l q) eqn: LL.
  destruct (select_loc_h l q) eqn: LH.
  left; apply H; auto. apply eqs_same; auto.
  right. apply select_loc_charact. auto.
  right. apply select_loc_charact. auto.
  intros; subst; auto.
  exact (select_loc_l_monotone l).
  exact (select_loc_h_monotone l).
Qed.

Lemma well_typed_move_charact:
  forall env l e k r rs,
  well_typed_move env l e = true ->
  EqSet.In (Eq k r l) e ->
  wt_regset env rs ->
  match l with
  | R mr => True
  | S sl ofs ty => Val.has_type (sel_val k rs#r) ty
  end.
Proof.
  unfold well_typed_move; intros.
  destruct l as [mr | sl ofs ty].
  auto.
  exploit loc_type_compat_charact; eauto. intros [A | A].
  simpl in A. eapply Val.has_subtype; eauto.
  generalize (H1 r). destruct k; simpl; intros.
  auto.
  destruct (rs#r); exact I.
  destruct (rs#r); exact I.
  eelim Loc.diff_not_eq. eexact A. auto.
Qed.

Remark val_lessdef_normalize:
  forall v v' ty,
  Val.has_type v ty -> Val.lessdef v v' ->
  Val.lessdef v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros. inv H0. rewrite Val.load_result_same; auto. auto.
Qed.

Lemma subst_loc_satisf:
  forall env src dst rs ls e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  wt_regset env rs ->
  satisf rs ls e' ->
  satisf rs (Locmap.set dst (ls src) ls) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H2 _ B).
  apply val_lessdef_normalize; auto. apply (H2 _ B).
  rewrite Locmap.gso; auto.
Qed.

Lemma can_undef_sound:
  forall e ml q,
  can_undef ml e = true -> EqSet.In q e -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto.
  eauto.
Qed.

Lemma undef_regs_outside:
  forall ml ls l,
  Loc.notin l (map R ml) -> undef_regs ml ls l = ls l.
Proof.
  induction ml; simpl; intros. auto.
  rewrite Locmap.gso. apply IHml. tauto. apply Loc.diff_sym. tauto.
Qed.

Lemma can_undef_satisf:
  forall ml e rs ls,
  can_undef ml e = true ->
  satisf rs ls e ->
  satisf rs (undef_regs ml ls) e.
Proof.
  intros; red; intros. rewrite undef_regs_outside. eauto.
  eapply can_undef_sound; eauto.
Qed.

Lemma can_undef_except_sound:
  forall lx e ml q,
  can_undef_except lx ml e = true -> EqSet.In q e -> Loc.diff (eloc q) lx -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  destruct (orb_true_elim _ _ H2).
  apply proj_sumbool_true in e0. congruence.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto.
  eapply IHml; eauto.
Qed.

Lemma subst_loc_undef_satisf:
  forall env src dst rs ls ml e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  can_undef_except dst ml e = true ->
  wt_regset env rs ->
  satisf rs ls e' ->
  satisf rs (Locmap.set dst (ls src) (undef_regs ml ls)) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H3 _ B).
  apply val_lessdef_normalize; auto. apply (H3 _ B).
  rewrite Locmap.gso; auto. rewrite undef_regs_outside. eauto.
  eapply can_undef_except_sound; eauto. apply Loc.diff_sym; auto.
Qed.

Lemma transfer_use_def_satisf:
  forall args res args' res' und e e' rs ls,
  transfer_use_def args res args' res' und e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list rs##args (reglist ls args') /\
  (forall v v', Val.lessdef v v' ->
    satisf (rs#res <- v) (Locmap.set (R res') v' (undef_regs und ls)) e).
Proof.
  unfold transfer_use_def; intros. MonadInv.
  split. eapply add_equations_lessdef; eauto.
  intros. eapply parallel_assignment_satisf; eauto. assumption.
  eapply can_undef_satisf; eauto.
  eapply add_equations_satisf; eauto.
Qed.

Lemma add_equations_res_lessdef:
  forall r oty l e e' rs ls,
  add_equations_res r oty l e = Some e' ->
  satisf rs ls e' ->
  Val.has_type rs#r (match oty with Some ty => ty | None => Tint end) ->
  Val.lessdef rs#r (Locmap.getpair (map_rpair R l) ls).
Proof.
  intros. functional inversion H; simpl.
- subst. eapply add_equation_lessdef with (q := Eq Full r (R mr)); eauto.
- subst. rewrite <- (val_longofwords_eq rs#r) by auto. 
  apply Val.longofwords_lessdef.
  eapply add_equation_lessdef with (q := Eq High r (R mr1)).
  eapply add_equation_satisf. eauto.
  eapply add_equation_lessdef with (q := Eq Low r (R mr2)).
  eauto.
Qed.

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => is_callee_save r = true
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: locset) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

Lemma return_regs_agree_callee_save:
  forall caller callee,
  agree_callee_save caller (return_regs caller callee).
Proof.
  intros; red; intros. unfold return_regs. red in H.
  destruct l.
  rewrite H; auto. 
  destruct sl; auto || congruence.
Qed.

Lemma no_caller_saves_sound:
  forall e q,
  no_caller_saves e = true ->
  EqSet.In q e ->
  callee_save_loc (eloc q).
Proof.
  unfold no_caller_saves, callee_save_loc; intros.
  exploit EqSet.for_all_2; eauto.
  hnf. intros. simpl in H1. rewrite H1. auto.
  lazy beta. destruct (eloc q). auto. destruct sl; congruence.
Qed.

Lemma val_hiword_longofwords:
  forall v1 v2, Val.lessdef (Val.hiword (Val.longofwords v1 v2)) v1.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.hiword.
  rewrite Int64.hi_ofwords. auto.
Qed.

Lemma val_loword_longofwords:
  forall v1 v2, Val.lessdef (Val.loword (Val.longofwords v1 v2)) v2.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.loword.
  rewrite Int64.lo_ofwords. auto.
Qed.

Lemma function_return_satisf:
  forall rs ls_before ls_after res res' sg e e' v,
  res' = loc_result sg ->
  remove_equations_res res res' e = Some e' ->
  satisf rs ls_before e' ->
  forallb (fun l => reg_loc_unconstrained res l e') (map R (regs_of_rpair res')) = true ->
  no_caller_saves e' = true ->
  Val.lessdef v (Locmap.getpair (map_rpair R res') ls_after) ->
  agree_callee_save ls_before ls_after ->
  satisf (rs#res <- v) ls_after e.
Proof.
  intros; red; intros.
  functional inversion H0.
- (* One register *)
  subst. rewrite <- H8 in *. simpl in *. InvBooleans.
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := R mr |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res (R mr))).
  subst q; simpl. rewrite Regmap.gss; auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec.
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto.
- (* Two 32-bit halves *)
  subst. rewrite <- H9 in *. simpl in *. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := R mr2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := R mr1 |} e)) in *.
  InvBooleans.
  destruct (OrderedEquation.eq_dec q (Eq Low res (R mr2))).
  subst q; simpl. rewrite Regmap.gss.
  eapply Val.lessdef_trans. apply Val.loword_lessdef. eauto. apply val_loword_longofwords.
  destruct (OrderedEquation.eq_dec q (Eq High res (R mr1))).
  subst q; simpl. rewrite Regmap.gss.
  eapply Val.lessdef_trans. apply Val.hiword_lessdef. eauto. apply val_hiword_longofwords.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec.
  exploit reg_loc_unconstrained_sound. eexact H. eauto. intros [A B].
  exploit reg_loc_unconstrained_sound. eexact H2. eauto. intros [C D].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto.
Qed.

Lemma compat_left_sound:
  forall r l e q,
  compat_left r l e = true -> EqSet.In q e -> ereg q = r -> ekind q = Full /\ eloc q = l.
Proof.
  unfold compat_left; intros.
  rewrite EqSet.for_all_between_iff in H.
  apply select_reg_charact in H1. destruct H1.
  exploit H; eauto. intros.
  destruct (ekind q); try discriminate.
  destruct (Loc.eq l (eloc q)); try discriminate.
  auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma compat_left2_sound:
  forall r l1 l2 e q,
  compat_left2 r l1 l2 e = true -> EqSet.In q e -> ereg q = r ->
  (ekind q = High /\ eloc q = l1) \/ (ekind q = Low /\ eloc q = l2).
Proof.
  unfold compat_left2; intros.
  rewrite EqSet.for_all_between_iff in H.
  apply select_reg_charact in H1. destruct H1.
  exploit H; eauto. intros.
  destruct (ekind q); try discriminate.
  InvBooleans. auto.
  InvBooleans. auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma compat_entry_satisf:
  forall rl ll e,
  compat_entry rl ll e = true ->
  forall vl ls,
  Val.lessdef_list vl (map (fun p => Locmap.getpair p ls) ll) ->
  satisf (init_regs vl rl) ls e.
Proof.
  intros until e. functional induction (compat_entry rl ll e); intros.
- (* no params *)
  simpl. red; intros. rewrite Regmap.gi. destruct (ekind q); simpl; auto.
- (* a param in a single location *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1).
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param split across two locations *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1).
  exploit compat_left2_sound; eauto.
  intros [[A B] | [A B]]; rewrite A; rewrite B; simpl.
  apply Val.lessdef_trans with (Val.hiword (Val.longofwords (ls l1) (ls l2))).
  apply Val.hiword_lessdef; auto. apply val_hiword_longofwords.
  apply Val.lessdef_trans with (Val.loword (Val.longofwords (ls l1) (ls l2))).
  apply Val.loword_lessdef; auto. apply val_loword_longofwords.
  eapply IHb; eauto.
- (* error case *)
  discriminate.
Qed.

Lemma call_regs_param_values:
  forall sg ls,
  map (fun p => Locmap.getpair p (call_regs ls)) (loc_parameters sg)
  = map (fun p => Locmap.getpair p ls) (loc_arguments sg).
Proof.
  intros. unfold loc_parameters. rewrite list_map_compose.
  apply list_map_exten; intros. symmetry.
  assert (A: forall l, loc_argument_acceptable l -> call_regs ls (parameter_of_argument l) = ls l).
  { destruct l as [r | [] ofs ty]; simpl; auto; contradiction. }
  exploit loc_arguments_acceptable; eauto. destruct x; simpl; intros.
- auto.
- destruct H0; f_equal; auto.
Qed.

Lemma return_regs_arg_values:
  forall sg ls1 ls2,
  tailcall_is_possible sg = true ->
  map (fun p => Locmap.getpair p (return_regs ls1 ls2)) (loc_arguments sg) 
  = map (fun p => Locmap.getpair p ls2) (loc_arguments sg).
Proof.
  intros.
  apply tailcall_is_possible_correct in H.
  apply list_map_exten; intros.
  apply Locmap.getpair_exten; intros.
  assert (In l (regs_of_rpairs (loc_arguments sg))) by (eapply in_regs_of_rpairs; eauto).
  exploit loc_arguments_acceptable_2; eauto. exploit H; eauto. 
  destruct l; simpl; intros; try contradiction. rewrite H4; auto.
Qed.

Lemma find_function_tailcall:
  forall tge ros ls1 ls2,
  ros_compatible_tailcall ros = true ->
  find_function tge ros (return_regs ls1 ls2) = find_function tge ros ls2.
Proof.
  unfold ros_compatible_tailcall, find_function; intros.
  destruct ros as [r|id]; auto.
  unfold return_regs. destruct (is_callee_save r). discriminate. auto.
Qed.

Lemma loadv_int64_split:
  forall m a v,
  Mem.loadv Mint64 m a = Some v -> Archi.splitlong = true ->
  exists v1 v2,
     Mem.loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ Mem.loadv Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef (Val.hiword v) v1
  /\ Val.lessdef (Val.loword v) v2.
Proof.
  intros. apply Archi.splitlong_ptr32 in H0. 
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & A & B & C).
  exists v1, v2. split; auto. split; auto.
  inv C; auto. destruct v1, v2; simpl; auto.
  rewrite Int64.hi_ofwords, Int64.lo_ofwords; auto.
Qed.

Lemma add_equations_builtin_arg_satisf:
  forall env rs ls arg arg' e e',
  add_equations_builtin_arg env arg arg' e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction arg; destruct arg'; simpl; intros; MonadInv; eauto.
  eapply add_equation_satisf; eauto.
  destruct arg'1; MonadInv. destruct arg'2; MonadInv. eauto using add_equation_satisf.
Qed.

Lemma add_equations_builtin_arg_lessdef:
  forall env (ge: RTL.genv) sp rs ls m arg v,
  eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  forall e e' arg',
  add_equations_builtin_arg env arg arg' e = Some e' ->
  satisf rs ls e' ->
  wt_regset env rs ->
  exists v', eval_builtin_arg ge ls sp m arg' v' /\ Val.lessdef v v'.
Proof.
  induction 1; simpl; intros e e' arg' AE SAT WT; destruct arg'; MonadInv.
- exploit add_equation_lessdef; eauto. simpl; intros.
  exists (ls x0); auto with barg.
- destruct arg'1; MonadInv. destruct arg'2; MonadInv.
  exploit add_equation_lessdef. eauto. simpl; intros LD1.
  exploit add_equation_lessdef. eapply add_equation_satisf. eauto. simpl; intros LD2.
  exists (Val.longofwords (ls x0) (ls x1)); split; auto with barg.
  rewrite <- (val_longofwords_eq rs#x). apply Val.longofwords_lessdef; auto.
  rewrite <- e0; apply WT.
  assumption.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit IHeval_builtin_arg1; eauto. eapply add_equations_builtin_arg_satisf; eauto.
  intros (v1 & A & B).
  exploit IHeval_builtin_arg2; eauto. intros (v2 & C & D).
  exists (Val.longofwords v1 v2); split; auto with barg. apply Val.longofwords_lessdef; auto.
Qed.

Lemma add_equations_builtin_args_satisf:
  forall env rs ls arg arg' e e',
  add_equations_builtin_args env arg arg' e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction arg; destruct arg'; simpl; intros; MonadInv; eauto using add_equations_builtin_arg_satisf.
Qed.

Lemma add_equations_builtin_args_lessdef:
  forall env (ge: RTL.genv) sp rs ls m tm arg vl,
  eval_builtin_args ge (fun r => rs#r) sp m arg vl ->
  forall arg' e e',
  add_equations_builtin_args env arg arg' e = Some e' ->
  satisf rs ls e' ->
  wt_regset env rs ->
  Mem.extends m tm ->
  exists vl', eval_builtin_args ge ls sp tm arg' vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 1; simpl; intros; destruct arg'; MonadInv.
- exists (@nil val); split; constructor.
- exploit IHlist_forall2; eauto. intros (vl' & A & B).
  exploit add_equations_builtin_arg_lessdef; eauto.
  eapply add_equations_builtin_args_satisf; eauto. intros (v1' & C & D).
  exploit (@eval_builtin_arg_lessdef _ ge ls ls); eauto. intros (v1'' & E & F).
  exists (v1'' :: vl'); split; constructor; auto. eapply Val.lessdef_trans; eauto.
Qed.

Lemma add_equations_debug_args_satisf:
  forall env rs ls arg arg' e e',
  add_equations_debug_args env arg arg' e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction arg; destruct arg'; simpl; intros; MonadInv; auto.
  destruct (add_equations_builtin_arg env a b e) as [e1|] eqn:A;
  eauto using add_equations_builtin_arg_satisf.
Qed.

Lemma add_equations_debug_args_eval:
  forall env (ge: RTL.genv) sp rs ls m tm arg vl,
  eval_builtin_args ge (fun r => rs#r) sp m arg vl ->
  forall arg' e e',
  add_equations_debug_args env arg arg' e = Some e' ->
  satisf rs ls e' ->
  wt_regset env rs ->
  Mem.extends m tm ->
  exists vl', eval_builtin_args ge ls sp tm arg' vl'.
Proof.
  induction 1; simpl; intros; destruct arg'; MonadInv.
- exists (@nil val); constructor.
- exists (@nil val); constructor.
- destruct (add_equations_builtin_arg env a1 b e) as [e1|] eqn:A.
+ exploit IHlist_forall2; eauto. intros (vl' & B).
  exploit add_equations_builtin_arg_lessdef; eauto.
  eapply add_equations_debug_args_satisf; eauto. intros (v1' & C & D).
  exploit (@eval_builtin_arg_lessdef _ ge ls ls); eauto. intros (v1'' & E & F).
  exists (v1'' :: vl'); constructor; auto.
+ eauto.
Qed.

Lemma add_equations_builtin_eval:
  forall ef env args args' e1 e2 m1 m1' rs ls (ge: RTL.genv) sp vargs t vres m2,
  wt_regset env rs ->
  match ef with
  | EF_debug _ _ _ => add_equations_debug_args env args args' e1
  | _              => add_equations_builtin_args env args args' e1
  end = Some e2 ->
  Mem.extends m1 m1' ->
  satisf rs ls e2 ->
  eval_builtin_args ge (fun r => rs # r) sp m1 args vargs ->
  external_call ef ge vargs m1 t vres m2 ->
  satisf rs ls e1 /\
  exists vargs' vres' m2',
     eval_builtin_args ge ls sp m1' args' vargs'
  /\ external_call ef ge vargs' m1' t vres' m2'
  /\ Val.lessdef vres vres'
  /\ Mem.extends m2 m2'.
Proof.
  intros.
  assert (DEFAULT: add_equations_builtin_args env args args' e1 = Some e2 ->
    satisf rs ls e1 /\
    exists vargs' vres' m2',
       eval_builtin_args ge ls sp m1' args' vargs'
    /\ external_call ef ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2').
  {
    intros. split. eapply add_equations_builtin_args_satisf; eauto.
    exploit add_equations_builtin_args_lessdef; eauto.
    intros (vargs' & A & B).
    exploit external_call_mem_extends; eauto.
    intros (vres' & m2' & C & D & E & F).
    exists vargs', vres', m2'; auto.
  }
  destruct ef; auto.
  split. eapply add_equations_debug_args_satisf; eauto.
  exploit add_equations_debug_args_eval; eauto.
  intros (vargs' & A).
  simpl in H4; inv H4.
  exists vargs', Vundef, m1'. intuition auto. simpl. constructor.
Qed.

Lemma parallel_set_builtin_res_satisf:
  forall env res res' e0 e1 rs ls v v',
  remove_equations_builtin_res env res res' e0 = Some e1 ->
  forallb (fun r => reg_unconstrained r e1) (params_of_builtin_res res) = true ->
  forallb (fun mr => loc_unconstrained (R mr) e1) (params_of_builtin_res res') = true ->
  satisf rs ls e1 ->
  Val.lessdef v v' ->
  satisf (regmap_setres res v rs) (Locmap.setres res' v' ls) e0.
Proof.
  intros. rewrite forallb_forall in *.
  destruct res, res'; simpl in *; inv H.
- apply parallel_assignment_satisf with (k := Full); auto.
  unfold reg_loc_unconstrained. rewrite H0 by auto. rewrite H1 by auto. auto.
- destruct res'1; try discriminate. destruct res'2; try discriminate.
  rename x0 into hi; rename x1 into lo. MonadInv. destruct (mreg_eq hi lo); inv H5.
  set (e' := remove_equation {| ekind := High; ereg := x; eloc := R hi |} e0) in *.
  set (e'' := remove_equation {| ekind := Low; ereg := x; eloc := R lo |} e') in *.
  simpl in *. red; intros.
  destruct (OrderedEquation.eq_dec q (Eq Low x (R lo))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gss. apply Val.loword_lessdef; auto.
  destruct (OrderedEquation.eq_dec q (Eq High x (R hi))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gso by (red; auto).
  rewrite Locmap.gss. apply Val.hiword_lessdef; auto.
  assert (EqSet.In q e'').
  { unfold e'', e', remove_equation; simpl; ESD.fsetdec. }
  rewrite Regmap.gso. rewrite ! Locmap.gso. auto.
  eapply loc_unconstrained_sound; eauto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
- auto.
Qed.

(** * Properties of the dataflow analysis *)

Lemma analyze_successors:
  forall f env bsh an pc bs s e,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ EqSet.Subset e' e.
Proof.
  unfold analyze; intros. exploit DS.fixpoint_allnodes_solution; eauto.
  rewrite H2. unfold DS.L.ge. destruct (transfer f env bsh s an#s); intros.
  exists e0; auto.
  contradiction.
Qed.

Lemma satisf_successors:
  forall f env bsh an pc bs s e rs ls,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  satisf rs ls e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ satisf rs ls e'.
Proof.
  intros. exploit analyze_successors; eauto. intros [e' [A B]].
  exists e'; split; auto. eapply satisf_incr; eauto.
Qed.

(** Inversion on [transf_function] *)

Inductive transf_function_spec (f: RTL.function) (tf: LTL.function) : Prop :=
  | transf_function_spec_intro:
      forall env an mv k e1 e2,
      wt_function f env ->
      analyze f env (pair_codes f tf) = Some an ->
      (LTL.fn_code tf)!(LTL.fn_entrypoint tf) = Some(expand_moves mv (Lbranch (RTL.fn_entrypoint f) :: k)) ->
      wf_moves mv ->
      transfer f env (pair_codes f tf) (RTL.fn_entrypoint f) an!!(RTL.fn_entrypoint f) = OK e1 ->
      track_moves env mv e1 = Some e2 ->
      compat_entry (RTL.fn_params f) (loc_parameters (fn_sig tf)) e2 = true ->
      can_undef destroyed_at_function_entry e2 = true ->
      RTL.fn_stacksize f = LTL.fn_stacksize tf ->
      RTL.fn_sig f = LTL.fn_sig tf ->
      transf_function_spec f tf.

Lemma transf_function_inv:
  forall f tf,
  transf_function f = OK tf ->
  transf_function_spec f tf.
Proof.
  unfold transf_function; intros.
  destruct (type_function f) as [env|] eqn:TY; try discriminate.
  destruct (regalloc f); try discriminate.
  destruct (check_function f f0 env) as [] eqn:?; inv H.
  unfold check_function in Heqr.
  destruct (analyze f env (pair_codes f tf)) as [an|] eqn:?; try discriminate.
  monadInv Heqr.
  destruct (check_entrypoints_aux f tf env x) as [y|] eqn:?; try discriminate.
  unfold check_entrypoints_aux, pair_entrypoints in Heqo0. MonadInv.
  exploit extract_moves_sound; eauto. intros [A B]. subst b.
  exploit check_succ_sound; eauto. intros [k EQ1]. subst b0.
  econstructor; eauto. eapply type_function_correct; eauto. congruence.
Qed.

Lemma invert_code:
  forall f env tf pc i opte e,
  wt_function f env ->
  (RTL.fn_code f)!pc = Some i ->
  transfer f env (pair_codes f tf) pc opte = OK e ->
  exists eafter, exists bsh, exists bb,
  opte = OK eafter /\
  (pair_codes f tf)!pc = Some bsh /\
  (LTL.fn_code tf)!pc = Some bb /\
  expand_block_shape bsh i bb /\
  transfer_aux f env bsh eafter = Some e /\
  wt_instr f env i.
Proof.
  intros. destruct opte as [eafter|]; simpl in H1; try discriminate. exists eafter.
  destruct (pair_codes f tf)!pc as [bsh|] eqn:?; try discriminate. exists bsh.
  exploit matching_instr_block; eauto. intros [bb [A B]].
  destruct (transfer_aux f env bsh eafter) as [e1|] eqn:?; inv H1.
  exists bb. exploit wt_instr_at; eauto.
  tauto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable scu: RTL_comp_unit.
Variable tcu: LTL_comp_unit.

Hypothesis TRANSF: match_cu scu tcu.

Variable sge sG: RTL.genv.
Variable tge tG: LTL.genv.

Hypothesis GE_INIT: RTL_IS.(init_genv_local) scu sge sG.
Hypothesis TGE_INIT: LTL_IS.(init_genv_local) tcu tge tG.
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

Lemma ge_match: ge_match_strict sge tge.
Proof. inv GE_INIT. inv TGE_INIT. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma sig_function_translated:
  forall f tf,
  transf_fundef f = OK tf ->
  LTL.funsig tf = RTL.funsig f.
Proof.
  intros; destruct f; monadInv H.
  destruct (transf_function_inv _ _ EQ). simpl; auto.
  auto.
Qed.

Lemma find_function_translated:
  forall ros rs fd ros' e e' ls,
  RTL.find_function sge ros rs = Some fd ->
  add_equation_ros ros ros' e = Some e' ->
  satisf rs ls e' ->
  exists tfd,
  LTL.find_function tge ros' ls = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  unfold RTL.find_function, LTL.find_function; intros.
  destruct ros as [r|id]; destruct ros' as [r'|id']; simpl in H0; MonadInv.
  (* two regs *)
  exploit add_equation_lessdef; eauto. intros LD. inv LD.
  eapply functions_translated; eauto.
  rewrite <- H2 in H. simpl in H. congruence.
  (* two symbols *)
  rewrite symbols_preserved. rewrite Heqo.
  eapply function_ptr_translated; eauto.
Qed.

Lemma exec_moves:
  forall mv env rs s f sp bb m e e' ls sigres0,
  track_moves env mv e = Some e' ->
  wf_moves mv ->
  satisf rs ls e' ->
  wt_regset env rs ->
  exists ls',
    star (step tge) (Core_Block s f sp (expand_moves mv bb) ls sigres0) m
         empfp (Core_Block s f sp bb ls' sigres0) m
    /\ satisf rs ls' e.
Proof.
Opaque destroyed_by_op.
  induction mv; simpl; intros.
  (* base *)
- unfold expand_moves; simpl. inv H. exists ls; split. apply star_refl. auto.
  (* step *)
- assert (wf_moves mv) by (inv H0; auto).
  destruct a as (src, dst); unfold expand_moves; simpl; MonadInv.
  destruct src as [rsrc | ssrc]; destruct dst as [rdst | sdst].
* (* reg-reg *)
  exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto.
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto.
  econstructor. simpl. eauto. simpl. eauto. auto. auto.
* (* reg->stack *)
  exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto.
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto.
  econstructor. simpl. eauto. auto.
* (* stack->reg *)
  simpl in Heqb. exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto.
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto.
  econstructor. auto. auto.
* (* stack->stack *)
  inv H0. simpl in H6. contradiction.
Qed.

(** The simulation relation *)

Inductive match_stackframes (sigres0: option typ) : list RTL.stackframe -> list LTL.stackframe -> signature -> Prop :=
| match_stackframes_nil:
    forall sg,
      sg.(sig_res) = sigres0 ->
      match_stackframes sigres0 nil nil sg
| match_stackframes_cons:
    forall res f sp pc rs s tf bb ls ts sg an e env 
      (STACKS: match_stackframes sigres0 s ts (fn_sig tf))
      (FUN: transf_function f = OK tf)
      (ANL: analyze f env (pair_codes f tf) = Some an)
      (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
      (WTF: wt_function f env)
      (WTRS: wt_regset env rs)
      (WTRES: env res = proj_sig_res sg)
      (STEPS: forall v ls1 m,
          Val.lessdef v (Locmap.getpair (map_rpair R (loc_result sg)) ls1) ->
          Val.has_type v (env res) ->
          agree_callee_save ls ls1 ->
          exists ls2,
            star (step tge) (Core_Block ts tf sp bb ls1 sigres0) m
                 empfp (Core_State ts tf sp pc ls2 sigres0) m
            /\ satisf (rs#res <- v) ls2 e),
      match_stackframes sigres0
                        (RTL.Stackframe res f sp pc rs :: s)
                        (LTL.Stackframe tf sp ls bb :: ts)
                        sg.

Inductive  MATCH_STATE:
  bool -> nat -> Injections.Mu -> FP.t -> FP.t ->
  RTL_local.core * mem -> LTL_local.core * mem -> Prop :=
| match_states_intro:
    forall mu fp fp' s f sp pc rs m ts tf ls m' an e env sigres0 
      (STACKS: match_stackframes sigres0 s ts (fn_sig tf))
      (FUN: transf_function f = OK tf)
      (ANL: analyze f env (pair_codes f tf) = Some an)
      (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
      (SAT: satisf rs ls e)
      (MEM: Mem.extends m m')
      (WTF: wt_function f env)
      (WTRS: wt_regset env rs)
      (** NEW *)
      (WTC: wt_core (RTL_local.Core_State s f sp pc rs))
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp'),
      MATCH_STATE true 0%nat mu fp fp'
                  (RTL_local.Core_State s f sp pc rs, m)
                  (LTL_local.Core_State ts tf sp pc ls sigres0, m')
| match_states_call:
    forall b mu fp fp' s f args m ts tf ls sigres0 m'
      (STACKS: match_stackframes sigres0 s ts (funsig tf))
      (FUN: transf_fundef f = OK tf)
      (ARGS: Val.lessdef_list args (map (fun p => Locmap.getpair p ls) (loc_arguments (funsig tf))))
      (AG: agree_callee_save (parent_locset ts) ls)
      (MEM: Mem.extends m m')
      (WTARGS: Val.has_type_list args (sig_args (funsig tf)))
      (** NEW *)
      (WTC: wt_core (RTL_local.Core_Callstate s f args))
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp'),
      MATCH_STATE b 0%nat mu fp fp'
                  (RTL_local.Core_Callstate s f args, m)
                  (LTL_local.Core_Callstate ts tf ls sigres0, m')
| match_states_return:
    forall mu fp fp' s res m ts ls m' sg sigres0
      (STACKS: match_stackframes sigres0 s ts sg)
      (RES: Val.lessdef res (Locmap.getpair (map_rpair R (loc_result sg)) ls))
      (AG: agree_callee_save (parent_locset ts) ls)
      (MEM: Mem.extends m m')
      (WTRES: Val.has_type res (proj_sig_res sg))
      (** NEW *)
      (WTC: wt_core (RTL_local.Core_Returnstate s res))
      (SVALID: forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b)
      (TVALID: forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b)
      (AGMU: proper_mu sge tge inject_id mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp'),
      MATCH_STATE true 0%nat mu fp fp'
                  (RTL_local.Core_Returnstate s res, m)
                  (LTL_local.Core_Returnstate ts ls sigres0, m').

Lemma match_stackframes_change_sig:
  forall sigres0 s ts sg sg',
  match_stackframes sigres0 s ts sg ->
  sg'.(sig_res) = sg.(sig_res) ->
  match_stackframes sigres0 s ts sg'.
Proof.
  intros. inv H.
  constructor. congruence.
  econstructor; eauto.
  unfold proj_sig_res in *. rewrite H0; auto.
  intros. rewrite (loc_result_exten sg' sg) in H by auto. eauto.
Qed.

Ltac UseShape :=
  match goal with
  | [ WT: wt_function _ _, CODE: (RTL.fn_code _)!_ = Some _, EQ: transfer _ _ _ _ _ = OK _ |- _ ] =>
      destruct (invert_code _ _ _ _ _ _ _ WT CODE EQ) as (eafter & bsh & bb & AFTER & BSH & TCODE & EBS & TR & WTI);
      inv EBS; unfold transfer_aux in TR; MonadInv
  end.

Remark addressing_not_long:
  forall env f addr args dst s r,
  wt_instr f env (Iload Mint64 addr args dst s) -> Archi.splitlong = true ->
  In r args -> r <> dst.
Proof.
  intros. inv H.
  assert (A: forall ty, In ty (type_of_addressing addr) -> ty = Tptr).
  { intros. destruct addr; simpl in H; intuition. }
  assert (B: In (env r) (type_of_addressing addr)).
  { rewrite <- H5. apply in_map; auto. }
  assert (C: env r = Tint).
  { apply A in B. rewrite B. unfold Tptr. rewrite Archi.splitlong_ptr32 by auto. auto. }    
  red; intros; subst r. rewrite C in H8; discriminate.
Qed.

Lemma load_int64_fp_split:
  forall b i mu,
    proper_mu sge tge inject_id mu ->
    (align_chunk Mint64 | Ptrofs.unsigned i) ->
    Archi.ptr64 = false ->
    Injections.FPMatch' mu (FMemOpFP.load_fp Mint64 b (Ptrofs.unsigned i))
                        (FP.union (FMemOpFP.load_fp Mint32 b (Ptrofs.unsigned i))
                                  (FMemOpFP.load_fp Mint32 b (Ptrofs.unsigned
                                                                (Ptrofs.add i (Ptrofs.of_int (Int.repr 4)))))).
Proof.
  clear. intros b i mu H ALIGN ARCHI.
  apply Injections.fp_match_union_T'; unfold FMemOpFP.load_fp; simpl;
    constructor; simpl; try (apply FMemOpFP.emp_loc_match);
      unfold FP.ge_reads,FP.ge_writes; simpl; repeat rewrite Locs.locs_union_emp;
        inv H; constructor; intros;
          apply FMemOpFP.range_locset_loc in H0.
  eapply Bset.inj_range in H; [|inv proper_mu_inject; eauto].
  destruct H. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H. eauto. inversion 1; subst.
  eexists; intuition. unfold Bset.inject_block. eauto. apply FMemOpFP.range_locset_loc; intuition.
  eapply Bset.inj_range in H; [|inv proper_mu_inject; eauto].
  destruct H. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H. eauto. inversion 1; subst.
  eexists; intuition. unfold Bset.inject_block. eauto. apply FMemOpFP.range_locset_loc.
  split; auto.
  generalize ALIGN ARCHI H0 H4. simpl. clear; intros.
  apply Mem.addressing_int64_split in ALIGN; auto. rewrite ALIGN in *. omega.
Qed.

Lemma store_int64_fp_split:
  forall b i mu,
    proper_mu sge tge inject_id mu ->
    (align_chunk Mint64 | Ptrofs.unsigned i) ->
    Archi.ptr64 = false ->
    Injections.FPMatch' mu (FMemOpFP.store_fp Mint64 b (Ptrofs.unsigned i))
                        (FP.union (FMemOpFP.store_fp Mint32 b (Ptrofs.unsigned i))
                                  (FMemOpFP.store_fp Mint32 b (Ptrofs.unsigned
                                                                (Ptrofs.add i (Ptrofs.of_int (Int.repr 4)))))).
Proof.
  clear. intros b i mu H ALIGN ARCHI.
  apply Injections.fp_match_union_T'; unfold FMemOpFP.load_fp; simpl;
    constructor; simpl; try (apply FMemOpFP.emp_loc_match);
      unfold FP.ge_reads,FP.ge_writes; simpl; repeat rewrite Locs.locs_union_emp;
        inv H; constructor; intros;
          apply FMemOpFP.range_locset_loc in H0.
  eapply Bset.inj_range in H; [|inv proper_mu_inject; eauto].
  destruct H. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H. eauto. inversion 1; subst.
  eexists; intuition. unfold Bset.inject_block. eauto. apply FMemOpFP.range_locset_loc; intuition.
  eapply Bset.inj_range in H; [|inv proper_mu_inject; eauto].
  destruct H. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H. eauto. inversion 1; subst.
  eexists; intuition. unfold Bset.inject_block. eauto. apply FMemOpFP.range_locset_loc.
  split; auto.
  generalize ALIGN ARCHI H0 H4. simpl. clear; intros.
  apply Mem.addressing_int64_split in ALIGN; auto. rewrite ALIGN in *. omega.
Qed.

Lemma add_equations_builtin_arg_fp_lessdef:
  forall env (ge: RTL.genv) sp rs ls arg fp,
    MemOpFP.eval_builtin_arg_fp ge (fun r => rs#r) sp arg fp ->
    forall e e' arg',
      add_equations_builtin_arg env arg arg' e = Some e' ->
      satisf rs ls e' ->
      wt_regset env rs ->
      MemOpFP.eval_builtin_arg_fp ge ls sp arg' fp.
Proof.
  induction 1; simpl; intros e e' arg' AE SAT WT; destruct arg'; MonadInv; try (econstructor; eauto; fail).
  destruct arg'1, arg'2; try discriminate. repeat econstructor; eauto.
  exploit IHeval_builtin_arg_fp1; eauto. eapply add_equations_builtin_arg_satisf; eauto.
  exploit IHeval_builtin_arg_fp2; eauto. intros. econstructor; eauto.
Qed.
Lemma add_equations_builtin_args_fp_lessdef:
  forall env (ge: RTL.genv) sp rs ls arg fp,
    MemOpFP.eval_builtin_args_fp ge (fun r => rs#r) sp arg fp ->
    forall arg' e e',
      add_equations_builtin_args env arg arg' e = Some e' ->
      satisf rs ls e' ->
      wt_regset env rs ->
      MemOpFP.eval_builtin_args_fp ge ls sp arg' fp.
Proof.
  clear. induction 1; simpl; intros; destruct arg'; MonadInv.
  - constructor.
  - exploit IHeval_builtin_args_fp; eauto. intros TLFP.
    econstructor; eauto. eapply add_equations_builtin_arg_fp_lessdef; eauto.
    eapply add_equations_builtin_args_satisf; eauto.
Qed.

Lemma callee_save_loc_arg_diff:
  forall l l', callee_save_loc l ->
          loc_argument_acceptable l' ->
          Loc.diff l' l.
Proof.
  clear. intros. 
  destruct l, l'; try contradiction; try (red; auto). 
  destruct r0, r; try congruence. destruct sl, sl0; try contradiction; auto.
Qed.

Ltac resolvfp:=
  match goal with
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: Injections.FPMatch' ?mu ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; [exact H| resolvfp]
  | _ => idtac
  end.

Ltac eresolvfp:= resolvfp; eauto.

Ltac PLUS:= do 3 eexists; split.
Ltac FP:= match goal with |- ?P /\ _ => assert P; [eresolvfp|] end.

Lemma wt_scu: wt_cu scu.
Proof.
  red; intros. 
  exploit list_forall2_in_left. eexact (proj1 TRANSF). eauto. 
  intros ([i' gd] & A & B & C). simpl in *; subst i'.
  inv C. destruct f; simpl in *.
- monadInv H1.  
  unfold transf_function in EQ.
  destruct (type_function f) as [env|] eqn:TF; try discriminate.
  econstructor. eapply type_function_correct; eauto.
- constructor.
Qed.

Theorem TRANSF_local_ldsim:
  @local_ldsim RTL_IS LTL_IS sG tG sge tge.
Proof.
  eapply (@Local_ldsim RTL_IS LTL_IS _ _ _ _ nat Nat.lt MATCH_STATE).
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
    assert (HSG: sG = sge) by (inv GE_INIT; auto).
    assert (HTG: tG = tge) by (inv TGE_INIT; auto).
    exploit wt_initial_core; eauto. exact wt_scu. inv GE_INIT. auto. intro WTC.
    unfold init_core_local in *. simpl in *.
    unfold RTL_local.init_core, init_core in *.
    unfold generic_init_core in INITCORE |- * .
    rewrite HTG, symbols_preserved.
    rewrite HSG in INITCORE.
    destruct (Genv.find_symbol sge fid) eqn: FIND; try discriminate.
    destruct (Genv.find_funct_ptr sge b) eqn: FINDB; try discriminate.
    exploit function_ptr_translated; eauto. intros (tf & FINDB' & TRANSL).
    rewrite FINDB'. 
    unfold RTL_local.fundef_init in INITCORE.
    destruct f; try discriminate.
    assert (exists tfd, tf = Internal tfd)  as [tfd INTERNAL] by (monadInv TRANSL; eauto). subst tf.
    unfold fundef_init.
    erewrite sig_function_translated; eauto.
    destruct (wd_args args (sig_args (RTL.funsig (Internal f)))) eqn: WDARGS; [|try discriminate].
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
    exploit sig_function_translated; eauto. simpl. intro SG. 
    econstructor; eauto.
    econstructor. simpl; rewrite SG; auto.
    { simpl. rewrite SG.
      revert WDARGS ARGREL. simpl. generalize (RTL.fn_sig f). clear. intros.
      rewrite <- wd_args_set_arguments_eq; auto. clear. induction args; auto. }
    { red. simpl. intros.
      generalize (RTL.fn_sig f) H. clear. intros.
      assert (forall pl, In pl (loc_arguments s) ->
                    match pl with
                    | One l' => Loc.diff l' l
                    | Twolong l1 l2 => Loc.diff l1 l /\ Loc.diff l2 l
                    end).
      { intros. apply loc_arguments_acceptable in H0. destruct pl; simpl in *.
        apply callee_save_loc_arg_diff; auto.
        split; apply callee_save_loc_arg_diff; tauto. }
      generalize (loc_arguments s) args H0. clear. induction l0; intros; auto.
      destruct args. auto. pose proof (H0 a (or_introl eq_refl)). destruct a; simpl.
      rewrite Locmap.gso; auto. apply IHl0. intros. apply H0. simpl; auto.
      repeat rewrite Locmap.gso; try tauto. apply IHl0. intros. apply H0. simpl; auto. }
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
    { simpl. rewrite SG. unfold wd_args in WDARGS. eapply val_has_type_list_func_charact. InvBooleans; auto. }
    { subst. auto. }
    { inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_src; auto. }
    { inv MEMINITINJ. inv LRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto. }
    { inv MEMINITINJ; econstructor; eauto.
      intros ? ? ? ? ? H A. exploit inj_inject_id. exact H. intro. inv H0. inv A. auto. }
    { apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto. }
    { apply Injections.fp_match_emp'. }
  - (* tau step *)
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP. right. exists 0%nat.
    simpl in STEP.
    assert (HSG: sG = sge) by (inv GE_INIT; auto);
      assert (HTG: tG = tge) by (inv TGE_INIT; auto).
    rewrite HSG in STEP. rewrite HTG.
    assert (globalenv_generic scu sge) by (inv GE_INIT; auto).
    pose proof (subject_reduction _ wt_scu _ H _ _ _ _ _ STEP) as WTC'. clear H.
    revert i mu Hfp Lfp Lcore Lm MS HSG HTG.
    induction STEP; intros until 1; try (inv MS); specialize (WTC' WTC); try UseShape; intros.

    + (* nop *)
      exploit exec_moves; eauto. intros [ls1 [X Y]]. intros.
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact X. econstructor; eauto. eresolvfp. eresolvfp. 
      FP. split; auto. 
      exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
      econstructor; eauto.
    + (* op move *)
      generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
      simpl in H0. inv H0.
      exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact X. econstructor; eauto.  eauto. eauto.
      FP. simpl in H1. eresolvfp. split; auto. 
      exploit satisf_successors; eauto. simpl; eauto. eapply subst_reg_satisf; eauto.
      intros [enext [U V]]. 
      econstructor; eauto.

    + (* op makelong *)
      generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
      simpl in H0. inv H0.
      exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact X. econstructor; eauto. eresolvfp. eresolvfp.
      FP. simpl in H1. eresolvfp. split; auto.
      exploit satisf_successors; eauto. simpl; eauto.
      eapply subst_reg_kind_satisf_makelong. eauto. eauto.
      intros [enext [U V]].
      econstructor; eauto.

    + (* op lowlong *)
      generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
      simpl in H0. inv H0.
      exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact X. econstructor; eauto. eresolvfp. eresolvfp.
      FP. simpl in *; eresolvfp. split; auto.
      exploit satisf_successors; eauto. simpl; eauto.
      eapply subst_reg_kind_satisf_lowlong. eauto. eauto.
      intros [enext [U V]].
      econstructor; eauto.

    + (* op highlong *)
      generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
      simpl in H0. inv H0.
      exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact X. econstructor; eauto. eresolvfp. eresolvfp.
      FP. simpl in *; eresolvfp. split; auto.
      exploit satisf_successors; eauto. simpl; eauto.
      eapply subst_reg_kind_satisf_highlong. eauto. eauto.
      intros [enext [U V]]. econstructor; eauto.

    + (* op regular *)
      generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
      exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
      exploit transfer_use_def_satisf; eauto. intros [X Y].
      exploit eval_operation_lessdef; eauto. intros [v' [F G]].
      exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
      exploit eval_operation_lessdef_fp; eauto. intros [fp' [F' G']].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact A1.
      eapply star_left. econstructor. instantiate (1 := v'). rewrite <- F.
      apply eval_operation_preserved. exact symbols_preserved.
      rewrite <-F'. eapply eval_operation_fp_preserved. exact symbols_preserved.
      eauto. eapply star_right. eexact A2. constructor.
      eresolvfp. eresolvfp. eresolvfp. eresolvfp.
      FP. eapply fp_inject_fp_match in G'; try (inv AGMU; eauto; fail). split. auto.
      exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]].
      econstructor; eauto. 

    + (* op dead *)
      exploit exec_moves; eauto. intros [ls1 [X Y]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact X. econstructor; eauto.
      eresolvfp. eresolvfp.
      FP. resolvfp. apply Injections.fp_match_union_S'. auto. split; auto.
      exploit satisf_successors. eauto. eauto. simpl; eauto. eauto.
      eapply reg_unconstrained_satisf; eauto.
      intros [enext [U V]].
      econstructor; eauto.
      eapply wt_exec_Iop; eauto.

    + (* load regular *)
      generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
      exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
      exploit transfer_use_def_satisf; eauto. intros [X Y].
      exploit eval_addressing_lessdef; eauto. intros [a' [F G]].
      exploit Mem.loadv_extends; eauto. intros [v' [P Q]].
      exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact A1.
      eapply star_left. econstructor. instantiate (1 := a'). rewrite <- F.
      apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto. eauto.
      eapply star_right. eexact A2. constructor.
      eresolvfp. eresolvfp. eresolvfp. eresolvfp.
      FP. generalize AGMU G P H1. clear. destruct a; simpl; try discriminate; intros; inv G.
      simpl. eapply fp_match_id; inv AGMU; eauto. split; auto.
      exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]].
      econstructor; eauto.

    + (* load pair *)
      generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
      exploit loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V1 & V2).
      set (v2' := if Archi.big_endian then v2 else v1) in *.
      set (v1' := if Archi.big_endian then v1 else v2) in *.
      exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
      assert (LD1: Val.lessdef_list rs##args (reglist ls1 args1')).
      { eapply add_equations_lessdef; eauto. }
      exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
      exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).
      set (ls2 := Locmap.set (R dst1') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
      assert (SAT2: satisf (rs#dst <- v) ls2 e2).
      { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto.
        eapply reg_unconstrained_satisf. eauto.
        eapply add_equations_satisf; eauto. assumption.
        rewrite Regmap.gss.
        apply Val.lessdef_trans with v1'; unfold sel_val; unfold kind_first_word; unfold v1'; destruct Archi.big_endian; auto.
      }
      exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
      assert (LD3: Val.lessdef_list rs##args (reglist ls3 args2')).
      { replace (rs##args) with ((rs#dst<-v)##args).
        eapply add_equations_lessdef; eauto.
        apply list_map_exten; intros. rewrite Regmap.gso; auto.
        eapply addressing_not_long; eauto.
      }
      exploit eval_addressing_lessdef. eexact LD3.
      eapply eval_offset_addressing; eauto; apply Archi.splitlong_ptr32; auto.
      intros [a2' [F2 G2]].
      assert (LOADX: exists v2'', Mem.loadv Mint32 Lm a2' = Some v2'' /\ Val.lessdef v2' v2'').
      { discriminate || (eapply Mem.loadv_extends; [eauto|eexact LOAD2|eexact G2]). }
      destruct LOADX as (v2'' & LOAD2' & LD4).
      set (ls4 := Locmap.set (R dst2') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls3)).
      assert (SAT4: satisf (rs#dst <- v) ls4 e0).
      { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto.
        eapply add_equations_satisf; eauto. assumption.
        rewrite Regmap.gss.
        apply Val.lessdef_trans with v2'; unfold sel_val; unfold kind_second_word; unfold v2'; destruct Archi.big_endian; auto.
      }
      exploit (exec_moves mv3); eauto. intros [ls5 [A5 B5]].
      PLUS.  eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact A1.
      eapply star_left. econstructor.
      instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
      eexact LOAD1'. eauto. instantiate (1 := ls2); auto.
      eapply star_trans. eexact A3.
      eapply star_left. econstructor.
      instantiate (1 := a2'). rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.
      eexact LOAD2'. eauto. instantiate (1 := ls4); auto.
      eapply star_right. eexact A5.
      constructor.
      eresolvfp. eresolvfp. eresolvfp. eresolvfp. eresolvfp. eresolvfp.
      FP. 
      { generalize AGMU F1 F2 G1 G2 H1 LOAD1 LOAD2 LOAD1' LOAD2'; clear. intros.
        destruct a; try discriminate. inv G1. inv G2. simpl in *.
        destruct Archi.ptr64 eqn:C; simpl in *; try discriminate.
        eapply load_int64_fp_split; eauto. exploit Mem.load_valid_access. exact H1. intros [_ ?]; auto. }
      split; auto.
      exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]].
      econstructor; eauto.

    + (* load first word of a pair *)
      generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
      exploit loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V1 & V2).
      set (v2' := if Archi.big_endian then v2 else v1) in *.
      set (v1' := if Archi.big_endian then v1 else v2) in *.
      exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
      assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
      { eapply add_equations_lessdef; eauto. }
      exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
      exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).
      set (ls2 := Locmap.set (R dst') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
      assert (SAT2: satisf (rs#dst <- v) ls2 e0).
      { eapply parallel_assignment_satisf; eauto.
        apply Val.lessdef_trans with v1';
          unfold sel_val; unfold kind_first_word; unfold v1'; destruct Archi.big_endian; auto.
        eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
      }
      exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact A1.
      eapply star_left. econstructor.
      instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
      eexact LOAD1'. eauto. instantiate (1 := ls2); auto.
      eapply star_right. eexact A3.
      constructor. eresolvfp. eresolvfp. eresolvfp. eresolvfp. 
      FP. destruct a; simpl in *; try discriminate. inv G1.
      exploit load_int64_fp_split; eauto. instantiate (1:=i). exploit Mem.load_valid_access. exact H1. intros [_ A']. auto.
      intros. simpl. eapply Injections.fp_match_subset_T'; eauto. apply FP.union_subset.
      split; auto.
      exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]].
      econstructor; eauto.

    + (* load second word of a pair *)
      generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
      exploit loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V1 & V2).
      set (v2' := if Archi.big_endian then v2 else v1) in *.
      set (v1' := if Archi.big_endian then v1 else v2) in *.
      exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
      assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
      { eapply add_equations_lessdef; eauto. }
      exploit eval_addressing_lessdef. eexact LD1.
      eapply eval_offset_addressing; eauto; apply Archi.splitlong_ptr32; auto.
      intros [a1' [F1 G1]].
      assert (LOADX: exists v2'', Mem.loadv Mint32 Lm a1' = Some v2'' /\ Val.lessdef v2' v2'').
      { discriminate || (eapply Mem.loadv_extends; [eauto|eexact LOAD2|eexact G1]). }
      destruct LOADX as (v2'' & LOAD2' & LD2).
      set (ls2 := Locmap.set (R dst') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls1)).
      assert (SAT2: satisf (rs#dst <- v) ls2 e0).
      { eapply parallel_assignment_satisf; eauto.
        apply Val.lessdef_trans with v2'; unfold sel_val; unfold kind_second_word; unfold v2'; destruct Archi.big_endian; auto.
        eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
      }
      exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact A1.
      eapply star_left. econstructor.
      instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
      eexact LOAD2'. eauto. instantiate (1 := ls2); auto.
      eapply star_right. eexact A3.
      constructor. eresolvfp. eresolvfp. eresolvfp. eresolvfp. 
      FP.
      destruct a; simpl in *; try discriminate. inv G1.
      exploit load_int64_fp_split; eauto. instantiate (1:=i). exploit Mem.load_valid_access. exact H1. intros [_ A']. auto.
      intros. simpl. eapply Injections.fp_match_subset_T'; eauto. rewrite FP.union_comm_eq. apply FP.union_subset.
      split; auto.
      exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]].
      econstructor; eauto.

    + (* load dead *)
      exploit exec_moves; eauto. intros [ls1 [X Y]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact X. econstructor; eauto.
      eresolvfp. eresolvfp. resolvfp.
      FP. apply Injections.fp_match_union_S'; auto. split; auto.
      exploit satisf_successors. eauto. eauto. simpl; eauto. eauto.
      eapply reg_unconstrained_satisf; eauto.
      intros [enext [U V]].
      econstructor; eauto.
      eapply wt_exec_Iload; eauto.

    + (* store *)
      revert HSG HTG.
      exploit exec_moves; eauto. intros [ls1 [X Y]]. 
      exploit add_equations_lessdef; eauto. intros LD. simpl in LD. inv LD.
      exploit eval_addressing_lessdef; eauto. intros [a' [F G]].
      exploit Mem.storev_extends; eauto. intros [m'' [P Q]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact X.
      eapply star_two. econstructor. instantiate (1 := a'). rewrite <- F.
      apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto. eauto.
      constructor. eresolvfp. eresolvfp. eresolvfp.
      revert HSG HTG; destruct a; try (simpl in *;  discriminate; fail); inv G. intros.
      FP.  eapply fp_match_id; inv AGMU; eauto. split; auto.
      exploit satisf_successors; eauto. simpl; eauto.
      eapply can_undef_satisf; eauto. eapply add_equations_satisf; eauto. intros [enext [U V]].
      econstructor; eauto.
      intros. eapply Mem.store_valid_block_1; eauto.
      intros. eapply Mem.store_valid_block_1; eauto.
      eapply MemClosures_local.store_val_inject_unmapped_closed_preserved; try (inv AGMU; eauto; fail).
      unfold inject_id. eauto. rewrite Z.add_0_r. eauto.

    + (* store 2 *)
      assert (SF: Archi.ptr64 = false) by (apply Archi.splitlong_ptr32; auto).
      exploit Mem.storev_int64_split; eauto.
      replace (if Archi.big_endian then Val.hiword rs#src else Val.loword rs#src)
        with (sel_val kind_first_word rs#src)
        by (unfold kind_first_word; destruct Archi.big_endian; reflexivity).
      replace (if Archi.big_endian then Val.loword rs#src else Val.hiword rs#src)
        with (sel_val kind_second_word rs#src)
        by (unfold kind_second_word; destruct Archi.big_endian; reflexivity).
      intros [m1 [STORE1 STORE2]].
      exploit (exec_moves mv1); eauto. intros [ls1 [X Y]].
      exploit add_equations_lessdef. eexact Heqo1. eexact Y. intros LD1.
      exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo1. eexact Y.
      simpl. intros LD2.
      set (ls2 := undef_regs (destroyed_by_store Mint32 addr) ls1).
      assert (SAT2: satisf rs ls2 e1).
      eapply can_undef_satisf. eauto.
      eapply add_equation_satisf. eapply add_equations_satisf; eauto.
      exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
      assert (F1': eval_addressing tge sp addr (reglist ls1 args1') = Some a1').
      rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
      exploit Mem.storev_extends. eauto. eexact STORE1. eexact G1. eauto.
      intros [m1' [STORE1' EXT1]].
      exploit (exec_moves mv2); eauto. intros [ls3 [U V]].
      exploit add_equations_lessdef. eexact Heqo. eexact V. intros LD3.
      exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo. eexact V.
      simpl. intros LD4.
      exploit eval_addressing_lessdef. eexact LD3. eauto. intros [a2' [F2 G2]].
      assert (F2': eval_addressing tge sp addr (reglist ls3 args2') = Some a2').
      rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.
      exploit (eval_offset_addressing tge); eauto. intros F2''.
      assert (STOREX: exists m2', Mem.storev Mint32 m1' (Val.add a2' (Vint (Int.repr 4))) (ls3 (R src2')) = Some m2' /\ Mem.extends m' m2').
      { try discriminate;
          (eapply Mem.storev_extends;
           [eexact EXT1 | eexact STORE2 | apply Val.add_lessdef; [eexact G2|eauto] | eauto]). }
      destruct STOREX as [m2' [STORE2' EXT2]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact X.
      eapply star_left.
      econstructor. eexact F1'. eexact STORE1'. eauto. instantiate (1 := ls2). auto.
      eapply star_trans. eexact U.
      eapply star_two.
      eapply exec_Lstore with (m' := m2'). eexact F2''. discriminate||exact STORE2'. eauto. eauto.
      constructor. eresolvfp. eresolvfp. eresolvfp. eresolvfp. eresolvfp.
      revert HSG HTG. destruct a; try (simpl in *; discriminate; fail); inv G1; inv G2. intros.
      FP.
      exploit store_int64_fp_split; eauto. instantiate (1:=i).
      exploit Mem.store_valid_access_3. exact H1. intros [_ A']. auto. 
      intros. simpl. destruct Archi.ptr64 eqn:Cont; [inv Cont|]. eauto.
      split; auto.
      exploit satisf_successors; eauto. simpl; eauto.
      eapply can_undef_satisf. eauto.
      eapply add_equation_satisf. eapply add_equations_satisf; eauto.
      intros [enext [P Q]].
      econstructor; eauto.
      intros. eapply Mem.store_valid_block_1; eauto.
      intros. eapply Mem.store_valid_block_1. exact STORE2'. eapply Mem.store_valid_block_1. exact STORE1'. eauto.
      assert (MemClosures_local.unmapped_closed mu m1 m1').
      { eapply MemClosures_local.store_val_inject_unmapped_closed_preserved; try (inv AGMU; eauto; fail).
        unfold inject_id. eauto. rewrite Z.add_0_r. eauto. }
      eapply MemClosures_local.store_val_inject_unmapped_closed_preserved; try exact H3; try (inv AGMU; eauto; fail).
      intros. eapply Mem.store_valid_block_1; eauto.
      intros. eapply Mem.store_valid_block_1. exact STORE1'. eauto. exact STORE2. 
      unfold inject_id. eauto. rewrite Z.add_0_r. exact STORE2'.

    + (* call *)
      set (sg := RTL.funsig fd) in *.
      set (args' := loc_arguments sg) in *.
      set (res' := loc_result sg) in *.
      exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
      exploit find_function_translated. eauto. eauto. eapply add_equations_args_satisf; eauto.
      intros [tfd [E F]].
      assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact A1. econstructor; eauto. eresolvfp. eresolvfp.
      FP. split. auto.
      exploit analyze_successors; eauto. simpl. left; eauto. intros [enext [U V]].
      econstructor; eauto.
      econstructor; eauto.
      inv WTI. congruence.
      intros. exploit (exec_moves mv2). eauto. eauto.
      eapply function_return_satisf with (v := v) (ls_before := ls1) (ls_after := ls0); eauto.
      eapply add_equation_ros_satisf; eauto.
      eapply add_equations_args_satisf; eauto.
      congruence.
      apply wt_regset_assign; auto.
      intros [ls2 [A2 B2]].
      exists ls2; split.
      eapply star_right. eexact A2. constructor. eresolvfp. 
      apply satisf_incr with eafter; auto.
      rewrite SIG. eapply add_equations_args_lessdef; eauto.
      inv WTI. rewrite <- H10. apply wt_regset_list; auto.
      simpl. red; auto.
      inv WTI. rewrite SIG. rewrite <- H10. apply wt_regset_list; auto.

    + (* tailcall *)
      set (sg := RTL.funsig fd) in *.
      set (args' := loc_arguments sg) in *.
      exploit Mem.free_parallel_extends; eauto. intros [m'' [P Q]].
      exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
      exploit find_function_translated. eauto. eauto. eapply add_equations_args_satisf; eauto.
      intros [tfd [E F]].
      assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact A1. econstructor; eauto.
      rewrite <- E. apply find_function_tailcall; auto.
      replace (fn_stacksize tf) with (RTL.fn_stacksize f); eauto.
      destruct (transf_function_inv _ _ FUN); auto.
      replace (fn_stacksize tf) with (RTL.fn_stacksize f); eauto.
      destruct (transf_function_inv _ _ FUN); auto. eresolvfp. eresolvfp. 
      FP. eapply fp_match_id; inv AGMU; eauto. split; auto.
      econstructor; eauto.
      eapply match_stackframes_change_sig; eauto. rewrite SIG. rewrite e0. decEq.
      destruct (transf_function_inv _ _ FUN); auto.
      rewrite SIG. rewrite return_regs_arg_values; auto. eapply add_equations_args_lessdef; eauto.
      inv WTI. rewrite <- H8. apply wt_regset_list; auto.
      apply return_regs_agree_callee_save.
      rewrite SIG. inv WTI. rewrite <- H8. apply wt_regset_list; auto.
      intros. eapply Mem.valid_block_free_1; eauto.
      intros. eapply Mem.valid_block_free_1; eauto.
      eapply MemClosures_local.free_inject_unmapped_closed_preserved; try (inv AGMU; eauto; fail).
      cbv; eauto. omega. omega.

    (* builtin *)
    + exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
      exploit add_equations_builtin_eval; eauto.
      exploit add_equations_builtin_args_fp_lessdef; eauto. destruct ef; eauto. inv H2.
      intros D' (C & vargs' & vres' & m'' & D & E & F & G).
      exploit helpers.i64ext_effects; try exact E; eauto. intros [X _]; subst m''.
      assert (WTRS': wt_regset env (regmap_setres res vres rs)) by (eapply wt_exec_Ibuiltin; eauto).
      set (ls2 := Locmap.setres res' vres' (undef_regs (destroyed_by_builtin ef) ls1)).
      assert (satisf (regmap_setres res vres rs) ls2 e0).
      { eapply parallel_set_builtin_res_satisf; eauto.
        eapply can_undef_satisf; eauto. }
      exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_trans. eexact A1.
      eapply star_left. econstructor.
      eapply eval_builtin_args_preserved with (ge1 := sge); eauto. exact symbols_preserved.
      eapply MemOpFP.eval_builtin_args_fp_preserved. exact symbols_preserved. eauto. eauto.
      eapply external_call_symbols_preserved. apply senv_preserved. eauto.
      instantiate (1 := ls2); auto.
      eapply star_right. eexact A3.
      econstructor. eresolvfp. eresolvfp. eresolvfp. eresolvfp.
      FP. eapply fp_match_id; inv AGMU; eauto. split; auto.
      exploit satisf_successors; eauto. simpl; eauto.
      intros [enext [U V]].
      econstructor; eauto.
      
    + (* cond *)
      exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
      exploit eval_condition_lessdef_fp; try eassumption. eapply add_equations_lessdef; eauto. intros [fp' [CFP INJFP]].
      eapply fp_inject_fp_match in INJFP; try (inv AGMU; eauto; fail).
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact A1.
      econstructor. eapply eval_condition_lessdef; eauto. eapply add_equations_lessdef; eauto.
      eauto. eauto. eauto. eresolvfp. eresolvfp.
      FP. split; auto.
      exploit satisf_successors; eauto.
      instantiate (1 := if b then ifso else ifnot). simpl. destruct b; auto.
      eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
      intros [enext [U V]].
      econstructor; eauto.
      
    + (* jumptable *)
      exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
      assert (Val.lessdef (Vint n) (ls1 (R arg'))).
      rewrite <- H0. eapply add_equation_lessdef with (q := Eq Full arg (R arg')); eauto.
      revert HSG HTG; inv H2. intros.
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_right. eexact A1.
      econstructor. eauto. eauto. eauto. eauto. eauto.
      FP. split; auto.
      exploit satisf_successors; eauto.
      instantiate (1 := pc'). simpl. eapply list_nth_z_in; eauto.
      eapply can_undef_satisf. eauto. eapply add_equation_satisf; eauto.
      intros [enext [U V]].
      econstructor; eauto.

    + (* return *)
      destruct (transf_function_inv _ _ FUN).
      exploit Mem.free_parallel_extends; eauto. rewrite H10. intros [m'' [P Q]].
      revert HSG HTG. inv WTI; MonadInv.
      ++ (* without an argument *)
        exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
        PLUS. eapply plus_left. econstructor; eauto.
        eapply star_right. eexact A1.
        econstructor. eauto. eauto. eauto. eauto. 
        FP. eapply fp_match_id; inv AGMU; eauto. split; auto.
        econstructor; eauto.
        apply return_regs_agree_callee_save.
        constructor.
        intros. eapply Mem.valid_block_free_1; eauto.
        intros. eapply Mem.valid_block_free_1; eauto.
        eapply MemClosures_local.free_inject_unmapped_closed_preserved; try (inv AGMU; eauto; fail).
        cbv; eauto. omega. omega.
      ++ (* with an argument *)
        exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
        PLUS. eapply plus_left. econstructor; eauto.
        eapply star_right. eexact A1.
        econstructor. eauto. eauto. eauto. eauto.
        FP. eapply fp_match_id; inv AGMU; eauto. split; auto.
        econstructor; eauto. rewrite <- H11.
        replace (Locmap.getpair (map_rpair R (loc_result (RTL.fn_sig f)))
                                (return_regs (parent_locset ts) ls1))
          with (Locmap.getpair (map_rpair R (loc_result (RTL.fn_sig f))) ls1).
        eapply add_equations_res_lessdef; eauto.
        rewrite H13. apply WTRS.
        generalize (loc_result_caller_save (RTL.fn_sig f)). 
        destruct (loc_result (RTL.fn_sig f)); simpl.
        intros A; rewrite A; auto.
        intros [A B]; rewrite A, B; auto.
        apply return_regs_agree_callee_save.
        unfold proj_sig_res. rewrite <- H11; rewrite H13. apply WTRS.
        intros. eapply Mem.valid_block_free_1; eauto.
        intros. eapply Mem.valid_block_free_1; eauto.
        eapply MemClosures_local.free_inject_unmapped_closed_preserved; try (inv AGMU; eauto; fail).
        cbv; eauto. omega. omega. 

    + (* internal function *)
      revert HSG HTG; monadInv FUN. simpl in *.
      destruct (transf_function_inv _ _ EQ).
      exploit Mem.alloc_extends; eauto. apply Zle_refl. rewrite H8; apply Zle_refl.
      intros [m'' [U V]].
      assert (WTRS: wt_regset env (init_regs args (fn_params f))).
      { apply wt_init_regs. inv H0. rewrite wt_params. rewrite H9. auto. }
      exploit (exec_moves mv). eauto. eauto.
      eapply can_undef_satisf; eauto. eapply compat_entry_satisf; eauto.
      rewrite call_regs_param_values. eexact ARGS.
      exact WTRS.
      intros [ls1 [A B]].
      PLUS. eapply plus_left. econstructor; eauto.
      eapply star_left. econstructor; eauto.
      eapply star_right. eexact A.
      econstructor; eauto.
      eauto. eauto. eauto. resolvfp.
      FP. unfold MemOpFP.alloc_fp. erewrite Mem.mext_next; eauto. rewrite H8. eapply fp_match_id; inv AGMU; eauto.
      split; auto. econstructor; eauto.
      intros. eapply Mem.valid_block_alloc; eauto.
      intros. eapply Mem.valid_block_alloc; eauto.
      eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; inv AGMU; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
      eapply Mem.alloc_unchanged_on; eauto.

    + (* external function (i64helpers) *)
      revert HSG HTG.
      exploit external_call_mem_extends; eauto. intros [v' [m'' [F [G [J K]]]]].
      exploit helpers.i64ext_effects; eauto. intros [X _]; subst m''.
      simpl in FUN; inv FUN. 
      PLUS. apply plus_one. econstructor; eauto.
      eapply external_call_symbols_preserved with (ge1 := sge); eauto. apply senv_preserved.
      FP. split; auto. econstructor; eauto.
      simpl. destruct (loc_result (ef_sig ef)) eqn:RES; simpl.
      rewrite Locmap.gss; auto.
      generalize (loc_result_pair (ef_sig ef)); rewrite RES; intros (A & B & C & D & E). 
      exploit external_call_well_typed; eauto. unfold proj_sig_res; rewrite B. intros WTRES'.
      rewrite Locmap.gss. rewrite Locmap.gso by (red; auto). rewrite Locmap.gss. 
      rewrite val_longofwords_eq by auto. auto.
      red; intros. rewrite (AG l H2).
      symmetry; apply Locmap.gpo. 
      assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
      { intros. destruct l; simpl in *. congruence. auto. }
      generalize (loc_result_caller_save (ef_sig ef)). destruct (loc_result (ef_sig ef)); simpl; intuition auto.
      eapply external_call_well_typed; eauto.

    + (* return *)
      revert HSG HTG; inv STACKS.
      exploit STEPS; eauto. rewrite WTRES0; auto. intros [ls2 [A B]].
      PLUS. eapply plus_left. constructor. eexact A. eauto.
      FP. split; auto. econstructor; eauto.
      apply wt_regset_assign; auto. rewrite WTRES0; auto.

  - (* at external *)
    simpl in *. unfold RTL_local.at_external, at_external.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MS ATEXT RC GARG.
    assert (HSG: sG = sge) by (inv GE_INIT; auto).
    assert (HTG: tG = tge) by (inv TGE_INIT; auto).
    destruct Hcore; try discriminate.
    destruct f0; try discriminate.
    destruct e; try discriminate.
    rewrite HSG in ATEXT.
    destruct (invert_symbol_from_string sge name) eqn:SYMBNAME; try discriminate.
    destruct peq; try discriminate.
    destruct peq; try discriminate. simpl in *.
    revert HSG HTG; inv ATEXT. inv MS. simpl in FUN. inv FUN. intros.
    erewrite match_genvs_invert_symbol_from_string_preserved; eauto.
    destruct peq; try contradiction.
    destruct peq; try contradiction. simpl in *.
    eexists 0%nat, _. split. eauto. split. 
    { simpl in *. unfold LDSimDefs.arg_rel. revert AGMU ARGS GARG; clear.
      generalize (map (fun p : rpair loc => Locmap.getpair p ls) (loc_arguments sg)). clear.
      induction argSrc; intros. simpl. inv ARGS. auto. inv ARGS. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto. destruct v2; auto.
      simpl in H2. eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H; eauto.
      intro. inv H0. econstructor. unfold Bset.inj_to_meminj; rewrite H. eauto. rewrite Ptrofs.add_zero; auto.  }
    split.
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    split; auto.
    split.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    econstructor; eauto. apply Injections.fp_match_emp'.
    rewrite HTG. eapply match_cu_match_genv; eauto.
    inv GE_INIT; eauto. inv TGE_INIT; eauto.
    intros. inv H; auto. destruct f1; monadInv H0; auto.

  - (* after external *)
    simpl. unfold LTL_local.after_external, after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    assert (HSG: sG = sge) by (inv GE_INIT; auto). assert (HTG: tG = tge) by (inv TGE_INIT; auto). revert HSG HTG.
    destruct Hcore; try discriminate.
    destruct f; try discriminate.
    destruct e; try discriminate.
    inv MS. monadInv FUN. simpl in *. intros.
    exploit wt_after_external; eauto. intro WTC'.
    assert (Hcore' = RTL_local.Core_Returnstate stack (match oresSrc with Some v => v | None => Vundef end)).
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
    exists (Core_Returnstate ts (Locmap.setpair (loc_result sg)
                                           (match oresTgt with Some v => v | None => Vundef end) ls) sigres0).
    split.
    { destruct oresSrc, oresTgt, (sig_res sg); try contradiction; auto.
      inv RESREL; destruct t; try contradiction; simpl in *; auto.
      rewrite HRES. auto. }
    intros Hm' Lm' HLRELY.
    destruct HLRELY as [HRELY LRELY INV].
    exists 0%nat. subst. econstructor; eauto.
    { unfold Locmap.getpair. destruct (loc_result sg) eqn:RESREG; simpl.
      rewrite Locmap.gss. destruct oresSrc, oresTgt, (sig_res sg); inv RESREL; auto; try contradiction.
      inv AGMU. apply proper_mu_inject_incr in H. inv H. rewrite Ptrofs.add_zero. auto.
      pose proof (loc_result_pair sg). rewrite RESREG in H. destruct H as (A & B & C & D & E).
      repeat rewrite Locmap.gss. simpl. 
      rewrite Locmap.gso by (red; auto). rewrite Locmap.gss.
      destruct oresSrc, oresTgt, (sig_res sg); inv RESREL; auto; inv B; try contradiction.
      rewrite val_longofwords_eq; auto. eapply proper_mu_inject_incr in H; eauto. inv H.
      rewrite Ptrofs.add_zero, val_longofwords_eq; auto. }
    { red; intros. rewrite (AG l H).
      symmetry; apply Locmap.gpo. 
      assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
      { intros. destruct l; simpl in *. congruence. auto. }
      generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto. }
    inv AGMU; eapply extends_rely_extends; eauto. econstructor; eauto.
    { unfold proj_sig_res. destruct (sig_res sg), oresSrc; auto; contradiction. }
    intros ? S. apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT; auto.
    intros ? T. apply TVALID in T. unfold Mem.valid_block in *. inv LRELY. rewrite EQNEXT; auto.
    inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.    

  - (* halt *)
    simpl.  unfold RTL_local.halted, halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES.
    destruct Hcore; try discriminate. destruct stack; try discriminate.
    inv HALT. inv MS. inv STACKS. clear AG. exists resSrc. 
    split. 
    { erewrite (Conventions1.loc_result_exten _ sg) ; eauto. f_equal.
      unfold get_result. destruct (loc_result sg); simpl in *; (inv RES; auto; contradiction). }
    split.
    { revert AGMU GRES. clear; intros. destruct resSrc; try constructor.
      econstructor. simpl in GRES. inv AGMU.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. inv A. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      rewrite Ptrofs.add_zero; auto. }
    split.
    inv AGMU; eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto.
    split; auto.
    inv AGMU; eapply extends_reach_closed_implies_inject; eauto.
Qed.

End PRESERVATION.


Theorem transf_local_ldsim:
  forall scu tcu,
    allocation.transf_program scu = OK tcu ->
    forall sge sG tge tG,
      init_genv_local RTL_IS scu sge sG ->
      init_genv_local LTL_IS tcu tge tG ->
      Genv.genv_next sge = Genv.genv_next tge ->
      local_ldsim sG tG sge tge.
Proof.
  intros. eapply TRANSF_local_ldsim; eauto.
  apply transf_program_match. auto.
Qed.