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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions Tailcall.

Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        Op_fp RTL_local RTLtyping_local tailcall Errors.

Require Import Lia. 

Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.


(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    Lia.lia.
    destruct (f!pc); try Lia.lia.
    destruct i; try Lia.lia.
    generalize (IHn n0). Lia.lia.
    generalize (IHn n0). Lia.lia.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  Lia.lia.
  destruct n2. lia. assert (n1 <= n2)%nat by Lia.lia.
  simpl. destruct f!pc; try Lia.lia. destruct i; try Lia.lia.
  generalize (IHn1 n2 n H0). Lia.lia.
  generalize (IHn1 n2 n H0). Lia.lia.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. lia. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. Lia.lia.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. Lia.lia.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. Lia.lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. Lia.lia. Lia.lia.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. Lia.lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. Lia.lia. Lia.lia.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  caseEq (is_return niter f n r && tailcall_is_possible s &&
          opt_typ_eq (sig_res s) (sig_res (fn_sig f))); intros.
  destruct (andb_prop _ _ H0). destruct (andb_prop _ _ H1).
  eapply transf_instr_tailcall; eauto.
  eapply is_return_charact; eauto.
  constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL_comp_unit) :=
  match_comp_unit_gen (fun f tf => OK (transf_fundef f) = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_cunit. auto.
Qed.

Section PRESERVATION.

Variable scu tcu: RTL_comp_unit.
Variable sge tge: RTL.genv.

Hypothesis SGEINIT: globalenv_generic scu sge.
Hypothesis TGEINIT: globalenv_generic tcu tge.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).

Hypothesis TRANSF: match_prog scu tcu.

Lemma ge_match: ge_match_strict sge tge.
Proof. eapply match_cu_ge_match_strict; eauto. Qed.

Lemma genv_match: Genv.match_genvs (match_globdef (fun f tf => OK (transf_fundef f) = OK tf) eq) sge tge.
Proof. eapply match_cu_match_genv; eauto. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol sge s.
Proof. destruct genv_match; eauto. Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr sge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  destruct genv_match.
  unfold fundef in *. simpl in *.
  unfold Genv.find_funct_ptr, Genv.find_def; intros.
  specialize (mge_defs b). inv mge_defs.
  rewrite <- H1 in H. discriminate.
  rewrite <- H0 in H. destruct x; inv H.
  inv H2. inv H3. eauto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct sge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  destruct v; simpl; intros; try discriminate.
  destruct Ptrofs.eq_dec; [|discriminate]. 
  apply funct_ptr_translated; auto.
Qed.

Lemma senv_preserved:
  Senv.equiv sge tge.
Proof. eapply match_cu_senv_preserved; eauto. Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function sge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol sge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

(** NEW: stack pointer is local *)
Definition local_block (b: block) : Prop := Ple (Genv.genv_next sge) b.
Definition stk_local (v: val) : Prop :=
  match v with
  | Vptr sp _ => local_block sp
  | _ => False
  end.

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      match_stackframes stk stk' ->
      regs_lessdef rs rs' ->
      stk_local (Vptr sp Ptrofs.zero) ->
      match_stackframes
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f,
      match_stackframes stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      stk_local (Vptr sp Ptrofs.zero) ->
      match_stackframes
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: core * mem -> core * mem -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f
             (STACKS: match_stackframes s s')
             (RLD: regs_lessdef rs rs')
             (MLD: Mem.extends m m')
             (LOCALSP: local_block sp),
      match_states (Core_State s f (Vptr sp Ptrofs.zero) pc rs, m)
                   (Core_State s' (transf_function f) (Vptr sp Ptrofs.zero) pc rs', m')
  | match_states_call:
      forall s f args m s' args' m',
      match_stackframes s s' ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_states (Core_Callstate s f args, m)
                   (Core_Callstate s' (transf_fundef f) args', m')
  | match_states_return:
      forall s v m s' v' m',
      match_stackframes s s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states (Core_Returnstate s v, m)
                   (Core_Returnstate s' v', m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v'
             (STACKS: match_stackframes s s')
             (MLD: Mem.extends m m')
             (LOCALSP: local_block sp),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_states (Core_State s f (Vptr sp Ptrofs.zero) pc rs, m)
                   (Core_Returnstate s' v', m').

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: core) : nat :=
  match st with
  | Core_State s f sp pc rs => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Core_Callstate s f args => 0%nat
  | Core_Returnstate s v => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Definition MS b n mu fp fp' cm cm': Prop :=
  match_states cm cm' /\
  Injections.FPMatch' mu fp fp' /\
  let (c, m) := cm in
  let (c', m') := cm' in
  (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
  (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
  (proper_mu sge tge inject_id mu) /\
  (MemClosures_local.unmapped_closed mu m m') /\
  n = measure c /\
  match c with
  | RTL_local.Core_State _ _ _ _ _ => b = true
  | RTL_local.Core_Callstate _ _ _ => True
  | RTL_local.Core_Returnstate _ _ => b = true
  end.

Ltac invMS :=
  match goal with
  | H: MS _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    destruct cm1 as [sc Hm]; destruct cm2 as [tc Lm];
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU [RCPRESV [INDEX FLAG]]]]]]]
  | H: MS _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    unfold MS in H; simpl in H;
    destruct H as [MS [FPMATCH [SVALID [TVALID [AGMU [RCPRESV [INDEX FLAG]]]]]]]
  end.

Ltac resolvfp:=
  match goal with
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; auto; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) ?fp1' => 
    eapply Injections.fp_match_union_S'; auto; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union ?fp1 _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union (FP.union ?fp1 _) _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union (FP.union ?fp1' _) _) (FP.union (FP.union ?fp1 _) _)=> 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp1 ?fp') =>
    rewrite FP.union_comm_eq; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp' _) =>
    apply FP.subset_union_subset; auto
  | |- Injections.FPMatch' _ _ empfp => apply Injections.fp_match_emp'
  | H: FP.subset ?fp1 ?fp2 |- Injections.FPMatch' _ ?fp2 ?fp1 =>
    apply Injections.fp_match_subset_T' with fp2; try exact H; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) ?fp2 =>
    apply Injections.fp_match_union_S'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union ?fp2 _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union'; resolvfp                                          
  | H: (forall b, Bset.belongsto (FP.blocks ?fp2) _ -> ~ Injections.SharedTgt ?mu _)
    |- Injections.FPMatch' _ _ ?fp2 =>
    apply Injections.fp_match_local_block; auto                                          
  | |- FP.subset ?fp ?fp => apply FP.subset_refl
  | H: fp_inject _ ?fp ?fp', H': proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp' =>
    eapply fp_inject_fp_match; inv H'; eauto
  | H: fp_inject inject_id ?fp ?fp'|- FP.subset ?fp' ?fp =>
    apply fp_inject_id_fp_subset
  | H: proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp => inv H; eapply fp_match_id; eauto
  | _ => idtac
  end.

Ltac eresolvfp:= resolvfp; eauto.

Ltac resvalid:=
  match goal with
  (** valid blocks *)
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.free ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_free_1; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.alloc ?m1 _ _ = (?m2,_)
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_alloc; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.store _ ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.store_valid_block_1; eauto
  (** Mem inv *)
  | H1: Mem.store _ ?m1 _ _ _ = Some ?m2,
        H2: Mem.store _ ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.store_val_inject_unmapped_closed_preserved;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.free ?m1 _ _ _ = Some ?m2,
        H2: Mem.free ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.alloc ?m1 _ _ = (?m2, _),
        H2: Mem.alloc ?m1' _ _ = (?m2', _),
            H3: proper_mu _ _ _ _
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto;
      try (eapply Mem.alloc_unchanged_on; eauto; fail)
  | _ => idtac
  end.

Ltac Ex_index :=
  match goal with
  | |- context[Core_State ?s ?f ?sp ?pc ?rs] => exists (measure (Core_State s f sp pc rs))
  | |- context[Core_Callstate] => exists 0%nat
  | |- context[Core_Returnstate ?s ?v] => exists (measure (Core_Returnstate s v))
  end.
Ltac Right := right; do 4 eexists; split; [apply plus_one|resolvfp].
Ltac FP:= match goal with |- ?P /\ _ => assert P; [eresolvfp| try (split;[auto; fail|])] end.
Ltac Left := left; Ex_index; split; [auto|eresolvfp].
Ltac splitMS :=
  split;
  [econstructor; eresolvfp |
   split; [eresolvfp|
           split; [try resvalid; auto |
                   split; [try resvalid; auto
                          |split; [auto|
                                   split; [try resvalid; eauto|
                                           split; eauto]]]]]].

Lemma free_sp_fp_match:
  forall j mu sp lo hi fp,
    proper_mu sge tge j mu ->
    local_block sp ->
    Injections.FPMatch' mu fp (FMemOpFP.free_fp sp lo hi).
Proof.
  intros. apply Injections.fp_match_local_block.
  unfold FMemOpFP.free_fp, FP.blocks, FP.locs, Bset.belongsto; simpl.
  repeat rewrite Locs.emp_union_locs. unfold Locs.blocks; Locs.unfolds.
  erewrite LDSimDefs.mu_shared_tgt; [|inv H; eauto].
  intros ? [] ? . apply FMemOpFP.range_locset_loc in H1. destruct H1. subst.
  unfold local_block, Ple, Plt in *. rewrite S_EQ in H0. lia.
Qed.

Lemma local_block_local:
  forall j mu sp,
    proper_mu sge tge j mu ->
    local_block sp ->
    ~ Injections.SharedTgt mu sp.
Proof.
  intros. erewrite LDSimDefs.mu_shared_tgt; [|inv H; eauto].
  unfold local_block, Ple, Plt in *. rewrite <- S_EQ. lia.
Qed.

Lemma local_block_local':
  forall j mu sp,
    proper_mu sge tge j mu ->
    local_block sp ->
    ~ Injections.SharedSrc mu sp.
Proof.
  intros. erewrite LDSimDefs.mu_shared_src; [|inv H; eauto].
  unfold local_block, Ple, Plt in *. lia.
Qed.

Theorem TRANSF_local_ldsim:
  @local_ldsim RTL_IS RTL_IS sge tge sge tge.
Proof.
  eapply (@Local_ldsim RTL_IS RTL_IS _ _ _ _ _ lt%nat MS).
  constructor.
  (* index wf *)
  - apply lt_wf.
  (* wd_mu *)
  - intros. invMS. eapply proper_mu_inject; eauto.
  (* inj ge *)
  - intros. invMS; eapply proper_mu_ge_init_inj; eauto.
  (* ge match *)
  - apply ge_match.
  (* initial call *)
  - intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    unfold init_core_local in *. simpl in *.
    unfold init_core in *.
    unfold generic_init_core in INITCORE |- * .
    rewrite symbols_preserved.     
    destruct (Genv.find_symbol sge fid) eqn: FIND; try discriminate.
    destruct (Genv.find_funct_ptr sge b) eqn: FINDB; try discriminate.
    erewrite funct_ptr_translated; eauto.
    unfold fundef_init in INITCORE |- *.
    rewrite sig_preserved. destruct f; try discriminate. simpl in *.
    destruct (wd_args args (sig_args (fn_sig f))) eqn: WDARGS; [|discriminate].
    erewrite wd_args_inject; eauto. eexists. split. eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ]. exists 0%nat. inv INITCORE.
    (** This could be a general purposed lemma... *)
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. induction args; intros args' REL G MEMREL; inv REL.
      auto. inv G. f_equal. inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. }
    subst args'.
    splitMS.
    econstructor; eauto. 
    { clear; induction args; auto. }
    { inv MEMINITINJ. inv HRELY. inv LRELY.
      eapply inject_implies_extends; eauto.
      intros b0 A. unfold Mem.valid_block in A; rewrite EQNEXT, <- dom_eq_src in A. eapply Bset.inj_dom in A; eauto.
      destruct A as [b' A]. unfold Bset.inj_to_meminj. rewrite A. eauto.
      inv GE_INIT_INJ. rewrite mu_shared_src in dom_eq_src. rewrite mu_shared_tgt in dom_eq_tgt. rewrite S_EQ in dom_eq_src.
      assert (forall b, Plt b (Mem.nextblock sm0) <-> Plt b (Mem.nextblock tm0)).
      { intro. rewrite <- dom_eq_src, <- dom_eq_tgt. tauto. }
      rewrite EQNEXT, EQNEXT0.
      destruct (Pos.lt_total (Mem.nextblock sm0) (Mem.nextblock tm0)) as [LT | [EQ | LT]]; auto;
        (generalize H3 LT; clear; intros; exfalso; apply H3 in LT; eapply Pos.lt_irrefl; eauto). }
    inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_src; auto.
    inv MEMINITINJ. inv LRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto.    
    inv MEMINITINJ; econstructor; eauto. simpl. intro.
    intros ? ? ? ? ? . exploit inj_inject_id. exact H. intro. inv H0.
    intro A. inv A. auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
  (* tau step *)
  - intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP. simpl in STEP.
    revert i mu Hfp Lfp Lcore Lm MS.
    induction STEP; intros until Lm; intros MS'; invMS; inv MS; EliminatedInstr.

    + (* nop *)
      TransfInstr. Right. eapply exec_Inop; eauto.
      FP. splitMS.
      
    + (* eliminated nop *)
      assert (s0 = pc') by congruence. subst s0.
      Left. simpl. Lia.lia. splitMS.

    + (* op *)
      TransfInstr.
      assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
      exploit eval_operation_lessdef; eauto.
      intros [v' [EVAL' VLD]].
      exploit eval_operation_lessdef_fp; eauto.
      intros [fp' [EVALFP' FPINJ]].
      Right. eapply exec_Iop; eauto.  rewrite <- EVAL'.
      apply eval_operation_preserved. exact symbols_preserved.
      rewrite <- EVALFP'. apply eval_operation_fp_preserved. exact symbols_preserved.
      FP. splitMS. apply set_reg_lessdef; auto.

    + (* eliminated move *)
      rewrite H2 in H. clear H2. inv H.
      Left. simpl. Lia.lia.
      splitMS. simpl in H0. rewrite PMap.gss. congruence.

    + (* load *)
      TransfInstr.
      assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
      exploit eval_addressing_lessdef; eauto.
      intros [a' [ADDR' ALD]].
      exploit Mem.loadv_extends; eauto.
      intros [v' [LOAD' VLD]].
      Right. 
      eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
      apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto.
      assert (a' = a) by (destruct a; try discriminate; inv ALD; auto). subst a'.
      FP. splitMS. apply set_reg_lessdef; auto.

    + (* store *)
      TransfInstr.
      assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
      exploit eval_addressing_lessdef; eauto.
      intros [a' [ADDR' ALD]].
      exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.
      intros [m'1 [STORE' MLD']].
      Right.
      eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
      apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto.
      destruct a; simpl in H1; try discriminate. inv ALD. simpl in STORE'.
      FP. splitMS. 

    + (* call *)
      exploit find_function_translated; eauto. intro FIND'.
      TransfInstr.
      ++ (* call turned tailcall *)
        assert ({ m'' | Mem.free Lm sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
        apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7.
        red; intros; lia.
        destruct X as [m'' FREE].
        Right. 
        eapply exec_Itailcall; eauto. apply sig_preserved.
        rewrite stacksize_preserved.
        FP. apply Injections.fp_match_union_T'; eresolvfp. eapply free_sp_fp_match; eauto.
        splitMS. eapply match_stackframes_tail; eauto. apply regs_lessdef_regs; auto.
        eapply Mem.free_right_extends; eauto.
        rewrite stacksize_preserved. rewrite H7. intros. lia.
        eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto.
        inv AGMU; auto. apply Mem.unchanged_on_refl.
        eapply Mem.free_unchanged_on; eauto using local_block_local.
        
      ++ (* call that remains a call *)
        Right. 
        eapply exec_Icall; eauto. apply sig_preserved.
        FP. splitMS.
        constructor; auto. apply regs_lessdef_regs; auto. 

    + (* tailcall *)
      exploit find_function_translated; eauto. intro FIND'.
      exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
      TransfInstr.
      Right.
      eapply exec_Itailcall; eauto. apply sig_preserved.
      rewrite stacksize_preserved; auto. eauto.
      rewrite stacksize_preserved; auto. 
      FP. splitMS. apply regs_lessdef_regs; auto. 

    + (* builtin *)
      TransfInstr.
      exploit (@eval_builtin_args_lessdef _ sge (fun r => rs#r) (fun r => rs'#r)); eauto.
      intros (vargs' & P & Q).
      exploit (MemOpFP.eval_builtin_args_fp_lessdef _ sge (fun r => rs#r) (fun r => rs'#r)); eauto.
      intros EVALFP.
      exploit external_call_mem_extends; eauto.
      intros [v' [m'1 [A [B [C D]]]]].
      pose proof A as A'. apply helpers.i64ext_effects in A'. destruct A'; subst.
      Right. 
      eapply exec_Ibuiltin; eauto.
      eapply eval_builtin_args_preserved with (ge1 := sge); eauto. exact symbols_preserved.
      eapply MemOpFP.eval_builtin_args_fp_preserved. apply senv_preserved. eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      FP. splitMS.
      apply set_res_lessdef; auto. auto.

    + (* cond *)
      TransfInstr.
      exploit eval_condition_lessdef_fp; try eassumption. apply regs_lessdef_regs; eauto.
      intros [fp' [EVALFP FPINJ]].
      Right. 
      eapply exec_Icond; eauto.
      apply eval_condition_lessdef with (rs##args) m; eauto. apply regs_lessdef_regs; eauto.
      FP. splitMS.

    + (* jumptable *)
      TransfInstr.
      Right. 
      eapply exec_Ijumptable; eauto.
      generalize (RLD arg). rewrite H0. intro. inv H2. auto.
      FP. splitMS.

    + (* return *)
      exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
      TransfInstr.
      Right. 
      apply exec_Ireturn; eauto. rewrite stacksize_preserved; eauto.
      rewrite stacksize_preserved; eauto. 
      FP. splitMS. destruct or; simpl. apply RLD. constructor. 

    + (* eliminated return None *)
      assert (or = None) by congruence. subst or.
      Left. simpl. Lia.lia.
      splitMS. eapply Mem.free_left_extends; eauto.
      eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto.
      inv AGMU; eauto. eapply Mem.free_unchanged_on; eauto using local_block_local'.
      apply Mem.unchanged_on_refl.
      
    + (* eliminated return Some *)
      assert (or = Some r) by congruence. subst or.
      Left. simpl. Lia.lia.
      splitMS. 
      eapply Mem.free_left_extends; eauto.
      eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto.
      inv AGMU; eauto. eapply Mem.free_unchanged_on; eauto using local_block_local'.
      apply Mem.unchanged_on_refl.

    + (* internal call *)
      exploit Mem.alloc_extends; eauto.
      instantiate (1 := 0). Lia.lia.
      instantiate (1 := fn_stacksize f). Lia.lia.
      intros [m'1 [ALLOC EXT]].
      assert (fn_stacksize (transf_function f) = fn_stacksize f /\
              fn_entrypoint (transf_function f) = fn_entrypoint f /\
              fn_params (transf_function f) = fn_params f).
      unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
      destruct H0 as [EQ1 [EQ2 EQ3]].
      Right. 
      simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
      rewrite EQ1. rewrite EQ2. rewrite EQ3.
      unfold MemOpFP.alloc_fp. erewrite Mem.mext_next; eauto.
      FP. splitMS. apply regs_lessdef_init_regs. auto.
      unfold local_block. destruct (plt stk (Genv.genv_next sge)); unfold Plt, Ple in *; [|lia].
      exfalso. apply Mem.alloc_result in H. subst.
      erewrite LDSimDefs.mu_shared_src in SVALID; [|inv AGMU; eauto].
      specialize (SVALID (Mem.nextblock m) p). unfold Mem.valid_block, Plt in SVALID. lia.

    + (* external call *)
      exploit external_call_mem_extends; eauto.
      intros [res' [m2' [A [B [C D]]]]].
      pose proof A as A'. apply helpers.i64ext_effects in A'; auto. destruct A'; subst.
      Right. econstructor; eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      FP. splitMS.
      
    + (* returnstate *)
      inv H3.
      ++ (* synchronous return in both programs *)
        Right. 
        apply exec_return.
        FP. splitMS. apply set_reg_lessdef; auto.
      ++ (* return instr in source program, eliminated because of tailcall *)
        Left. unfold measure. simpl length.
        generalize (return_measure_bounds (fn_code f) pc). unfold niter. Lia.lia.
        splitMS.
        rewrite Regmap.gss. auto.

  (* at ext *)
  - unfold at_external_local; simpl; unfold at_external; simpl.
    intros. invMS. inv MS; try discriminate.
    destruct f0; simpl; try discriminate. destruct e; try discriminate.
    destruct invert_symbol_from_string eqn:FINDID; try discriminate.
    erewrite match_genvs_invert_symbol_from_string_preserved; eauto using genv_match.
    destruct peq; simpl in *. try discriminate.
    destruct peq; simpl in *. try discriminate.
    inv H0. do 2 eexists. split; eauto. split.
    { simpl in *. unfold LDSimDefs.arg_rel. revert args' AGMU H2 H7; clear.
      (** should be extracted as a lemma ... *)
      induction argSrc; intros args' AGMU GARG LD. simpl. inv LD. auto. inv LD. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto. destruct v2; auto.
      simpl in H2. eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H; eauto.
      intro. inv H0. econstructor. unfold Bset.inj_to_meminj; rewrite H. eauto. rewrite Ptrofs.add_zero; auto. }
    split. eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    split; eresolvfp. split.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    splitMS.
    intros. inv H; auto. inv H3. destruct f1; simpl; auto. 

  - (* after external *)
    simpl. unfold after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    destruct Hcore; try discriminate. destruct f; try discriminate. destruct e; try discriminate.
    invMS; inv MS; try discriminate.
    assert (oresSrc = oresTgt).
    { destruct oresSrc, oresTgt; try contradiction; auto. simpl in RESREL.
      inv RESREL; simpl in GRES; auto; try contradiction.
      inv AGMU. apply proper_mu_inject_incr in H. inv H. rewrite Ptrofs.add_zero. auto. }
    subst. 
    assert (Hcore' = Core_Returnstate stack (match oresTgt with Some v => v | None => Vundef end)).
    { destruct oresTgt, (sig_res sg); inv AFTEXT; auto. 
      destruct (val_has_type_func v t); inv H0. auto. } 
    rename H into AFTEXT'.
    exists (Core_Returnstate s' (match oresTgt with Some v => v | None => Vundef end)). split.
    { destruct oresTgt, (sig_res sg); try discriminate; auto.
      destruct val_has_type_func; try discriminate; auto. }
    intros Hm' Lm' [HRELY LRELY INV]. subst. Ex_index. splitMS.
    inv AGMU; eapply extends_rely_extends; eauto. econstructor; eauto.
    intros ? S. apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT; auto.
    intros ? T. apply TVALID in T. unfold Mem.valid_block in *. inv LRELY. rewrite EQNEXT; auto.
    inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
  - (* halt *)
    simpl. unfold halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES. destruct Hcore, stack; try discriminate.
    inv HALT. invMS; inv MS. inv H3. exists resSrc.
    split. { f_equal. inv H5; auto. contradiction. } split.
    { revert AGMU GRES. clear; intros. (** should be extracted to lemma *)
      destruct resSrc; try constructor. econstructor. simpl in GRES. inv AGMU.
      eapply Bset.inj_dom in GRES; eauto. destruct GRES as [b' INJ].
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite INJ; eauto.
      intro A. inv A. unfold Bset.inj_to_meminj; rewrite INJ; eauto. rewrite Ptrofs.add_zero; auto. }
    split. inv AGMU; eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; eauto.
    split. eresolvfp. inv AGMU; eapply extends_reach_closed_implies_inject; eauto.    
Qed.

End PRESERVATION.


Theorem transf_local_ldsim:
  forall scu tcu,
    transf_program scu = OK tcu ->
    forall sge sG tge tG,
      init_genv_local RTL_IS scu sge sG ->
      init_genv_local RTL_IS tcu tge tG ->
      Genv.genv_next sge = Genv.genv_next tge ->
      local_ldsim sG tG sge tge.
Proof.
  intros. inv H0. inv H1. eapply TRANSF_local_ldsim; eauto.
  apply transf_program_match. auto.
Qed.
