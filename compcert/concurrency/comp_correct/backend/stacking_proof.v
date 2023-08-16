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

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib Errors.
Require Import Integers AST Linking.
Require Import Values Memory Separation Events Globalenvs Smallstep.

Require Import Op Locations Bounds Conventions Stacklayout Lineartyping.

Local Open Scope sep_scope.

Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        LTL LTL_local Linear Linear_local Lineartyping_local
        Mach Mach_local
        Stacking stacking.

Definition match_cu (cu: Linear_comp_unit) (tcu: Mach_comp_unit) :=
  match_comp_unit_gen (fun f tf => transf_fundef f = OK tf) eq cu tcu.

Lemma transf_program_match:
  forall cu tcu, transf_program cu = OK tcu -> match_cu cu tcu.
Proof.
  intros. eapply match_transform_partial_cunit; eauto.
Qed.

Lemma set_arguments_no_mreg:
  forall sg args ls r,
    set_arguments (loc_arguments sg) args ls (R r) = ls (R r).
Proof.
  clear. intros. 
  unfold loc_arguments. destruct Archi.ptr64 eqn:? . inv Heqb.
  generalize args (sig_args sg) 0. clear. 
  induction args; destruct l; simpl; auto.
  destruct t; intros; simpl;
    repeat rewrite Locmap.gso; simpl; auto.
Qed.

(** * Basic properties of the translation *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Remark align_type_chunk:
  forall ty, align_chunk (chunk_of_type ty) = 4 * Locations.typealign ty.
Proof.
  destruct ty; reflexivity.
Qed.

Lemma slot_outgoing_argument_valid:
  forall f ofs ty sg,
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> slot_valid f Outgoing ofs ty = true.
Proof.
  intros. exploit loc_arguments_acceptable_2; eauto. intros [A B].
  unfold slot_valid. unfold proj_sumbool.
  rewrite zle_true by Lia.lia.
  rewrite pred_dec_true by auto.
  auto.
Qed.

Lemma load_result_inject:
  forall j ty v v',
  Val.inject j v v' -> Val.has_type v ty -> Val.inject j v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros until v'; unfold Val.has_type, Val.load_result; destruct Archi.ptr64;
  destruct 1; intros; auto; destruct ty; simpl;
  try contradiction; try discriminate; econstructor; eauto.
Qed.


Section PRESERVATION.
  
(** This predicate is defined in Asmgenproof0 *)
Variable return_address_offset: Mach.function -> Mach.code -> ptrofs -> Prop.

Let Mach_IS := Mach_IS return_address_offset.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
    is_tail (Mcall sg ros :: c) (fn_code f) ->
    exists ofs, return_address_offset f c ofs.


Let step := Mach_local.step return_address_offset.

(** Declare properties on compunits and global envs *)
Variable scu: Linear_comp_unit.
Variable tcu: Mach_comp_unit.
Hypothesis TRANSF: match_cu scu tcu.

Variables sge sG: Linear.genv.
Variables tge tG: Mach.genv.

Hypothesis GE_INIT: Linear_IS.(init_genv_local) scu sge sG.
Hypothesis TGE_INIT: Mach_IS.(init_genv_local) tcu tge tG.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).

Lemma wt_prog:
  forall i fd, In (i, Gfun fd) scu.(cu_defs) -> wt_fundef fd.
Proof.
  intros.
  exploit list_forall2_in_left. eexact (proj1 TRANSF). eauto.
  intros ([i' g] & P & Q & R). simpl in *. inv R. destruct fd; simpl in *.
- monadInv H1. unfold transf_function in EQ.
  destruct (wt_function f). auto. discriminate.
- auto.
Qed.

(** Frame properties, part of them are already proved in Stackingproof.v *)
(** Need to inspect Separation.v to make sure understanding memory assertions *)
Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
  intros; discriminate.
Qed.

Lemma transf_function_well_typed:
  wt_function f = true.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb. auto. intros; discriminate.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= Ptrofs.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. Lia.lia.
  intros; discriminate.
Qed.

Remark bound_stack_data_stacksize:
  f.(Linear.fn_stacksize) <= b.(bound_stack_data).
Proof.
  unfold b, function_bounds, bound_stack_data. apply Zmax1.
Qed.

(** * Memory assertions used to describe the contents of stack frames *)

Local Opaque Z.add Z.mul Z.divide.

(** Accessing the stack frame using [load_stack] and [store_stack]. *)
Lemma contains_get_stack:
  forall spec m ty sp ofs,
  m |= contains (chunk_of_type ty) sp ofs spec ->
  exists v, load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v /\ spec v.
Proof.
  intros. unfold load_stack. 
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply loadv_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed.

Lemma hasvalue_get_stack:
  forall ty m sp ofs v,
  m |= hasvalue (chunk_of_type ty) sp ofs v ->
  load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v.
Proof.
  intros. exploit contains_get_stack; eauto. intros (v' & A & B). congruence.
Qed.

Lemma contains_set_stack:
  forall (spec: val -> Prop) v spec1 m ty sp ofs P,
  m |= contains (chunk_of_type ty) sp ofs spec1 ** P ->
  spec (Val.load_result (chunk_of_type ty) v) ->
  exists m',
      store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) v = Some m'
  /\ m' |= contains (chunk_of_type ty) sp ofs spec ** P.
Proof.
  intros. unfold store_stack. 
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply storev_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed.

(** The original contains_locations' proof depends on progam.... although don't need to...
    thus can't be reused........ *)
Program Definition contains_locations (j: meminj) (sp: block) (pos bound: Z) (sl: slot) (ls: locset) : massert := {|
  m_pred := fun m =>
    (8 | pos) /\ 0 <= pos /\ pos + 4 * bound <= Ptrofs.modulus /\
    Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable /\
    forall ofs ty, 0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
    exists v, Mem.load (chunk_of_type ty) m sp (pos + 4 * ofs) = Some v
           /\ Val.inject j (ls (S sl ofs ty)) v;
  m_footprint := fun b ofs =>
    b = sp /\ pos <= ofs < pos + 4 * bound
                                                                                                                 |}.
Next Obligation.
  (* clear unused context... *)
  clear S_EQ Mach_IS TRANSF return_address_offset_exists GE_INIT TGE_INIT step
        scu tcu sge tge sG tG TRANSF_F return_address_offset b fe f tf.
  intuition auto. 
- red; intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exploit H4; eauto. intros (v & A & B). exists v; split; auto.
  eapply Mem.load_unchanged_on; eauto.
  simpl; intros. rewrite size_type_chunk, typesize_typesize in H8. 
  split; auto. Lia.lia.
Qed.
Next Obligation.
  (* clear unused context... *)
  clear S_EQ Mach_IS TRANSF return_address_offset_exists GE_INIT TGE_INIT step
        scu tcu sge tge sG tG TRANSF_F return_address_offset b fe f tf.
  eauto with mem.
Qed.

Remark valid_access_location:
  forall m sp pos bound ofs ty p,
  (8 | pos) ->
  Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Mem.valid_access m (chunk_of_type ty) sp (pos + 4 * ofs) p.
Proof.
  intros; split.
- red; intros. apply Mem.perm_implies with Freeable; auto with mem. 
  apply H0. rewrite size_type_chunk, typesize_typesize in H4. Lia.lia.
- rewrite align_type_chunk. apply Z.divide_add_r. 
  apply Zdivide_trans with 8; auto.
  exists (8 / (4 * typealign ty)); destruct ty; reflexivity.
  apply Z.mul_divide_mono_l. auto.
Qed.

Lemma get_location:
  forall m j sp pos bound sl ls ofs ty,
  m |= contains_locations j sp pos bound sl ls ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) = Some v
  /\ Val.inject j (ls (S sl ofs ty)) v.
Proof.
  intros. destruct H as (D & E & F & G & H).
  exploit H; eauto. intros (v & U & V). exists v; split; auto.
  unfold load_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; auto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). Lia.lia.
Qed.

Lemma set_location:
  forall m j sp pos bound sl ls P ofs ty v v',
  m |= contains_locations j sp pos bound sl ls ** P ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) v' = Some m'
  /\ m' |= contains_locations j sp pos bound sl (Locmap.set (S sl ofs ty) v ls) ** P.
Proof.
  (* clear unused context... *)
  clear S_EQ Mach_IS TRANSF return_address_offset_exists GE_INIT TGE_INIT step
        scu tcu sge tge sG tG TRANSF_F return_address_offset b fe f tf.
  intros. destruct H as (A & B & C). destruct A as (D & E & F & G & H).
  edestruct Mem.valid_access_store as [m' STORE]. 
  eapply valid_access_location; eauto. 
  assert (PERM: Mem.range_perm m' sp pos (pos + 4 * bound) Cur Freeable).
  { red; intros; eauto with mem. }
  exists m'; split.
- unfold store_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; eauto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). Lia.lia.
- simpl. intuition auto.
+ unfold Locmap.set. 
  destruct (Loc.eq (S sl ofs ty) (S sl ofs0 ty0)); [|destruct (Loc.diff_dec (S sl ofs ty) (S sl ofs0 ty0))].
* (* same location *)
  inv e. rename ofs0 into ofs. rename ty0 into ty.
  exists (Val.load_result (chunk_of_type ty) v'); split.
  eapply Mem.load_store_similar_2; eauto. Lia.lia. 
  apply Val.load_result_inject; auto.
* (* different locations *)
  exploit H; eauto. intros (v0 & X & Y). exists v0; split; auto.
  rewrite <- X; eapply Mem.load_store_other; eauto.
  destruct d. congruence. right. rewrite ! size_type_chunk, ! typesize_typesize. Lia.lia.
* (* overlapping locations *)
  destruct (Mem.valid_access_load m' (chunk_of_type ty0) sp (pos + 4 * ofs0)) as [v'' LOAD].
  apply Mem.valid_access_implies with Writable; auto with mem. 
  eapply valid_access_location; eauto.
  exists v''; auto.
+ apply (m_invar P) with m; auto. 
  eapply Mem.store_unchanged_on; eauto. 
  intros i; rewrite size_type_chunk, typesize_typesize. intros; red; intros.
  eelim C; eauto. simpl. split; auto. Lia.lia.
Qed.

Lemma initial_locations:
  forall j sp pos bound P sl ls m,
  m |= range sp pos (pos + 4 * bound) ** P ->
  (8 | pos) ->
  (forall ofs ty, ls (S sl ofs ty) = Vundef) ->
  m |= contains_locations j sp pos bound sl ls ** P.
Proof.
  clear.
  intros. destruct H as (A & B & C). destruct A as (D & E & F). split.
- simpl; intuition auto. red; intros; eauto with mem. 
  destruct (Mem.valid_access_load m (chunk_of_type ty) sp (pos + 4 * ofs)) as [v LOAD].
  eapply valid_access_location; eauto.
  red; intros; eauto with mem.
  exists v; split; auto. rewrite H1; auto.
- split; assumption.
Qed.

Lemma contains_locations_exten:
  forall ls ls' j sp pos bound sl,
  (forall ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j sp pos bound sl ls').
Proof.
  clear.
  intros; split; simpl; intros; auto.
  intuition auto. rewrite H. eauto.
Qed.

Lemma contains_locations_incr:
  forall j j' sp pos bound sl ls,
  inject_incr j j' ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j' sp pos bound sl ls).
Proof.
  clear.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H5; eauto. intros (v & A & B). exists v; eauto.
Qed.

(** [contains_callee_saves j sp pos rl ls] is a memory assertion that holds
  if block [sp], starting at offset [pos], contains the values of the
  callee-save registers [rl] as given by the location map [ls],
  up to the memory injection [j].  The memory layout of the registers in [rl]
  is the same as that implemented by [save_callee_save_rec]. *)

Fixpoint contains_callee_saves (j: meminj) (sp: block) (pos: Z) (rl: list mreg) (ls: locset) : massert :=
  match rl with
  | nil => pure True
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let pos1 := align pos sz in
      contains (chunk_of_type ty) sp pos1 (fun v => Val.inject j (ls (R r)) v)
      ** contains_callee_saves j sp (pos1 + sz) rl ls
  end.

Lemma contains_callee_saves_incr:
  forall j j' sp ls,
  inject_incr j j' ->
  forall rl pos,
  massert_imp (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j' sp pos rl ls).
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_1; auto. apply contains_imp. eauto.
Qed.

Lemma contains_callee_saves_exten:
  forall j sp ls ls' rl pos,
  (forall r, In r rl -> ls' (R r) = ls (R r)) ->
  massert_eqv (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j sp pos rl ls').
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_2; auto. rewrite H by auto. reflexivity.
Qed.

(** Separation logic assertions describing the stack frame at [sp].
  It must contain:
  - the values of the [Local] stack slots of [ls], as per [contains_locations]
  - the values of the [Outgoing] stack slots of [ls], as per [contains_locations]
  - the [parent] pointer representing the back link to the caller's frame
  - the [retaddr] pointer representing the saved return address
  - the initial values of the used callee-save registers as given by [ls0],
    as per [contains_callee_saves].

In addition, we use a nonseparating conjunction to record the fact that
we have full access rights on the stack frame, except the part that
represents the Linear stack data. *)

Definition frame_contents_1 (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) :=
    contains_locations j sp fe.(fe_ofs_local) b.(bound_local) Local ls
 ** contains_locations j sp fe_ofs_arg b.(bound_outgoing) Outgoing ls
 ** hasvalue Mptr sp fe.(fe_ofs_link) parent
 ** hasvalue Mptr sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0.

Definition frame_contents (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) :=
  mconj (frame_contents_1 j sp ls ls0 parent retaddr)
        (range sp 0 fe.(fe_stack_data) **
         range sp (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

(** Accessing components of the frame. *)

Lemma frame_get_local:
  forall ofs ty j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) = Some v
  /\ Val.inject j (ls (S Local ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_proj1 in H.
  eapply get_location; eauto. 
Qed.

Lemma frame_get_outgoing:
  forall ofs ty j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) = Some v
  /\ Val.inject j (ls (S Outgoing ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick2 in H.
  eapply get_location; eauto. 
Qed.

Lemma frame_get_parent:
  forall j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  load_stack m (Vptr sp Ptrofs.zero) Tptr (Ptrofs.repr fe.(fe_ofs_link)) = Some parent.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick3 in H. rewrite <- chunk_of_Tptr in H.
  eapply hasvalue_get_stack; eauto.
Qed.

Lemma frame_get_retaddr:
  forall j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  load_stack m (Vptr sp Ptrofs.zero) Tptr (Ptrofs.repr fe.(fe_ofs_retaddr)) = Some retaddr.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick4 in H. rewrite <- chunk_of_Tptr in H.
  eapply hasvalue_get_stack; eauto.
Qed.

(** Assigning a [Local] or [Outgoing] stack slot. *)

Lemma frame_set_local:
  forall ofs ty v v' j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Local ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1. 
  rewrite ! sep_assoc; intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc; exact B.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

Lemma frame_set_outgoing:
  forall ofs ty v v' j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Outgoing ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc, sep_swap. intros SEP. 
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc, sep_swap; eauto.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

(** Invariance by change of location maps. *)

Lemma frame_contents_exten:
  forall ls ls0 ls' ls0' j sp parent retaddr P m,
  (forall sl ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  (forall r, In r b.(used_callee_save) -> ls0' (R r) = ls0 (R r)) ->
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp ls' ls0' parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- ! (contains_locations_exten ls ls') by auto.
  erewrite  <- contains_callee_saves_exten by eauto.
  assumption.
Qed.

(** Invariance by assignment to registers. *)

Corollary frame_set_reg:
  forall r v j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.set (R r) v ls) ls0 parent retaddr ** P.
Proof.
  intros. apply frame_contents_exten with ls ls0; auto.
Qed.

Corollary frame_undef_regs:
  forall j sp ls ls0 parent retaddr m P rl,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (LTL.undef_regs rl ls) ls0 parent retaddr ** P.
Proof.
Local Opaque sepconj.
  induction rl; simpl; intros.
- auto.
- apply frame_set_reg; auto. 
Qed.

Corollary frame_set_regpair:
  forall j sp ls0 parent retaddr m P p v ls,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setpair p v ls) ls0 parent retaddr ** P.
Proof.
  intros. destruct p; simpl.
  apply frame_set_reg; auto.
  apply frame_set_reg; apply frame_set_reg; auto.
Qed.

Corollary frame_set_res:
  forall j sp ls0 parent retaddr m P res v ls,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setres res v ls) ls0 parent retaddr ** P.
Proof.
  induction res; simpl; intros.
- apply frame_set_reg; auto.
- auto.
- eauto.
Qed.

(** Invariance by change of memory injection. *)

Lemma frame_contents_incr:
  forall j sp ls ls0 parent retaddr m P j',
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  inject_incr j j' ->
  m |= frame_contents j' sp ls ls0 parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- (contains_locations_incr j j') by auto.
  rewrite <- (contains_locations_incr j j') by auto.
  erewrite  <- contains_callee_saves_incr by eauto.
  assumption.
Qed.

(** * Agreement between location sets and Mach states *)

(** TODO: 
    we have to strengthen agree_reg, to forbid such behavior when
    Linear regs of value Vundef are mapped to pointer to global vars in Mach regs. *)

(** when evaluating an comparison, a cmp footprint would be generated when 
    comparing pointer values with others. Thus this behavior would introduce
    new footprint (comparison) which is not desirable *)

(** but it is not enough... we want to preserve agree_reg all the time,
    where as loading memory contents to registers might invalidate the predicate..
    Linear: load 0 eax
    Mach: load 0 eax
    where m[0] = Vundef, m'[0] = Vptr _ _... *)

(** I have to consider, in what situation a pointer value would be related to Vundef? *)

(** DONE: modified semantics of operations in Op.v and Cminor.v, excluding behaviour of comparing Vundefs *)
(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, Val.inject j (ls (R r)) (rs r).

(** Agreement over locations *)

Record agree_locs (ls ls0: locset) : Prop :=
  mk_agree_locs {

    (** Unused registers have the same value as in the caller *)
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);

    (** Incoming stack slots have the same value as the
        corresponding Outgoing stack slots in the caller *)
    agree_incoming:
       forall ofs ty,
       In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters f.(Linear.fn_sig))) ->
       ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty)
}.

(** Auxiliary predicate used at call points *)

Definition agree_callee_save (ls ls0: locset) : Prop :=
  forall l,
  match l with
  | R r => is_callee_save r = true
  | S _ _ _ => True
  end ->
  ls l = ls0 l.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)

Lemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> Val.inject j (ls (R r)) (rs r).
Proof.
  intros. auto.
Qed.

Lemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> Val.inject_list j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor; auto using agree_reg.
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros.
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0.
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_set_pair:
  forall j p v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setpair p v ls) (set_pair p v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_regs_set_reg; auto.
- apply agree_regs_set_reg. apply agree_regs_set_reg; auto. 
  apply Val.hiword_inject; auto. apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_set_res:
  forall j res v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setres res v ls) (set_res res v' rs).
Proof.
  induction res; simpl; intros.
- apply agree_regs_set_reg; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_inject; auto.
  apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_exten:
  forall j ls rs ls' rs',
  agree_regs j ls rs ->
  (forall r, ls' (R r) = Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs j ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A | [A B]].
  rewrite A. constructor.
  rewrite A; rewrite B; auto.
Qed.

Lemma agree_regs_undef_regs:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_regs rl ls) (Mach.undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set_reg; auto.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs sl ofs ty v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S sl ofs ty) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros; eauto with stacking.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (call_regs ls) rs.
Proof.
  intros.
  unfold call_regs; intros; red; intros; auto.
Qed.

(** ** Properties of [agree_locs] *)

(** Preservation under assignment of machine register. *)
Lemma agree_locs_set_reg:
  forall ls ls0 r v,
  agree_locs ls ls0 ->
  mreg_within_bounds b r ->
  agree_locs (Locmap.set (R r) v ls) ls0.
Proof.
  clear.
  intros. inv H; constructor; auto; intros.
  rewrite Locmap.gso. auto. red. subst b. intuition congruence.
Qed.

Lemma caller_save_reg_within_bounds:
  forall r,
  is_callee_save r = false -> mreg_within_bounds b r.
Proof.
  intros; red; intros. congruence.
Qed.

Lemma agree_locs_set_pair:
  forall ls0 p v ls,
  agree_locs ls ls0 ->
  forall_rpair (fun r => is_callee_save r = false) p ->
  agree_locs (Locmap.setpair p v ls) ls0.
Proof.
  intros.
  destruct p; simpl in *.
  apply agree_locs_set_reg; auto. apply caller_save_reg_within_bounds; auto.
  destruct H0.
  apply agree_locs_set_reg; auto. apply agree_locs_set_reg; auto.
  apply caller_save_reg_within_bounds; auto. apply caller_save_reg_within_bounds; auto. 
Qed.

Lemma agree_locs_set_res:
  forall ls0 res v ls,
  agree_locs ls ls0 ->
  (forall r, In r (params_of_builtin_res res) -> mreg_within_bounds b r) ->
  agree_locs (Locmap.setres res v ls) ls0.
Proof.
  induction res; simpl; intros.
- eapply agree_locs_set_reg; eauto.
- auto.
- apply IHres2; auto using in_or_app.
Qed.

Lemma agree_locs_undef_regs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  induction regs; simpl; intros.
  auto.
  apply agree_locs_set_reg; auto.
Qed.

Lemma agree_locs_undef_locs_1:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> is_callee_save r = false) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_regs; eauto.
  intros. apply caller_save_reg_within_bounds. auto.
Qed.

Lemma agree_locs_undef_locs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  existsb is_callee_save regs = false ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_locs_1; eauto. 
  intros. destruct (is_callee_save r) eqn:CS; auto. 
  assert (existsb is_callee_save regs = true).
  { apply existsb_exists. exists r; auto. }
  congruence.
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_locs_set_slot:
  forall ls ls0 sl ofs ty v,
  agree_locs ls ls0 ->
  slot_writable sl = true ->
  agree_locs (Locmap.set (S sl ofs ty) v ls) ls0.
Proof.
  intros. destruct H; constructor; intros.
- rewrite Locmap.gso; auto. red; auto.
- rewrite Locmap.gso; auto. red. left. destruct sl; discriminate.
Qed.

(** Preservation at return points (when [ls] is changed but not [ls0]). *)

Lemma agree_locs_return:
  forall ls ls0 ls',
  agree_locs ls ls0 ->
  agree_callee_save ls' ls ->
  agree_locs ls' ls0.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite H0; auto.
Qed.

(** Preservation at tailcalls (when [ls0] is changed but not [ls]). *)
Lemma agree_locs_tailcall:
  forall ls ls0 ls0',
  agree_locs ls ls0 ->
  agree_callee_save ls0 ls0' ->
  agree_locs ls ls0'.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite <- H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite <- H0; auto.
Qed.

(** ** Properties of [agree_callee_save]. *)

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto. rewrite H; auto.
Qed.

Lemma agree_callee_save_set_result:
  forall sg v ls1 ls2,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.setpair (loc_result sg) v ls1) ls2.
Proof.
  intros; red; intros. rewrite Locmap.gpo. apply H; auto. 
  assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
  { intros. destruct l; auto. simpl; congruence. }
  generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

(** ** Properties of destroyed registers. *)
Definition no_callee_saves (l: list mreg) : Prop :=
  existsb is_callee_save l = false.

Remark destroyed_by_op_caller_save:
  forall op, no_callee_saves (destroyed_by_op op).
Proof.
  unfold no_callee_saves; destruct op; reflexivity.
Qed.

Remark destroyed_by_load_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_load chunk addr).
Proof.
  unfold no_callee_saves; destruct chunk; reflexivity.
Qed.

Remark destroyed_by_store_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_store chunk addr).
Proof.
Local Transparent destroyed_by_store.
  unfold no_callee_saves, destroyed_by_store; intros; destruct chunk; try reflexivity; destruct Archi.ptr64; reflexivity.
Qed.

Remark destroyed_by_cond_caller_save:
  forall cond, no_callee_saves (destroyed_by_cond cond).
Proof.
  unfold no_callee_saves; destruct cond; reflexivity.
Qed.

Remark destroyed_by_jumptable_caller_save:
  no_callee_saves destroyed_by_jumptable.
Proof.
  red; reflexivity.
Qed.

Remark destroyed_by_setstack_caller_save:
  forall ty, no_callee_saves (destroyed_by_setstack ty).
Proof.
  unfold no_callee_saves; destruct ty; reflexivity.
Qed.

Remark destroyed_at_function_entry_caller_save:
  no_callee_saves destroyed_at_function_entry.
Proof.
  red; reflexivity.
Qed.

Hint Resolve destroyed_by_op_caller_save destroyed_by_load_caller_save
    destroyed_by_store_caller_save
    destroyed_by_cond_caller_save destroyed_by_jumptable_caller_save
    destroyed_at_function_entry_caller_save: stacking.

Remark destroyed_by_setstack_function_entry:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_function_entry.
Proof.
Local Transparent destroyed_by_setstack destroyed_at_function_entry.
  unfold incl; destruct ty; simpl; tauto.
Qed.

Remark transl_destroyed_by_op:
  forall op e, destroyed_by_op (transl_op e op) = destroyed_by_op op.
Proof.
  intros; destruct op; reflexivity.
Qed.

Remark transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

Remark transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Section SAVE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls: locset.

Hypothesis ls_temp_undef:
  forall ty r, In r (destroyed_by_setstack ty) -> ls (R r) = Vundef.

Hypothesis wt_ls: forall r, Val.has_type (ls (R r)) (mreg_type r).

Lemma save_callee_save_rec_correct:
  forall k l pos rs lf m P,
    (forall r, In r l -> is_callee_save r = true) ->
    m |= range sp pos (size_callee_save_area_rec l pos) ** P ->
    agree_regs j ls rs ->
    exists rs', exists m', exists fp,
          star (step tge)
               (Core_State cs fb (Vptr sp Ptrofs.zero) (save_callee_save_rec l pos k) rs lf) m
               fp (Core_State cs fb (Vptr sp Ptrofs.zero) k rs' lf) m'
          /\ m' |= contains_callee_saves j sp pos l ls ** P
          /\ (forall ofs k p, Mem.perm m sp ofs k p -> Mem.perm m' sp ofs k p)
          /\ agree_regs j ls rs'
          (** add properties about fp: simply contained in sp. *)
          /\ Mem.unchanged_on (fun b _ => b <> sp) m m'
          /\ (forall b, FP.blocks fp b -> b = sp).
Proof.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl; intros until P; intros CS SEP AG.
- exists rs, m, FP.emp. 
  split. apply star_refl.
  split. rewrite sep_pure; split; auto. eapply sep_drop; eauto.
  split. auto. 
  split. auto.
  split. apply Mem.unchanged_on_refl.
  intros. inv H. inv H0.
- set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (pos1 := align pos sz) in *.
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (SZREC: pos1 + sz <= size_callee_save_area_rec l (pos1 + sz)) by (apply size_callee_save_area_rec_incr).
  assert (POS1: pos <= pos1) by (apply align_le; auto).
  assert (AL1: (align_chunk (chunk_of_type ty) | pos1)).
  { unfold pos1. apply Zdivide_trans with sz.
    unfold sz; rewrite <- size_type_chunk. apply align_size_chunk_divides.
    apply align_divides; auto. }
  apply range_drop_left with (mid := pos1) in SEP; [ | Lia.lia ].
  apply range_split with (mid := pos1 + sz) in SEP; [ | Lia.lia ].
  unfold sz at 1 in SEP. rewrite <- size_type_chunk in SEP.
  apply range_contains in SEP; auto.
  exploit (contains_set_stack (fun v' => Val.inject j (ls (R r)) v') (rs r)).
  eexact SEP.
  apply load_result_inject; auto. apply wt_ls. 
  clear SEP; intros (m1 & STORE & SEP).
  set (rs1 := undef_regs (destroyed_by_setstack ty) rs).
  assert (AG1: agree_regs j ls rs1).
  { red; intros. unfold rs1. destruct (In_dec mreg_eq r0 (destroyed_by_setstack ty)).
    erewrite ls_temp_undef by eauto. auto.
    rewrite undef_regs_other by auto. apply AG. }
  rewrite sep_swap in SEP. 
  exploit (IHl (pos1 + sz) rs1 lf m1); eauto.
  intros (rs2 & m2 & fp2 & A & B & C & D & E & F).
  exists rs2, m2. eexists.
  split. eapply star_left; eauto. constructor. exact STORE. auto. traceEq.
  split. rewrite sep_assoc, sep_swap. exact B.
  split. intros. apply C. unfold store_stack in STORE; simpl in STORE. eapply Mem.perm_store_1; eauto.
  split. auto.
  split. eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on.
  unfold store_stack, Mem.storev in STORE. simpl in STORE. eauto. intros; auto. auto.
  
  intros. apply FP.union_belongsto in H. destruct H; auto.
  generalize H; clear.
  cbn. unfold FMemOpFP.store_fp, FP.blocks, Locs.blocks, FP.locs; simpl.
  destruct 1. Locs.unfolds. unfold FMemOpFP.range_locset in H.
  red_boolean_true; try congruence.
  destruct eq_block; congruence.
Qed.

End SAVE_CALLEE_SAVE.

Remark LTL_undef_regs_same:
  forall r rl ls, In r rl -> LTL.undef_regs rl ls (R r) = Vundef.
Proof.
  induction rl; simpl; intros. contradiction.
  unfold Locmap.set. destruct (Loc.eq (R a) (R r)). auto.
  destruct (Loc.diff_dec (R a) (R r)); auto.
  apply IHrl. intuition congruence.
Qed.

Remark LTL_undef_regs_others:
  forall r rl ls, ~In r rl -> LTL.undef_regs rl ls (R r) = ls (R r).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. intuition. red. intuition.
Qed.

Remark LTL_undef_regs_slot:
  forall sl ofs ty rl ls, LTL.undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. red; auto.
Qed.

Remark undef_regs_type:
  forall ty l rl ls,
  Val.has_type (ls l) ty -> Val.has_type (LTL.undef_regs rl ls l) ty.
Proof.
  induction rl; simpl; intros.
- auto.
- unfold Locmap.set. destruct (Loc.eq (R a) l). red; auto.
  destruct (Loc.diff_dec (R a) l); auto. red; auto.
Qed.

Lemma save_callee_save_correct:
  forall j ls ls0 rs sp cs fb k lf m P,
    m |= range sp fe.(fe_ofs_callee_save) (size_callee_save_area b fe.(fe_ofs_callee_save)) ** P ->
    (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
    agree_callee_save ls ls0 ->
    agree_regs j ls rs ->
    let ls1 := LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) in
    let rs1 := undef_regs destroyed_at_function_entry rs in
    exists rs', exists m', exists fp,
          star (step tge)
               (Core_State cs fb (Vptr sp Ptrofs.zero) (save_callee_save fe k) rs1 lf) m
               fp (Core_State cs fb (Vptr sp Ptrofs.zero) k rs' lf) m'
          /\ m' |= contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0 ** P
          /\ (forall ofs k p, Mem.perm m sp ofs k p -> Mem.perm m' sp ofs k p)
          /\ agree_regs j ls1 rs'
          (** add properties about fp: simply contained in sp. *)
          /\ Mem.unchanged_on (fun b _ => b <> sp) m m'
          /\ (forall b, FP.blocks fp b -> b = sp).
Proof.
  intros until P; intros SEP TY AGCS AG; intros ls1 rs1.
  exploit (save_callee_save_rec_correct j cs fb sp ls1).
- intros. unfold ls1. apply LTL_undef_regs_same. eapply destroyed_by_setstack_function_entry; eauto.
- intros. unfold ls1. apply undef_regs_type. apply TY. 
- exact b.(used_callee_save_prop).
- eexact SEP.
- instantiate (1 := rs1). apply agree_regs_undef_regs. apply agree_regs_call_regs. auto.
- clear SEP. intros (rs' & m' & fp' & EXEC & SEP & PERMS & AG' & UNCHG & FP_sp).
  exists rs', m'. eexists.
  split. eexact EXEC.
  split. rewrite (contains_callee_saves_exten j sp ls0 ls1). exact SEP.
  intros. apply b.(used_callee_save_prop) in H.
    unfold ls1. rewrite LTL_undef_regs_others. unfold call_regs. 
    apply AGCS; auto.
    red; intros.
    assert (existsb is_callee_save destroyed_at_function_entry = false)
       by  (apply destroyed_at_function_entry_caller_save).
    assert (existsb is_callee_save destroyed_at_function_entry = true).
    { apply existsb_exists. exists r; auto. }
    congruence.
  split. exact PERMS. split. exact AG'.
  split. exact UNCHG. exact FP_sp.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)

Lemma alloc_parallel_rule_2':
  forall (F V: Type) (ge: Genv.t F V) m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
  m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
  Mem.alloc m1 0 sz1 = (m1', b1) ->
  Mem.alloc m2 0 sz2 = (m2', b2) ->
  (8 | delta) ->
  lo = delta ->
  hi = delta + Zmax 0 sz1 ->
  0 <= sz2 <= Ptrofs.max_unsigned ->
  0 <= delta -> hi <= sz2 ->
  exists j',
     m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ j' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> j' b = j b).
Proof.
  clear. intros. 
  set (j1 := fun b => if eq_block b b1 then Some(b2, delta) else j b).
  assert (X: inject_incr j j1).
  { unfold j1; red; intros. destruct (eq_block b b1); auto. 
    subst b. eelim Mem.fresh_block_alloc. eexact H0. 
    eapply Mem.valid_block_inject_1. eauto. apply sep_proj1 in H. eexact H. }
  assert (Y: inject_separated j j1 m1 m2).
  { unfold j1; red; intros. destruct (eq_block b0 b1). 
  - inversion H9; clear H9; subst b3 delta0 b0. split; eapply Mem.fresh_block_alloc; eauto.
  - congruence. }
  rewrite sep_swap in H. eapply globalenv_inject_incr with (j' := j1) in H; eauto. rewrite sep_swap in H.
  clear X Y.
  exploit alloc_parallel_rule; eauto. 
  intros (j' & A & B & C & D).
  exists j'; split; auto.
  rewrite sep_swap4 in A. rewrite sep_swap4. apply globalenv_inject_incr with j1 m1; auto.
- red; unfold j1; intros. destruct (eq_block b b1). congruence. rewrite D; auto.
- red; unfold j1; intros. destruct (eq_block b0 b1). congruence. rewrite D in H9 by auto. congruence.
Qed.


Lemma function_prologue_correct:
  forall j ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k lf P,
  agree_regs j ls rs ->
  agree_callee_save ls ls0 ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) ->
  rs1 = undef_regs destroyed_at_function_entry rs ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tptr -> Val.has_type ra Tptr ->
  m1' |= minjection j m1 ** globalenv_inject sge j ** P ->
  exists j', exists rs', exists m2', exists sp', exists m3', exists m4', exists m5', exists fp,
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_retaddr_ofs) ra = Some m4'
  /\ star (step tge)
         (Core_State cs fb (Vptr sp' Ptrofs.zero) (save_callee_save fe k) rs1 lf) m4'
         fp (Core_State cs fb (Vptr sp' Ptrofs.zero) k rs' lf) m5'
  /\ agree_regs j' ls1 rs'
  /\ agree_locs ls1 ls0
  /\ m5' |= frame_contents j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject sge j' ** P
  /\ j' sp = Some(sp', fe.(fe_stack_data))
  /\ inject_incr j j'
  (** add properties about fp: simply contained in sp. *)
  /\ sep_inject j j'
  /\ Mem.unchanged_on (fun b _ => Mem.valid_block m1' b) m1' m5'
  /\ (forall b, FP.blocks fp b -> b = sp').
Proof.
  intros until P; intros AGREGS AGCS WTREGS LS1 RS1 ALLOC TYPAR TYRA SEP.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Stack layout info *)
Local Opaque b fe.
  generalize (frame_env_range b) (frame_env_aligned b). replace (make_env b) with fe by auto. simpl. 
  intros LAYOUT1 LAYOUT2.
  (* Allocation step *)
  destruct (Mem.alloc m1' 0 (fe_size fe)) as [m2' sp'] eqn:ALLOC'.
  exploit alloc_parallel_rule_2'.
  eexact SEP. eexact ALLOC. eexact ALLOC'. 
  instantiate (1 := fe_stack_data fe). tauto.
  reflexivity. 
  instantiate (1 := fe_stack_data fe + bound_stack_data b). rewrite Z.max_comm. reflexivity.
  
  generalize (bound_stack_data_pos b) (size_no_overflow) LAYOUT1. 
  clear; intros. destruct LAYOUT1. subst b fe. Lia.lia. 
  
  tauto.
  tauto.
  rename SEP into SEPOLD. intros (j' & SEP & INCR & SAME & SEPINJ).
    
  (* Remember the freeable permissions using a mconj *)
  assert (SEPCONJ:
    m2' |= mconj (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
                 (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
           ** minjection j' m2 ** globalenv_inject sge j' ** P).
  { apply mconj_intro; rewrite sep_assoc; assumption. }
  (* Dividing up the frame *)
  apply (frame_env_separated b) in SEP. replace (make_env b) with fe in SEP by auto.
  (* Store of parent *)
  rewrite sep_swap3 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = parent) parent (fun _ => True) m2' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m3' & STORE_PARENT & SEP).
  rewrite sep_swap3 in SEP.
  (* Store of return address *)
  rewrite sep_swap4 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = ra) ra (fun _ => True) m3' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m4' & STORE_RETADDR & SEP).
  rewrite sep_swap4 in SEP.
  (* Saving callee-save registers *)
  rewrite sep_swap5 in SEP.
  exploit (save_callee_save_correct j' ls ls0 rs); eauto.
  apply agree_regs_inject_incr with j; auto.
  replace (LTL.undef_regs destroyed_at_function_entry (call_regs ls)) with ls1 by auto.
  replace (undef_regs destroyed_at_function_entry rs) with rs1 by auto.
  clear SEP; intros (rs2 & m5' & fp & SAVE_CS & SEP & PERMS & AGREGS' & UNCHG & FP_sp).
  rewrite sep_swap5 in SEP.
  (* Materializing the Local and Outgoing locations *)
  exploit (initial_locations j'). eexact SEP. tauto. 
  instantiate (1 := Local). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  exploit (initial_locations j'). eexact SEP. tauto. 
  instantiate (1 := Outgoing). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  (* Now we frame this *)
  assert (SEPFINAL: m5' |= frame_contents j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject sge j' ** P).
  { eapply frame_mconj. eexact SEPCONJ.
    rewrite chunk_of_Tptr in SEP.  
    unfold frame_contents_1; rewrite ! sep_assoc. exact SEP.
    assert (forall ofs k p, Mem.perm m2' sp' ofs k p -> Mem.perm m5' sp' ofs k p).
    { intros. apply PERMS. 
      unfold store_stack in STORE_PARENT, STORE_RETADDR.
      simpl in STORE_PARENT, STORE_RETADDR.
      eauto using Mem.perm_store_1. }
    eapply sep_preserved. eapply sep_proj1. eapply mconj_proj2. eexact SEPCONJ.
    intros; apply range_preserved with m2'; auto.
    intros; apply range_preserved with m2'; auto.
  }
  clear SEP SEPCONJ.
(* Conclusions *)
  exists j', rs2, m2', sp', m3', m4', m5', fp.
  split. auto.
  split. exact STORE_PARENT.
  split. exact STORE_RETADDR.
  split. eexact SAVE_CS.
  split. exact AGREGS'.
  split. rewrite LS1. apply agree_locs_undef_locs; [|reflexivity].
    constructor; intros. unfold call_regs. apply AGCS. 
    unfold mreg_within_bounds in H; tauto.
    unfold call_regs. apply AGCS. auto.
  split. exact SEPFINAL.
  split. exact SAME.
  split. exact INCR.
  split. intros b1 b1' bimg ofs1 ofs1' INJ1 INJ1'.
    destruct (eq_block b1' sp). 
    subst b1'. rewrite SAME in INJ1'. inv INJ1'.
    apply Mem.fresh_block_alloc in ALLOC'. apply sep_pick1 in SEPOLD. simpl in SEPOLD.
    eapply Mem.mi_mappedblocks in INJ1; eauto. exfalso; apply ALLOC'. eauto.
    apply SEPINJ in n. rewrite <- n; auto.
  split.
    pose proof (Mem.fresh_block_alloc _ _ _ _ _ ALLOC') as SPFRESH.
    apply Mem.unchanged_on_trans with m4'.
    apply Mem.unchanged_on_trans with m3'.
    apply Mem.unchanged_on_trans with m2'.
    eapply Mem.alloc_unchanged_on; eauto.
    eapply Mem.store_unchanged_on; eauto. unfold store_stack, Mem.storev in STORE_PARENT. simpl in STORE_PARENT; eauto.
    eapply Mem.store_unchanged_on; eauto. unfold store_stack, Mem.storev in STORE_RETADDR. simpl in STORE_RETADDR; eauto.
    eapply Mem.unchanged_on_implies. eauto. intros. simpl. intro. subst b0. congruence.
  auto.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls0: locset.
Variable m: mem.

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> Val.inject j (ls0 (R r)) (rs r).

Lemma restore_callee_save_rec_correct:
  forall l ofs rs k lf,
  m |= contains_callee_saves j sp ofs l ls0 ->
  agree_unused ls0 rs ->
  (forall r, In r l -> mreg_within_bounds b r) ->
  exists rs', exists fp,
    star (step tge)
      (Core_State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save_rec l ofs k) rs lf) m
      fp (Core_State cs fb (Vptr sp Ptrofs.zero) k rs' lf) m
  /\ (forall r, In r l -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'
  /\ (forall b, FP.blocks fp b -> b = sp).
Proof.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl; intros.
- (* base case *)
  exists rs, FP.emp. intuition auto. apply star_refl. inv H2. inv H3.
- (* inductive case *)
  set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (ofs1 := align ofs sz).
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (OFSLE: ofs <= ofs1) by (apply align_le; auto).
  assert (BOUND: mreg_within_bounds b r) by eauto.
  exploit contains_get_stack.
    eapply sep_proj1; eassumption.
  intros (v & LOAD & SPEC).
  exploit (IHl (ofs1 + sz) (rs#r <- v)).
    eapply sep_proj2; eassumption.
    red; intros. rewrite Regmap.gso. auto. intuition congruence.
    eauto.
  intros (rs' & fp' & A & B & C & D & E).
  exists rs'. eexists.
  split. eapply star_step; eauto. 
    econstructor. exact LOAD. traceEq.
  split. intros.
    destruct (In_dec mreg_eq r0 l). auto. 
    assert (r = r0) by tauto. subst r0.
    rewrite C by auto. rewrite Regmap.gss. exact SPEC.
  split. intros. 
    rewrite C by tauto. apply Regmap.gso. intuition auto.
  split. exact D.
    intros. destruct (FP.union_belongsto _ _ _ H2); auto.
    generalize H3; clear; cbn.
    unfold FP.blocks, FMemOpFP.load_fp, FMemOpFP.range_locset, FP.locs; simpl.
    unfold Bset.belongsto, Locs.blocks. Locs.unfolds. intros (ofs' & ?).
    red_boolean_true; try congruence. destruct eq_block; congruence.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_callee_save_correct:
  forall m j sp ls ls0 pa ra P rs k cs fb lf,
  m |= frame_contents j sp ls ls0 pa ra ** P ->
  agree_unused j ls0 rs ->
  exists rs', exists fp,
    star (step tge)
         (Core_State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save fe k) rs lf) m
         fp (Core_State cs fb (Vptr sp Ptrofs.zero) k rs' lf) m
  /\ (forall r,
        is_callee_save r = true -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r,
        is_callee_save r = false -> rs' r = rs r)
  /\ (forall b, FP.blocks fp b -> b = sp).
Proof.
  intros.
  unfold frame_contents, frame_contents_1 in H. 
  apply mconj_proj1 in H. rewrite ! sep_assoc in H. apply sep_pick5 in H. 
  exploit restore_callee_save_rec_correct; eauto.
  intros; unfold mreg_within_bounds; auto.
  intros (rs' & fp  & A & B & C & D & E).
  exists rs', fp.
  split. eexact A.
  split; intros.
  destruct (In_dec mreg_eq r (used_callee_save b)).
  apply B; auto.
  rewrite C by auto. apply H0. unfold mreg_within_bounds; tauto.
  split; intros; auto.
  apply C. red; intros. apply (used_callee_save_prop b) in H2. congruence.
Qed.

(** As a corollary, we obtain the following correctness result for
  the execution of a function epilogue (reloading of used callee-save
  registers + reloading of the link and return address + freeing
  of the frame). *)

Lemma function_epilogue_correct:
  forall m' j sp' ls ls0 pa ra P m rs sp m1 k cs fb lf,
  m' |= frame_contents j sp' ls ls0 pa ra ** minjection j m ** P ->
  agree_regs j ls rs ->
  agree_locs ls ls0 ->
  j sp = Some(sp', fe.(fe_stack_data)) ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1', exists fp,
     load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ star (step tge)
         (Core_State cs fb (Vptr sp' Ptrofs.zero) (restore_callee_save fe k) rs lf) m'
         fp (Core_State cs fb (Vptr sp' Ptrofs.zero) k rs1 lf) m'
  /\ agree_regs j (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ m1' |= minjection j m1 ** P
  /\ (forall b, FP.blocks fp b -> b = sp').
Proof.
  intros until lf; intros SEP AGR AGL INJ FREE.
  (* Can free *)
  exploit free_parallel_rule.
    rewrite <- sep_assoc. eapply mconj_proj2. eexact SEP.
    eexact FREE.
    eexact INJ.
    auto. rewrite Z.max_comm; reflexivity.
  intros (m1' & FREE' & SEP').
  (* Reloading the callee-save registers *)
  exploit restore_callee_save_correct.
    eexact SEP.
    instantiate (1 := rs). 
    red; intros. destruct AGL. rewrite <- agree_unused_reg0 by auto. apply AGR.
  intros (rs' & fp & LOAD_CS & CS & NCS & HFP).
  (* Reloading the back link and return address *)
  unfold frame_contents in SEP; apply mconj_proj1 in SEP.
  unfold frame_contents_1 in SEP; rewrite ! sep_assoc in SEP.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick3; eexact SEP. intros LOAD_LINK.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick4; eexact SEP. intros LOAD_RETADDR.
  clear SEP.
  (* Conclusions *)
  rewrite unfold_transf_function; simpl.
  exists rs', m1', fp.
  split. assumption.
  split. assumption.
  split. assumption.
  split. eassumption.
  split. red; unfold return_regs; intros. 
    destruct (is_callee_save r) eqn:C.
    apply CS; auto.
    rewrite NCS by auto. apply AGR.
  split. red; unfold return_regs; intros.
    destruct l; auto. rewrite H; auto.
  split; auto. 
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariants *)

(** This is the memory assertion that captures the contents of the stack frames
  mentioned in the call stacks. *)


(** TODO:
    since we made additional load_frame, need a new assertion relating load_frame and stack frames. 

    Partly done.. *)

Fixpoint stack_contents (j: meminj) (f0: Linear.function) (ls0: locset) (sp0: block) (tyl0: list typ)
         (cs: list Linear.stackframe) (cs': list Mach.stackframe) : massert :=
  match cs, cs' with
  | nil, nil => 
    (* 1. contents of ls0 agrees with contents of sp0 (arguments of the initial function call) *)
    contains_locations j sp0 fe_ofs_arg (loadframe.tyl_length tyl0) Outgoing ls0
  (* 2. ? *) 
  | Linear.Stackframe f _ ls c :: cs, Mach.Stackframe fb (Vptr sp' _) ra c' :: cs' =>
    frame_contents f j sp' ls (parent_locset0 ls0 cs) (parent_sp0 sp0 cs') (parent_ra cs')
                   ** stack_contents j f0 ls0 sp0 tyl0 cs cs'
  | _, _ => pure False
  end.

(** [match_stacks] captures additional properties (not related to memory)
  of the Linear and Mach call stacks. *)

(** TODO:
    we permit initial function to have arbitrary signature, thus might invalidate tailcall_possible.
    how do we specify sg in match_stacks? *)
(* additional properties about load_frame *)
(* 1. args in ls0 = args0 *)
(* 2. sig of fd0 agrees with typl0 and sigres0 *)
(* 3. contents in sp0 agrees with typl0 and args0, thus agrees with ls0 *)

(** generic lemma, should be put in loadframe.v *)
Lemma arg_len_rec_val:
  forall args0 tyl0 z,
    loadframe.args_len_rec args0 tyl0 = Some z ->
    z = loadframe.tyl_length tyl0.
Proof.
  clear. induction args0; simpl; intros.
  destruct tyl0; simpl in *; inv H; auto.
  destruct tyl0; inv H. destruct val_has_type_func; inv H1.
  destruct loadframe.args_len_rec eqn:C; inv H0.
  apply IHargs0 in C. subst z0; simpl; auto.
Qed.
  
Lemma tyl_length_non_neg:
  forall l, loadframe.tyl_length l >= 0.
Proof.
  clear. induction l as[|a h']; simpl; [| pose proof (typesize_pos a)]; Lia.lia.
Qed.
Lemma stack_contains_match_stacks_args_agree_rec:
  forall j f0 ls0 sp0 args0 tyl0 m,
    m |= contains_locations j sp0 0 (loadframe.tyl_length tyl0) Outgoing ls0 ->
    wd_args args0 tyl0 = true ->
    sig_args (Linear.fn_sig f0) = tyl0 ->
    set_arguments (loc_arguments (Linear.fn_sig f0)) args0 (Locmap.init Vundef) = ls0 ->
    forall n: nat,
      (n <= length tyl0)%nat ->
      let headN := (length tyl0 - n)%nat in
      let tyl := skipn headN tyl0 in
      let args := skipn headN args0 in
      let headn := firstn headN tyl0 in
      let ofs := loadframe.tyl_bytes headn in
      exists args',
        loadframe.agree_args_contains_aux m sp0 ofs args' tyl /\
        Val.inject_list j args args'.
Proof.
  clear. intros until n.
  assert (length args0 = length tyl0).
  { unfold wd_args in H0. repeat rewrite andb_true_iff in H0; destruct H0 as ((?&?)&?).
    clear H H1. generalize dependent tyl0; clear.
    induction args0; destruct tyl0; intro H; inv H; auto.
    rewrite andb_true_iff in H1; destruct H1. simpl. erewrite IHargs0; eauto. }
  induction n; intros.
  -
    simpl in *. subst headN. subst tyl args.
    assert (forall A (l: list A), skipn (length l) l = nil).
    { clear. induction l; auto. }
    rewrite Nat.sub_0_r, H5. rewrite <- H3, H5. exists nil. simpl. auto.
  -
    assert (n<=length tyl0)%nat by Lia.lia. specialize (IHn H5); clear H5.
    assert (Datatypes.S (length tyl0 - Datatypes.S n) = length tyl0 - n)%nat by Lia.lia.
    assert (forall A (l: list A) n, n < length l ->
                               exists a, l = (firstn n l) ++ a :: (skipn (n + 1) l))%nat.
    { clear. intros.
      remember (firstn n l) as h. remember (skipn (n+1) l)%nat as t. remember (skipn n l)%nat as t'.
      rewrite <- (firstn_skipn (n+1)%nat l). rewrite <- Heqt.
      rewrite <- (firstn_skipn (n)%nat l). rewrite <- Heqh, <- Heqt'.
      replace n with (length h). rewrite firstn_app_2.
      cut (exists a, firstn 1 t' = a :: nil). intros [a ?]. exists a. rewrite H0.
      rewrite <- app_assoc. simpl. auto.
      subst t'.
      assert (skipn n l <> nil).
      { clear Heqh Heqt. generalize dependent n. clear. intros n H C.
        pose proof (firstn_skipn n l).
        pose proof (app_length (firstn n l) (skipn n l)).
        rewrite firstn_length_le in H1; try Lia.lia.
        rewrite H0 in H1. assert (length (skipn n l) > 0)%nat by Lia.lia.
        rewrite C in H2. simpl in H2. Lia.lia. }
      destruct (skipn n l) eqn:?; [contradiction|].
      exists a. simpl. auto. rewrite Heqh. apply firstn_length_le; Lia.lia. }
    exploit (H6 _ tyl0 headN). subst headN; Lia.lia. intros [ty Htyl0].
    exploit (H6 _ args0 headN). subst headN; Lia.lia. intros [v Hargs0].
    replace tyl with (ty :: skipn (length tyl0 - n) tyl0).
    replace args with (v :: skipn (length tyl0 - n) args0).
    unfold loadframe.agree_args_contains_aux.
    unfold loadframe.load_stack, Mach.load_stack. destruct H as (_ & _ & ? & ? & ?).
    rewrite Z.add_0_l in H.
    remember (loadframe.tyl_length headn) as ofsn.
    
    pose proof (tyl_length_non_neg headn).
    assert (ofsn + typesize ty <= loadframe.tyl_length tyl0).
    { rewrite Htyl0. subst ofsn headn. generalize (firstn headN tyl0) (skipn (headN+1) tyl0).
      clear. intros l l0. induction l; intros; simpl; pose proof (tyl_length_non_neg l0); Lia.lia. }
    destruct IHn as [args' [AGREE' INJLIST']].
    assert (Val.has_type v ty /\ v <> Vundef) as [? ?].
    { generalize H3 H0 Htyl0 Hargs0; clear. generalize headN. clear. intros n H.
      assert (length (firstn n tyl0) = length (firstn n args0)).
      { destruct (le_dec n (length args0)).
        rewrite firstn_length_le; try congruence.
        rewrite firstn_length_le; try congruence.
        rewrite firstn_all2; try Lia.lia. rewrite firstn_all2; try Lia.lia. }
      unfold wd_args. repeat rewrite andb_true_iff. intros ((? & ?) & ?) ? ? .
      apply val_has_type_list_func_charact in H1. rewrite Htyl0, Hargs0 in H1. rewrite Hargs0 in H2.
      apply has_type_list_tail in H1; auto. apply vals_defined_tail in H2. simpl in H1, H2.
      split;[tauto| intro; subst; congruence].
    }

    pose proof (wd_args_set_arguments_get_agree
                  (Linear.fn_sig f0) args0 (loc_arguments (Linear.fn_sig f0)) ls0) as Hls0.
    rewrite H1 in Hls0. specialize (Hls0 H0 eq_refl H2 headN
                                         match ty with
                                         | Tlong => Twolong (S Outgoing (ofsn + 1) Tint) (S Outgoing ofsn Tint)
                                         | _ => One (S Outgoing ofsn ty)
                                         end
                                   ).
    exploit Hls0.
    { unfold loc_arguments. destruct Archi.ptr64 eqn:C; inversion C; clear C. rewrite H1.
      rewrite Htyl0. generalize H4 H5 Htyl0 Heqofsn. clear. intros. assert (headN < length tyl0)%nat by (subst headN; Lia.lia).
      rewrite (Zplus_0_r_reverse (loadframe.tyl_length headn)) in Heqofsn.
      subst headN headn. generalize H Htyl0 Heqofsn; clear. generalize (length tyl0 - Datatypes.S n)%nat. generalize 0.
      induction tyl0. intros until 1. inversion H.
      intros. destruct n0.
      simpl in *. subst; auto.
      simpl in *. apply IHtyl0; clear IHtyl0; [Lia.lia|congruence|Lia.lia]. }
    intros (v' & Hargs_v' & Val_v'); clear Hls0.
    assert (v = v').
    { generalize Hargs_v' Hargs0 H3. clear. intros. subst headN. rewrite Hargs0, <-H3 in Hargs_v'. clear Hargs0 H3.
      assert (length args0 - (Datatypes.S n) <= length args0)%nat by Lia.lia.
      revert H Hargs_v'. generalize (length args0 - Datatypes.S n)%nat. clear. intros.
      rewrite nth_error_app2, firstn_length_le, Nat.sub_diag in Hargs_v'; auto. inversion Hargs_v'; auto.
      rewrite firstn_length_le; auto. }
    subst v.

    assert (ty = Tlong \/ ty <> Tlong) as [Case_long | Case_normal].
    { clear. destruct ty; auto; right; intro C; inv C. }
    (* Tlong *)    
    { subst ty. simpl. 
      exploit (H8 (loadframe.tyl_length headn) Tint); try (simpl in *; Lia.lia; fail). apply Z.divide_1_l. 
      rewrite <- Heqofsn. intros (vlo & LOAD2 & INJ2).
      exploit (H8 (loadframe.tyl_length headn + 1) Tint); try (simpl in *; Lia.lia; fail). apply Z.divide_1_l.
      rewrite <- Heqofsn, Z.mul_add_distr_l, Z.add_assoc, Z.mul_1_r.
      intros (vhi & LOAD1 & INJ1).
      exists (v'::args'). destruct v'; inversion H11; try congruence.
      split; auto.
      pose proof (loadframe.tyl_length_agree tyl0). rewrite Z.mul_comm in H13. 
      cut (0 <= loadframe.tyl_bytes headn + 4 < loadframe.tyl_bytes tyl0). rewrite <- H13; intro.
      repeat loadframe.red_ptr.
      (* Vhi *)
      split. subst ofs headn. loadframe.red_ptr.
      rewrite Heqofsn, Z.mul_comm, Z.add_0_l, loadframe.tyl_length_agree in LOAD1.
      simpl in LOAD1. rewrite LOAD1. f_equal.
      generalize INJ1 INJ2 Val_v'; clear. unfold Locmap.getpair, Val.longofwords.
      generalize (ls0 (S Outgoing (ofsn + 1) Tint)) (ls0 (S Outgoing ofsn Tint)). clear. 
      intros vhi0 vlo0 INJhi INJlo [Heqhi Heqlo]. subst; inv INJhi; auto.

      (* Vlo *)
      split. subst ofs headn. loadframe.red_ptr.
      assert (0 <= loadframe.tyl_bytes (firstn headN tyl0) < 4 * loadframe.tyl_length tyl0).
      { match goal with |- context[loadframe.tyl_bytes ?x] => pose proof (loadframe.tyl_bytes_non_neg x); Lia.lia end. }
      repeat loadframe.red_ptr. rewrite Heqofsn, Z.mul_comm, Z.add_0_l, loadframe.tyl_length_agree in LOAD2.
      simpl in LOAD2. rewrite LOAD2. f_equal.
      generalize INJ1 INJ2 Val_v'; clear. unfold Locmap.getpair, Val.longofwords.
      generalize (ls0 (S Outgoing (ofsn + 1) Tint)) (ls0 (S Outgoing ofsn Tint)). clear. 
      intros vhi0 vlo0 INJhi INJlo [Heqhi Heqlo]. subst; inv INJlo; auto.

      generalize AGREE'. 
      cut (loadframe.tyl_bytes headn + AST.typesize Tlong = (loadframe.tyl_bytes (firstn (length tyl0 - n) tyl0))).
      intro OFS. rewrite <- OFS. auto.
      
      subst ofs.
      cut (headn ++ Tlong :: nil = firstn (length tyl0 - n) tyl0). intro A. rewrite <- A.
      rewrite loadframe.tyl_bytes_app. auto. rewrite <- H5. subst headn headN.
      assert (length tyl0 - Datatypes.S n < length tyl0)%nat by Lia.lia.
      generalize (length tyl0 - Datatypes.S n)%nat Htyl0 H15. clear.
      { intro n. generalize (skipn (n + 1) tyl0)%nat. intros l Htyl0 H0.
        assert (length (firstn n tyl0) = n) by (apply firstn_length_le; Lia.lia).
        generalize (firstn n tyl0) H0 H Htyl0. clear. intros. rewrite Htyl0. clear Htyl0 H0 tyl0.
        subst n. induction l0; auto.
        simpl in *. destruct (l0 ++ Tlong :: l) eqn:C. destruct l0; inv C.
        rewrite <- IHl0. auto. }

      rewrite Htyl0. subst headn. clear. rewrite loadframe.tyl_bytes_app.
      unfold loadframe.tyl_bytes; fold loadframe.tyl_bytes. unfold AST.typesize.
      pose proof (loadframe.tyl_bytes_non_neg (firstn headN tyl0)).
      pose proof (loadframe.tyl_bytes_non_neg (skipn (headN + 1) tyl0)). Lia.lia.
    }
    
    (* not Tlong *)
    {
      exploit H8; eauto; try Lia.lia; try (destruct ty; try contradiction; apply Z.divide_1_l).
      intros (v0 & LOAD & INJ). rewrite Z.add_0_l, Z.mul_comm in LOAD.
      replace ofs with (ofsn * 4).
      assert (ls0 (S Outgoing ofsn ty) = v') as Val_v.
      { destruct ty; auto. contradiction. }
      assert (Htriv: ofsn * 4 + AST.typesize ty = (loadframe.tyl_bytes (firstn (length tyl0 - n) tyl0))).
      { subst ofsn. rewrite loadframe.tyl_length_agree. 
        rewrite Htyl0 at 2. subst headn headN. generalize H5 H4. clear. 
        generalize (skipn (length tyl0 - Datatypes.S n + 1) tyl0). intro l'.
        intro. rewrite <- H5. clear H5. generalize (Datatypes.S n)%nat. clear. intros.
        pose proof (firstn_length_le tyl0). specialize (H (length tyl0 - n)%nat). exploit H; try Lia.lia.
        clear. generalize (length tyl0 - n)%nat, (firstn (length tyl0 - n) tyl0). clear.
        intros. rewrite <- Nat.add_1_r, <- H, firstn_app_2, loadframe.tyl_bytes_app. simpl. Lia.lia. }
      assert (0 <= ofsn * 4 <= Ptrofs.max_unsigned).
      { subst ofsn headn. split; try Lia.lia. generalize H10 H. clear. intros.
        pose proof (typesize_pos ty). unfold Ptrofs.max_unsigned. Lia.lia. }
      clear Val_v'. exists (v0 :: args'). split.
      destruct ty;
        try contradiction;
        (split; [auto; simpl; loadframe.red_ptr; rewrite Ptrofs.unsigned_repr; auto|
                 rewrite Htriv; auto]).
      constructor; congruence.
      subst ofsn ofs. apply loadframe.tyl_length_agree.
    } 

    pose proof (firstn_skipn headN args0). eapply (app_inv_head (firstn headN args0)).
    subst headn args headN. rewrite Nat.add_1_r, H5 in Hargs0. congruence.

    pose proof (firstn_skipn headN tyl0). eapply (app_inv_head (firstn headN tyl0)).
    subst headn tyl headN. rewrite Nat.add_1_r, H5 in Htyl0. congruence.
Qed.
    
  

Lemma stack_contains_match_stacks_args_agree:
  forall j f0 ls0 sp0 args0 tyl0 m,
    m |= contains_locations j sp0 0 (loadframe.tyl_length tyl0) Outgoing ls0 ->
    wd_args args0 tyl0 = true ->
    sig_args (Linear.fn_sig f0) = tyl0 ->
    set_arguments (loc_arguments (Linear.fn_sig f0)) args0 (Locmap.init Vundef) = ls0 ->
    exists args',
      loadframe.agree_args_contains m sp0 args' tyl0 /\
      Val.inject_list j args0 args'.
Proof.
  clear. intros. unfold loadframe.agree_args_contains.
  subst ls0. 
  exploit stack_contains_match_stacks_args_agree_rec; eauto.
  simpl. rewrite Nat.sub_diag; simpl. auto.
Qed.    
    

(** stacks are local *)
Inductive stacks_local (mu: Injections.Mu) (sp0: block) : list stackframe -> Prop :=
| stacks_local_loadframe:
    ~ Injections.SharedTgt mu sp0 ->
    stacks_local mu sp0 nil
| stacks_local_cons:
    forall fb sp ra c cs',
      ~ Injections.SharedTgt mu sp ->
      stacks_local mu sp0 cs' ->
      stacks_local mu sp0 (Stackframe fb (Vptr sp Ptrofs.zero) ra c :: cs').
                            
Inductive match_stacks (j: meminj)
          (f0: Linear.function) (ls0: locset)
          (sp0: block) (args0: list val) (tyl0: list typ) (sigres0: option typ) : 
          list Linear.stackframe -> list stackframe -> signature -> Prop :=
| match_stacks_empty:
    forall sg args0_src
      (SG_TAILCALL: sg = (Linear.fn_sig f0) \/
                    tailcall_possible sg)
(*      (ARGS: forall ofs ty,
          In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
          slot_within_bounds (function_bounds f0) Outgoing ofs ty) *)
      (WDARGS0: wd_args args0_src tyl0 = true)
      (ARGSREL: Val.inject_list j args0_src args0)
      (ARGSVAL: ls0 = set_arguments (loc_arguments (Linear.fn_sig f0))
                                    args0_src (Locmap.init Vundef))
      (ARGSTYP: sig_args (Linear.fn_sig f0) = tyl0 /\
                sig_res (Linear.fn_sig f0) = sigres0),
      match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 nil nil sg
| match_stacks_cons: forall f sp ls c cs fb sp' ra c' cs' sg trf
                       (TAIL: is_tail c (Linear.fn_code f))
                       (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
                       (TRF: transf_function f = OK trf)
                       (TRC: transl_code (make_env (function_bounds f)) c = c')
                       (INJ: j sp = Some(sp', (fe_stack_data (make_env (function_bounds f)))))
                       (TY_RA: Val.has_type ra Tptr)
                       (AGL: agree_locs f ls (parent_locset0 ls0 cs))
                       (ARGS: forall ofs ty,
                           In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
                           slot_within_bounds (function_bounds f) Outgoing ofs ty)
                       (STK: match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' (Linear.fn_sig f)),
    match_stacks j f0 ls0 sp0 args0 tyl0 sigres0
                 (Linear.Stackframe f (Vptr sp Ptrofs.zero) ls c :: cs)
                 (Stackframe fb (Vptr sp' Ptrofs.zero) ra c' :: cs')
                 sg.

(** Invariance with respect to change of memory injection. *)

Lemma stack_contents_change_meminj:
  forall m j j', inject_incr j j' ->
  forall f0 ls0 sp0 tyl0 cs cs' P,
  m |= stack_contents j f0 ls0 sp0 tyl0 cs cs' ** P ->
  m |= stack_contents j' f0 ls0 sp0 tyl0 cs cs' ** P.
Proof.
Local Opaque sepconj.
  induction cs as [ | [] cs]; destruct cs' as [ | [] cs']; simpl; intros; auto.
  rewrite <- contains_locations_incr with (j:=j); auto.
  destruct sp1; auto.
  rewrite sep_assoc in *.
  apply frame_contents_incr with (j := j); auto.
  rewrite sep_swap. apply IHcs. rewrite sep_swap. assumption.
Qed.

Lemma match_stacks_change_meminj:
  forall j j', inject_incr j j' ->
  forall f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg,
  match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg ->
  match_stacks j' f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg.
Proof.
  induction 2; intros.
- econstructor; eauto.
- econstructor; eauto.
Qed.

(** Invariance with respect to change of signature. *)

Lemma match_stacks_change_sig:
  forall sg1 j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg,
  match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg ->
  (* tailcall_possible (Linear.fn_sig f0) /\ tailcall_possible sg /\ *)
  tailcall_possible sg1 ->
  match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg1.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  intros. elim (H0 _ H1).
Qed.

(** Typing properties of [match_stacks]. *)

(** replace parent_sp into parent_sp0 *)
Lemma match_stacks_type_sp:
  forall j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg,
  match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg ->
  Val.has_type (parent_sp0 sp0 cs') Tptr.
Proof.
  induction 1; unfold parent_sp0; apply Val.Vptr_has_type.
Qed. 

Lemma match_stacks_type_retaddr:
  forall j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg,
  match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg ->
  Val.has_type (parent_ra cs') Tptr.
Proof.
  induction 1; unfold parent_ra. apply Val.Vnullptr_has_type. auto.
Qed.

(** * Syntactic properties of the translation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_save_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (save_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Remark find_label_restore_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (restore_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Lemma transl_code_eq:
  forall fe i c, transl_code fe (i :: c) = transl_instr fe i (transl_code fe c).
Proof.
  unfold transl_code; intros. rewrite list_fold_right_eq. auto.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
- auto.
- rewrite transl_code_eq.
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
  simpl. destruct (peq lbl l). reflexivity. auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) =
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl.
  unfold transl_body. unfold save_callee_save. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code tail property for Linear executions. *)

Lemma find_label_tail:
  forall lbl c c',
  Linear.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed.

(** Code tail property for translations *)

Lemma is_tail_save_callee_save:
  forall l ofs k,
  is_tail k (save_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto. 
Qed.

Lemma is_tail_restore_callee_save:
  forall l ofs k,
  is_tail k (restore_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto. 
Qed.

Lemma is_tail_transl_instr:
  forall fe i k,
  is_tail k (transl_instr fe i k).
Proof.
  intros. destruct i; unfold transl_instr; auto with coqlib.
  destruct s; auto with coqlib.
  destruct s; auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
Qed.

Lemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
Proof.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq.
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed.

Lemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (Linear.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (fn_code tf).
Proof.
  intros. rewrite (unfold_transf_function _ _ H). simpl.
  unfold transl_body, save_callee_save. 
  eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed.

(** TODO: move to one of the above sections *)
Lemma store_args_rec_contains_locations:
  forall j args args' m sp z tyl m' bound rs P ,
    Val.inject_list j args args' ->
    0 <= z ->
    size_arguments_32 tyl z <= bound ->
    loadframe.store_args_rec m (Vptr sp Ptrofs.zero) (4 * z) args' tyl = Some m' ->
    m |= contains_locations j sp 0 bound Outgoing rs ** P ->
    m' |= contains_locations j sp 0 bound Outgoing
       (set_arguments (loc_arguments_32 tyl z) args rs) ** P.
Proof.
  clear.
  induction args; intros. inv H. destruct tyl; [|discriminate]. simpl in *. inv H2. auto.
  inv H. destruct tyl. discriminate. simpl in H1.
  assert (t = Tlong \/ t <> Tlong) as [HT|HT] by (destruct t; auto; right; discriminate).
  * subst.
    exploit Val.hiword_inject; eauto.
    exploit Val.loword_inject; eauto.
    intros INJLO INJHI.
    exploit set_location; try exact INJHI.
    exact H3. instantiate (1:=z + 1). Lia.lia. instantiate (1:=Tint). simpl.
    apply Zle_trans with (size_arguments_32 tyl (z + typesize Tlong));
      [apply Zle_trans with (z + typesize Tlong);[simpl;Lia.lia|apply size_arguments_32_above] |Lia.lia].
    simpl; apply Z.divide_1_l.
    intros (m'0 & STOREHI & SEP').
    exploit set_location; try exact INJLO.
    exact SEP'. instantiate (1:=z). Lia.lia. instantiate (1:=Tint). simpl.
    apply Zle_trans with (size_arguments_32 tyl (z + typesize Tlong));
      [apply Zle_trans with (z + typesize Tlong);[simpl;Lia.lia|apply size_arguments_32_above] |Lia.lia].
    simpl; apply Z.divide_1_l.
    intros (m'1 & STORELO & SEP'').
    assert (STOREARGS': loadframe.store_args_rec m'1 (Vptr sp Ptrofs.zero)
                                                 (4 * z + AST.typesize Tlong) vl' tyl = Some m').
    { clear IHargs. destruct v'; try (simpl in H2; discriminate; fail).
      rewrite <- H2. clear H2.
      unfold loadframe.store_args_rec at 2. unfold loadframe.store_stack.
      unfold fe_ofs_arg in *. replace (0 + 4 * z + 4) with (0 + 4 * (z + 1)) by Lia.lia.
      unfold Val.hiword in STOREHI. unfold Val.loword in STORELO.
      rewrite STOREHI, STORELO. auto. }
    eapply (IHargs vl' m'1 sp (z + typesize Tlong) tyl m' bound) in SEP''; eauto.
    pose proof (set_arguments_reorder Tlong a tyl args z z rs).
    unfold set_arguments at 1, loc_arguments_32 at 1 in H.
    unfold set_arguments at 1, loc_arguments_32 at 1. fold set_arguments loc_arguments_32.
    rewrite H. unfold set_arguments at 2, loc_arguments_32 at 2. rewrite locmap_set_reorder. auto.
    simpl. right; simpl; Lia.lia. Lia.lia. simpl; Lia.lia.
    rewrite typesize_typesize in STOREARGS'. rewrite Z.mul_add_distr_l. auto.
    
  * assert (TALIGN: typealign t = 1) by (destruct t; auto; contradiction).
    assert (SIZEPOS: typesize t > 0) by (destruct t; simpl; Lia.lia).
    exploit set_location; eauto. instantiate (1:= t). 
    apply Zle_trans with (size_arguments_32 tyl (z + typesize t));
      [apply size_arguments_32_above| Lia.lia].
    rewrite TALIGN. apply Z.divide_1_l.
    intros (m'0 & STORE & SEP').
    assert (STOREARGS': loadframe.store_args_rec m'0 (Vptr sp Ptrofs.zero) (4 * z + AST.typesize t) vl' tyl = Some m').
    { clear IHargs. rewrite <- H2. clear H2.
      unfold loadframe.store_args_rec at 2. unfold loadframe.store_stack. 
      unfold fe_ofs_arg in *. rewrite STORE.
      destruct t; auto; discriminate. }
    assert (OFSABOVE: 0 <= z + typesize t) by (destruct t; simpl; Lia.lia).
    replace (4 * z + AST.typesize t) with (4 * (z + typesize t)) in STOREARGS'
      by (rewrite typesize_typesize; Lia.lia).
    specialize (IHargs vl' m'0 sp (z + typesize t) tyl m' bound
                       (Locmap.set (S Outgoing z t) a rs) P H8 OFSABOVE H1 STOREARGS' SEP').
    pose proof (set_arguments_reorder t a tyl args z z rs).
    unfold set_arguments at 1, loc_arguments_32 at 1 in H.
    unfold set_arguments at 1, loc_arguments_32 at 1. fold set_arguments loc_arguments_32.
    rewrite H. unfold set_arguments at 2, loc_arguments_32 at 2. 
    destruct t; auto. contradiction. Lia.lia. 
Qed.
        
(** * Semantic preservation *)

(** Preservation / translation of global symbols and functions. *)

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

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto.
  auto.
Qed.

Lemma find_function_translated:
  forall j ls rs m ros f,
  agree_regs j ls rs ->
  m |= globalenv_inject sge j ->
  Linear.find_function sge ros ls = Some f ->
  exists bf, exists tf,
     find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG [bound [_ [?????]]] FF.
  destruct ros; simpl in FF.
- exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF.
  rewrite Genv.find_funct_find_funct_ptr in FF.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  rewrite DOMAIN in H2. inv H2. simpl. auto. eapply FUNCTIONS; eauto.
- destruct (Genv.find_symbol sge i) as [b|] eqn:?; try discriminate.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  rewrite symbols_preserved. auto.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.
(** loader information *)
Variable ls0: locset.
Variable f0: Linear.function.
Variable sp0: block.
Variable args0: list val.
Variable tyl0: list typ.
Variable sigres0: option typ.

Variable j: meminj.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': block.
Hypothesis MS: match_stacks j f0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset0 ls0 cs).
Variable m': mem.

Hypothesis SEP: m' |= stack_contents j f0 ls0 sp0 tyl0 cs cs'.

(** when there's an external call with empty call-stack, 
    then this call must be a tailcall. *)
Hypothesis TAILCALL: cs' <> nil \/ tailcall_possible sg.


Lemma transl_external_argument:
  forall l,
  In l (regs_of_rpairs (loc_arguments sg)) ->
  exists v, extcall_arg rs m' (parent_sp0 sp0 cs') l v /\ Val.inject j (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l) by (apply loc_arguments_acceptable_2 with sg; auto).
  destruct l; red in H0.
- exists (rs r); split. constructor. auto.
- destruct sl; try contradiction.
  inv MS.
+ destruct TAILCALL as [C | TAILCALL']; [contradiction|].
  elim (TAILCALL' _ H).
+ simpl in SEP. unfold parent_sp0.
  assert (slot_valid f Outgoing pos ty = true).
  { destruct H0. unfold slot_valid, proj_sumbool. 
    rewrite zle_true by Lia.lia. rewrite pred_dec_true by auto. reflexivity. }
  assert (slot_within_bounds (function_bounds f) Outgoing pos ty) by eauto.
  exploit frame_get_outgoing; eauto. intros (v & A & B).
  exists v; split.
  constructor. exact A. red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_argument_2:
  forall p,
  In p (loc_arguments sg) ->
  exists v, extcall_arg_pair rs m' (parent_sp0 sp0 cs') p v /\ Val.inject j (Locmap.getpair p ls) v.
Proof.
  intros. destruct p as [l | l1 l2].
- destruct (transl_external_argument l) as (v & A & B). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists v; split; auto. constructor; auto. 
- destruct (transl_external_argument l1) as (v1 & A1 & B1). eapply in_regs_of_rpairs; eauto; simpl; auto.
  destruct (transl_external_argument l2) as (v2 & A2 & B2). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists (Val.longofwords v1 v2); split. 
  constructor; auto.
  apply Val.longofwords_inject; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
      list_forall2 (extcall_arg_pair rs m' (parent_sp0 sp0 cs')) locs vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) locs) vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument_2; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
      extcall_arguments rs m' (parent_sp0 sp0 cs') sg vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments.
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** TODO: this should be a general purposed lemma, move to another file? *)
Lemma loadv_fp_match:
  forall mu j chunk a a',
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (Injections.inj mu)) j ->
    sep_inject (Bset.inj_to_meminj (Injections.inj mu)) j ->
    Val.inject j a a' ->
    a <> Vundef ->
    Injections.FPMatch' mu (MemOpFP.loadv_fp chunk a)
                        (MemOpFP.loadv_fp chunk a').
Proof.
  clear. intros. 
  inv H2; simpl; try apply Injections.fp_match_emp'; try congruence.
  unfold FMemOpFP.loadv_fp. constructor; try apply FMemOpFP.emp_loc_match.
  unfold FP.ge_reads, FP.ge_writes; simpl.
  constructor; intros. exists b1.
  Locs.unfolds. unfold FMemOpFP.range_locset in *.
  destruct (eq_block b2 b); try discriminate.
  destruct zle, zlt; try discriminate.
  destruct eq_block; [|congruence]. subst. simpl.
  exploit Bset.inj_range. inv H; eauto. eauto.
  intros [b' INJ].
  assert (Bset.inj_to_meminj (Injections.inj mu) b' = Some (b, 0)).
  { unfold Bset.inj_to_meminj. rewrite INJ. auto. }
  eapply H1 in H6; eauto. apply H6 in H4.
  unfold Bset.inj_to_meminj in H4.
  destruct (Injections.inj mu b1) eqn:?;[|discriminate].
  inv H4. split. unfold Bset.inject_block. auto.
  clear H5. rewrite Ptrofs.add_zero in l0. rewrite Ptrofs.add_zero in l.
  destruct zle, zlt; try Lia.lia; auto.
Qed.

Lemma storev_fp_match:
  forall mu j chunk a a',
    Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu) ->
    inject_incr (Bset.inj_to_meminj (Injections.inj mu)) j ->
    sep_inject (Bset.inj_to_meminj (Injections.inj mu)) j ->
    Val.inject j a a' ->
    a <> Vundef ->
    Injections.FPMatch' mu (MemOpFP.storev_fp chunk a)
                        (MemOpFP.storev_fp chunk a').
Proof.
  clear. intros. 
  inv H2; simpl; try apply Injections.fp_match_emp'; try congruence.
  unfold FMemOpFP.store_fp. constructor; try apply FMemOpFP.emp_loc_match.
  unfold FP.ge_writes; simpl. rewrite Locs.locs_union_emp.
  constructor; intros. exists b1.
  Locs.unfolds. unfold FMemOpFP.range_locset in *.
  destruct (eq_block b2 b); try discriminate.
  destruct zle, zlt; try discriminate.
  destruct eq_block; [|congruence]. subst. simpl.
  exploit Bset.inj_range. inv H; eauto. eauto.
  intros [b' INJ].
  assert (Bset.inj_to_meminj (Injections.inj mu) b' = Some (b, 0)).
  { unfold Bset.inj_to_meminj. rewrite INJ. auto. }
  eapply H1 in H6; eauto. apply H6 in H4.
  unfold Bset.inj_to_meminj in H4.
  destruct (Injections.inj mu b1) eqn:?;[|discriminate].
  inv H4. split. unfold Bset.inject_block. auto.
  clear H5. rewrite Ptrofs.add_zero in l0. rewrite Ptrofs.add_zero in l.
  destruct zle, zlt; try Lia.lia; auto.
Qed.

Lemma loadv_fp_belongsto:
  forall chunk sp ofs fp,
    MemOpFP.loadv_fp chunk (Vptr sp ofs) = fp ->
    (forall b, Bset.belongsto (FP.blocks fp) b -> b = sp).
Proof.
  clear. intros; subst fp.
  unfold FP.blocks, FP.locs, Bset.belongsto, Locs.blocks in H0. Locs.unfolds. simpl in H0. destruct H0.
  red_boolean_true. unfold FMemOpFP.range_locset in H0. destruct eq_block; auto; discriminate.
  discriminate.
Qed.

Lemma load_stack_fp_belongsto:
  forall sp ty ofs ofs' fp,
    loadframe.load_stack_fp (Vptr sp ofs) ty ofs' = fp ->
    forall b, Bset.belongsto (FP.blocks fp) b -> b = sp.
Proof.
  clear. unfold loadframe.load_stack_fp. intros; subst fp.
  eapply loadv_fp_belongsto; eauto.
Qed.

(** Preservation of the arguments to a builtin. *)
Section BUILTIN_ARGUMENTS.
Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.
Variable j: meminj.
Variables m m': mem.
Variables ls ls0: locset.
Variable rs: regset.
Variables sp sp': block.
Variables parent retaddr: val.
Hypothesis INJ: j sp = Some(sp', fe.(fe_stack_data)).
Hypothesis AGR: agree_regs j ls rs.
Hypothesis SEP: m' |= frame_contents f j sp' ls ls0 parent retaddr ** minjection j m ** globalenv_inject sge j.

Lemma transl_builtin_arg_correct:
  forall a v,
  eval_builtin_arg sge ls (Vptr sp Ptrofs.zero) m a v ->
  (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) ->
  exists v',
     eval_builtin_arg sge rs (Vptr sp' Ptrofs.zero) m' (transl_builtin_arg fe a) v'
  /\ Val.inject j v v'.
Proof.
  assert (SYMB: forall id ofs, Val.inject j (Senv.symbol_address sge id ofs) (Senv.symbol_address sge id ofs)).
  { assert (G: meminj_preserves_globals sge j).
    { eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eexact SEP. }
    intros; unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol sge id) eqn:FS; auto.
    destruct G. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
Local Opaque fe.
  induction 1; simpl; intros VALID BOUNDS.
- assert (loc_valid f x = true) by auto.
  destruct x as [r | [] ofs ty]; try discriminate.
  + exists (rs r); auto with barg.
  + exploit frame_get_local; eauto. intros (v & A & B). 
    exists v; split; auto. constructor; auto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- set (ofs' := Ptrofs.add ofs (Ptrofs.repr (fe_stack_data fe))).
  apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  instantiate (1 := Val.offset_ptr (Vptr sp' Ptrofs.zero) ofs').
  simpl. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto. 
- econstructor; split; eauto with barg.
  unfold Val.offset_ptr. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
- apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. 
- destruct IHeval_builtin_arg1 as (v1 & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2); auto using in_or_app.
  exists (Val.longofwords v1 v2); split; auto with barg.
  apply Val.longofwords_inject; auto.
Qed.

Lemma transl_builtin_args_correct:
  forall al vl,
  eval_builtin_args sge ls (Vptr sp Ptrofs.zero) m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists vl',
     eval_builtin_args sge rs (Vptr sp' Ptrofs.zero) m' (List.map (transl_builtin_arg fe) al) vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; simpl; intros VALID BOUNDS.
- exists (@nil val); split; constructor.
- exploit transl_builtin_arg_correct; eauto using in_or_app. intros (v1' & A & B).
  exploit IHlist_forall2; eauto using in_or_app. intros (vl' & C & D).
  exists (v1'::vl'); split; constructor; auto.
Qed.


Variable mu: Injections.Mu.
Hypothesis BSETINJ: Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu).
Hypothesis INJINCR: inject_incr (Bset.inj_to_meminj (Injections.inj mu)) j.
Hypothesis SEPINJ : sep_inject (Bset.inj_to_meminj (Injections.inj mu)) j.
Hypothesis SYMBS: forall id bid, Senv.find_symbol sge id = Some bid -> (Injections.SharedSrc mu) bid.
Hypothesis STACKLOCAL: ~ (Injections.SharedTgt mu sp').

Lemma transl_builtin_arg_fp_match:
  forall a fp,
    MemOpFP.eval_builtin_arg_fp sge ls (Vptr sp Ptrofs.zero) a fp ->
    forall v, eval_builtin_arg sge ls (Vptr sp Ptrofs.zero) m a v ->
    (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
    (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) -> 
    exists fp', MemOpFP.eval_builtin_arg_fp sge rs (Vptr sp' Ptrofs.zero) (transl_builtin_arg fe a) fp'
           /\ Injections.FPMatch' mu fp fp'.
Proof.
  assert (SYMB: forall id ofs, Val.inject j (Senv.symbol_address sge id ofs) (Senv.symbol_address sge id ofs)).
  { assert (G: meminj_preserves_globals sge j).
    { eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eexact SEP. }
    intros; unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol sge id) eqn:FS; auto.
    destruct G. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
Local Opaque fe.
  induction 1; simpl; intros v EVAL VALID BOUNDS;
  try (exists FP.emp; split; [constructor|apply Injections.fp_match_emp']; fail).
- destruct x as [r | [] ofs ty]; try discriminate.
  + exists FP.emp. split. constructor. apply Injections.fp_match_emp'.
  + eexists. split. econstructor. apply Injections.fp_match_local_block. intros.
    eapply loadv_fp_belongsto in H; simpl; eauto. subst. auto.
  + exists FP.emp. split. constructor. apply Injections.fp_match_emp'.
  + exists FP.emp. split. constructor. apply Injections.fp_match_emp'.    
- eexists. split. econstructor. apply Injections.fp_match_local_block. intros.
  eapply loadv_fp_belongsto in H; simpl; eauto. subst. auto.
- eexists. split. econstructor. eapply loadv_fp_match; eauto. intro. inv EVAL. rewrite H in H4. discriminate.
- inv EVAL.
  exploit transl_builtin_arg_correct; try exact H4; eauto using in_or_app.
  exploit transl_builtin_arg_correct; try exact H6; eauto using in_or_app.
  intros [vlo' [EVAL2 _]] [vhi' [EVAL1 _]].
  exploit IHeval_builtin_arg_fp1; eauto using in_or_app.
  exploit IHeval_builtin_arg_fp2; eauto using in_or_app.
  intros [fp2' [EVALFP2 MATCH2]] [fp1' [EVALFP1 MATCH1]].
  eexists. split. econstructor; eauto. apply Injections.fp_match_union'; auto.
Qed.

Lemma transl_builtin_args_fp_match:
  forall al fp,
  MemOpFP.eval_builtin_args_fp sge ls (Vptr sp Ptrofs.zero) al fp ->
  forall vl, eval_builtin_args sge ls (Vptr sp Ptrofs.zero) m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists fp',
     MemOpFP.eval_builtin_args_fp sge rs (Vptr sp' Ptrofs.zero) (List.map (transl_builtin_arg fe) al) fp'
     /\ Injections.FPMatch' mu fp fp'.
Proof.
  induction 1; simpl; intros vl EVAL VALID BOUNDS.
- exists FP.emp. split. constructor. apply Injections.fp_match_emp'.
- inv EVAL. exploit transl_builtin_arg_fp_match; eauto using in_or_app. intros (fp1' & A & B).
  exploit IHeval_builtin_args_fp; eauto using in_or_app. intros (fp' & C & D).
  eexists. split. econstructor; eauto. apply Injections.fp_match_union'; auto.
Qed.

End BUILTIN_ARGUMENTS.
(** We don't need this since we do not support builtin functions *)

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Satisfaction of the separation logic assertions that describe the contents 
  of memory.  This is a separating conjunction of facts about:
-- the current stack frame
-- the frames in the call stack
-- the injection from the Linear memory state into the Mach memory state
-- the preservation of the global environment.
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs].
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Well-typedness of [f].
*)


(** New:
    match_states matching not only stack/memory but also footprints and mu *)

(** index := nat, since we don't have one to zero step case. *)

(** already included in stack_contents and match_stacks *)
(** TODO: we might need additional information about wd_args... 
Inductive match_load_frame : load_frame -> loadframe.load_frame -> mem -> Prop :=
| match_lf_intro:
    forall ls0 fd0 sp0 args0 typl0 sigres0 m,
      (* 1. args in ls0 = args0 *)
      ls0 = set_arguments (loc_arguments (Linear.fn_sig fd0)) args0 (Locmap.init Vundef) ->
      (* 2. sig of fd0 agrees with typl0 and sigres0 *)
      sig_args (Linear.fn_sig fd0) = typl0 ->
      sig_res (Linear.fn_sig fd0) = sigres0 ->
      (* 3. contents in sp0 agrees with typl0 and args0, thus agrees with ls0 *)
      loadframe.agree_args_contains m sp0 args0 typl0 ->
      (* 4. ? *)
      match_load_frame (mk_load_frame ls0 fd0) (loadframe.mk_load_frame sp0 args0 typl0 sigres0) m.
 *)

Inductive proper_stack_bottom (current_fd: Linear.fundef) (f0: Linear.function) : list Linear.stackframe -> Prop :=
| proper_nil:
    (** it is the initial function executing or [f0] is tailcall possible *)
    current_fd = (Internal f0) \/ tailcall_possible (Linear.funsig current_fd) ->
    proper_stack_bottom current_fd f0 nil
| proper_cons:
    forall f v ls c cs,
      proper_stack_bottom (Internal f) f0 cs ->
      proper_stack_bottom current_fd f0 (Linear.Stackframe f v ls c :: cs).
  
Inductive MATCH_STATE: bool -> nat -> Injections.Mu -> FP.t -> FP.t ->
                       Linear_local.core * mem -> Mach_local.core * mem -> Prop :=
| MATCH_STATE_intro:
    forall cs f sp c ls m cs' fb sp' rs m' j tf ls0 fd0 sp0 args0 tyl0 sigres0 mu n fp fp'
      (WT: wt_core (Linear_local.Core_State cs f (Vptr sp Ptrofs.zero) c ls (mk_load_frame ls0 fd0)))
      (STACKB: proper_stack_bottom (Internal f) fd0 cs)
      (STACKS: match_stacks j fd0 ls0 sp0 args0 tyl0 sigres0 cs cs' f.(Linear.fn_sig))
      (TRANSL: transf_function f = OK tf)
      (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
      (AGREGS: agree_regs j ls rs)
      (AGLOCS: agree_locs f ls (parent_locset0 ls0 cs))
      (INJSP: j sp = Some(sp', fe_stack_data (make_env (function_bounds f))))
      (TAIL: is_tail c (Linear.fn_code f))
      (SEP: m' |= frame_contents f j sp' ls (parent_locset0 ls0 cs) (parent_sp0 sp0 cs') (parent_ra cs')
               ** stack_contents j fd0 ls0 sp0 tyl0 cs cs'
               ** minjection j m
               ** globalenv_inject sge j)
      (** NEW *)
      (SPLOCAL: ~ Injections.SharedTgt mu sp')
      (STACKLOCAL: stacks_local mu sp0 cs')
      (AGMU: proper_mu sge tge j mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE true n mu fp fp'
                  (Linear_local.Core_State cs f (Vptr sp Ptrofs.zero) c ls
                                           (mk_load_frame ls0 fd0), m)
                  (Core_State cs' fb (Vptr sp' Ptrofs.zero) (transl_code (make_env (function_bounds f)) c) rs
                              (loadframe.mk_load_frame sp0 args0 tyl0 sigres0), m')
| MATCH_STATE_call_internal:
    forall cs f ls m cs' fb rs m' j tf ls0 fd0 sp0 args0 tyl0 sigres0 mu n fp fp'
      (WT: wt_core (Linear_local.Core_Callstate cs f ls (mk_load_frame ls0 fd0)))
      (STACKB: proper_stack_bottom f fd0 cs)
      (STACKS: match_stacks j fd0 ls0 sp0 args0 tyl0 sigres0 cs cs' (Linear.funsig f))
      (TRANSL: transf_fundef f = OK (Internal tf))
      (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
      (AGREGS: agree_regs j ls rs)
      (AGLOCS: agree_callee_save ls (parent_locset0 ls0 cs))
      (SEP: m' |= stack_contents j fd0 ls0 sp0 tyl0 cs cs'
               ** minjection j m
               ** globalenv_inject sge j)
      (** NEW *)
      (STACKLOCAL: stacks_local mu sp0 cs')
      (AGMU: proper_mu sge tge j mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE true n mu fp fp'
                  (Linear_local.Core_Callstate cs f ls (mk_load_frame ls0 fd0), m)
                  (Core_Callstate cs' fb rs (loadframe.mk_load_frame sp0 args0 tyl0 sigres0), m')
| MATCH_STATE_return:
    forall cs ls m cs' rs m' j sg ls0 fd0 sp0 args0 tyl0 sigres0 mu n fp fp' f
      (WT: wt_core (Linear_local.Core_Returnstate cs ls (mk_load_frame ls0 fd0)))
      (STACKB: proper_stack_bottom f fd0 cs)      
      (STACKS: match_stacks j fd0 ls0 sp0 args0 tyl0 sigres0 cs cs' sg)
      (AGREGS: agree_regs j ls rs)
      (AGLOCS: agree_callee_save ls (parent_locset0 ls0 cs))
      (SEP: m' |= stack_contents j fd0 ls0 sp0 tyl0 cs cs'
               ** minjection j m
               ** globalenv_inject sge j)
      (** NEW *)
      (STACKLOCAL: stacks_local mu sp0 cs')
      (AGMU: proper_mu sge tge j mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE true n mu fp fp'
                  (Linear_local.Core_Returnstate cs ls (mk_load_frame ls0 fd0), m)
                  (Core_Returnstate cs' rs (loadframe.mk_load_frame sp0 args0 tyl0 sigres0), m')
(* note here we have to deal with two cases: normal call / tailcall *)
| MATCH_STATE_call_external:
    forall cs f ls m cs' fb rs m' j tf callee args ls0 fd0 sp0 args0 tyl0 sigres0 mu b n fp fp'
      (WT: wt_core (Linear_local.Core_Callstate cs f ls (mk_load_frame ls0 fd0)))
      (STACKB: proper_stack_bottom f fd0 cs)
      (STACKS: match_stacks j fd0 ls0 sp0 args0 tyl0 sigres0 cs cs' (Linear.funsig f))
      (TRANSL: transf_fundef f = OK tf)
      (FIND: Genv.find_funct_ptr tge fb = Some tf)
      (AGREGS: agree_regs j ls rs)
      (AGLOCS: agree_callee_save ls (parent_locset0 ls0 cs))
      (SEP: m' |= stack_contents j fd0 ls0 sp0 tyl0 cs cs'
               ** minjection j m
               ** globalenv_inject sge j)
      (** NEW *)
      (STACKLOCAL: stacks_local mu sp0 cs')

      (EXTFUN: Genv.find_funct_ptr tge fb = Some (External callee))
      (TAILCALL: cs' <> nil \/ tailcall_possible (ef_sig callee))
      (EXTARG: extcall_arguments rs m' (parent_sp0 sp0 cs') (ef_sig callee) args)
      (ARGINJ: Val.inject_list j (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments (ef_sig callee)) args)
      
      (AGMU: proper_mu sge tge j mu)
      (RCPRESV: MemClosures_local.unmapped_closed mu m m')
      (FPMATCH: Injections.FPMatch' mu fp fp')
    ,
      MATCH_STATE b n mu fp fp'
                  (Linear_local.Core_Callstate cs f ls (mk_load_frame ls0 fd0), m)
                  (Core_CallstateOut cs' fb callee args rs (loadframe.mk_load_frame sp0 args0 tyl0 sigres0), m')

| MATCH_STATE_init:
    forall fd0 ls0 m fb m' j tf sp0 (* which is simply place holder *) args0 tyl0 sigres0 mu n
      (WT: wt_core (Linear_local.Core_CallstateIn nil (Internal fd0) ls0 (mk_load_frame ls0 fd0)))      
      (STACKS: match_stacks j fd0 ls0 sp0 args0 tyl0 sigres0 nil nil (Linear.fn_sig fd0))
      (TRANSL: transf_fundef (Internal fd0) = OK tf)
      (FIND: Genv.find_funct_ptr tge fb = Some tf)
      (SEP: m' |= minjection j m ** globalenv_inject sge j)
      
      (** NEW: *)

      (AGMU: proper_mu sge tge j mu)
      (Rcpresv: MemClosures_local.unmapped_closed mu m m')
    ,
      MATCH_STATE true n mu FP.emp FP.emp
                  (Linear_local.Core_CallstateIn nil (Internal fd0) ls0 (mk_load_frame ls0 fd0), m)
                  (Core_CallstateIn fb args0 tyl0 sigres0, m')
.



(** FOOTPRINT LEMMAS *)
Lemma shared_valid:
  forall mu j m m',
    proper_mu sge tge j mu ->
    m' |= minjection j m ->
    forall b, Injections.SharedTgt mu b -> Mem.valid_block m' b.
Proof.
  intros. inv H. exploit Bset.inj_range; eauto. inv proper_mu_inject; eauto. intros [b0 INJ].
  exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite INJ. eauto. intro INJ'.
  inv H0. eapply mi_mappedblocks; eauto.
Qed.

Lemma alloc_not_shared:
  forall mu j m m' stk lo hi m'',
    proper_mu sge tge j mu ->
    m' |= minjection j m ->
    Mem.alloc m' lo hi = (m'', stk) ->
    ~ Injections.SharedTgt mu stk.
Proof.
  intros. intro C. 
  exploit shared_valid; eauto.
  eapply Mem.fresh_block_alloc; eauto.
Qed.

Lemma alloc_fp_not_shared:
  forall mu j m m' lo hi fp fp0,
    proper_mu sge tge j mu ->
    m' |= minjection j m ->
    MemOpFP.alloc_fp m' lo hi = fp ->
    Injections.FPMatch' mu fp0 fp.
Proof.
  intros. subst fp. destruct (Mem.alloc m' lo hi) as [m'' stk] eqn:ALLOC.
  exploit Mem.alloc_result; eauto. intro STK.
  constructor; try apply FMemOpFP.emp_loc_match.
  constructor. intros. apply MemOpFP.alloc_fp_loc in H2. destruct H2; subst.
  exploit alloc_not_shared; eauto. intro; contradiction.
Qed.


Lemma store_stack_fp_belongsto:
  forall sp ty ofs ofs' fp,
    loadframe.store_stack_fp (Vptr sp ofs) ty ofs' = fp ->
    forall b, Bset.belongsto (FP.blocks fp) b -> b = sp.
Proof.
  clear. unfold loadframe.store_stack_fp. intros; subst fp.
(*   unfold FMemOpFP.loadv_fp in H0. *)
  unfold FP.blocks, FP.locs, Bset.belongsto, Locs.blocks in H0. Locs.unfolds. simpl in H0. destruct H0.
  red_boolean_true.
  fold (Locs.belongsto (FMemOpFP.range_locset sp
                                              (Ptrofs.unsigned (Ptrofs.add ofs ofs'))
                                              (size_chunk (chunk_of_type ty)))
                       b x) in H0. rewrite FMemOpFP.range_locset_loc in H0; tauto.
  Locs.unfolds. discriminate.
Qed.

Lemma store_args_fp_belongsto:
  forall sp tyl fp,
    loadframe.store_args_fp sp tyl = fp ->
    forall b, Bset.belongsto (FP.blocks fp) b -> b = sp.
Proof.
  clear. unfold loadframe.store_args_fp. intros; subst fp. revert H0. generalize 0.
  induction tyl; intros; simpl in H0.
  inv H0. inv H. 
  destruct a;
    apply FP.union_belongsto in H0; destruct H0; eauto; eauto using store_stack_fp_belongsto.
  apply FP.union_belongsto in H; destruct H; eauto using store_stack_fp_belongsto.
Qed.

Lemma free_fp_belongsto:
  forall sp lo hi fp,
    MemOpFP.free_fp sp lo hi = fp ->
    forall b, Bset.belongsto (FP.blocks fp) b -> b = sp.
Proof.
  clear. unfold FP.blocks, Bset.belongsto, Locs.blocks, FP.locs.
  intros; subst fp. simpl in H0. repeat rewrite Locs.emp_union_locs in H0. destruct H0.
  rewrite FMemOpFP.range_locset_loc in H. tauto.
Qed.

Lemma extcall_arguments_fp_exists:
  forall sp sg, exists fp, extcall_arguments_fp sp sg fp.
Proof.
  clear. unfold extcall_arguments_fp. intros.
  pose proof (loc_arguments_acceptable_2 sg). revert H.
  generalize (loc_arguments sg). clear. intros l H.
  induction l; intros. eexists; econstructor; eauto.
  destruct IHl. intros. apply H. simpl. apply in_app; auto.
  destruct a. destruct r.
  repeat econstructor; eauto.
  specialize (H (S sl pos ty) (or_introl eq_refl)); simpl in H.
  destruct sl; try contradiction. 
  repeat econstructor; eauto.
  destruct rhi, rlo; simpl in H; try (repeat econstructor; eauto; fail).
  1-3:destruct sl; try destruct sl0;
    match goal with
    | |- context[S Local ?x ?y] => specialize (H (S Local x y)); simpl in H; exfalso; apply H; auto
    | |- context[S Incoming ?x ?y] => specialize (H (S Incoming x y)); simpl in H; exfalso; apply H; auto
    | _ => idtac
    end;
    repeat econstructor; eauto.
Qed.

Lemma extcall_arguments_fp_belongsto:
  forall sp ofs sg fp, extcall_arguments_fp (Vptr sp ofs) sg fp ->
                  forall b, Bset.belongsto (FP.blocks fp) b -> b = sp.
Proof.
  clear. unfold extcall_arguments_fp. induction 1.
  intros. inv H. inv H0.
  inv H. inv H2.
  rewrite FP.emp_union_fp; auto.
  intros. apply FP.union_belongsto in H. destruct H; auto. eapply load_stack_fp_belongsto; eauto.
  inv H2; inv H3; repeat rewrite FP.emp_union_fp; repeat rewrite FP.fp_union_emp; auto.
  intros. apply FP.union_belongsto in H. destruct H; auto. eapply load_stack_fp_belongsto; eauto.
  intros. apply FP.union_belongsto in H. destruct H; auto. eapply load_stack_fp_belongsto; eauto.
  intros. apply FP.union_belongsto in H; destruct H; auto.
  apply FP.union_belongsto in H; destruct H; eapply load_stack_fp_belongsto; eauto.
Qed.
  
Ltac resolve_local_fps:=
  match goal with
  | H: Injections.FPMatch' ?mu ?fp ?fp' |- Injections.FPMatch' ?mu (FP.union ?fp _) (FP.union ?fp' _) =>
    apply Injections.fp_match_union'; [auto|resolve_local_fps]
  | |- Injections.FPMatch' _ _ (FP.union _ _) =>
    apply Injections.fp_match_union_T'; resolve_local_fps
  | |- Injections.FPMatch' _ _ FP.emp =>
    apply Injections.fp_match_emp'
  | |- Injections.FPMatch' _ _ (loadframe.load_stack_fp _ _ _) =>
    let b := fresh in
    let H := fresh in
    apply Injections.fp_match_local_block; intros b H;
    (exploit load_stack_fp_belongsto; eauto); intros; subst b; auto
  | |- Injections.FPMatch' _ _ (loadframe.store_stack_fp _ _ _) =>
    let b := fresh in
    let H := fresh in
    apply Injections.fp_match_local_block; intros b H;
    (exploit store_stack_fp_belongsto; eauto); intros; subst b; auto
  | |- Injections.FPMatch' _ _ (loadframe.store_args_fp _ _) =>
    let b := fresh in
    let H := fresh in
    apply Injections.fp_match_local_block; intros b H;
    (exploit store_args_fp_belongsto; eauto); intros; subst b; auto
  | H: (extcall_arguments_fp _ _ ?fp) |- Injections.FPMatch' _ _ ?fp =>
    let b := fresh in
    let H := fresh in
    apply Injections.fp_match_local_block; intros b H;
    (exploit extcall_arguments_fp_belongsto; eauto); intros; subst b; auto
  | |- Injections.FPMatch' _ _ (FMemOpFP.free_fp _ _ _) =>
    let b := fresh in
    let H := fresh in
    apply Injections.fp_match_local_block; intros b H;
    (exploit free_fp_belongsto; eauto); intros; subst b; auto
  | |- Injections.FPMatch' _ _ (MemOpFP.alloc_fp _ _ _) =>
    eapply alloc_fp_not_shared; eauto
  | H: forall b, FP.blocks ?fp b -> b = _ |- Injections.FPMatch' _ _ ?fp =>
    let b := fresh in
    let H' := fresh in
    apply Injections.fp_match_local_block; intros b H'; apply H in H'; subst b; auto
  | H: Injections.FPMatch' _ ?x ?y |- Injections.FPMatch' _ ?x ?y => eassumption    
  | _ => idtac
  end.

Lemma val_inject_length:
  forall j vl1 vl2,
    Val.inject_list j vl1 vl2 ->
    length vl1 = length vl2.
Proof. clear; induction vl1; intros vl2 H; inversion H; simpl; auto. Qed.

Theorem TRANSF_local_ldsim:
  @local_ldsim Linear_IS Mach_IS sG tG sge tge.
Proof.
  eapply (@Local_ldsim Linear_IS Mach_IS _ _ _ _ nat Nat.lt MATCH_STATE).
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
    exploit wt_initial_state; eauto. subst sG; eauto. apply wt_prog.  intro WT.
    assert (ARGINJ: Val.inject_list (Bset.inj_to_meminj (Injections.inj mu)) args args').
    { generalize ARGREL; clear. auto. } (* induction 1; eauto. constructor; auto. inv H; eauto. } *)
    unfold init_core_local in *. simpl in *.
    unfold Linear_local.init_core, init_core in *.
    unfold generic_init_core in INITCORE.
    rewrite HTG, symbols_preserved.
    rewrite HSG in INITCORE.
    destruct (Genv.find_symbol sge fid) eqn: FIND; try discriminate.
    destruct (Genv.find_funct_ptr sge b) eqn: FINDB; try discriminate.
    exploit function_ptr_translated; eauto. intros (tf & FINDB' & TRANSL).
    rewrite FINDB'.
    unfold Linear_local.fundef_init in INITCORE.
    destruct f; try discriminate.
    assert (exists tfd, tf = Internal tfd)  as [tfd INTERNAL] by (monadInv TRANSL; eauto). subst tf.
    unfold fundef_init.
    erewrite sig_preserved;[|eauto].
    destruct (wd_args args (sig_args (Linear.funsig (Internal f)))) eqn: WDARGS; [|discriminate].
    erewrite wd_args_inject; eauto.
    eexists. split. eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists 0%nat.
    inversion INITCORE; clear INITCORE.
    econstructor; eauto. subst. eauto.
    instantiate (2:= (Bset.inj_to_meminj (Injections.inj mu))).
    econstructor; eauto.

    unfold globalenv_inject, minjection; simpl.
    split; simpl. unfold LDefs.Inv in MINJ. auto.
    split; simpl. exists (Genv.genv_next tge). split.
    inv LRELY. apply (Ple_trans _ (Mem.nextblock tm0)); auto.
    inv INITTM. rewrite dom_match. eauto with coqlib. rewrite EQNEXT. eauto with coqlib.
    inversion GE_INIT_INJ.
    constructor.
    
    intros. exploit Bset.inj_range. inv mu_inject; eauto. rewrite mu_shared_tgt. eauto. intros (b00 & INJ0).
    inv MEMINITINJ. exploit inj_inject_id. unfold Bset.inj_to_meminj. rewrite INJ0. eauto. 
    unfold inject_id. intro INJ0'. inv INJ0'. unfold Bset.inj_to_meminj. rewrite INJ0. auto.

    intros. exploit Bset.inj_range. inv mu_inject; eauto. rewrite mu_shared_tgt. eauto. intros (b00 & INJ0).
    inv MEMINITINJ. exploit inj_inject_id. unfold Bset.inj_to_meminj. rewrite INJ0. eauto. 
    unfold inject_id. intro INJ0'. inv INJ0'. unfold Bset.inj_to_meminj in H. 
    destruct (Injections.inj mu b1) eqn: INJ1; inv H. eapply Bset.inj_injective; eauto. inv wd_mu_init; eauto.

    intros until b0; rewrite <- symbols_preserved. apply Genv.genv_symb_range.
    intros. exploit function_ptr_translated; eauto. intros (? & ? & ?).
    unfold Genv.find_funct_ptr in H1. destruct Genv.find_def eqn:C; inv H1. eapply Genv.genv_defs_range; eauto.
    unfold Genv.find_var_info. intros. rewrite <- S_EQ. destruct Genv.find_def eqn:C; inv H. eapply Genv.genv_defs_range; eauto.
    unfold disjoint_footprint; simpl; intros; auto.
    constructor; auto. inv GE_INIT_INJ; auto. 
    intros ? ? ? ? ?; auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.
  (* tau step *)
  - right. exists i. revert H. revert Hfp Lfp Lcore Lm.
    pose proof H0 as HWTC. intros Hfp Lfp Lcore Lm MATCH.
    eapply step_type_preservation in HWTC.
    Focus 2. inv GE_INIT. simpl in *. unfold Linear_local.init_genv. split; eauto.
    Focus 2. apply wt_prog.
    Focus 2. inv MATCH; auto.
    generalize Hfp Lfp Lcore Lm MATCH; clear Hfp Lfp Lcore Lm MATCH.

    induction H0; intros Hfp0 Lfp0 Lcore Lm MS; try inv MS;
      try rewrite transl_code_eq;
      try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
           intro BOUND; simpl in BOUND);
      unfold transl_instr.
    + (* Lgetstack *)
      destruct BOUND as [BOUND1 BOUND2].
      exploit wt_core_getstack; eauto. intros SV.
      unfold destroyed_by_getstack; destruct sl.
      * (* Lgetstack, local *)
        exploit frame_get_local; eauto. intros (v & A & B).
        eexists _, _, Lm. split.
        apply plus_one. apply exec_Mgetstack. exact A. reflexivity.
        split. apply Injections.fp_match_union'; auto.
        resolve_local_fps.
        econstructor; eauto with coqlib. 
        apply agree_regs_set_reg; auto.
        apply agree_locs_set_reg; auto.
        resolve_local_fps.
      * (* Lgetstack, incoming *)
        assert (HTG:tG = tge) by (inv TGE_INIT; auto).
        unfold slot_valid in SV. InvBooleans.
        exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
        inversion STACKS; clear STACKS.
        ** (* 1. s = nil -> not tailcall possible or it is the initial function f0 *)
          destruct SG_TAILCALL as [SG_TAILCALL|SG_TAILCALL]; [|elim (SG_TAILCALL _ IN_ARGS)].
          (** TODO: need to prove save_arguments -> frame_contents...  at initial call *)
          subst s cs'. inversion STACKB. destruct H1 as [INITF0|C]; [|elim (C _ IN_ARGS)]. inv INITF0.
          simpl in SEP.
          assert (exists v, load_stack Lm (Vptr sp1 Ptrofs.zero) ty (Ptrofs.repr (0 + 4 * ofs)) = Some v /\
                       Val.inject j ((set_arguments (loc_arguments (Linear.fn_sig fd0))
                                                    args0_src (Locmap.init Vundef)) (S Outgoing ofs ty)) v).
          { apply sep_pick2 in SEP. exploit loc_arguments_acceptable_2; eauto. intros [? ?].
            eapply get_location; eauto; try Lia.lia.
            apply Zle_trans with (m:=size_arguments (Linear.fn_sig fd0)).
            apply loc_arguments_bounded; auto.
            unfold size_arguments.
            rewrite loadframe.tyl_length_size_arguments_32.
            destruct Archi.ptr64 eqn:C; inv C. destruct ARGSTYP. rewrite H3. Lia.lia. }
          destruct H1 as  (v & A & B).
          eexists _, _, Lm. split.
          apply plus_one. eapply exec_Mgetparam; eauto.
          rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs.
          eapply frame_get_parent. eexact SEP.
          split. inv STACKLOCAL. resolve_local_fps.
          econstructor; eauto with coqlib. econstructor; eauto.
          apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto.
          erewrite agree_incoming by eauto. simpl. exact B.
          apply agree_locs_set_reg; auto. apply agree_locs_undef_locs; auto.
          inv STACKLOCAL. resolve_local_fps.
        ** (* 2. non-nil *)
          subst s cs'. exploit frame_get_outgoing.
          apply sep_proj2 in SEP. simpl in SEP. rewrite sep_assoc in SEP. eexact SEP.
          eapply ARGS; eauto.
          eapply slot_outgoing_argument_valid; eauto.
          intros (v & A & B).
          eexists _, _, Lm. split.
          apply plus_one. eapply exec_Mgetparam; eauto. subst tG. eauto.
          simpl. rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs.
          eapply frame_get_parent. eexact SEP.
          split. inv STACKLOCAL; resolve_local_fps.
          econstructor; eauto with coqlib. econstructor; eauto.
          apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto.
          erewrite agree_incoming by eauto. exact B.
          apply agree_locs_set_reg; auto. apply agree_locs_undef_locs; auto.
          inv STACKLOCAL. resolve_local_fps.
      * (* Lgetstack, outgoing *)
        exploit frame_get_outgoing; eauto. intros (v & A & B).
        eexists _, _, Lm. split.
        apply plus_one. apply exec_Mgetstack. exact A. eauto.
        split. resolve_local_fps.
        econstructor; eauto with coqlib.
        apply agree_regs_set_reg; auto.
        apply agree_locs_set_reg; auto.
        resolve_local_fps.
    + (* Lsetstack *)
      exploit wt_core_setstack; eauto. intros (SV & SW).
      set (ofs' := match sl with
                   | Local => offset_local (make_env (function_bounds f)) ofs
                   | Incoming => 0 (* dummy *)
                   | Outgoing => offset_arg ofs
                   end).
      eapply frame_undef_regs with (rl := destroyed_by_setstack ty) in SEP.
      assert (A: exists Lm',
                 store_stack Lm (Vptr sp' Ptrofs.zero) ty (Ptrofs.repr ofs') (rs0 src) = Some Lm'
                 /\ Lm' |= frame_contents f j sp' (Locmap.set (S sl ofs ty) (rs (R src))
                                                             (LTL.undef_regs (destroyed_by_setstack ty) rs))
                       (parent_locset0 ls0 s) (parent_sp0 sp1 cs') (parent_ra cs')
                       ** stack_contents j fd0 ls0 sp1 tyl0 s cs' ** minjection j m ** globalenv_inject sge j).
      { unfold ofs'; destruct sl; try discriminate.
        eapply frame_set_local; eauto. 
        eapply frame_set_outgoing; eauto. }
      eapply sep_pick3 in SEP; rename SEP into SEPOLD; destruct A as (Lm' & STORE & SEP).
      set (fp' := loadframe.store_stack_fp (Vptr sp' Ptrofs.zero)ty (Ptrofs.repr ofs')).
      eexists fp', _, Lm'. split.
      apply plus_one. destruct sl; try discriminate.
      econstructor. eexact STORE. eauto. eauto.
      econstructor. eexact STORE. eauto. eauto.
      split. subst fp'. resolve_local_fps.
      econstructor. eauto. eauto. eauto. eauto. eauto.
      apply agree_regs_set_slot. apply agree_regs_undef_regs. auto.
      apply agree_locs_set_slot. apply agree_locs_undef_locs. auto. apply destroyed_by_setstack_caller_save. auto.
      eauto. eauto with coqlib. eauto. eauto. auto. auto.
      eapply MemClosures_local.unchanged_on_unmapped_closed_preserved.
      eapply proper_mu_inject; eauto. 
      eapply MemClosures_local.inject_shared_src_valid.
      eapply proper_mu_inject; eauto. eapply proper_mu_inject_incr; eauto. simpl in SEPOLD. eauto.
      eapply MemClosures_local.inject_shared_tgt_valid.
      eapply proper_mu_inject; eauto. eapply proper_mu_inject_incr; eauto. simpl in SEPOLD. eauto.
      exact RCPRESV. apply Mem.unchanged_on_refl. eapply Mem.store_unchanged_on.
      unfold store_stack, Mem.storev in STORE. simpl in STORE. exact STORE.
      intros. auto.
      subst fp'. resolve_local_fps.
    + (* Lop *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      assert (exists v',
                 eval_operation sge (Vptr sp' Ptrofs.zero) (transl_op (make_env (function_bounds f)) op) rs0##args Lm = Some v'
                 /\ Val.inject j v v').
      eapply eval_operation_inject; eauto.
      eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
      eapply agree_reglist; eauto.
      apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. exact SEP.
      subst sG; auto.
      destruct H1 as [v' [A B]].

      erewrite (eval_operation_preserved tge sge) in A; [|intros; rewrite symbols_preserved; auto].
      pose proof SEP as C. repeat apply sep_drop in C. apply globalenv_inject_preserves_globals in C.
      pose proof SEP as D. do 2 apply sep_drop in D. apply sep_pick1 in D. 
      exploit (Op_fp.eval_operation_fp_inject C).
      exact INJSP. eapply agree_reglist. eauto. exact D. subst sG; exact H. subst sG; exact H0.
      intros (fp' & EVALFP' & FPINJ).
      erewrite (Op_fp.eval_operation_fp_preserved tge sge) in EVALFP'; [|intros; rewrite symbols_preserved; auto].
      eapply (@Op_fp.fp_inject_fp_match mu j fp fp') in FPINJ.
      exploit exec_Mop. exact A. exact EVALFP'. eauto. intro STEP.
      
      exists fp'. eexists. exists Lm.
      split. apply plus_one. unfold step_local. simpl. subst tG. exact STEP.

      split. apply Injections.fp_match_union'; auto.
      
      econstructor; eauto.

      apply agree_regs_set_reg; auto.
      rewrite transl_destroyed_by_op. apply agree_regs_undef_regs; auto. 
      apply agree_locs_set_reg; auto. apply agree_locs_undef_locs. auto. apply destroyed_by_op_caller_save.
      eauto with coqlib.
      apply frame_set_reg. apply frame_undef_regs. exact SEP.
      apply Injections.fp_match_union'; auto.
      eapply proper_mu_inject_incr; eauto.
      eapply proper_mu_sep_inject; eauto.
      eapply proper_mu_inject; eauto.
    + (* Lload *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      assert (exists a',
                 eval_addressing sge (Vptr sp' Ptrofs.zero)
                                 (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
                 /\ Val.inject j a a').
      eapply eval_addressing_inject; eauto.
      eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
      eapply agree_reglist; eauto. subst sG; eauto.
      destruct H1 as [a' [A B]].
      exploit loadv_parallel_rule.
      apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. eexact SEP.
      eauto. eauto. 
      intros [v' [C D]].

      exploit Injections.fp_match_union'. eauto.
      eapply (loadv_fp_match mu j chunk a a'); eauto.
      eapply proper_mu_inject; eauto.
      eapply proper_mu_inject_incr; eauto.      
      eapply proper_mu_sep_inject; eauto.
      inv B; simpl in H0; inversion H0. congruence.
      intros FPMATCH'. 
      
      eexists (MemOpFP.loadv_fp chunk a'), _, Lm. split.
      apply plus_one. econstructor.
      instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. rewrite <- HTG. exact symbols_preserved.
      eexact C. eauto. eauto.
      split. auto.
      
      econstructor; eauto with coqlib.
      
      apply agree_regs_set_reg. rewrite transl_destroyed_by_load. apply agree_regs_undef_regs; auto. auto.
      apply agree_locs_set_reg. apply agree_locs_undef_locs. auto. apply destroyed_by_load_caller_save. auto. 

    + (* Lstore *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      assert (exists a',
                 eval_addressing sge (Vptr sp' Ptrofs.zero)
                                 (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
                 /\ Val.inject j a a').
      eapply eval_addressing_inject; eauto.
      eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
      eapply agree_reglist; eauto. subst sG; eauto.
      destruct H1 as [a' [A B]].
      rewrite sep_swap3 in SEP.
      exploit storev_parallel_rule. eexact SEP. eauto. eauto. apply AGREGS. 
      apply sep_pick1 in SEP. rename SEP into SEPOLD; intros (m1' & C & SEP).
      rewrite sep_swap3 in SEP.

      exploit Injections.fp_match_union'. eauto.
      eapply (storev_fp_match mu j chunk a a'); eauto.
      eapply proper_mu_inject; eauto.
      eapply proper_mu_inject_incr; eauto.      
      eapply proper_mu_sep_inject; eauto.
      inv B; simpl in H0; inversion H0. congruence.
      intros FPMATCH'.
      
      eexists (FMemOpFP.storev_fp chunk a'), _, m1'. split.
      apply plus_one. econstructor.
      instantiate (1 := a'). rewrite <- A, <- HTG. apply eval_addressing_preserved. exact symbols_preserved.
      eexact C. eauto. eauto.
      split. auto.

      econstructor. eauto. eauto. eauto. eauto. eauto.
      rewrite transl_destroyed_by_store. apply agree_regs_undef_regs; auto.
      apply agree_locs_undef_locs. auto. apply destroyed_by_store_caller_save.
      auto. eauto with coqlib.
      eapply frame_undef_regs; eauto.
      auto. auto. auto.

      inv B; try discriminate. simpl in H0, C, SEPOLD. destruct AGMU.
      eapply MemClosures_local.store_val_inject_unmapped_closed_preserved; try eassumption.
      eapply MemClosures_local.inject_shared_src_valid; try eassumption.
      eapply MemClosures_local.inject_shared_tgt_valid; try eassumption.
      replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))) with (Ptrofs.unsigned ofs1 + delta) in C; eauto.
      exploit Mem.mi_representable; eauto. instantiate (1:= ofs1). left.
      exploit Mem.store_valid_access_3. exact H0. intros [RANGE _].
      eapply Mem.perm_implies. eapply Mem.perm_cur_max. eapply RANGE. destruct chunk; simpl; Lia.lia.
      constructor. intros [GE RANGE].
      rewrite Ptrofs.add_unsigned. do 2 rewrite Ptrofs.unsigned_repr. auto.
      pose proof (Ptrofs.unsigned_range_2 ofs1). Lia.lia. auto.
      pose proof (Ptrofs.unsigned_range_2 ofs1). Lia.lia. 

      auto.
    + (* Lcall internal/external *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      exploit find_function_translated; eauto.
      eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP. rewrite HSG; eauto. 
      intros [bf [tf' [A [B C]]]].
      exploit is_tail_transf_function; eauto. intros IST.
      rewrite transl_code_eq in IST. simpl in IST.
      exploit return_address_offset_exists. eexact IST. intros [ra D].
      destruct tf' as [tf'|ef'].
      * (* internal call *)
        eexists FP.emp, _, Lm. split.
        apply plus_one. econstructor; subst tG; eauto.
        split. resolve_local_fps.
        econstructor; eauto.
        constructor; auto.
        econstructor; eauto with coqlib.
        apply Val.Vptr_has_type.
        intros; red.
        apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
        apply loc_arguments_bounded; auto.
        simpl; red; auto.
        simpl. rewrite sep_assoc. exact SEP.
        constructor; auto.
        resolve_local_fps.
      * (* external call *)
        rewrite <- sep_assoc in SEP.
        (** build match_stacks at call point like regular internal call *)
        assert (STACKS': match_stacks j fd0 ls0 sp1 args0 tyl0 sigres0
                                      (Linear.Stackframe f (Vptr sp0 Ptrofs.zero) rs b :: s)
                                      (Stackframe fb (Vptr sp' Ptrofs.zero) (Vptr fb ra)
                                                  (transl_code (make_env (function_bounds f)) b) :: cs') 
                                      (Linear.funsig f')).
        { econstructor; eauto.
          eapply is_tail_trans. eapply is_tail_cons. apply is_tail_refl. eauto.
          unfold Tptr; simpl. destruct Archi.ptr64; auto.
          intros; red. apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
          apply loc_arguments_bounded; auto. }
        
        exploit transl_external_arguments.
        exact STACKS'.
        exact AGREGS.
        simpl; red; auto.
        simpl. apply sep_pick1 in SEP. eauto.
        left. intro Contra; inv Contra.
        intros [vl [ARGS VINJ]].

        destruct (extcall_arguments_fp_exists (Vptr sp' Ptrofs.zero) (Linear.funsig f')) as [fp' EXTARGFP].
        eexists _, _, Lm. split.
        eapply plus_one. eapply exec_Mcall_external; try (rewrite <- HTG; eauto; fail).
        rewrite <- (sig_preserved f' (External ef')) in ARGS. simpl in ARGS. eauto. auto.
        rewrite <- (sig_preserved f' (External ef')) in EXTARGFP. simpl in EXTARGFP. eauto. auto.
        split. resolve_local_fps.
        econstructor; eauto with coqlib.
        constructor; auto.
        simpl; red; auto.
        constructor; auto.
        left. intro CONTRA; inv CONTRA.
        simpl in ARGS|- * .
        rewrite <- (sig_preserved f' (External ef')) in ARGS; auto.
        rewrite <- (sig_preserved f' (External ef')) in VINJ; auto.    
        resolve_local_fps.
    + (* Ltailcall internal/external *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      rewrite (sep_swap (stack_contents j fd0 rs0 sp0 _ s cs')) in SEP.
      exploit function_epilogue_correct; eauto.
      apply sep_pick2 in SEP; rename SEP into SEPOLD. intros (rs2 & m1' & fp' & P & Q & R & S & T & U & SEP & STACKFP).
      rewrite sep_swap in SEP.
      exploit find_function_translated; eauto. 
      eapply sep_proj2. eapply sep_proj2. eexact SEP. rewrite HSG. eauto.
      intros [bf [tf' [A [B C]]]].
      assert (TAILCALL: tailcall_possible (Linear.funsig f')).
      { apply zero_size_arguments_tailcall_possible. eapply wt_core_tailcall; eauto. }
      assert (SPLOCALSRC: ~ Injections.SharedSrc mu stk).
      {
        generalize AGMU INJSP SPLOCAL. clear. intros. inv AGMU.
        intro. apply SPLOCAL. exploit Bset.inj_dom; eauto. intros [stk' INJ'].
        exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite INJ'. eauto. intro C.
        rewrite INJSP in C; inv C. eapply Bset.inj_range'; eauto. inv proper_mu_inject; eauto.
      }
      destruct tf' as [tfd' | ef'].

      ++ (* internal *)
        eexists _, _, m1'. split.
        eapply plus_right. simpl. rewrite <-HTG. eexact S. econstructor; try (rewrite <-HTG; eauto; fail); eauto.
        traceEq.
        split. resolve_local_fps.
        econstructor; eauto.
        inv STACKB; constructor; auto. 
        apply match_stacks_change_sig with (Linear.fn_sig f); auto.
        simpl in SEPOLD; inv AGMU; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; try eassumption.
        eapply MemClosures_local.inject_shared_src_valid; eauto.
        eapply MemClosures_local.inject_shared_tgt_valid; eauto.
        eapply Mem.free_unchanged_on. eauto. intros; auto.
        eapply Mem.free_unchanged_on. eauto. intros; auto. 
        resolve_local_fps.
      ++ (* external *)
        exploit transl_external_arguments.
        apply match_stacks_change_sig with (Linear.fn_sig f); eauto.
        eassumption.
        apply agree_callee_save_return_regs.
        apply sep_pick1 in SEP; exact SEP.
        auto.
        intros [vl [ARGS VINJ]]. erewrite <- sig_preserved in ARGS; eauto. simpl in ARGS.
        destruct (extcall_arguments_fp_exists (parent_sp0 sp0 cs') (ef_sig ef')) as [fp'' ARGSFP].
        eexists _, _, m1'. split.
        eapply plus_right. simpl. rewrite <-HTG. eexact S.
        eapply Mach_exec_Mtailcall_external; eauto; try (rewrite <-HTG; eauto; fail).
        erewrite <- sig_preserved in TAILCALL; eauto. eauto. 
       
        eapply tailcall_possible_extcall_arguments.
        erewrite <- sig_preserved in TAILCALL; eauto. eauto. eauto. 
        eapply tailcall_possible_extcall_arguments_fp.
        erewrite <- sig_preserved in TAILCALL; eauto. eauto. eauto. eauto.
        split. inv STACKLOCAL; resolve_local_fps.
        econstructor; eauto.
        inv STACKB; constructor; auto. 
        apply match_stacks_change_sig with (Linear.fn_sig f); auto.
        erewrite <- sig_preserved in TAILCALL; eauto. auto.
        erewrite <- sig_preserved in VINJ; eauto. auto.
        
        simpl in SEPOLD; inv AGMU; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; try eassumption.
        eapply MemClosures_local.inject_shared_src_valid; eauto.
        eapply MemClosures_local.inject_shared_tgt_valid; eauto.
        eapply Mem.free_unchanged_on. eauto. intros; auto.
        eapply Mem.free_unchanged_on. eauto. intros; auto.
        
        inv STACKLOCAL; resolve_local_fps.
    + (* Lbuiltin *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      destruct BOUND as [BND1 BND2].
      rewrite <- HSG in H, H0. 
      exploit transl_builtin_args_correct.
      eauto. eauto. rewrite sep_swap in SEP; apply sep_proj2 in SEP; eexact SEP.
      eauto. rewrite <- forallb_forall. eapply wt_core_builtin; eauto. exact BND2. intros [vargs' [P Q]].
      exploit transl_builtin_args_fp_match.
      eauto. eauto. rewrite sep_swap in SEP; apply sep_proj2 in SEP; eexact SEP.
      inv AGMU; eauto. inv AGMU; eauto. inv AGMU; eauto. auto. eauto. eauto.
      rewrite <- forallb_forall. eapply wt_core_builtin; eauto. exact BND2. intros [fp' [P' Q']].
      rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
      exploit helpers.i64ext_inject; eauto. eapply globalenv_inject_preserves_globals.
      rewrite sep_swap in SEP. apply sep_pick1 in SEP. rewrite <- HSG. eauto.
      apply sep_pick1 in SEP. eauto. rewrite <- HSG. intros [res' [EC RES]].
      eexists fp', _, Lm. split.
      apply plus_one. econstructor; eauto; try rewrite <- HTG; eauto.
      eapply eval_builtin_args_preserved with (ge1 := sge); eauto. exact symbols_preserved.
      eapply MemOpFP.eval_builtin_args_fp_preserved with (ge1 := sge); eauto. exact symbols_preserved.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      split. apply Injections.fp_match_union'; auto.
      eapply MATCH_STATE_intro; eauto with coqlib.
      apply agree_regs_set_res; auto. apply agree_regs_undef_regs; auto. 
      apply agree_locs_set_res; auto. apply agree_locs_undef_regs; auto.
      rewrite <- sep_assoc, sep_comm, sep_assoc in SEP. 
      apply frame_set_res. apply frame_undef_regs. auto.
      apply Injections.fp_match_union'; auto.

    + (* Llabel *)
      eexists FP.emp, _, Lm. split.
      apply plus_one; apply exec_Mlabel. split. resolve_local_fps.
      econstructor; eauto with coqlib. resolve_local_fps.
      
    + (* Lgoto *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      eexists FP.emp, _, Lm. split.
      apply plus_one; eapply exec_Mgoto; eauto; try (rewrite <- HTG; eauto; fail).
      apply transl_find_label; eauto.
      split. resolve_local_fps.
      econstructor; eauto.
      eapply find_label_tail; eauto.
      resolve_local_fps.

    + (* Lcond true *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      exploit Op_fp.eval_condition_fp_inject; try eassumption.
      eapply agree_reglist; eauto.
      apply sep_pick3 in SEP; exact SEP.
      intros (fp' & OPFP & FPINJ).
      eapply Op_fp.fp_inject_fp_match in FPINJ.
      eexists _, _, Lm. split.
      apply plus_one. eapply exec_Mcond_true; eauto.
      eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
      rewrite <- HTG. eauto. 
      eapply transl_find_label; eauto.
      split. resolve_local_fps. 
      econstructor; try eassumption.
      eapply find_label_tail; eauto.
      resolve_local_fps. 
      eapply proper_mu_inject_incr; eauto.
      eapply proper_mu_sep_inject; eauto.
      eapply proper_mu_inject; eauto.
    + (* Lcond false *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      exploit Op_fp.eval_condition_fp_inject; try eassumption.
      eapply agree_reglist; eauto.
      apply sep_pick3 in SEP; exact SEP.
      intros (fp' & OPFP & FPINJ).
      eapply Op_fp.fp_inject_fp_match in FPINJ.
      eexists _, _, Lm. split.
      apply plus_one. eapply exec_Mcond_false; eauto.
      eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
      split. resolve_local_fps.
      econstructor; eauto with coqlib. resolve_local_fps.
      eapply proper_mu_inject_incr; eauto.
      eapply proper_mu_sep_inject; eauto.
      eapply proper_mu_inject; eauto.
      
    + (* Ljumbtable *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      assert (rs0 arg = Vint n).
      { generalize (AGREGS arg). rewrite H. intro IJ; inv IJ; auto. }
      eexists _, _, Lm. split.
      apply plus_one; eapply exec_Mjumptable; eauto; try (rewrite <- HTG; eauto; fail).
      apply transl_find_label; eauto.
      split. resolve_local_fps.
      econstructor. eauto. eauto. eauto. eauto. eauto.
      apply agree_regs_undef_regs; auto.
      apply agree_locs_undef_locs. auto. apply destroyed_by_jumptable_caller_save.
      auto. eapply find_label_tail; eauto.
      apply frame_undef_regs; auto.
      auto. auto. auto. auto. resolve_local_fps.

    + (* Lreturn *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      rewrite (sep_swap (stack_contents j _ _ _ _ s cs')) in SEP.
      exploit function_epilogue_correct; eauto.
      intros (rs' & m1' & fp' & A & B & C & D & E & F & G & I).
      eexists _, _, m1'. split.
      eapply plus_right. rewrite <- HTG. eexact D. econstructor; eauto; try (rewrite <- HTG; eauto; fail). traceEq.
      split. eapply Injections.fp_match_union'; auto.
      resolve_local_fps.
      econstructor; eauto.
      rewrite sep_swap; exact G.
      assert (SPLOCALSRC: ~ Injections.SharedSrc mu stk).
      { generalize AGMU INJSP SPLOCAL. clear. intros. inv AGMU.
        intro. apply SPLOCAL. exploit Bset.inj_dom; eauto. intros [stk' INJ'].
        exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite INJ'. eauto. intro C.
        rewrite INJSP in C; inv C. eapply Bset.inj_range'; eauto. inv proper_mu_inject; eauto.
      }
      apply sep_pick2 in SEP. inv AGMU; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; try eassumption.
      eapply MemClosures_local.inject_shared_src_valid; eauto.
      eapply MemClosures_local.inject_shared_tgt_valid; eauto.
      simpl in SEP; eauto.
      eapply Mem.free_unchanged_on; eauto.
      eapply Mem.free_unchanged_on; eauto.
      
      resolve_local_fps.

    + (* internal function *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      revert TRANSL. unfold transf_fundef, transf_partial_fundef.
      destruct (transf_function f) as [tfn|] eqn:TRANSL; simpl; try congruence.
      intros EQ; inversion EQ; clear EQ; subst tf.
      rewrite sep_comm, sep_assoc in SEP. 
      exploit function_prologue_correct; eauto.
      red; intros; eapply wt_core_callstate_wt_regs; eauto.
      eapply match_stacks_type_sp; eauto.
      eapply match_stacks_type_retaddr; eauto.
      rename SEP into SEP_old;
        intros (j' & rs' & m2' & sp' & m3' & m4' & m5' & fp' & A & B & C & D & E & F & SEP & J & K & K' & K'' & L).
      apply sep_pick1 in SEP_old.
      pose proof (alloc_not_shared _ _ _ _ _ _ _ _ AGMU SEP_old A) as SPLOCAL.
      rewrite (sep_comm (globalenv_inject sge j')) in SEP.
      rewrite (sep_swap (minjection j' m')) in SEP.
      eexists _, _, _. split.
      eapply plus_left. econstructor; eauto; try (rewrite <- HTG; eauto; fail).
      rewrite <- HTG, (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body.
      eexact D. traceEq. 
      split. 
      resolve_local_fps. 
      eapply MATCH_STATE_intro with (j := j'); eauto with coqlib.
      eapply match_stacks_change_meminj; eauto.
      rewrite sep_swap in SEP. rewrite sep_swap. eapply stack_contents_change_meminj; eauto.
      (** TODO: function_prologue_correct should strengthen the "K: inject_incr j j'" part to
          inject_incr j j' /\ sep... /\ unchanged_on ... *)
      constructor; inv AGMU; auto.
      intros ? ? ? ? . apply K; auto.
      intros ? ? ? ? ? ? ? . eapply proper_mu_sep_inject; eauto.
      simpl in SEP_old; inv AGMU. eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; try eassumption.
      eapply MemClosures_local.inject_shared_src_valid; eauto.
      eapply MemClosures_local.inject_shared_tgt_valid; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      resolve_local_fps.
    + (* extcall: not possible case *)
      (* contradiction by:
         transf_fundef (Internal f) = OK tf ,
         Genv.find_funct_ptr tge fb = Some tf,
         Genv.find_funct_ptr tge fb = Some (External callee) *)
      rewrite FIND in EXTFUN. inv EXTFUN.
      exfalso. generalize TRANSL; clear.
      intro C. monadInv C.
    + (* dummy step, marshalling arguments *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      inversion STACKS.
      exploit loadframe.args_len_rec_exists; eauto. intros (z & ARGLEN).
      eapply loadframe.args_len_rec_inject in ARGLEN; try eassumption.
      Focus 2. unfold wd_args in WDARGS0. InvBooleans; auto.
      destruct (Mem.alloc Lm 0 (4 * z)) as [m' sp0'] eqn:? .
      exploit loadframe.store_args_exists. eapply wd_args_inject; eauto. eauto. eauto. intros (m'' & STOREARGS).
      assert (m''|= contains_locations j sp0'  fe_ofs_arg z Outgoing rs0 **
                 minjection j m ** globalenv_inject sge j).
      { (** TODO: store_args -> stack contains corresponding vars *)
        exploit alloc_rule; eauto; try Lia.lia.
        apply loadframe.args_len_rec_bound in ARGLEN; eauto.
        
        apply val_inject_length in ARGSREL.
        unfold wd_args in WDARGS0. destruct zlt. generalize l ARGLEN ARGSREL. clear.
        unfold Ptrofs.modulus, Int.max_unsigned, Int.modulus, Int.wordsize, Ptrofs.wordsize,
        Wordsize_32.wordsize, Wordsize_Ptrofs.wordsize. destruct Archi.ptr64 eqn:C;[inv C|].
        repeat rewrite Zlength_correct. intros. rewrite ARGSREL in *. clear ARGSREL. Lia.lia.
        simpl in WDARGS0; InvBooleans. discriminate.
        intro ALLOCSEP. replace (4 * z) with (0 + 4 * z) in ALLOCSEP by Lia.lia.
        exploit (initial_locations j sp0' 0 z). eauto. apply Z.divide_0_r.
        intros. instantiate (2:= Locmap.init Vundef). unfold Locmap.init; auto.
        instantiate (1:= Outgoing). clear ALLOCSEP; intros ALLOCSEP.
        generalize (minjection j m ** globalenv_inject sge j) ALLOCSEP STOREARGS ARGLEN WDARGS0 ARGSREL ARGSVAL ARGSTYP.
        clear. intro P; intros. destruct ARGSTYP as [ARGSTYP _].
        subst rs0. eapply store_args_rec_contains_locations; eauto. Lia.lia.
        erewrite ARGSTYP, loadframe.tyl_length_size_arguments_32, <- arg_len_rec_val; eauto. Lia.lia.
        unfold loadframe.store_args in STOREARGS. rewrite ARGSTYP. replace (4*0) with 0 by Lia.lia. auto.
      }
      assert (exists tfd, tf = Internal tfd) as [tfd INTERNAL].
      { monadInv TRANSL; eauto. }
      pose proof (alloc_not_shared mu j _ _ _ _ _ _ AGMU (sep_pick1 _ _ _ SEP) Heqp)
        as SPLOCAL.
      eexists _, _, _. split.
      apply plus_one. econstructor; eauto.
      split. resolve_local_fps. apply sep_pick1 in SEP; eauto.
      econstructor; eauto.
      constructor. auto.
      econstructor; eauto.
      rewrite <- INTERNAL. auto.
      rewrite <- INTERNAL. auto.
      { subst rs0. intro r.
        rewrite set_arguments_no_mreg. cbv. auto.
      }
      subst rs0. simpl; red; auto.
      simpl. erewrite <- arg_len_rec_val; eauto.
      constructor. auto.
      
      apply sep_pick1 in SEP; simpl in SEP; inv AGMU.
      eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; try eassumption.
      eapply MemClosures_local.inject_shared_src_valid; eauto.
      eapply MemClosures_local.inject_shared_tgt_valid; eauto.
      apply Mem.unchanged_on_refl.
      apply Mem.unchanged_on_trans with m'.
      eapply Mem.alloc_unchanged_on; eauto.
      eapply Mem.unchanged_on_implies. eapply loadframe.store_args_unchanged_on; eauto.
      intros. simpl. intro. subst b. congruence.
      resolve_local_fps. apply sep_pick1 in SEP; eauto.

    + (* impossible case *) monadInv TRANSL.
    + (* external call: i64ext *)
      assert (HSG: sge = sG) by (inv GE_INIT; auto).
      assert (HTG: tge = tG) by (inv TGE_INIT; auto).
      revert HSG HTG. rewrite FIND in EXTFUN. inv EXTFUN. monadInv TRANSL.
      intros. exploit helpers.i64ext_inject; eauto.
      eapply globalenv_inject_preserves_globals. do 2 apply sep_drop in SEP. rewrite <- HSG. eauto.
      apply sep_pick2 in SEP. eauto. intros [res' [EC RES]].
      eexists FP.emp, _, Lm. split. apply plus_one.
      eapply exec_function_external; eauto; try rewrite <- HSG; try rewrite <- HTG; eauto.
      eapply external_call_symbols_preserved. exact senv_preserved. rewrite HSG. eauto.
      repeat rewrite FP.fp_union_emp. split; auto.
      econstructor; eauto. apply agree_regs_set_pair; auto.
      apply agree_callee_save_set_result; auto.
      
    + exists FP.emp. destruct cs'; inv STACKS.
      exists (Core_State cs' fb (Vptr sp' Ptrofs.zero) (transl_code (make_env (function_bounds f)) c)
                    rs1 (loadframe.mk_load_frame sp0 args0 tyl0 sigres0)), Lm.
      split. apply plus_one. constructor.
      repeat rewrite FP.fp_union_emp. split; auto.
      econstructor; eauto.
      inv STACKB; auto.
      apply agree_locs_return with rs0; auto.
      apply frame_contents_exten with rs0 (parent_locset0 ls0 s); auto.
      simpl in SEP. rewrite sep_assoc in SEP. auto.
      inv STACKLOCAL; auto.
      inv STACKLOCAL; auto.
  (* at_external *)
  - intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MATCH ATEXT MEMCLOSURE GARGS.
    unfold at_external_local in ATEXT. simpl in ATEXT.
    unfold Linear_local.at_external in ATEXT.
    inv MATCH; try (inv ATEXT; fail).
    destruct f0 as [|e]; [discriminate|destruct e; try discriminate].
    destruct f0 as [|e]; [discriminate|destruct e; try discriminate].
    unfold at_external_local. simpl. exists 0%nat, args. rewrite FIND in EXTFUN. inversion EXTFUN; subst tf; clear EXTFUN.
    assert (callee = EF_external name sg0) by (monadInv TRANSL; auto). subst callee.
    assert (DEFINED: vals_defined argSrc = true).
    { revert GARGS. clear. induction argSrc; simpl; intros; auto.
      inv GARGS. destruct a; simpl in H1; auto.
    }
    destruct (invert_symbol_from_string sG _) eqn:FINDNAME; try discriminate.
    eapply match_genvs_invert_symbol_from_string_preserved in FINDNAME; eauto. rewrite FINDNAME.
    destruct peq; try discriminate.
    destruct peq; try discriminate.
    unfold init_genv_local in *. simpl in *. unfold init_genv, Linear_local.init_genv in *.
    destruct GE_INIT; subst sG; destruct TGE_INIT; subst tG.
    simpl in *; inv ATEXT.
    split. auto.
    split.
    { simpl in ARGINJ.
      generalize AGMU (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments sg) args ARGINJ GARGS. clear.
      induction l; intros.
      inv ARGINJ. constructor.
      inv ARGINJ. inv GARGS. exploit (IHl vl'); auto. clear IHl; intro IH.
      constructor; auto. clear IH.
      inv H1; try constructor; simpl in H2; try contradiction.
      econstructor; eauto. unfold Bset.inj_to_meminj. inv AGMU.
      eapply Bset.inj_dom in H2; eauto. destruct H2. rewrite H0.
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H0. eauto.
      intro. congruence.
    }
    split.
    inv AGMU. eapply sep_pick2 in SEP; simpl in SEP.
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_injection; eauto.
    eapply MemClosures_local.inject_shared_src_valid; eauto.
    eapply MemClosures_local.inject_shared_tgt_valid; eauto.
    eapply MemClosures_local.sep_inject_rc_inject; eauto.
    split. auto.
    split. unfold LDefs.Inv. inv AGMU. eapply sep_pick2 in SEP; simpl in SEP.
    eapply MemClosures_local.sep_inject_rc_inject; eauto.
    econstructor; eauto with coqlib.
    apply Injections.fp_match_emp'.

    exploit match_cu_match_genv. eauto.
    inv GE_INIT; eauto. inv TGE_INIT; eauto.
    inv GE_INIT; inv TGE_INIT. auto. eauto.
    intros. inv H; simpl; auto. destruct f1; destruct f2; monadInv H0; auto.

  (* after_external *)
  - intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MATCH GRES AFTEXT ORESREL.
    unfold after_external_local in AFTEXT. simpl in AFTEXT.
    unfold Linear_local.after_external in AFTEXT. inv MATCH.
    rewrite FIND in EXTFUN; inv EXTFUN.
    destruct f; inv AFTEXT. destruct e; inv H0.
    assert (callee = EF_external name sg) by (monadInv TRANSL; auto). subst callee.
    unfold after_external_local. simpl.
    exists (match oresTgt with
       | Some v => Core_Returnstate cs' (set_pair (loc_result sg) v rs) (loadframe.mk_load_frame sp0 args0 tyl0 sigres0)
       | None => Core_Returnstate cs' (set_pair (loc_result sg) Vundef rs) (loadframe.mk_load_frame sp0 args0 tyl0 sigres0)
       end).
    assert (Hcore' =
            match oresSrc with
            | Some v => (Linear_local.Core_Returnstate cs (Locmap.setpair (loc_result sg) v ls) (mk_load_frame ls0 fd0))
            | None => (Linear_local.Core_Returnstate cs (Locmap.setpair (loc_result sg) Vundef ls) (mk_load_frame ls0 fd0))
            end).
    { destruct oresSrc; destruct (sig_res sg); inv H1; auto.
      destruct val_has_type_func; inv H0; auto. }
    subst Hcore'. 
    split. destruct oresSrc; destruct oresTgt; destruct (sig_res sg); inv ORESREL; 
             destruct val_has_type_func; inv H1; try contradiction; auto. exact Vundef. exact Tint.
    intros. exists 0%nat. rename H1 into HTCORE'.
    assert (SEP': Lm' |= stack_contents j fd0 ls0 sp0 tyl0 cs cs' ** minjection j Hm' ** globalenv_inject sge j).
    { apply sep_swap in SEP.
      destruct SEP as (A & B & C).
      apply sep_swap. split; [|split].
      inv H. inv H0. inv H1. simpl in A |- * . inv AGMU.
      eapply MemClosures_local.sep_inject_rely_inject; eauto.
      apply m_invar with (m0 := Lm). exact B.
      * generalize H STACKLOCAL; clear. intro.
        revert cs. induction cs'; intros.
        inv STACKLOCAL. inv H. inv H2. eapply Mem.unchanged_on_implies; eauto.
        intros. destruct H2. destruct cs. simpl in H2. destruct H2. subst b. auto.
        simpl in H2. destruct s; simpl in H2. contradiction.
        simpl in H2. contradiction.
        
        inv STACKLOCAL. pose proof H3 as STACKLOCAL'. destruct cs. simpl.
        apply (IHcs' nil) in H3. inv H3.
        constructor; auto; intros. destruct H0; contradiction. destruct H0; contradiction.
        apply (IHcs' cs) in H3. clear IHcs'.
        apply Mem.unchanged_on_implies with
            (fun b ofs => m_footprint (stack_contents j fd0 ls0 sp0 tyl0 cs cs' ** globalenv_inject sge j) b ofs
            \/ ~ Bset.belongsto (Injections.SharedTgt mu) b); auto.
        inv H. inv H1. clear H0 H4 H5. 
        { inv H3; inv H; constructor; auto.
          intros. destruct H; eauto.
          intros. destruct H; eauto. }
        { intros. destruct H0. simpl in H0. destruct s. destruct H0.
          right.
          { unfold frame_contents in H0. destruct H0. unfold frame_contents_1 in H0.
            generalize H0 H2; clear. generalize (function_bounds f); clear. intro.
            generalize (fe_ofs_callee_save (make_env b0)). intro.
            generalize (used_callee_save b0). clear; intro.
            generalize (parent_locset0 ls0 cs). clear. intro.
            intro H.
            repeat match goal with
                   | H: m_footprint (_ ** _) _ _ |- _ =>
                     destruct H; try unfold contains_locations in H;
                       try unfold contains_callee_save; simpl in H
                   | H: b = _ /\ _ |- _ =>
                     destruct H; subst b; auto
                   end.
            revert l0 sp b ofs j z H. induction l; intros. contradiction.
            destruct H. unfold contains in H; simpl in H; destruct H; subst; auto.
            fold contains_callee_saves in H. eauto.
            destruct H0. unfold range in H0. simpl in H0. destruct H0. subst; auto.
            unfold range in H0. destruct H0. subst; auto.
          }
          { left. left. auto. }
          { right. auto. }
        }
      * generalize C H AGMU STACKLOCAL A. simpl. clear. 
        intros. intros b ofs INJFP STACKFP.
        specialize (C b ofs). unfold minjection in *; simpl in *.
        destruct INJFP as (b0 & delta & INJ & PERM').
        assert (m_footprint (stack_contents j fd0 ls0 sp0 tyl0 cs cs') b ofs ->
                ~ Injections.SharedTgt mu b).
        { generalize cs' cs H STACKLOCAL. clear. 
          induction cs'; simpl; intros.
          inv STACKLOCAL. destruct cs. simpl in H0. destruct H0; subst; auto.
          simpl in H0. destruct s. contradiction.
          inv STACKLOCAL. destruct cs. simpl in H0. contradiction.
          unfold stack_contents in H0. destruct s. fold stack_contents in H0.
          destruct H0.
          unfold frame_contents in H0. destruct H0. unfold frame_contents_1 in H0.
          generalize H0 H3; clear. generalize (function_bounds f); clear. intro.
          generalize (fe_ofs_callee_save (make_env b0)). intro.
          generalize (used_callee_save b0). clear; intro.
          generalize (parent_locset0 ls0 cs). clear. intro.
          intros FP H0. unfold contains_locations in FP.
          destruct FP. destruct H; subst; auto.
          destruct H. destruct H; subst; auto.
          unfold hasvalue, contains in H. destruct H. destruct H; subst; auto.
          destruct H. destruct H; subst ;auto.
          revert l0 sp b ofs j z H H0. induction l; intros. contradiction.
          destruct H. unfold contains in H; simpl in H; destruct H; subst; auto.
          fold contains_callee_saves in H. eauto.
          destruct H0. unfold range in H0. simpl in H0. destruct H0. subst; auto.
          unfold range in H0. destruct H0. subst; auto.
          eapply (IHcs' cs); auto.         
        }
        inv AGMU. destruct STACKFP; [|contradiction]. specialize (H0 H1).
        rewrite <- Mem.unchanged_on_perm in PERM'; eauto.
        apply C. exists b0, delta. split; eauto. left; auto.
        inv H. inv H2. eauto.
        simpl. inv H; inv H2. intro. eapply Bset.inj_dom in H2; eauto. destruct H2.
        exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H2. eauto.
        intro. rewrite INJ in H6. inv H6.
        eapply Bset.inj_range' in H2; eauto. inv proper_mu_inject; eauto.
        destruct (plt b0 (Mem.nextblock Hm)); auto.
        eapply Mem.mi_freeblocks in n; eauto. congruence.
    }
    destruct oresSrc; destruct oresTgt; try (inv ORESREL; fail).
    + econstructor; eauto with coqlib.
      (* wt_core *)
      inv WT. constructor; auto. apply wt_setpair.
      apply val_has_type_funcP. destruct sg; simpl in HTCORE'|-* . unfold proj_sig_res; simpl.
      destruct sig_res;[|discriminate]. destruct val_has_type_func eqn:?; inv HTCORE'; auto.
      auto.
      apply agree_regs_set_pair; auto. inv ORESREL; auto.
      econstructor; eauto. eapply proper_mu_inject_incr in H0; eauto.
      apply agree_callee_save_set_result; auto.
      inv H. inv H1. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
      
    + econstructor; eauto with coqlib.
      (* wt_core *)
      inv WT. constructor; auto. apply wt_setpair. auto. auto.
      apply agree_regs_set_pair; auto.
      apply agree_callee_save_set_result; auto.
      inv H. inv H1. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.

  (* halt *)
  - intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MATCH HALT HRC GRES.
    unfold halt_local in *; simpl in HALT |- * .
    unfold halted. unfold Linear_local.halted in HALT.
    inv MATCH; try discriminate.
    inv STACKS; try discriminate.
    eexists; split. eauto.
    assert (Val.inject j resSrc
                       (match loc_result {| sig_args := nil; sig_res := sigres0; sig_cc := cc_default |} with
                        | One r => rs r
                        | Twolong r1 r2 => Val.longofwords (rs r1) (rs r2)
                        end)).
    { inv HALT. unfold get_result. destruct ARGSTYP. unfold loc_result.
      destruct Archi.ptr64 eqn:C; inv C.
      unfold loc_result_32; simpl. destruct (sig_res (Linear.fn_sig fd0)).
      destruct t; try apply Val.longofwords_inject; try apply AGREGS.
      apply AGREGS. }
    split. 
    inv H; try constructor. simpl in GRES.
    inv AGMU. eapply Bset.inj_dom in GRES; eauto. destruct GRES.
    exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H. eauto. intro. rewrite H1 in H2; inv H2.
    econstructor. unfold Bset.inj_to_meminj. rewrite H; eauto. auto.
    split.
    inv AGMU. apply sep_pick2 in SEP; simpl in SEP.
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_injection; eauto.
    eapply MemClosures_local.inject_shared_src_valid; eauto.
    eapply MemClosures_local.inject_shared_tgt_valid; eauto.
    eapply MemClosures_local.sep_inject_rc_inject; eauto.
    split. auto.
    inv AGMU. apply sep_pick2 in SEP; simpl in SEP.
    eapply MemClosures_local.sep_inject_rc_inject; eauto.
    
    Unshelve. exact 1%positive.
Qed.

End PRESERVATION.      




Theorem transf_local_ldsim:
  forall return_address_offset
    (EXISTSOFS: forall f sg ros c, is_tail (Mcall sg ros::c) (fn_code f) ->
                              exists ofs, return_address_offset f c ofs),
    forall scu tcu,
      stacking.transf_program scu = OK tcu ->
      forall sge sG tge tG,
        init_genv_local Linear_IS scu sge sG ->
        init_genv_local (Mach_IS return_address_offset) tcu tge tG ->
        Genv.genv_next sge = Genv.genv_next tge ->
        local_ldsim sG tG sge tge.
Proof.
  intros. eapply TRANSF_local_ldsim; eauto.
  apply transf_program_match. auto.
Qed.

