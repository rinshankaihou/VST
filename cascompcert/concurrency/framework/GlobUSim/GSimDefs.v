Require Import List.

Require Import Values.

Require Import Blockset Footprint GlobDefs Injections.
Definition pc_valid_tid {ge}(pc:@ProgConfig ge)(t:tid):Prop:=
       ThreadPool.valid_tid pc.(thread_pool) t /\ ~ThreadPool.halted pc.(thread_pool) t.
(** This file defines matching conditions used in the
    global simulations. *)

Inductive cs_match {ge1 ge2: GlobEnv.t} :
  @CallStack.t ge1 -> @CallStack.t ge2 -> Prop :=
| match_cs_emp:
    forall cs1 cs2,
      CallStack.is_emp cs1 ->
      CallStack.is_emp cs2 ->
      cs_match cs1 cs2
| match_cs_cons:
    forall c1 cs1 c2 cs2,
      cs_match cs1 cs2 ->
      cs_match (c1::cs1) (c2::cs2).
      
Inductive ocs_match {ge1 ge2: GlobEnv.t} :
  option (@CallStack.t ge1) -> option (@CallStack.t ge2)-> Prop :=
| match_ocs_none: 
    ocs_match None None
| match_ocs_some:
    forall cs1 cs2,
      cs_match cs1 cs2 ->
      ocs_match (Some cs1) (Some cs2).

(** ThreadPool has same domain (valid thread id)
    and valid threads has the same call-stack length *)
Inductive thrddom_eq {ge1 ge2: GlobEnv.t} :
  @ProgConfig ge1-> @ProgConfig ge2-> Prop :=
  Thrddom_eq:
    forall pc1 pc2 tp1 tp2,
        tp1 = pc1.(thread_pool) ->
        tp2 = pc2.(thread_pool) ->
        (forall t, ocs_match (ThreadPool.get_cs tp1 t) (ThreadPool.get_cs tp2 t)) ->
        thrddom_eq pc1 pc2.


(** weaker version of thrddom_eq *)
Inductive cs_match' {ge1 ge2: GlobEnv.t} : @CallStack.t ge1 -> @CallStack.t ge2 -> Prop :=
| match_cs_emp' : forall cs1 cs2,
    CallStack.is_emp cs1 ->
    CallStack.is_emp cs2 ->
    cs_match' cs1 cs2
| match_cs_non_emp' : forall cs1 cs2,
    ~ CallStack.is_emp cs1 ->
    ~ CallStack.is_emp cs2 ->
    cs_match' cs1 cs2.

Lemma cs_match_cs_match' :
  forall ge1 ge2 (cs1: @CallStack.t ge1) (cs2: @CallStack.t ge2),
    cs_match cs1 cs2 ->
    cs_match' cs1 cs2.
Proof.
  induction 1.
  - constructor; auto.
  - eapply match_cs_non_emp'; intro C; inversion C.
Qed.

Inductive ocs_match' {ge1 ge2 : GlobEnv.t}
  : option (@CallStack.t ge1) -> option (@CallStack.t ge2) -> Prop :=
| match_ocs_none' : ocs_match' None None
| match_ocs_some' : forall cs1 cs2 : CallStack.t,
    cs_match' cs1 cs2 -> ocs_match' (Some cs1) (Some cs2).

Lemma ocs_match_ocs_match' :
  forall ge1 ge2 (ocs1: option (@CallStack.t ge1)) (ocs2: option (@CallStack.t ge2)),
    ocs_match ocs1 ocs2 ->
    ocs_match' ocs1 ocs2.
Proof.
  inversion 1.
  - constructor; auto.
  - apply match_ocs_some', cs_match_cs_match'; auto.
Qed.

Inductive thrddom_eq' {ge1 ge2 : GlobEnv.t} :
  @ProgConfig ge1 -> @ProgConfig ge2 -> Prop :=
  Thrddom_eq' : forall (pc1 pc2 : ProgConfig) (tp1 tp2 : ThreadPool.t),
    tp1 = thread_pool pc1 ->
    tp2 = thread_pool pc2 ->
    (forall t : tid,
        ocs_match' (ThreadPool.get_cs tp1 t) (ThreadPool.get_cs tp2 t)) ->
    thrddom_eq' pc1 pc2.

Lemma thrddom_eq_thrddom_eq':
  forall ge1 ge2 (pc1: @ProgConfig ge1) (pc2: @ProgConfig ge2),
    thrddom_eq pc1 pc2 ->
    thrddom_eq' pc1 pc2.
Proof.
  inversion 1; subst; simpl in *.
  econstructor; intros; eauto.
  apply ocs_match_ocs_match'; auto.
Qed.


Inductive atombit_eq {ge1 ge2: GlobEnv.t} :
  @ProgConfig ge1-> @ProgConfig ge2-> Prop :=
  Atombit_eq:
    forall pc1 pc2,
      pc1.(atom_bit) = pc2.(atom_bit) ->
      atombit_eq pc1 pc2.

Inductive tid_eq {ge1 ge2: GlobEnv.t} :
  @ProgConfig ge1 -> @ProgConfig ge2 -> Prop :=
  Tid_eq: forall pc1 pc2,
    pc1.(cur_tid) = pc2.(cur_tid) -> tid_eq pc1 pc2.


(* Target Footprint subset of F union S *)
Inductive fpG : FP.t -> Bset.t -> GlobEnv.t -> tid -> Prop :=
  FPG : forall fp Shared ge t,
    (forall b ofs,
        Locs.belongsto (Locs.union (Locs.union fp.(FP.cmps) fp.(FP.reads))
                                   (Locs.union fp.(FP.writes) fp.(FP.frees))) b ofs ->
        (* here we require b in Shared or _any_ freelist of thread t. *)
        Bset.belongsto Shared b \/ FLists.bbelongsto (GlobEnv.freelists ge) t b ) ->
    fpG fp Shared ge t.

Lemma fpG_emp:
  forall S GE t,
    fpG FP.emp S GE t.
Proof.
  intros.
  constructor; intros.
  unfold FP.emp in *; simpl in *.
  exfalso. eauto with locs.
Qed.

Lemma fpG_union:
  forall fp1 fp2 S GE t,
    fpG fp1 S GE t ->
    fpG fp2 S GE t ->
    fpG (FP.union fp1 fp2) S GE t.
Proof.
  intros.
  constructor; intros.
  inversion H; inversion H0; subst; simpl in *.  clear H H0.
  specialize (H2 b ofs).
  specialize (H7 b ofs).
  
  destruct (Locs.belongsto_dec
              (Locs.union (Locs.union (FP.cmps fp1) (FP.reads fp1)) (Locs.union (FP.writes fp1) (FP.frees fp1)))
              b ofs);
  destruct (Locs.belongsto_dec
              (Locs.union (Locs.union (FP.cmps fp2) (FP.reads fp2)) (Locs.union (FP.writes fp2) (FP.frees fp2)))
              b ofs);
  auto.
  exfalso. clear H2 H7 S GE t.
  unfold Locs.belongsto, Locs.union in *.
  destruct (FP.cmps fp1 b ofs); destruct (FP.cmps fp2 b ofs);
    destruct (FP.reads fp1 b ofs); destruct (FP.reads fp2 b ofs);
      destruct (FP.writes fp1 b ofs); destruct (FP.writes fp2 b ofs);
        destruct (FP.frees fp1 b ofs); destruct (FP.frees fp2 b ofs);
          simpl in *; contradiction.
Qed.

Lemma fpG_subset:
  forall fp1 fp2 S GE t,
    fpG fp1 S GE t ->
    FP.subset fp2 fp1 ->
    fpG fp2 S GE t.
Proof.
  intros.
  constructor; intros.
  inversion H; inversion H0; subst; simpl in *. clear H H0.
  apply (H2 b ofs). clear H2.
  generalize H1. pose proof (Locs.belongsto_subset).
  edestruct H. eapply H0. clear H H0 H2 H1.
  unfold Locs.subset, Locs.belongsto, Locs.union in *. intros.
  repeat (match goal with [H: forall b ofs, _ |- _]=> specialize (H b0 ofs0) end).
  destruct (FP.cmps fp1 b0 ofs0); destruct (FP.cmps fp2 b0 ofs0);
    destruct (FP.reads fp1 b0 ofs0); destruct (FP.reads fp2 b0 ofs0);
      destruct (FP.writes fp1 b0 ofs0); destruct (FP.writes fp2 b0 ofs0);
        destruct (FP.frees fp1 b0 ofs0); destruct (FP.frees fp2 b0 ofs0);
          simpl in *; eauto with bool.
Qed.

Definition LFPG (mu: Mu) (geTgt: GlobEnv.t) (t:tid) (fpSrc fpTgt: FP.t) : Prop :=
  FPMatch' mu fpSrc fpTgt /\ fpG fpTgt mu.(SharedTgt) geTgt t.

Lemma LFPG_union:
  forall mu TGE t fpS fpT fpS' fpT',
    LFPG mu TGE t fpS fpT ->
    LFPG mu TGE t fpS' fpT' ->
    LFPG mu TGE t (FP.union fpS fpS') (FP.union fpT fpT').
Proof.
  intros. destruct H, H0.
  split.
  apply fp_match_union'; auto.
  apply fpG_union; auto.
Qed.

Lemma LFPG_union_S:
  forall mu TGE t fpS fpT fpS',
    LFPG mu TGE t fpS fpT ->
    LFPG mu TGE t (FP.union fpS fpS') fpT.
Proof.
  intros. destruct H.
  split; auto.
  apply fp_match_union_S'; auto.
Qed.

Lemma LFPG_union_T:
  forall mu TGE t fpS fpT fpT',
    LFPG mu TGE t fpS fpT ->
    LFPG mu TGE t fpS fpT' ->
    LFPG mu TGE t fpS (FP.union fpT fpT').
Proof.
  intros. destruct H; destruct H0.
  split.
  apply fp_match_union_T'; auto.
  apply fpG_union; auto.
Qed.

Lemma LFPG_subset_S:
  forall mu TGE t fpS fpS' fpT,
    LFPG mu TGE t fpS fpT ->
    FP.subset fpS fpS' ->
    LFPG mu TGE t fpS' fpT.
Proof.
  intros. destruct H.
  split; auto.
  eapply fp_match_subset_S'; eauto.
Qed.

Lemma LFPG_subset_T:
  forall mu TGE t fpS fpT fpT',
    LFPG mu TGE t fpS fpT ->
    FP.subset fpT' fpT ->
    LFPG mu TGE t fpS fpT'.
Proof.
  intros. destruct H. split; auto.
  eapply fp_match_subset_T'; eauto.
  eapply fpG_subset; eauto.
Qed.
  

Lemma LocMatch_emp:
  forall mu ,LocMatch mu Locs.emp Locs.emp.
Proof.
  intros.
  constructor.
  intros.
  exists b. split;auto.
  unfold Locs.emp in H0.
  compute in H0.
  inversion H0.
Qed.
Lemma LFPG_emp:
  forall mu ge id,
    LFPG mu ge id FP.emp FP.emp.
Proof.
  intros.
  constructor.
  constructor;apply LocMatch_emp.
  apply fpG_emp.
Qed.


  
                
    

