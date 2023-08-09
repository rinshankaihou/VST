Require Import Coqlib Axioms Maps.
Require Import Values Blockset.

(** * Footprint *)
(** This file defines location set and footprint *)

(** ** Location set *)
Module Type LocsType.
  Parameter t : Type.
  Parameter belongsto : t -> block -> Z -> Prop.
  Parameter eq : t -> t -> Prop.
  Parameter emp : t.
  Parameter univ : t.
  Parameter subset : t -> t -> Prop.

  (* relations between [belongsto], [eq], and [subset] *)
  Axiom belongsto_eq: forall x y, 
      eq x y <-> (forall b ofs, belongsto x b ofs <-> belongsto y b ofs).
  Axiom belongsto_subset: forall x y,
      subset x y <-> (forall b ofs, belongsto x b ofs -> belongsto y b ofs).
  Axiom eq_subset: forall x y,
      eq x y <-> (subset x y /\ subset y x).
  (* subset is a partial order on [t], with bottom emp and top univ *)
  Parameter union : t -> t -> t.
  Parameter intersect : t -> t -> t.
  Parameter complement : t -> t.
  (* partial order properties of subset *)
  Axiom subset_emp: forall x, subset emp x.
  Axiom subset_univ: forall x, subset x univ.
  Axiom subset_refl: forall x, subset x x.
  Axiom subset_trans: forall x y z, subset x y -> subset y z -> subset x z.
  Axiom subset_antisym: forall x y, subset x y -> subset y x -> eq x y.
  (* properties on union, intersect, and complement *)
  Axiom union_emp: forall x, eq (union x emp) x.
  Axiom union_univ: forall x, eq (union x univ) univ.
  Axiom union_sym: forall x y, eq (union x y) (union y x).
  Axiom union_refl: forall x, eq (union x x) x.
  Axiom union_assoc:
    forall x y z, eq (union x (union y z)) (union (union x y) z).
  Axiom union_incr: forall x y, subset x (union x y).
  Axiom union_decr: forall x y z, subset (union x y) z -> subset x z.
  Axiom union_subset:
    forall x y z, subset x z -> subset y z -> subset (union x y) z.

  Axiom intersect_emp: forall x, eq (intersect x emp) emp.
  Axiom intersect_univ: forall x, eq (intersect x univ) x.
  Axiom intersect_sym: forall x y, eq (intersect x y) (intersect y x).
  Axiom intersect_refl: forall x, eq (intersect x x) x.
  Axiom intersect_assoc:
    forall x y z, eq (intersect x (intersect y z)) (intersect (intersect x y) z).
  Axiom intersect_incr: forall x y z, subset x (intersect y z) -> subset x y.
  Axiom intersect_decr: forall x y, subset (intersect x y) x.
  Axiom intersect_subset:
    forall x y z, subset x y -> subset x z -> subset x (intersect y z).
  
  Axiom union_intersect_distr:
    forall x y z,
      eq (union (intersect x z) (intersect y z))
         (intersect (union x y) z).

  Axiom complement_emp: eq (complement emp) univ.
  Axiom complement_univ: eq (complement univ) emp.
  Axiom complement_involution: forall x, eq (complement (complement x)) x.
  Axiom complement_union: forall x, eq (union x (complement x)) univ.
  Axiom complement_intersect: forall x, eq (intersect x (complement x)) emp.
  Axiom complement_contrapositive: forall x y, subset x y -> subset (complement y) (complement x).
  
  Axiom demorgan_union: forall x y, eq (complement (union x y)) (intersect (complement x) (complement y)).
  Axiom demorgan_intersect: forall x y, eq (complement (intersect x y)) (union (complement x) (complement y)).
                                  
End LocsType.




Module Locs <: LocsType.

  (** Location is defined as boolean valued function of block and offset *)
  Definition t : Type := block -> Z -> bool.
  Definition belongsto (ls:t) (b:block) (ofs:Z) : Prop := ls b ofs = true.
  Definition eq (ls1 ls2: t): Prop := forall b ofs, ls1 b ofs = ls2 b ofs.
  Theorem locs_eq: forall ls1 ls2,eq ls1 ls2 -> ls1=ls2.
  Proof.
    intros. unfold eq in H. assert(forall b:block,ls1 b=ls2 b). intro;specialize (H b); apply functional_extensionality;auto. apply functional_extensionality;auto.
  Qed.
  Theorem eq_refl: forall ls, eq ls ls.
  Proof. unfold eq. auto. Qed.
  Theorem eq_sym: forall ls1 ls2, eq ls1 ls2 -> eq ls2 ls1.
  Proof. unfold eq. auto. Qed.
  Theorem eq_trans: forall ls1 ls2 ls3, eq ls1 ls2 -> eq ls2 ls3 -> eq ls1 ls3.
  Proof. unfold eq. intros. rewrite H. auto. Qed.
  
  Definition emp : t := fun _ => fun _ => false.
  Definition univ : t := fun _ => fun _ => true.
  Definition subset (ls1 ls2: t) : Prop :=
    forall b ofs, belongsto ls1 b ofs -> belongsto ls2 b ofs.

  Theorem belongsto_emp:
    forall b ofs, belongsto emp b ofs -> False.
  Proof. firstorder. inversion H. Qed.
  Theorem belongsto_univ:
    forall b ofs, belongsto univ b ofs.
  Proof. firstorder. Qed.
  (* relations between eq, subset, belongsto *)
  Theorem belongsto_eq: forall x y, 
      eq x y <-> (forall b ofs, belongsto x b ofs <-> belongsto y b ofs).
  Proof.
    unfold belongsto, eq.
    split; intros. rewrite H. tauto.
    specialize (H b ofs).
    destruct (x b ofs), (y b ofs); auto;
      destruct H as [H1 H2]; firstorder.
  Qed.
  Theorem belongsto_subset: forall x y,
      subset x y <-> (forall b ofs, belongsto x b ofs -> belongsto y b ofs).
  Proof. firstorder. Qed.
  Theorem eq_subset: forall x y,
      eq x y <-> (subset x y /\ subset y x).
  Proof. intros. rewrite belongsto_eq. firstorder. Qed.

  Theorem belongsto_dec: forall x b ofs, {belongsto x b ofs} + {~ belongsto x b ofs}.
  Proof. intros. unfold belongsto. destruct (x b ofs); auto. Qed.
      
  Local Hint Resolve belongsto_eq belongsto_subset eq_subset : locs.

  
  (* subset is a partial order on [t], with bottom emp and top univ *)
  Definition union (ls1 ls2: t) : t := fun b => fun ofs => orb (ls1 b ofs) (ls2 b ofs).
  Definition intersect (ls1 ls2: t) : t := fun b => fun ofs => andb (ls1 b ofs) (ls2 b ofs).
  Definition complement (ls: t) : t := fun b => fun ofs => negb (ls b ofs).


  (* [TODO] should these definitions be included in this module?? *)
  (* By doing this, reasongning about these definitions would have to expose the module content *)
  (* set difference, A \ B = A \cap B' *)
  (* symmetric_difference, A \triangle B = A \ B \cup B \ A *)
  (* locset smile, A \cap B = \emptyset *)
  Definition diff (ls1 ls2 : t) : t := intersect ls1 (complement ls2).
  Definition sym_diff (ls1 ls2: t) : t := union (diff ls1 ls2) (diff ls2 ls1).
  Definition smile (ls1 ls2 : t) : Prop := eq (intersect ls1 ls2) emp.
  Definition nonemp (ls: t) : Prop :=  exists b ofs, belongsto ls b ofs.
  
  Definition blocks (ls: t): Bset.t := fun b => exists ofs, belongsto ls b ofs.
  
  Ltac unfolds :=
    unfold sym_diff, diff, smile, nonemp, subset, belongsto, eq, emp, univ, union, intersect, complement in *.

  (* partial order properties of subset *)
  Theorem subset_emp: forall x, subset emp x.
  Proof. intros. unfold subset. firstorder. inversion H. Qed.
  Theorem subset_univ: forall x, subset x univ.
  Proof. firstorder. Qed.
  Theorem subset_refl: forall x, subset x x.
  Proof. firstorder. Qed.
  Theorem subset_trans: forall x y z, subset x y -> subset y z -> subset x z.
  Proof. firstorder. Qed.
  Theorem subset_antisym: forall x y, subset x y -> subset y x -> eq x y.
  Proof. (* firstorder with locs. *) intros; rewrite eq_subset. auto. Qed.
  Local Hint Resolve subset_emp subset_univ subset_refl subset_trans subset_antisym : locs.
  Require Import Rtauto.
  (* properties on union, intersect, and complement *)
  Theorem union_emp: forall x, eq (union x emp) x.
  Proof. unfolds. intuition. Qed.
  Theorem union_univ: forall x, eq (union x univ) univ.
  Proof. unfolds. intuition. Qed.
  Theorem union_sym: forall x y, eq (union x y) (union y x).
  Proof. unfolds. intuition. Qed.
  Theorem union_sym_eq: forall x y,union x y = union y x.
  Proof. intros. apply locs_eq. apply union_sym. Qed.
  Theorem union_refl: forall x, eq (union x x) x.
  Proof. unfolds. intros. apply orb_diag. Qed.
  Theorem union_assoc:
    forall x y z, eq (union x (union y z)) (union (union x y) z).
  Proof. unfolds. intuition. Qed.
  Theorem union_assoc_eq: forall x y z,union x (union y z) = (union (union x y) z).
  Proof. intros;apply locs_eq;apply union_assoc. Qed.
  Theorem union_incr: forall x y, subset x (union x y).
  Proof. unfolds. intuition. Qed.
  Theorem union_decr: forall x y z, subset (union x y) z -> subset x z.
  Proof. unfolds. intuition. Qed.
  Theorem union_subset:
    forall x y z, subset x z -> subset y z -> subset (union x y) z.
  Proof. unfolds; intros; specialize (H b ofs); specialize (H0 b ofs);
           destruct (x b ofs), (y b ofs); auto. Qed.
  Local Hint Resolve
        union_emp union_univ union_sym union_refl
        union_assoc union_incr union_decr union_subset : locs.
  
  Theorem intersect_emp: forall x, eq (intersect x emp) emp.
  Proof. unfolds. eauto with bool. Qed.
  Theorem intersect_univ: forall x, eq (intersect x univ) x.
  Proof. unfolds. eauto with bool. Qed.
  Theorem intersect_sym: forall x y, eq (intersect x y) (intersect y x).
  Proof. unfolds. eauto with bool. Qed.
  Theorem intersect_refl: forall x, eq (intersect x x) x.
  Proof. unfolds. intros; destruct (x b ofs); auto. Qed.
  Theorem intersect_assoc:
    forall x y z, eq (intersect x (intersect y z)) (intersect (intersect x y) z).
  Proof. unfolds. eauto with bool. Qed.
  Theorem intersect_incr: forall x y z, subset x (intersect y z) -> subset x y.
  Proof. unfolds. intros. apply H in H0. destruct (y b ofs); auto. Qed.
  Theorem intersect_decr: forall x y, subset (intersect x y) x.
  Proof. unfolds. intros. destruct (x b ofs); auto. Qed.
  Theorem intersect_subset:
    forall x y z, subset x y -> subset x z -> subset x (intersect y z).
  Proof. unfolds. intros. specialize (H _ _ H1). specialize (H0 _ _ H1). rewrite H, H0. auto. Qed.
  
  Theorem union_intersect_distr:
    forall x y z,
      eq (union (intersect x z) (intersect y z))
         (intersect (union x y) z).
  Proof. unfolds. intros. destruct (x _ _), (y _ _), (z _ _); auto. Qed.
  Local Hint Resolve intersect_emp intersect_univ intersect_sym intersect_refl
        intersect_assoc intersect_incr intersect_decr intersect_subset union_intersect_distr : locs.
  
  Theorem complement_emp: eq (complement emp) univ.
  Proof. intuition. Qed.
  Theorem complement_univ: eq (complement univ) emp.
  Proof. intuition. Qed.
  Theorem complement_involution: forall x, eq (complement (complement x)) x.
  Proof. unfolds. intros. destruct (x _ _); auto. Qed.
  Theorem complement_union: forall x, eq (union x (complement x)) univ.
  Proof. unfolds. intros. destruct (x _ _); auto. Qed.
  Theorem complement_intersect: forall x, eq (intersect x (complement x)) emp.
  Proof. unfolds. intros. destruct (x _ _); auto. Qed.
  Theorem complement_contrapositive: forall x y, subset x y -> subset (complement y) (complement x).
  Proof. unfolds. intros. specialize (H b ofs). destruct (x _ _); auto. rewrite H in H0; auto. Qed.

  Theorem complement_smile: forall x,smile x (complement x).
  Proof. unfolds;intros;destruct x;auto. Qed.
  Theorem smile_complement_subset: forall l1 l2, smile l1 l2 ->  subset l1 (Locs.complement l2).
  Proof. Locs.unfolds;intros. specialize (H b ofs). rewrite H0 in H. destruct l2;auto.  Qed.
  Theorem demorgan_union:
    forall x y, eq (complement (union x y)) (intersect (complement x) (complement y)).
  Proof. unfolds. intros. destruct (x _ _), (y _ _); auto. Qed.
  Lemma complement_union_subset: forall x y,subset (complement (union x y))(complement y).
  Proof. unfolds;intros. destruct x,y;auto. Qed.
  Theorem demorgan_intersect:
    forall x y, eq (complement (intersect x y)) (union (complement x) (complement y)).
  Proof. unfolds. intros. destruct (x _ _), (y _ _); auto. Qed.

  Lemma locs_intersect_emp:
  forall x ,Locs.intersect x Locs.emp = Locs.emp.
  Proof. intro. apply Locs.locs_eq. apply Locs.intersect_emp. Qed.
  Lemma locs_intersect_emp_sym:
    forall x, Locs.intersect Locs.emp x =Locs.emp.
  Proof.
    intro.
    apply Locs.locs_eq.
    pose proof Locs.intersect_sym Locs.emp x.
    apply Locs.locs_eq in H.
    rewrite H.
    rewrite locs_intersect_emp.
    apply Locs.eq_refl.
  Qed.
  Lemma locs_union_emp:
    forall x,Locs.union x Locs.emp = x.
  Proof. intro. apply Locs.locs_eq. apply Locs.union_emp. Qed.
  Lemma emp_union_locs:
    forall x,Locs.union Locs.emp x=x.
  Proof. intro. apply Locs.locs_eq. pose proof Locs.union_sym Locs.emp x. apply Locs.locs_eq in H. rewrite H. rewrite locs_union_emp. apply Locs.eq_refl. Qed.
  Lemma locs_emp:
    ~ Locs.nonemp Locs.emp.
  Proof.
    intro.
    unfold Locs.nonemp in H.
    destruct H as[b[ofs H] ].
    inversion H.
  Qed.
  Lemma smile_sym: forall l1 l2,smile l1 l2 -> smile l2 l1.
  Proof. unfolds;intros. specialize (H b ofs). destruct l1,l2;auto. Qed.
  Lemma smile_union:
    forall l1 l2 l3, smile l1 l2->smile l1 l3-> smile l1 (Locs.union l2 l3).
  Proof. unfolds;intros; specialize (H b ofs);specialize (H0 b ofs);destruct l1,l2,l3;auto. Qed.
  Lemma smile_subset:
    forall l1 l2 l3, smile l1 l2 -> subset l3 l2 ->smile l1 l3.
  Proof.
    unfolds;intros.
    specialize (H b ofs).
    specialize (H0 b ofs).
    destruct l1 eqn:e1,l2 eqn:e2;auto;inversion H.
    destruct l3 eqn:e3;[destruct H0|];auto.
  Qed.
End Locs.

Hint Resolve
     Locs.eq_sym Locs.eq_refl Locs.eq_trans
     Locs.belongsto_emp Locs.belongsto_univ
     Locs.belongsto_eq Locs.belongsto_subset Locs.eq_subset Locs.belongsto_dec
     Locs.subset_emp Locs.subset_univ Locs.subset_refl Locs.subset_trans Locs.subset_antisym 
     Locs.union_emp Locs.union_univ Locs.union_sym Locs.union_refl
     Locs.union_assoc Locs.union_incr Locs.union_decr Locs.union_subset 
     Locs.intersect_emp Locs.intersect_univ Locs.intersect_sym Locs.intersect_refl
     Locs.intersect_assoc Locs.intersect_incr Locs.intersect_decr
     Locs.intersect_subset Locs.union_intersect_distr 
     Locs.complement_emp Locs.complement_univ Locs.complement_involution
     Locs.complement_union Locs.complement_intersect Locs.complement_contrapositive
     Locs.demorgan_union Locs.demorgan_intersect : locs.

(* TODO: move to another file? *)
(* are these tactics redundant? is there built-in approaches for the same purpose? *)
Ltac red_boolean_hypothesis_true' :=
  match goal with
  | H: ?x || ?y = true |- _ =>
    let Hx := fresh in
    rewrite orb_true_iff in H; destruct H as [Hx|Hx];
    try (rewrite Hx; clear Hx)
  | H: ?x && ?y = true |- _ =>
    let Hx := fresh in
    rewrite andb_true_iff in H; destruct H as [H Hx];
    try (rewrite H; clear H);
    try (rewrite Hx; clear Hx)
  | H: ?x = true |- _ =>
    try (rewrite H; clear H)
  end.
Ltac red_b_hypo_true:= repeat red_boolean_hypothesis_true'.

Ltac red_boolean_goal_true' :=
  match goal with
  | |- context[?x || true] =>
    rewrite orb_true_r
  | |- context[true || ?x] =>
    rewrite orb_true_l
  | |- context[true && ?x] =>
    rewrite andb_true_l
  | |- context[?x && true] =>
    rewrite andb_true_r
  end.
Ltac red_b_goal_true:= repeat red_boolean_goal_true'.

Ltac red_boolean_true :=
  red_b_hypo_true; red_b_goal_true; auto.


(** ** Footprint Definition *)

Module FP.

  (** Footprint is defined as a record with 4 fields:
      - [cmps] : locations corresponding to operations that observe memory permissions, e.g. checking if a pointer is valid
      - [reads] : locations corresponding to read operations
      - [writes] : locations corresponding to write operations
      - [frees] : locations corresponding to operations that modifies memory permissions, e.g. alloc and free
   *)

  (** By making footprint more precise, we are able to allow more programs to be data-race-free.
      E.g.,
                 array a[10];
               T1                T2
          x < a + 10;  ||  [x] <- 42;
      where T1 checks if x is within bound of the array [a], which in CompCert's semantics would observe memory permission of [x];
      and T2 writes to location x.
      If we simply treat [cmps] as normal meomry reads, this program would have data-race. 
   *)
      

  Record t :=
    { cmps: Locs.t;
      reads: Locs.t;
      writes: Locs.t;
      frees: Locs.t;
    }.

  Definition locs (fp: t) : Locs.t :=
    (Locs.union (cmps fp)
                (Locs.union (reads fp)
                            (Locs.union (writes fp) (frees fp)))).

  Definition blocks (fp: t) : Bset.t :=
    Locs.blocks (locs fp).
                  
  Definition emp : t := Build_t Locs.emp Locs.emp Locs.emp Locs.emp.

  Record eq (fp1 fp2: t) : Prop :=
    { eq_cmps: Locs.eq (fp1.(cmps)) (fp2.(cmps));
      eq_reads: Locs.eq (fp1.(reads)) (fp2.(reads));
      eq_writes: Locs.eq (fp1.(writes)) (fp2.(writes));
      eq_frees: Locs.eq (fp1.(frees)) (fp2.(frees));
    }.
  
  Definition union (fp1 fp2: t) : t :=
    Build_t (Locs.union fp1.(cmps) fp2.(cmps))
            (Locs.union fp1.(reads) fp2.(reads))
            (Locs.union fp1.(writes) fp2.(writes))
            (Locs.union fp1.(frees) fp2.(frees)).

  Definition intersect (fp1 fp2: t) : t :=
    Build_t (Locs.intersect fp1.(cmps) fp2.(cmps))
            (Locs.intersect fp1.(reads) fp2.(reads))
            (Locs.intersect fp1.(writes) fp2.(writes))
            (Locs.intersect fp1.(frees) fp2.(frees)).

  Record subset (fp1 fp2: t) : Prop :=
    { subset_cmps: Locs.subset (fp1.(cmps)) (fp2.(cmps));
      subset_reads: Locs.subset (fp1.(reads)) (fp2.(reads));
      subset_writes: Locs.subset (fp1.(writes)) (fp2.(writes));
      subset_frees: Locs.subset (fp1.(frees)) (fp2.(frees));
    }.

  (* ++ frees > writes > reads > cmps *)
  Definition ge_frees (fp: t) : Locs.t := frees fp.
  Definition ge_writes (fp: t) : Locs.t := Locs.union (writes fp) (ge_frees fp).
  Definition ge_reads (fp: t) : Locs.t := Locs.union (reads fp) (ge_writes fp).
  Definition ge_cmps (fp: t) : Locs.t := Locs.union (cmps fp) (ge_reads fp).
  
  Ltac unfolds_thrshd := unfold ge_cmps, ge_reads, ge_writes, ge_frees in *.

  Lemma eq_fp_eq_ge_cmps:
    forall fp1 fp2, eq fp1 fp2 -> Locs.eq (ge_cmps fp1) (ge_cmps fp2).
  Proof.
    intros. inversion H. unfolds_thrshd. Locs.unfolds.
    intros. repeat match goal with | H: forall _ _, _ = _ |- _ => rewrite H; clear H end.
    auto.
  Qed.

  Lemma eq_fp_eq_ge_reads:
    forall fp1 fp2, eq fp1 fp2 -> Locs.eq (ge_reads fp1) (ge_reads fp2).
  Proof.
    intros. inversion H. unfolds_thrshd. Locs.unfolds.
    intros. repeat match goal with | H: forall _ _, _ = _ |- _ => rewrite H; clear H end.
    auto.
  Qed.

  Lemma eq_fp_eq_ge_writes:
    forall fp1 fp2, eq fp1 fp2 -> Locs.eq (ge_writes fp1) (ge_writes fp2).
  Proof.
    intros. inversion H. unfolds_thrshd. Locs.unfolds.
    intros. repeat match goal with | H: forall _ _, _ = _ |- _ => rewrite H; clear H end.
    auto.
  Qed.

  Lemma eq_fp_eq_ge_frees:
    forall fp1 fp2, eq fp1 fp2 -> Locs.eq (ge_frees fp1) (ge_frees fp2).
  Proof.
    intros. inversion H. unfolds_thrshd. Locs.unfolds.
    intros. repeat match goal with | H: forall _ _, _ = _ |- _ => rewrite H; clear H end.
    auto.
  Qed.

  Lemma union_ge_cmps_comm:
    forall fp1 fp2, ge_cmps (union fp1 fp2) = Locs.union (ge_cmps fp1) (ge_cmps fp2).
  Proof.
    intros. destruct fp1, fp2. unfolds_thrshd. unfold union. simpl. apply Locs.locs_eq.
    Locs.unfolds. intros. repeat rewrite orb_assoc.
    
    repeat match goal with
           | |- _ || ?x = _ || ?x =>
             destruct x; [do 2 rewrite orb_true_r; auto| do 2 rewrite orb_false_r]
           | _ => auto; rewrite orb_comm; repeat rewrite orb_assoc
           end.
  Qed.

  Lemma union_ge_reads_comm:
    forall fp1 fp2, ge_reads (union fp1 fp2) = Locs.union (ge_reads fp1) (ge_reads fp2).
  Proof.
    intros. destruct fp1, fp2. unfolds_thrshd. unfold union. simpl. apply Locs.locs_eq.
    Locs.unfolds. intros. repeat rewrite orb_assoc.
    
    repeat match goal with
           | |- _ || ?x = _ || ?x =>
             destruct x; [do 2 rewrite orb_true_r; auto| do 2 rewrite orb_false_r]
           | _ => auto; rewrite orb_comm; repeat rewrite orb_assoc
           end.
  Qed.

  Lemma union_ge_writes_comm:
    forall fp1 fp2, ge_writes (union fp1 fp2) = Locs.union (ge_writes fp1) (ge_writes fp2).
  Proof.
    intros. destruct fp1, fp2. unfolds_thrshd. unfold union. simpl. apply Locs.locs_eq.
    Locs.unfolds. intros. repeat rewrite orb_assoc.
    
    repeat match goal with
           | |- _ || ?x = _ || ?x =>
             destruct x; [do 2 rewrite orb_true_r; auto| do 2 rewrite orb_false_r]
           | _ => auto; rewrite orb_comm; repeat rewrite orb_assoc
           end.
  Qed.

  Lemma union_ge_frees_comm:
    forall fp1 fp2, ge_frees (union fp1 fp2) = Locs.union (ge_frees fp1) (ge_frees fp2).
  Proof.
    intros. destruct fp1, fp2. unfolds_thrshd. unfold union. simpl. apply Locs.locs_eq.
    Locs.unfolds. intros. repeat rewrite orb_assoc.
    
    repeat match goal with
           | |- _ || ?x = _ || ?x =>
             destruct x; [do 2 rewrite orb_true_r; auto| do 2 rewrite orb_false_r]
           | _ => auto; rewrite orb_comm; repeat rewrite orb_assoc
           end.
  Qed.
    
  Lemma subset_ge_cmps_subset:
    forall fp1 fp2, FP.subset fp1 fp2 -> Locs.subset (ge_cmps fp1) (ge_cmps fp2).
  Proof.
    intros. destruct fp1, fp2. destruct H. unfolds_thrshd. Locs.unfolds. intros; simpl in *.
    red_b_hypo_true;
      repeat match goal with
             | H: forall _ _, _ |- _ => specialize (H b ofs)
             | H: ?x -> _, H': ?x |- _ => apply H in H'; clear H; rewrite H'
             end;
      red_b_goal_true; auto.
  Qed.

  Lemma subset_ge_reads_subset:
    forall fp1 fp2, FP.subset fp1 fp2 -> Locs.subset (ge_reads fp1) (ge_reads fp2).
  Proof.
    intros. destruct fp1, fp2. destruct H. unfolds_thrshd. Locs.unfolds. intros; simpl in *.
    red_b_hypo_true;
      repeat match goal with
             | H: forall _ _, _ |- _ => specialize (H b ofs)
             | H: ?x -> _, H': ?x |- _ => apply H in H'; clear H; rewrite H'
             end;
      red_b_goal_true; auto.
  Qed.

  Lemma subset_ge_writes_subset:
    forall fp1 fp2, FP.subset fp1 fp2 -> Locs.subset (ge_writes fp1) (ge_writes fp2).
  Proof.
    intros. destruct fp1, fp2. destruct H. unfolds_thrshd. Locs.unfolds. intros; simpl in *.
    red_b_hypo_true;
      repeat match goal with
             | H: forall _ _, _ |- _ => specialize (H b ofs)
             | H: ?x -> _, H': ?x |- _ => apply H in H'; clear H; rewrite H'
             end;
      red_b_goal_true; auto.
  Qed.

  Lemma subset_ge_frees_subset:
    forall fp1 fp2, FP.subset fp1 fp2 -> Locs.subset (ge_frees fp1) (ge_frees fp2).
  Proof.
    intros. destruct fp1, fp2. destruct H. unfolds_thrshd. Locs.unfolds. intros; simpl in *.
    red_b_hypo_true;
      repeat match goal with
             | H: forall _ _, _ |- _ => specialize (H b ofs)
             | H: ?x -> _, H': ?x |- _ => apply H in H'; clear H; rewrite H'
             end;
      red_b_goal_true; auto.
  Qed.

  Lemma ge_frees_subset_ge_writes:
    forall fp, Locs.subset (ge_frees fp) (ge_writes fp).
  Proof.
    intro. destruct fp. unfolds_thrshd. unfold locs. Locs.unfolds. simpl.
    intros. red_boolean_true.
  Qed.

  Lemma ge_writes_subset_ge_reads:
    forall fp, Locs.subset (ge_writes fp) (ge_reads fp).
  Proof.
    intro. destruct fp. unfolds_thrshd. unfold locs. Locs.unfolds. simpl.
    intros. red_boolean_true.
  Qed.

  Lemma ge_reads_subset_ge_cmps:
    forall fp, Locs.subset (ge_reads fp) (ge_cmps fp).
  Proof.
    intro. destruct fp. unfolds_thrshd. unfold locs. Locs.unfolds. simpl.
    intros. red_boolean_true.
  Qed.

  (* ++ *)




  
  (** 2 footprints conflict if either
      - [conflict_cf] : [cmps]-[frees] conflict
      - [conflict-rf] : [reads]-[frees] conflict
      - [conflict-wf] : [writes]-[frees] conflict
      - [conflict_ff] : [frees]-[frees] conflict
      - [conflict_rw] : [reads]-[writes] conflict, conventional read-write conflict
      - [conflict_ww] : [writes]-[writes] conflict, conventional write-write conflict

      The first 4 conflicting cases are required since we extended footprint with [cmps] and [frees], and the last 2 conflicting cases are conventional read-write and write-write conflicts. 
   *)

  Inductive conflict (fp1 fp2: t) : Prop :=
  | conflict_cf: Locs.nonemp ( Locs.union (Locs.intersect fp1.(cmps) fp2.(frees))
                                          (Locs.intersect fp2.(cmps) fp1.(frees)) )
                 -> conflict fp1 fp2
  | conflict_rf: Locs.nonemp ( Locs.union (Locs.intersect fp1.(reads) fp2.(frees))
                                          (Locs.intersect fp2.(reads) fp1.(frees)) )
                 -> conflict fp1 fp2
  | conflict_wf: Locs.nonemp ( Locs.union (Locs.intersect fp1.(writes) fp2.(frees))
                                          (Locs.intersect fp2.(writes) fp1.(frees)) )
                 -> conflict fp1 fp2
  | conflict_ff: Locs.nonemp ( Locs.intersect fp1.(frees) fp2.(frees) )
                 -> conflict fp1 fp2
  | conflict_rw: Locs.nonemp ( Locs.union (Locs.intersect fp1.(reads) fp2.(writes))
                                          (Locs.intersect fp2.(reads) fp1.(writes)) )
                 -> conflict fp1 fp2
  | conflict_ww: Locs.nonemp ( Locs.intersect fp1.(writes) fp2.(writes) )
                 -> conflict fp1 fp2
  .

  Inductive conflict' (fp1 fp2: t) : Prop :=
  | conflict_cf': Locs.nonemp (Locs.union (Locs.intersect (ge_cmps fp1) (ge_frees fp2))
                                          (Locs.intersect (ge_cmps fp2) (ge_frees fp1)))
                  -> conflict' fp1 fp2
  | conflict_rw': Locs.nonemp (Locs.union (Locs.intersect (ge_reads fp1) (ge_writes fp2))
                                          (Locs.intersect (ge_reads fp2) (ge_writes fp1)))
                  -> conflict' fp1 fp2.

  Lemma conflict'_conflict_equiv:
    forall fp1 fp2, conflict fp1 fp2 <-> conflict' fp1 fp2.
  Proof.
    intros. destruct fp1, fp2.
    split; intro H; inv H; destruct H0 as (b&ofs&H0).
    1-6: try (econstructor; unfolds_thrshd; Locs.unfolds; exists b, ofs; simpl in *;
              red_boolean_true; fail).
    1-2: unfolds_thrshd; Locs.unfolds; simpl in *; red_b_hypo_true;
      try (econstructor; Locs.unfolds; exists b, ofs; simpl; red_boolean_true; fail).
  Qed.

  Record smile (fp1 fp2: t) : Prop :=
    {
      smile_cf: Locs.smile fp1.(cmps) fp2.(frees) /\ Locs.smile fp2.(cmps) fp1.(frees);
      smile_rf: Locs.smile fp1.(reads) fp2.(frees) /\ Locs.smile fp2.(reads) fp1.(frees);
      smile_rw: Locs.smile fp1.(reads) fp2.(writes) /\ Locs.smile fp2.(reads) fp1.(writes);
      smile_wf: Locs.smile fp1.(writes) fp2.(frees) /\ Locs.smile fp2.(writes) fp1.(frees);
      smile_ww: Locs.smile fp1.(writes) fp2.(writes);
      smile_ff: Locs.smile fp1.(frees) fp2.(frees);
    }.

  Record smile' (fp1 fp2: t) : Prop :=
    {
      smile'_cf:
        Locs.smile (ge_cmps fp1) (ge_frees fp2) /\ Locs.smile (ge_cmps fp2) (ge_frees fp1);
      smile'_rw:
        Locs.smile (ge_reads fp1) (ge_writes fp2) /\ Locs.smile (ge_reads fp2) (ge_writes fp1);
    }.

  Lemma smile'_smile_equiv:
    forall fp1 fp2, smile fp1 fp2 <-> smile' fp1 fp2.
  Proof.
    intros. destruct fp1, fp2.
    split; intro H; inv H;
      constructor; unfolds_thrshd; Locs.unfolds; try split; simpl in *; intros b ofs;
        intuition;
        repeat (
            try 
              match goal with
              | |- ?x = ?x => auto
              | |- _ && false = false => apply andb_false_r
              | |- false && _ = false => apply andb_false_l
              | |- context[false || _] => rewrite orb_false_l
              | |- context[_ || false] => rewrite orb_false_r
              end;
            match goal with
            | H: forall _ _, _ |- _ => specialize (H b ofs)
            | H: _ = false |- _ => rewrite H; clear H
            | H: _ && _ = false |- _ => rewrite andb_false_iff in H; destruct H
            | H: ?x || ?y = false |- _ => apply orb_false_iff in H; destruct H
            end).
  Qed.
  

  Definition maxsmile (fp:t):t:=
    Build_t (Locs.complement (frees fp))
            (Locs.complement (Locs.union (writes fp) (frees fp)))
            (Locs.complement (Locs.union (reads fp)(Locs.union (writes fp)(frees fp))))
            (Locs.complement (Locs.union (frees fp)(Locs.union (writes fp)(Locs.union(cmps fp) (reads fp))))).


  
  (* Relations between eq and subset *)
  Theorem subset_eq:
    forall fp1 fp2, subset fp1 fp2 -> subset fp2 fp1 -> eq fp1 fp2.
  Proof.
    intros fp1 fp2 H1 H2; destruct H1, H2.
    constructor; eauto with locs.
  Qed.

  Theorem conflict_sym : forall fp1 fp2, conflict fp1 fp2 <-> conflict fp2 fp1.
  Proof.
    split;
    intro H;
    (destruct H;
      [apply conflict_cf | 
       apply conflict_rf |
       apply conflict_wf |
       apply conflict_ff |
       apply conflict_rw |
       apply conflict_ww];
      Locs.unfolds;
      destruct H as (b&ofs&H); exists b, ofs;
        eauto with bool).
  Qed.

  Ltac conflict_constructor :=
    match goal with
    | [H1: _ = cmps ?x ?b ?ofs, H2: _ = frees ?y ?b ?ofs|- conflict ?x ?y]
      => apply conflict_cf
    | [H1: _ = reads ?x ?b ?ofs, H2: _ = frees ?y ?b ?ofs |- conflict ?x ?y]
      => apply conflict_rf
    | [H1: _ = writes ?x ?b ?ofs, H2: _ = frees ?y ?b ?ofs |- conflict ?x ?y]
      => apply conflict_wf
    | [H1: _ = frees ?x ?b ?ofs, H2: _ = frees ?y ?b ?ofs |- conflict ?x ?y]
      => apply conflict_ff
    | [H1: _ = reads ?x ?b ?ofs, H2: _ = writes ?y ?b ?ofs |- conflict ?x ?y]
      => apply conflict_rw
    | [H1: _ = writes ?x ?b ?ofs, H2: _ = writes ?y ?b ?ofs |- conflict ?x ?y]
      => apply conflict_ww
    end.


  Theorem smile_conflict_compat:
    forall fp1 fp2,
      ~ conflict fp1 fp2 <-> smile fp1 fp2.
  Proof.
    split.
    - intros.
      constructor; Locs.unfolds; try split; intros;
        match goal with
        | [_:_ |- ?x && ?y = _] =>
          remember x as x'; remember y as y';
            destruct x', y'; auto
        end; exfalso; apply H;
          repeat (try conflict_constructor;
                  try (exists b,ofs;
                                Locs.unfolds;
                                eauto with bool;
                                fail);
                  rewrite conflict_sym
                 ).
    - intros H Contra.
      destruct H, Contra;
      Locs.unfolds;
      firstorder;
      repeat
        match goal with
        | [H:forall b ofs, _ |-_] => specialize (H b ofs)
        end;
      eauto with bool.
  Qed.

  Theorem smile'_conflict'_compat:
    forall fp1 fp2,
      ~ conflict' fp1 fp2 <-> smile' fp1 fp2.
  Proof.
    intros. rewrite <- conflict'_conflict_equiv, <- smile'_smile_equiv.
    apply smile_conflict_compat.
  Qed.

  Theorem fp_eq:forall fp1 fp2,FP.eq fp1 fp2 -> fp1 = fp2.
  Proof.
    intros.
    inversion H.
    apply Locs.locs_eq in eq_cmps0 ;apply Locs.locs_eq in eq_frees0; apply Locs.locs_eq in eq_writes0; apply Locs.locs_eq in eq_reads0.
    destruct fp1,fp2; simpl in eq_cmps0,eq_reads0,eq_writes0,eq_frees0; subst; auto.
  Qed.
  
  Lemma eq_sym:
    forall fp1 fp2, eq fp1 fp2 -> eq fp2 fp1.
  Proof.
    intros. inversion H; constructor; eauto with locs.
  Qed.
    
  Theorem union_comm:
    forall fp1 fp2, eq (union fp1 fp2) (union fp2 fp1).
  Proof. intros. constructor; simpl; eauto with locs. Qed.

  Corollary union_comm_eq : 
    forall fp1 fp2,union fp1 fp2=union fp2 fp1.
  Proof. intros;apply fp_eq;apply union_comm. Qed.
  Lemma union_subset:
    forall fp1 fp2,
      subset fp1 (union fp1 fp2).
  Proof.
    intros. unfold union. constructor; simpl; eauto with locs.
  Qed.

  Lemma union_emp:
    forall fp, eq (union fp emp) fp.
  Proof.
    intros. unfold union. destruct fp; constructor; simpl; eauto with locs.
  Qed.
  Corollary fp_union_emp :
    forall fp,union fp emp = fp.
  Proof. intros. apply fp_eq. apply union_emp. Qed.
  Corollary emp_union_fp:
    forall fp,union emp fp = fp.
  Proof. intros. apply fp_eq. rewrite union_comm_eq. apply union_emp. Qed.

  Theorem fp_union_assoc':
    forall fp1 fp2 fp3,eq (union fp1(union fp2 fp3))(union (union fp1 fp2) fp3).
  Proof.
    intros.
    unfold union.
    destruct fp1,fp2,fp3.
    simpl.
    assert(union_assoc_eq:forall x y z,Locs.union x(Locs.union y z) = Locs.union(Locs.union x y) z).
    intros.
    apply Locs.locs_eq. apply Locs.union_assoc.
    repeat rewrite union_assoc_eq.
    constructor;apply Locs.eq_refl.
  Qed.

  Corollary fp_union_assoc :
    forall fp1 fp2 fp3,union fp1 (union fp2 fp3) = union (union fp1 fp2) fp3.
  Proof. intros. apply fp_eq;apply fp_union_assoc'. Qed.
  Lemma union2_subset:
    forall fp1 fp2 fp,
      subset fp1 fp2 ->
      subset (union fp1 fp) (union fp2 fp).
  Proof.
    intros. inversion H. clear H.
    unfold union.
    constructor; simpl;
      (* need similar lemma in Locs *)
      unfold Locs.subset, Locs.belongsto, Locs.union in *;
      intros;
      repeat
        match goal with
        | [H:forall b ofs, _ |-_] => specialize (H b ofs)
        end
    .
    destruct (cmps fp1 _ _). rewrite subset_cmps0; auto. inversion H. rewrite H1. eauto with bool.
    destruct (reads fp1 _ _). rewrite subset_reads0; auto. inversion H. rewrite H1. eauto with bool.
    destruct (writes fp1 _ _). rewrite subset_writes0; auto. inversion H. rewrite H1. eauto with bool.
    destruct (frees fp1 _ _). rewrite subset_frees0; auto. inversion H. rewrite H1. eauto with bool.    
  Qed.
    
  Lemma subset_union_subset:
    forall fp1 fp2 fp',
      FP.subset fp1 fp2 ->
      FP.subset fp1 (FP.union fp2 fp').
  Proof.
    clear. unfold FP.union. intros [] []; intros. inv H; constructor; simpl in *.
    Locs.unfolds; intros. apply subset_cmps0 in H. rewrite H. auto.
    Locs.unfolds; intros. apply subset_reads0 in H. rewrite H. auto.
    Locs.unfolds; intros. apply subset_writes0 in H. rewrite H. auto.
    Locs.unfolds; intros. apply subset_frees0 in H. rewrite H. auto.
  Qed.
  
  Lemma subset_parallel_union:
    forall fp1 fp1' fp2 fp2',
      FP.subset fp1 fp1' ->
      FP.subset fp2 fp2' ->
      FP.subset (FP.union fp1 fp2) (FP.union fp1' fp2').
  Proof.
    clear. intros. destruct fp1, fp1', fp2, fp2'.
    inv H; inv H0; constructor; simpl in *;
      repeat match goal with | H: context[Locs.subset ?x _] |- context[?x] => revert H end; clear; intros H1 H2;
        Locs.unfolds; intros b ofs H; specialize (H1 b ofs); specialize (H2 b ofs); red_boolean_true; intuition.
  Qed.

  Lemma subset_refl:
    forall fp, FP.subset fp fp.
  Proof. clear. constructor; apply Locs.subset_refl. Qed.

  Lemma subset_emp:
    forall fp, FP.subset FP.emp fp.
  Proof. clear. constructor; simpl; eauto with locs. Qed.
  
  Lemma belongsto_subset:
    forall fp1 fp2 b,
      Bset.belongsto (blocks fp1) b ->
      FP.subset fp1 fp2 ->
      Bset.belongsto (blocks fp2) b.
  Proof.
    intros. destruct fp1, fp2. destruct H. exists x. inv H0.
    unfold locs in *. Locs.unfolds. simpl in *.
    red_boolean_true;
    repeat match goal with
           | [H:forall b ofs, _ -> _ |-_] => specialize (H b x)
           | [H1: ?x, H2: ?x -> _ |- _] => apply H2 in H1
           end;
    red_boolean_true.
  Qed.
  

         
         
  Lemma union_belongsto:
    forall fp1 fp2 b,
      Bset.belongsto (blocks (union fp1 fp2)) b ->
      Bset.belongsto (blocks fp1) b \/
      Bset.belongsto (blocks fp2) b.
  Proof.
    intros. destruct fp1, fp2. destruct H.
    unfold Bset.belongsto, blocks, Locs.blocks, locs in *; simpl in *; Locs.unfolds.
    red_boolean_true;
      try (left; exists x; red_boolean_true; fail);
      try (right; exists x; red_boolean_true).
  Qed.
  
  Lemma fp_never_conflict_emp:
    forall fp, ~ FP.conflict fp FP.emp.
  Proof.
    intro.
    intro.
    unfold FP.emp in H.
    inversion H;simpl in H0;repeat rewrite Locs.locs_intersect_emp in H0;repeat rewrite Locs.locs_intersect_emp_sym in H0;repeat rewrite Locs.locs_union_emp in H0;try apply Locs.locs_emp;auto.
  Qed.
  
  Lemma emp_never_conflict:
    forall fp1 fp2, FP.conflict fp1 fp2-> fp1<>FP.emp /\ fp2<> FP.emp.
  Proof.
    intros.
    split.
    intro; subst; inversion H;simpl in H;repeat rewrite Locs.locs_intersect_emp in H0;repeat rewrite Locs.locs_intersect_emp_sym in H0;repeat rewrite Locs.locs_union_emp in H0;try apply Locs.locs_emp;auto.
    intro; subst. apply fp_never_conflict_emp in H.  auto.
  Qed.
  
  Lemma maxsmile_smile: forall fp1,smile fp1 (maxsmile fp1).
  Proof.
    intro;destruct fp1;unfold maxsmile;constructor;simpl;try split;Locs.unfolds;intros;destruct (cmps0 b ofs) eqn:?,(reads0 b ofs)eqn:?,(writes0 b ofs) eqn:?,(frees0 b ofs) eqn:?;auto with bool.
  Qed.
  Lemma maxsmile_smile_subset:
    forall fp1 fp2,
      smile fp1 fp2 ->
      subset fp1 (maxsmile fp2).
  Proof.
    intros fp1 fp2 [].
    unfold maxsmile.
    repeat match goal with H:_/\_|-_=>destruct H end.
    constructor;simpl;eapply Locs.smile_complement_subset;eauto.
    apply Locs.smile_union;auto.
    rewrite Locs.union_sym_eq.
    apply Locs.smile_union;auto.
    apply Locs.smile_union;auto.
    apply Locs.smile_sym;auto.
    repeat try apply Locs.smile_union;auto;try apply Locs.smile_sym;auto.
  Qed.
    
End FP.

