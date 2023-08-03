(* This file is adapted from [reach.v] of Compositional CompCert. 
   Modifications are explained in comments. *)
   

Require Import Coqlib Maps Integers Values Memdata.
Require Import Blockset Memperm GMemory.


Import GMem.


(** * Memory Closures *)

(** This file defines closures on memory *)

Local Notation "a # b" := (PMap.get b a) (at level 1).

Inductive reach' (gm: gmem) (B: Bset.t) : list (block * ptrofs) -> block -> Prop :=
| reach_nil: forall b, Bset.belongsto B b -> reach' gm B nil b
| reach_cons: forall b L b' z ofs q n,
    reach' gm B L b' ->
    perm gm b' z Max Readable ->
    ZMap.get z (mem_contents gm)!!b' = Fragment (Vptr b ofs) q n->
    reach' gm B ((b',ofs)::L) b.

Inductive reachable : gmem -> Bset.t -> block -> Prop :=
  Reachable : forall gm bs b L,
    reach' gm bs L b -> reachable gm bs b.

(** MODIFICATION:
    strengthen [reach_closed], requiring memory contains no Vundef / Undef values within block set of interest *)
Record reach_closed (gm: gmem) (B: Bset.t) : Prop :=
  {
    reachable_closure: forall b, reachable gm B b -> Bset.belongsto B b;
    no_undef: forall b z,
        Bset.belongsto B b ->
        perm gm b z Max Readable ->
        (~ ZMap.get z (mem_contents gm) !! b = Undef);
    no_vundef: forall b z q n,
        Bset.belongsto B b ->
        perm gm b z Max Readable ->
        (~ ZMap.get z (mem_contents gm) !! b = Fragment Vundef q n);
  }.

Lemma bset_eq_reach':
  forall bs1 bs2,
    (forall b, bs1 b <-> bs2 b) ->
    forall m L b, reach' m bs1 L b <-> reach' m bs2 L b.
Proof.
  intros bs1 bs2 EQ m.
  induction L.
  - split; intro H; inversion H;
      constructor; unfold Bset.belongsto in *;
        apply EQ; auto.
  - split; intros H; inversion H; subst; simpl in *.
    econstructor; eauto. apply IHL. auto.
    econstructor; eauto. apply IHL. auto.
Qed.

Lemma bset_eq_reachable:
  forall bs1 bs2 m,
    (forall b, bs1 b <-> bs2 b) ->
    (forall b, reachable m bs1 b <-> reachable m bs2 b).
Proof.
  clear. intros.
  split; intros.
  - inversion H0. subst.
    rewrite bset_eq_reach' in H1; eauto.
    econstructor; eauto.
  - inversion H0. subst.
    rewrite bset_eq_reach' in H1; eauto.
    econstructor; eauto. firstorder.
Qed.
  
Lemma bset_eq_reach_closed:
  forall bs1 bs2 m,
    (forall b, bs1 b <-> bs2 b) ->
    reach_closed m bs1 <-> reach_closed m bs2.
Proof.
  clear. intros.  
  split; constructor; unfold Bset.belongsto.
  intros. eapply bset_eq_reachable in H1; eauto. apply H. eapply reachable_closure; eauto.
  inv H0. intros. apply H in H0. auto.
  inv H0. intros. apply H in H0. auto.
  intros. eapply bset_eq_reachable in H1; eauto. apply H. eapply reachable_closure; eauto. intro. split; apply H.
  inv H0. intros. apply H in H0. auto.
  inv H0. intros. apply H in H0. auto.
Qed.