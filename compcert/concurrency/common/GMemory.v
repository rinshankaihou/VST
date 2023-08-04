(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* This file is mostly derived from the original CompCert memory model,
   where we keep track of a list of valid blocks,
   instead of maintaining a [nextblock] field, 
   to allow allocation that might be not consecutive.. 
 *)

Require Import Coqlib Maps.
Require Import Archi Integers Values Memdata.
Require Import Blockset Memperm.
(* Require Import Footprint.*)

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes. 

Local Notation "a # b" := (PMap.get b a) (at level 1).

(** * Global Memory *)
(** The basic definition of memory, without operations, 
    do not deal with allocations.
   [forward] property is defined here *)

(** We followed the CompCert memory definition, 
    with the only difference on the way recording valid blocks and doing allocation:
- CompCert: keep track of [nextblock], 
    block < [nextblock] are valid, 
    allocation takes [nextblock] as the new block
- GMem in this file: keep track of [validblocks], 
    a list of blocks recorded as valid,
    allocation takes a block from thread local freelist, and add to [validblocks].
    This is to support thread local allocation and avoid racing on [nextblock].
*)


(** There are three basic memory fields:
- [content]:     contains memory contents
- [access]:      records which location is accessible, i.e. [locs(m)]
- [validblocks]: records validity of blocks, i.e. [dom(m)] 
    Memory could be inferred as [block -> offset -> content]

    Others fields are assumptions on memory permissions and default memory contents,
    as assumed by CompCert
 *) 

Module GMem.
  Record gmem' : Type :=
    mk_gmem {
        mem_contents: PMap.t (ZMap.t memval);
        mem_access: PMap.t (Z -> perm_kind -> option permission);
        validblocks: list block;
        access_max:
          forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
        invalid_noaccess:
          forall b ofs k, ~ In b (validblocks) -> mem_access#b ofs k = None;
        contents_default:
          forall b, fst mem_contents#b = Undef
      }.
  
  Definition valid_block (gm: gmem') (b: block) : Prop := In b (validblocks gm).

  Definition valid_blockb (gm: gmem') (b: block) : bool :=
    if in_dec eq_block b (validblocks gm) then true else false.

  Theorem valid_block_bool:
    forall gm b,
      valid_blockb gm b = true <-> valid_block gm b.
  Proof.
    unfold valid_blockb; split; intro H;
      destruct (in_dec eq_block b (validblocks gm)); auto.
      try discriminate.
  Qed.
      
  Record forward (gm1 gm2: gmem'): Prop :=
    {
      (* dom(gm1) \subset dom(gm2) *)
      dom_forward:
        forall b, valid_block gm1 b -> valid_block gm2 b;
      (* locs(gm2)\cap\dom(gm1) \subset \locs(gm1) *)
      alloc_forward:
        forall b ofs k p,
          valid_block gm1 b ->
          perm_order' (gm2.(mem_access)#b ofs k) p ->
          perm_order' (gm1.(mem_access)#b ofs k) p;
    }.

  Theorem forward_refl:
    forall gm, forward gm gm.
  Proof. intro; constructor; intros; auto. Qed.

  Theorem forward_trans:
    forall gm1 gm2 gm3,
      forward gm1 gm2 ->
      forward gm2 gm3 ->
      forward gm1 gm3.
  Proof.
    intros.
    inversion H; inversion H0.
    constructor; auto.
  Qed.

  Record eq (gm1 gm2: gmem') : Prop :=
    {
      eq_contents:
        forall b ofs,
          perm_order' (gm1.(mem_access)#b ofs Max) Readable ->
          ZMap.get ofs gm1.(mem_contents)#b = ZMap.get ofs gm2.(mem_contents)#b;
      eq_access:
        forall b ofs k, perm_order'' (gm1.(mem_access)#b ofs k) (gm2.(mem_access)#b ofs k) /\
                        perm_order'' (gm2.(mem_access)#b ofs k) (gm1.(mem_access)#b ofs k) ;
      eq_validblocks:
        forall b, valid_block gm1 b <-> valid_block gm2 b;
    }.

  Theorem eq_refl : forall gm, eq gm gm.
  Proof.
    firstorder;
    unfold perm_order'';
    destruct ((mem_access _) # _ _ _); constructor.
  Qed.

  Lemma eq_access_eq_perm:
    forall p1 p2,
      perm_order'' p1 p2 /\ perm_order'' p2 p1 <->
      p1 = p2.
  Proof.
    unfold perm_order'' in *.
    split; intros.
    destruct H.
    destruct p1, p2; try congruence; try contradiction.
    inversion H; inversion H0; try congruence.
    subst p1. destruct p2; auto.
    split; apply perm_refl.
  Qed.
  
  Theorem eq_sym : forall gm1 gm2, eq gm1 gm2 -> eq gm2 gm1.
  Proof.
    intros.
    destruct H; constructor; try firstorder.
    specialize (eq_contents0 b ofs).
    symmetry; apply eq_contents0.
    generalize eq_access0 H; clear; intros.
    specialize (eq_access0 b ofs Max).
    rewrite eq_access_eq_perm in eq_access0.
    rewrite eq_access0. auto.
  Qed.


  Theorem eq_trans : forall gm1 gm2 gm3, eq gm1 gm2 -> eq gm2 gm3 -> eq gm1 gm3.
  Proof. intros. destruct H, H0.
         constructor; intros; try congruence.
         { unfold block, ZIndexed.t in *;
             repeat
               match goal with
               | [H: forall (b: positive), _|-_] =>
                 specialize (H b)
               | [H: forall (ofs: Z), _|-_] =>
                 specialize (H ofs)
               | [H: forall (k: perm_kind), _|-_] =>
                 specialize (H k)
               end.
           rewrite <- eq_contents1.
           apply eq_contents0. auto.
           specialize (eq_access0 Max).
           apply eq_access_eq_perm in eq_access0. congruence.
         }
         {
           repeat match goal with
           | H: forall b ofs k, _ |- _ => specialize (H b ofs k); destruct H
           end.
           split; eapply perm_order''_trans; eauto. 
         }
         { rewrite <- eq_validblocks1. auto. }
  Qed.


   Record eq' (gm1 gm2: gmem') : Prop :=
    {
      eq_contents':
        forall b ofs,
          perm_order' (gm1.(mem_access)#b ofs Max) Readable ->
          ZMap.get ofs gm1.(mem_contents)#b = ZMap.get ofs gm2.(mem_contents)#b;
      eq_access':
        forall b ofs k, perm_order'' (gm1.(mem_access)#b ofs k) (gm2.(mem_access)#b ofs k) /\
                        perm_order'' (gm2.(mem_access)#b ofs k) (gm1.(mem_access)#b ofs k) ;
      eq_validblocks':
        forall b, valid_block gm1 b <-> valid_block gm2 b;
    }.

  Theorem eq'_refl : forall gm, eq' gm gm.
  Proof.
    firstorder;
    unfold perm_order'';
    destruct ((mem_access _) # _ _ _); constructor.
  Qed.

  Theorem eq'_sym : forall gm1 gm2, eq' gm1 gm2 -> eq' gm2 gm1.
  Proof.
    intros.
    destruct H; constructor; try firstorder.
    specialize (eq_contents'0 b ofs).
    symmetry; apply eq_contents'0.
    generalize eq_access'0 H; clear; intros.
    specialize (eq_access'0 b ofs Max).
    rewrite eq_access_eq_perm in eq_access'0.
    rewrite eq_access'0. auto.
  Qed.


  Theorem eq'_trans : forall gm1 gm2 gm3, eq' gm1 gm2 -> eq' gm2 gm3 -> eq' gm1 gm3.
  Proof. intros. destruct H, H0.
         constructor; intros; try congruence.
         { unfold block, ZIndexed.t in *;
             repeat
               match goal with
               | [H: forall (b: positive), _|-_] =>
                 specialize (H b)
               | [H: forall (ofs: Z), _|-_] =>
                 specialize (H ofs)
               | [H: forall (k: perm_kind), _|-_] =>
                 specialize (H k)
               end.
           rewrite <- eq_contents'1.
           apply eq_contents'0. auto.
           specialize (eq_access'0 Max).
           apply eq_access_eq_perm in eq_access'0. congruence.
         }
         {
           repeat match goal with
           | H: forall b ofs k, _ |- _ => specialize (H b ofs k); destruct H
           end.
           split; eapply perm_order''_trans; eauto. 
         }
         { rewrite <- eq_validblocks'1. auto. }
  Qed.


  Definition perm (gm: gmem') b ofs k p :=
    perm_order' (gm.(mem_access)#b ofs k) p.

  Remark perm_order_dec:
    forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
  Proof.
    intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
  Defined.

  Remark perm_order'_dec:
    forall op p, {perm_order' op p} + {~perm_order' op p}.
  Proof.
    intros. destruct op; unfold perm_order'.
    apply perm_order_dec.
    right; tauto.
  Defined.

  Theorem perm_dec:
    forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
  Proof.
    unfold perm; intros.
    apply perm_order'_dec.
  Defined.

  Definition range_perm (m: gmem') (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
    forall ofs, lo <= ofs < hi -> perm m b ofs k p.
  
  Definition eq_perm (P: block -> Z -> Prop) (m1 m2: gmem') : Prop :=
     forall b ofs k p,
       P b ofs ->
       perm m1 b ofs k p <-> perm m2 b ofs k p.

  Definition eq_content (P: block -> Z -> Prop) (m1 m2: gmem') : Prop :=
    forall b ofs,
      P b ofs ->
      ZMap.get ofs m1.(mem_contents)#b = ZMap.get ofs m2.(mem_contents)#b.




  

  (** * Generic injections *)

  (** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
   *)

  Record mem_inj (f: meminj) (m1 m2: gmem') : Prop :=
    mk_mem_inj {
        mi_perm:
          forall b1 b2 delta ofs k p,
            f b1 = Some(b2, delta) ->
            perm m1 b1 ofs k p ->
            perm m2 b2 (ofs + delta) k p;
        mi_align:
          forall b1 b2 delta chunk ofs p,
            f b1 = Some(b2, delta) ->
            range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
            (align_chunk chunk | delta);
        mi_memval:
          forall b1 ofs b2 delta,
            f b1 = Some(b2, delta) ->
            perm m1 b1 ofs Max Readable ->
            memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2)
      }.

  Definition meminj_no_overlap (f: meminj) (m: gmem') : Prop :=
    forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
      b1 <> b2 ->
      f b1 = Some (b1', delta1) ->
      f b2 = Some (b2', delta2) ->
      perm m b1 ofs1 Max Nonempty ->
      perm m b2 ofs2 Max Nonempty ->
      b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
  
  (** * Memory injections *)

  (** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
   *)

  Record inject' (f: meminj) (m1 m2: gmem') : Prop :=
    mk_inject {
        mi_inj:
          mem_inj f m1 m2;
        mi_freeblocks:
          forall b, ~(valid_block m1 b) -> f b = None;
        mi_mappedblocks:
          forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
        mi_no_overlap:
          meminj_no_overlap f m1;
        mi_representable:
          forall b b' delta ofs,
            f b = Some(b', delta) ->
            perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
            delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
        mi_perm_inv:
          forall b1 ofs b2 delta k p,
            f b1 = Some(b2, delta) ->
            perm m2 b2 (ofs + delta) k p ->
            perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
      }.
  Definition inject := inject'.

  (** * Blockwise injection *)
  (** A special form of memory injection, where f b = Some (b, 0) if b in dom(f).*)
  Record Binject_weak (phi: Bset.inj) (m1 m2: gmem') : Prop :=
    mk_binj_weak {
        bmiw_inject:
          inject' (Bset.inj_to_meminj phi) m1 m2;
      }.
  (** A stronger blockwise injection, it also require domains and locs are equal w.r.t. f. *)
  Record Binject (phi: Bset.inj) (m1 m2: gmem') : Prop :=
    mk_binject {
        bmi_weak:
          Binject_weak phi m1 m2;
        bmi_dom_inj_1:
          forall b,
            valid_block m1 b -> exists b', phi b = Some b';
        bmi_dom_inj_2:
          forall b',
            valid_block m2 b' -> exists b, phi b = Some b';
        bmi_perm_eq:
          forall b2 ofs k p,
            perm m2 b2 ofs k p ->
            exists b1,
              phi b1 = Some b2 /\
              perm m1 b1 ofs k p;
      }.

  Lemma Binject_Binject_weak:
    forall f m1 m2,
      Binject f m1 m2 -> Binject_weak f m1 m2.
  Proof. intros f m1 m2 H; inversion H; auto. Qed.

  
  Section UNCHANGED_ON.

    Variable P: block -> Z -> Prop.

    Record unchanged_on (m_before m_after: gmem') : Prop :=
      mk_unchanged_on {
          unchanged_on_validity:
            forall b ofs,
              P b ofs ->
              (valid_block m_before b <-> valid_block m_after b);
          unchanged_on_perm:
            forall b ofs k p,
              P b ofs -> valid_block m_before b ->
              (perm m_before b ofs k p <-> perm m_after b ofs k p);
          unchanged_on_contents:
            forall b ofs,
              P b ofs -> perm m_before b ofs Max Readable ->
              ZMap.get ofs (PMap.get b m_after.(mem_contents)) =
              ZMap.get ofs (PMap.get b m_before.(mem_contents))
        }.

    Theorem unchanged_on_refl:
      forall m, unchanged_on m m.
    Proof.
      intros. constructor; firstorder.
    Qed.
    
    Theorem unchanged_on_trans:
      forall m1 m2 m3,
        unchanged_on m1 m2 ->
        unchanged_on m2 m3 ->
        unchanged_on m1 m3.
    Proof.
      intros.
      inversion H; inversion H0.
      constructor; intros.
      rewrite unchanged_on_validity0; eauto.
      rewrite unchanged_on_perm0; eauto.
      apply unchanged_on_perm1; eauto.
      rewrite <- unchanged_on_validity0; eauto.
      erewrite <- unchanged_on_contents0; eauto.
      apply unchanged_on_contents1; auto.
      rewrite <- unchanged_on_perm0; auto.
      destruct (in_dec eq_block b (validblocks m1)); auto.
      apply (invalid_noaccess m1 b ofs Max) in n.
      unfold perm, perm_order' in H2.
      rewrite n in H2. contradiction.
    Qed.
    
  End UNCHANGED_ON.

  Lemma unchanged_on_implies:
    forall (P Q: block -> Z -> Prop) m m',
      unchanged_on P m m' ->
      (forall b ofs, Q b ofs -> P b ofs) ->
      unchanged_on Q m m'.
  Proof.
    intros. destruct H. constructor; intros.
    - eapply unchanged_on_validity0; eauto.
    - apply unchanged_on_perm0; auto. 
    - apply unchanged_on_contents0; auto. 
  Qed.
  
      
End GMem.



Definition gmem := GMem.gmem'.

