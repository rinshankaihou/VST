(** This file gives the specification of spin-lock, 
and it's implementation in x86-tso. 
(Corresponding to the code shown in Figure 10 
in submission #115 supplemental text) *)
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

(** * Implementation of the lock specification *)
(** Lock variable *)
Definition lock_L: globdef SpecLang.fundef unit :=
  Gvar (mkglobvar
          (* Unit *)
          tt
          (* init data *)
          (Init_int32 Int.one :: nil)
          (* readonly? *)
          false
          (* volatile? *)
          false).

(** Lock variable ident *)
Definition lock_L_ident: ident := Pos.of_nat 1.
  
(** Lock acquire function *) 
Local Notation Sskip := SpecLang.Sskip.
Local Notation Sassign := SpecLang.Sassign.
Local Notation Sloadv := SpecLang.Sloadv.
Local Notation Sstorev := SpecLang.Sstorev.
Local Notation Sseq := SpecLang.Sseq.
Local Notation Swhile := SpecLang.Swhile.
Local Notation Satom := SpecLang.Satom.
Local Notation Sassert := SpecLang.Sassert.

(* local variable *)
Definition r : ident := Pos.of_nat 1.
Definition x : ident := Pos.of_nat 2.

(** 
lock_acquire_fnbody :
The specification of the function lock of spain-lock,
corresponding to the function lock in Figure 10(a) 
in submission #115 supplemental text.
*)
Definition lock_acquire_fnbody : SpecLang.function :=
  SpecLang.Build_function
    (mksignature nil None (mkcallconv false false false))
    (
      Sseq
      (Sseq (Sassign r Int.zero)
            (Sseq (Sassign x Int.zero)
       (Sseq (
         Swhile (SpecLang.BEq r Int.zero)
               (Satom (Sseq (Sloadv r lock_L_ident) (Sstorev x lock_L_ident)))
           ) Sskip))) Sskip
    ).

Definition lock_acquire_ident := Pos.of_nat 2.

Definition lock_acquire : globdef SpecLang.fundef unit :=
  Gfun (Internal lock_acquire_fnbody).

(** Lock release function *)
(**
lock_release_fnbody : 
The specification of the function unlock of spain-lock, 
corresponding to the function unlock in Figure 10(a) 
in submission #115 supplemental text. 
*)
Definition lock_release_fnbody : SpecLang.function :=
  SpecLang.Build_function
    (mksignature nil None (mkcallconv false false false))
    (
      Sseq 
      (Satom
        (
          Sseq (Sloadv r lock_L_ident)
          (Sseq (Sassign x (Int.one))
          (Sseq (Sassert (SpecLang.BEq r Int.zero)) (Sstorev x lock_L_ident)
          ))
        )) Sskip
    ).

Definition lock_release_ident := Pos.of_nat 3.

Definition lock_release : globdef SpecLang.fundef unit :=
  Gfun (Internal lock_release_fnbody).

Definition lock_comp_unit : InteractionSemantics.comp_unit SpecLang.speclang :=
  Build_comp_unit_generic SpecLang.fundef unit
                          ((lock_L_ident, lock_L)
                             :: (lock_acquire_ident, lock_acquire)
                             :: (lock_release_ident, lock_release)
                             :: nil)
                          (lock_L_ident :: lock_acquire_ident
                                        :: lock_release_ident :: nil).

(** * Implementation of the lock x86-TSO *)
(** Lock variable *)
Definition lock_L_tso: globdef fundef unit :=
  Gvar (mkglobvar
          (* Unit *)
          tt
          (* init data *)
          (Init_int32 Int.one :: nil)
          (* readonly? *)
          false
          (* volatile? *)
          false).

(** Lock acquire function *)
(* code segment label *) 
Definition lock_lbl := (Pos.of_nat 1).
Definition spin_lbl := (Pos.of_nat 2). 
Definition enter_lbl := (Pos.of_nat 3).
Definition lock_acquire_lbl := (Pos.of_nat 4).

(**
lock_acquire_tso_fnbody : 
the implementation of the function lock of spain-lock in x86-tso, 
corresponding to the function lock in Figure 10(b)
in submission #115 supplemental text. 
*)
Definition lock_acquire_tso_fnbody : function :=
  mkfunction
    (mksignature nil None (mkcallconv false false false))
    (
      Plabel lock_lbl 
             :: Pmov_rs RCX lock_L_ident
             :: Pmovl_ri RDX Int.zero ::
      Plabel lock_acquire_lbl
             :: Pmovl_ri RAX Int.one
             :: Plock_cmpxchg (Addrmode (Some RCX) None (inl 0%Z)) RDX
             :: Pjcc Cond_e enter_lbl ::
      Plabel spin_lbl
             :: Pmovl_rm RBX (Addrmode (Some RCX) None (inl 0%Z))
             :: Pcmpl_ri RBX (Int.zero)
             :: Pjcc Cond_e spin_lbl
             :: Pjmp_l lock_acquire_lbl :: 
      Plabel enter_lbl
             :: Pmovl_ri RAX (Int.zero)
             :: Pret :: nil
    ).

Definition lock_acquire_tso : globdef fundef unit :=
  Gfun (Internal lock_acquire_tso_fnbody).

(** Lock release function *)
(* code segment label *)
Definition unlock_lbl := (Pos.of_nat 4).

(**
lock_release_tso_fnbody : 
the implementation of the function unlock of spain-lock in x86-tso, 
corresponding to the function unlock in Figure 10(b) 
in submission #115 supplemental text
*)
Definition lock_release_tso_fnbody : function :=
   mkfunction
     (mksignature nil None (mkcallconv false false false))
     (
       Plabel unlock_lbl
              :: Pmov_rs RCX lock_L_ident
              :: Pmovl_ri RDX (Int.one)
              :: Pmovl_mr (Addrmode (Some RCX) None (inl 0%Z)) RDX
              :: Pmovl_ri RAX (Int.zero)
              :: Pret :: nil
     ).

Definition lock_release_tso : globdef fundef unit :=
  Gfun (Internal lock_release_tso_fnbody).

Definition lock_comp_tso_unit : AsmTSO.comp_unit := 
  Build_comp_unit_generic fundef unit
                          ((lock_L_ident, lock_L_tso)
                             :: (lock_acquire_ident, lock_acquire_tso)
                             :: (lock_release_ident, lock_release_tso)
                             :: nil)
                          (lock_L_ident :: lock_acquire_ident
                                        :: lock_release_ident :: nil).
