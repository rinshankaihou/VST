(* Adapted compiler code from compcert. *)

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

(** Register allocation by external oracle and a posteriori validation. *)

Require Import FSets FSetAVLplus.
Require Import Coqlib Ordered Maps Errors Integers Floats.
Require Import AST Lattice Kildall Memdata.
Require Archi.
Require Import Op Registers RTL Locations Conventions RTLtyping LTL.


Require Import Allocation.

Require Import CUAST IS_local RTL_local LTL_local DisableDebug.

Definition transf_program (cu: RTL_comp_unit) : res LTL_comp_unit :=
  transform_partial_cunit _ _ _ transf_fundef cu.

 