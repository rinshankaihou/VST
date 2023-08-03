(* Adapted compiler code from CompCert *)

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

(** Layout of activation records; translation from Linear to Mach. *)

Require Import Coqlib Errors Integers AST.

Require Import Op Locations Linear_local Mach_local.

Require Import Bounds Conventions Stacklayout Lineartyping.

Require Import Stacking CUAST DisableDebug.

Local Open Scope error_monad_scope.

Definition transf_program (cu: Linear_comp_unit) : res Mach_comp_unit :=
  transform_partial_cunit _ _ _ transf_fundef cu.

