(* Adapted compiler code from CompCert. *)

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

(** Linearization of the control-flow graph: translation from LTL to Linear *)

Require Import FSets FSetAVL.
Require Import Coqlib Maps Ordered Errors Lattice Kildall.
Require Import AST Op Locations LTL Linear.

Open Scope error_monad_scope.

Require Import Linearize.

Require Import CUAST IS_local LTL_local Linear_local DisableDebug.

Definition transf_program (cu: LTL_comp_unit) : res Linear_comp_unit :=
  transform_partial_cunit _ _ _ transf_fundef cu.


