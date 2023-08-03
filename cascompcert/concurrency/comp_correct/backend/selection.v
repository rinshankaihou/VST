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

Require String.
Require Import Coqlib Maps.
Require Import AST Errors Integers Globalenvs Switch.
Require Cminor.
Require Import Op CminorSel.
Require Import SelectOp SplitLong SelectLong SelectDiv.
Require Machregs.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.


Require Import CUAST IS_local Cminor_local CminorSel_local DisableDebug Selection.

Definition transf_program (cu: cminor_comp_unit) : res cminorsel_comp_unit :=
  let dm := comp_unit_defmap cu in
  do hf <- get_helpers dm;
    transform_partial_cunit _ _ _ (sel_fundef dm hf) cu.