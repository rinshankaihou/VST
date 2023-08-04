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

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import CminorSel.
Require Import RTL.

Local Open Scope string_scope.

Require Import CUAST IS_local RTLgen CminorSel_local RTL_local DisableDebug.

Definition transf_program (cu: cminorsel_comp_unit) : Errors.res RTL_comp_unit :=
  transform_partial_cunit _ _ _ transl_fundef cu.