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

Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking.
Require Import Ctypes Cop Cminor Csharpminor.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Require Import CUAST IS_local Csharpminor_local CminorLang Cminor_local.

Require Import Cminorgen.
Definition transl_program (cu: Csharpminor_local.comp_unit) : Errors.res Cminor_local.cminor_comp_unit :=
  transform_partial_cunit _ _ _ transl_fundef cu.
