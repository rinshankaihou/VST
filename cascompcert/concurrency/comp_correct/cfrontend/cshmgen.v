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
Require Import Ctypes Cop Clight Cminor Csharpminor.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Require Import CUAST IS_local ClightLang Clight_local Csharpminor_local.

Require Import Cshmgen.

Definition clight_cu_to_cu (cu: clight_comp_unit) : comp_unit_generic Clight.fundef type :=
  Build_comp_unit_generic _ _ (cu_defs cu) (cu_public cu).
Coercion clight_cu_to_cu : clight_comp_unit >-> comp_unit_generic.
           
Definition transl_program (cu: clight_comp_unit) : Errors.res Csharpminor_local.comp_unit :=
  transform_partial_cunit2 _ _ _ _ (transl_fundef cu.(cu_comp_env)) transl_globvar cu.
