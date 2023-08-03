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

Require Import Coqlib Maps AST Registers Op RTL Conventions.

Require Import CUAST IS_local RTL_local.

Require Import Renumber Errors.

Definition transf_program (cu: RTL_comp_unit) : res RTL_comp_unit :=
  transform_partial_cunit _ _ _ (fun f => OK (transf_fundef f)) cu.
