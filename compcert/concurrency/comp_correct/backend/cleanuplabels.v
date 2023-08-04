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

Require Import CUAST Linear_local Errors CleanupLabels.

Definition transf_program (p: Linear_comp_unit) : res Linear_comp_unit:=
  transform_partial_cunit _ _ _ (fun f => OK (transf_fundef f)) p.