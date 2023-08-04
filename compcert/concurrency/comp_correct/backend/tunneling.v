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

Require Import CUAST LTL_local Errors Tunneling.


Definition transf_program (p: LTL_comp_unit) : res LTL_comp_unit:=
  transform_partial_cunit _ _ _ (fun f => OK (tunnel_fundef f)) p.

