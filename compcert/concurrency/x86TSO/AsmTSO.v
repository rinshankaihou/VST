(* This file is a modified version of [x86/Asm.v] of CompCert,
   with support for TSO memory model. 
 *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file gives the syntax and semantics of x86TSO language *)
Require Import Coqlib Maps.  
Require Import Locations AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Stacklayout Conventions.

Require Import Asm.

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory TSOMem.
Require Import loadframe.

Require Import ASM_local.
Require Import AsmLang.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** counter part of interaction semantics *)
Definition F : Type := fundef.
Definition V : Type := unit.
Definition comp_unit : Type := Asm_comp_unit.
Definition core : Type := core.
Definition internal_fn : comp_unit -> list ident := CUAST.internal_fn.
Definition init_genv (cu: Asm_comp_unit) (ge: genv) : Prop :=
  ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).
Definition init_core := init_core.
Definition halt := halted.
Definition at_external := at_external.
Definition after_external := after_external.

(** TSO related definitions *)
Definition init_gmem := init_mem.
(** TSO memory initialization *)
Definition init_tsomem ge gm :=
  init_gmem ge (memory gm) /\ (tso_buffers gm = fun _ => nil).

(** ** builtin args *)
Section EVAL_BUILTIN_ARG.

Context {A: Type}.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: tsofmem.

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      tsoloadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      tsoloadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.

(** ** x86TSO Semantics  *)
Section x86TSO_Semantics.

Variable ge : genv.
  
(** The outcome of x86_TSO execution *)
Inductive outcome_TSO : Type :=
  Next : regset -> tsofmem -> outcome_TSO | Stuck : outcome_TSO.

(** exec_load from TSO memory model *)
Definition exec_load_TSO (chunk: memory_chunk) (bm : tsofmem)
                         (a : addrmode) (rs : regset) (rd: preg) :=
  match tsoloadv chunk bm (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v)) bm
  | None => Stuck
  end.

(** exec_store from TSO memory model *)
Definition exec_store_TSO (chunk: memory_chunk) (bm : tsofmem)
           (a : addrmode) (rs : regset) (r1 : preg) (destroyed : list preg) :=
  match tsostorev chunk bm (eval_addrmode ge a rs) (rs r1) with
  | Some bm' => Next (nextinstr_nf (undef_regs destroyed rs)) bm'
  | None => Stuck
  end.

(** compare_ints_TSO *)
Definition check_compare_ints_TSO (x y: val) (bm: tsofmem) : bool :=
  if Val.cmpu_bool (tso_valid_pointer bm) Ceq x y then true else false.

Definition compare_ints_TSO (x y : val) (rs : regset) (bm : tsofmem) :=
  ((((rs # ZF <- (Val.cmpu (tso_valid_pointer bm) Ceq x y)) # CF <-
   (Val.cmpu (tso_valid_pointer bm) Clt x y)) # SF <-
   (Val.negative (Val.sub x y))) # OF <- (Val.sub_overflow x y)) # PF <- Vundef.

(** compare_longs_TSO *)
Definition compare_longs_TSO (x y : val) (rs : regset) (bm : tsofmem) :=
  ((((rs # ZF <- (Val.maketotal (Val.cmplu (tso_valid_pointer bm) Ceq x y)))
   # CF <- (Val.maketotal (Val.cmplu (tso_valid_pointer bm) Clt x y))) # SF <-
  (Val.negativel (Val.subl x y))) # OF <- (Val.subl_overflow x y)) # PF <- Vundef.

(** tso_goto_label *)
Definition tso_goto_label (f : function) (lbl : label) (rs : regset) (bm : tsofmem) :=
  match label_pos lbl 0 (fn_code f) with
  | Some pos =>
    match rs PC with
    | Vundef => Stuck
    | Vint _ => Stuck
    | Vlong _ => Stuck
    | Vfloat _ => Stuck
    | Vsingle _ => Stuck
    | Vptr b _ => Next rs # PC <- (Vptr b (Ptrofs.repr pos)) bm
    end
  | None => Stuck
  end.

(** The result of dec will update the value of flag *)
Definition dec_upd_flag (n : int) (rs : regset) :=
  ((rs # ZF <- (Val.of_optbool (Some (Int.cmpu Ceq n Int.one))))
       # SF <- (Val.negative (Val.sub (Vint n) (Vint Int.one))))
      # OF <- (Val.sub_overflow (Vint n) (Vint Int.one)) # PF <- Vundef.

(** The execution of x86_TSO instructions *)
Definition exec_instr_TSO
           (f: function) (i: instruction) (rs: regset) (bm: tsofmem) :
  outcome_TSO :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) bm
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n))) bm
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n))) bm
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero))) bm
  | Pmovl_rm rd a =>
      exec_load_TSO Mint32 bm a rs rd
  | Pmovq_rm rd a =>
      exec_load_TSO Mint64 bm a rs rd
  | Pmovl_mr a r1 =>
      exec_store_TSO Mint32 bm a rs r1 nil
  | Pmovq_mr a r1 =>
      exec_store_TSO Mint64 bm a rs r1 nil
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) bm
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n))) bm
  | Pmovsd_fm rd a =>
      exec_load_TSO Mfloat64 bm a rs rd
  | Pmovsd_mf a r1 =>
      exec_store_TSO Mfloat64 bm a rs r1 nil
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n))) bm
  | Pmovss_fm rd a =>
      exec_load_TSO Mfloat32 bm a rs rd
  | Pmovss_mf a r1 =>
      exec_store_TSO Mfloat32 bm a rs r1 nil
  | Pfldl_m a =>
      exec_load_TSO Mfloat64 bm a rs ST0
  | Pfstpl_m a =>
      exec_store_TSO Mfloat64 bm a rs ST0 (ST0 :: nil)
  | Pflds_m a =>
      exec_load_TSO Mfloat32 bm a rs ST0
  | Pfstps_m a =>
      exec_store_TSO Mfloat32 bm a rs ST0 (ST0 :: nil)
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store_TSO Mint8unsigned bm a rs r1 nil
  | Pmovw_mr a r1 =>
      exec_store_TSO Mint16unsigned bm a rs r1 nil
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) bm
  | Pmovzb_rm rd a =>
      exec_load_TSO Mint8unsigned bm a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) bm
  | Pmovsb_rm rd a =>
      exec_load_TSO Mint8signed bm a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) bm
  | Pmovzw_rm rd a =>
      exec_load_TSO Mint16unsigned bm a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) bm
  | Pmovsw_rm rd a =>
      exec_load_TSO Mint16signed bm a rs rd
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) bm
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) bm
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) bm
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) bm
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) bm
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) bm
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) bm
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1)))) bm
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1)))) bm
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1)))) bm
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1)))) bm
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1)))) bm
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1)))) bm
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge a rs))) bm
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge a rs))) bm
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) bm
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd))) bm
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n)))) bm
  | Paddq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n)))) bm
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) bm
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1))) bm
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) bm
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1))) bm
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) bm
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n)))) bm
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1))) bm
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1))) bm
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1))) bm
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1))) bm
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31))))) bm
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63))))) bm
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) bm
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) bm
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) bm
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) bm
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) bm
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1))) bm
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) bm
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n)))) bm
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) bm
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1))) bm
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) bm
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n)))) bm
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero)) bm
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero))) bm
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) bm
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1))) bm 
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) bm
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n)))) bm
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd))) bm
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd))) bm
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX))) bm
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX))) bm
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) bm
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n)))) bm
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX))) bm
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX))) bm
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) bm
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n)))) bm
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX))) bm
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX))) bm
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) bm
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n)))) bm
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n)))))) bm
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) bm
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n)))) bm
  | Pcmpl_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true =>
      if check_compare_ints_TSO (rs r1) (rs r2) bm
      then Next (nextinstr (compare_ints_TSO (rs r1) (rs r2) rs bm)) bm
      else Stuck
    end      
  | Pcmpq_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true =>  Next (nextinstr (compare_longs_TSO (rs r1) (rs r2) rs bm)) bm
    end
  | Pcmpl_ri r1 n =>
    match check_vundef (rs r1)(Vint n) with
    | false => Stuck
    | true =>
      if check_compare_ints_TSO (rs r1) (Vint n) bm
      then Next (nextinstr (compare_ints_TSO (rs r1) (Vint n) rs bm)) bm
      else Stuck
    end
  | Pcmpq_ri r1 n =>
    match check_vundef (rs r1)(Vlong n) with
    | false => Stuck
    | true => Next (nextinstr (compare_longs_TSO (rs r1) (Vlong n) rs bm)) bm
    end
  | Ptestl_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true =>
      Next (nextinstr (compare_ints_TSO (Val.and (rs r1) (rs r2)) Vzero rs bm)) bm
    end      
  | Ptestq_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true => Next (nextinstr (compare_longs_TSO (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs bm)) bm
    end
  | Ptestl_ri r1 n =>
    match check_vundef (rs r1)(Vint n) with
    | false => Stuck
    | true =>
      Next (nextinstr (compare_ints_TSO (Val.and (rs r1) (Vint n)) Vzero rs bm)) bm
    end
  | Ptestq_ri r1 n =>
      match check_vundef (rs r1)(Vlong n) with
    | false => Stuck
    | true => Next (nextinstr (compare_longs_TSO (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs bm)) bm
      end
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1))) bm
      | Some false => Next (nextinstr rs) bm
      | None => Next (nextinstr (rs#rd <- Vundef)) bm
      end
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs)))) bm
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) bm
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) bm
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) bm
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) bm
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd))) bm
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd))) bm
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) bm
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero))) bm
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1))) bm
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1))) bm
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1))) bm
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1))) bm
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd))) bm
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd))) bm
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs)) bm
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero))) bm
  (** Branches and calls *)
  | Pjmp_l lbl =>
      tso_goto_label f lbl rs bm
  | Pjmp_s id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) bm
  | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) bm
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => tso_goto_label f lbl rs bm
      | Some false => Next (nextinstr rs) bm
      | None => Stuck
      end        
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => tso_goto_label f lbl rs bm
      | Some _, Some _ => Next (nextinstr rs) bm
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => tso_goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) bm
          end
      | _ => Stuck
      end
  | Pcall_s id sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) bm
  | Pcall_r r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs r)) bm
  | Pret =>
      Next (rs#PC <- (rs#RA)) bm
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load_TSO (if Archi.ptr64 then Many64 else Many32) bm a rs rd
  | Pmov_mr_a a r1 =>
      exec_store_TSO (if Archi.ptr64 then Many64 else Many32) bm a rs r1 nil
  | Pmovsd_fm_a rd a =>
      exec_load_TSO Many64 bm a rs rd
  | Pmovsd_mf_a a r1 =>
      exec_store_TSO Many64 bm a rs r1 nil
  (** Pseudo-instructions *)
  | Plabel lbl =>
    Next (nextinstr rs) bm
  | Pallocframe sz ofs_rs ofs_link => Stuck
  | Pfreeframe sz ofs_ra ofs_link =>
      match tsoloadv Mptr bm (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
        match tsoloadv Mptr bm (Val.offset_ptr rs#RSP ofs_link) with
        | None => Stuck
        | Some sp =>  
          match rs#RSP with
          | Vptr stk ofs =>
            match tsofree bm stk 0 sz with
            | None => Stuck
            | Some bm' => Next (nextinstr (rs#RSP <- sp #RA <- ra)) bm'
            end
          | _ => Stuck
          end
        end
      end
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Padcl_ri _ _
  | Padcl_rr _ _
  | Paddl_mi _ _
  | Paddl_rr _ _
  | Pbsfl _ _
  | Pbsfq _ _
  | Pbsrl _ _
  | Pbsrq _ _
  | Pbswap64 _
  | Pbswap32 _
  | Pbswap16 _
  | Pcfi_adjust _
  | Pfmadd132 _ _ _
  | Pfmadd213 _ _ _
  | Pfmadd231 _ _ _
  | Pfmsub132 _ _ _
  | Pfmsub213 _ _ _
  | Pfmsub231 _ _ _
  | Pfnmadd132 _ _ _
  | Pfnmadd213 _ _ _
  | Pfnmadd231 _ _ _
  | Pfnmsub132 _ _ _
  | Pfnmsub213 _ _ _
  | Pfnmsub231 _ _ _
  | Pmaxsd _ _
  | Pminsd _ _
  | Pmovb_rm _ _
  | Pmovsq_rm _ _
  | Pmovsq_mr _ _
  | Pmovsb
  | Pmovsw
  | Pmovw_rm _ _
  | Prep_movsl
  | Psbbl_rr _ _
  | Psqrtsd _ _
  | Psubl_ri _ _
  | Psubq_ri _ _ => Stuck
  | Plock_movl_rm rd r2 =>
    match bm with
    | mktsofmem bf m =>
      match bf with
      | nil =>
        exec_load_TSO Mint32 bm r2 rs rd
      | _ => Stuck
      end
    end
  | Plock_xchg a rd =>
    match bm with
    | mktsofmem bf m =>
      match bf with
      | nil =>
        match Mem.loadv Mint32 m (eval_addrmode ge a rs) with
        | Some v =>
          match Mem.storev Mint32 m (eval_addrmode ge a rs) (rs rd) with
          | Some m' => Next (nextinstr (rs#rd <- v)) (mktsofmem bf m')
          | _ => Stuck
          end
        | _ => Stuck
        end
      | _ => Stuck
      end
    end  
  | Plock_cmpxchg a rd =>
    match bm with
    | mktsofmem bf m =>
      match bf with
      | nil =>
        match Mem.loadv Mint32 m (eval_addrmode ge a rs) with
        | Some v =>
          match Val.cmpu_bool (Mem.valid_pointer m) Ceq v (rs RAX) with
          | Some true =>
            match Mem.storev Mint32 m (eval_addrmode ge a rs) (rs rd) with
            | Some m' =>
              (** TODO: Should this instruction invalidate some registers? *)
              Next (nextinstr ((rs# (CR ZF) <- Vtrue))) (mktsofmem bf m')
            | _ => Stuck
            end
          | Some false =>
            Next (nextinstr ((rs # (CR ZF) <- Vfalse) # RAX <- v)) bm
          | None => Stuck
          end
        | _ => Stuck  
        end
      | _ => Stuck
      end
    end
  | Plock_dec a =>
    match bm with
    | mktsofmem bf m =>
      match bf with
      | nil =>
        match Mem.loadv Mint32 m (eval_addrmode ge a rs) with
        | Some v =>
          match v with
          | Vint n =>
            let v' := Val.sub v (Vint Int.one) in
            match Mem.storev Mint32 m (eval_addrmode ge a rs) v' with
            | Some m' => Next (nextinstr (dec_upd_flag n rs)) (mktsofmem bf m')
            | _ => Stuck
            end
          | _ => Stuck
          end
        | _ => Stuck
        end
      | _ => Stuck
      end
    end
  | Pjns lbl =>
    match rs SF with
    | Vundef => Stuck
    | Vint n =>
      if Int.eq n Int.zero then
        tso_goto_label f lbl rs bm
      else
        Next (nextinstr rs) bm
    | Vlong _
    | Vfloat _
    | Vsingle _
    | Vptr _ _ => Stuck
    end
  end.

(** x86-TSO alloc footprint *)
Definition tsoalloc_fp (stk : block) (lo hi : Z) :=
  uncheck_alloc_fp stk lo hi.

(** compare footprint *)
(* apply buffer on tsofmem *)
Definition tso_weak_valid_pointer_fp := 
  fun (bm : tsofmem) (b : block) (ofs : Z) =>
    if tso_valid_pointer bm b ofs
    then valid_pointer_fp b ofs
    else
      {|
        FP.cmps := range_locset b (ofs - 1) 2;
        FP.reads := Locs.emp;
        FP.writes := Locs.emp;
        FP.frees := Locs.emp |}.

Definition tso_cmpu_bool_fp_total (bm: tsofmem) (c: comparison) (v1 v2: val) :
  footprint :=
  match v1, v2 with
  | Vint _, Vint _ => empfp
  | Vint n1, Vptr b2 ofs2 =>
    if Archi.ptr64 then empfp
    else if Int.eq n1 Int.zero
         then if Val.cmp_different_blocks c                   
              then (tso_weak_valid_pointer_fp bm b2 (Ptrofs.unsigned ofs2))
              else empfp
         else empfp
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if Archi.ptr64 then empfp
    else if eq_block b1 b2
         then (FP.union (tso_weak_valid_pointer_fp bm b1 (Ptrofs.unsigned ofs1))
                        (tso_weak_valid_pointer_fp bm b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                             (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else empfp
  | Vptr b1 ofs1, Vint n2 =>
    if Archi.ptr64 then empfp
    else if Int.eq n2 Int.zero
         then if Val.cmp_different_blocks c
              then (tso_weak_valid_pointer_fp bm b1 (Ptrofs.unsigned ofs1))
              else empfp
         else empfp
  | _, _ => empfp
  end.

Definition tso_cmplu_bool_fp_total (bm: tsofmem) (c: comparison) (v1 v2: val) :
  footprint :=
  match v1, v2 with
  | Vlong n1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then empfp
    else if Int64.eq n1 Int64.zero
         then if Val.cmp_different_blocks c
              then (tso_weak_valid_pointer_fp bm b2 (Ptrofs.unsigned ofs2))
              else empfp
         else empfp
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then empfp
    else if eq_block b1 b2
         then (FP.union (tso_weak_valid_pointer_fp bm b1 (Ptrofs.unsigned ofs1))
                        (tso_weak_valid_pointer_fp bm b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                                  (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else empfp
  | Vptr b1 ofs1, Vlong n2 =>
    if negb Archi.ptr64 then empfp
    else if Int64.eq n2 Int64.zero
         then if Val.cmp_different_blocks c
              then (tso_weak_valid_pointer_fp bm b1 (Ptrofs.unsigned ofs1))
              else empfp
         else empfp
  | _, _ => empfp
  end.

Definition compare_ints_TSO_fp (x y : val) (bm : tsofmem) :=
  FP.union (tso_cmpu_bool_fp_total bm Ceq x y)
           (tso_cmpu_bool_fp_total bm Clt x y).

Definition compare_longs_TSO_fp (x y : val) (bm : tsofmem) :=
  FP.union (tso_cmplu_bool_fp_total bm Ceq x y)
           (tso_cmplu_bool_fp_total bm Clt x y).
          
(** footprint of [exec_inst_TSO] *)
Definition exec_instr_TSO_fp (f : function) (i : instruction) (rs : regset) (bm : tsofmem) : footprint :=
  match i with
  (** Moves *)
  | Pmovl_rm rd a =>
    exec_load_fp ge Mint32 a rs
  | Pmovq_rm rd a =>
    exec_load_fp ge Mint64 a rs
  | Pmovl_mr a r1 =>
    exec_store_fp ge Mint32 a rs
  | Pmovq_mr a r1 =>
    exec_store_fp ge Mint64 a rs
  | Pmovsd_fm rd a =>
    exec_load_fp ge Mfloat64 a rs
  | Pmovsd_mf a r1 =>
    exec_store_fp ge Mfloat64 a rs
  | Pmovss_fm rd a =>
    exec_load_fp ge Mfloat32 a rs
  | Pmovss_mf a r1 =>
    exec_store_fp ge Mfloat32 a rs
  | Pfldl_m a =>
    exec_load_fp ge Mfloat64 a rs
  | Pfstpl_m a =>
    exec_store_fp ge Mfloat64 a rs
  | Pflds_m a =>
    exec_load_fp ge Mfloat32 a rs
  | Pfstps_m a =>
    exec_store_fp ge Mfloat32 a rs
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
    exec_store_fp ge Mint8unsigned a rs
  | Pmovw_mr a r1 =>
    exec_store_fp ge Mint16unsigned a rs
  | Pmovzb_rm rd a =>
    exec_load_fp ge Mint8unsigned a rs
  | Pmovsb_rm rd a =>
    exec_load_fp ge Mint8signed a rs
  | Pmovzw_rm rd a =>
    exec_load_fp ge Mint16unsigned a rs
  | Pmovsw_rm rd a =>
    exec_load_fp ge Mint16signed a rs
  (** Integer arithmetic *)
  | Pcmpl_rr r1 r2 =>
    compare_ints_TSO_fp (rs r1) (rs r2) bm
  | Pcmpq_rr r1 r2 =>
    compare_longs_TSO_fp (rs r1) (rs r2) bm
  | Pcmpl_ri r1 n =>
    compare_ints_TSO_fp (rs r1) (Vint n) bm
  | Pcmpq_ri r1 n =>
    compare_longs_TSO_fp (rs r1) (Vlong n) bm
  | Ptestl_rr r1 r2 =>
    compare_ints_TSO_fp (Val.and (rs r1) (rs r2)) Vzero bm
  | Ptestq_rr r1 r2 =>
    compare_longs_TSO_fp (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) bm
  | Ptestl_ri r1 n =>
    compare_ints_TSO_fp (Val.and (rs r1) (Vint n)) Vzero bm
  | Ptestq_ri r1 n =>
    compare_longs_TSO_fp (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) bm
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
    exec_load_fp ge (if Archi.ptr64 then Many64 else Many32) a rs
  | Pmov_mr_a a r1 =>
    exec_store_fp ge (if Archi.ptr64 then Many64 else Many32) a rs
  | Pmovsd_fm_a rd a =>
    exec_load_fp ge Many64 a rs
  | Pmovsd_mf_a a r1 =>
    exec_store_fp ge Many64 a rs 
  (** Pseudo-instructions *)
  | Pallocframe sz ofs_ra ofs_link => empfp
  | Pfreeframe sz ofs_ra ofs_link =>
    match rs#RSP with
    | Vptr stk ofs =>
      FP.union (FP.union (loadv_fp Mptr (Val.offset_ptr rs#RSP ofs_ra))
                         (loadv_fp Mptr (Val.offset_ptr rs#RSP ofs_link)))
               (free_fp stk 0 sz)
    | _ => empfp
    end

  | Plock_movl_rm rd r2 =>
    exec_load_fp ge Mint32 r2 rs
  (** exchange contents of a and rd *)
  | Plock_xchg a rd =>
    FP.union (loadv_fp Mint32 (eval_addrmode ge a rs))
             (storev_fp Mint32 (eval_addrmode ge a rs))
  (** CAS *)
  | Plock_cmpxchg a rd =>
    match bm with
    | mktsofmem bf m =>
      match bf with
      | nil =>
        match Mem.loadv Mint32 m (eval_addrmode ge a rs) with
        | Some v =>
          match Val.cmpu_bool (Mem.valid_pointer m) Ceq v (rs RAX) with
          | Some true =>
            FP.union (loadv_fp Mint32 (eval_addrmode ge a rs))
                     (FP.union (of_optfp(Cop_fp.cmpu_bool_fp m Ceq v (rs RAX)))
                               (storev_fp Mint32 (eval_addrmode ge a rs)))
          | _ => FP.union (loadv_fp Mint32 (eval_addrmode ge a rs))(of_optfp (Cop_fp.cmpu_bool_fp m Ceq v (rs RAX)))
          end
        | _ => loadv_fp Mint32 (eval_addrmode ge a rs)
        end
      | _ => empfp
      end
    end

  | Plock_dec a =>
    match bm with
    | mktsofmem bf m =>
      match bf with
      | nil => 
        FP.union (loadv_fp Mint32 (eval_addrmode ge a rs))
                 (storev_fp Mint32 (eval_addrmode ge a rs))
      | _ => empfp
      end
    end
  | _ => empfp
          
  end.

(** x86-TSO extcall args *)
Inductive extcall_arg (rs: regset) (m: tsofmem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      tsoloadv (chunk_of_type ty) m
                (Val.offset_ptr (rs (IR RSP)) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: tsofmem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: tsofmem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

(** TSOMem version of store_args *)
Definition store_stack_fmem (m: tsofmem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val)
  : option tsofmem :=
  tsostorev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

Fixpoint store_args_rec_fmem (m: tsofmem) (sp: val) (ofs: Z)
         (args: list val) (tys: list typ) 
  : option tsofmem :=
  match args,tys with
  | nil, nil => Some m
  | a::args',ty::tys' =>
    match ty, a with
    | Tlong, Vlong n =>
      match store_stack_fmem m sp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs + 4)) (Vint (Int64.hiword n)) with
      | Some m' =>
        match store_stack_fmem m' sp Tint (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)) (Vint (Int64.loword n)) with
        | Some m'' => store_args_rec_fmem m'' sp (ofs + typesize ty) args' tys'
        | Non => None
        end
      | None => None
      end
    | Tlong, _ => None
    | _, _ =>
      match store_stack_fmem m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + ofs)) a with
      | None => None
      | Some m' => store_args_rec_fmem m' sp (ofs + typesize ty) args' tys'
      end
    end
  | _,_ => None
  end.

Definition store_args_fmem (m: tsofmem) (sp: block) (args: list val) (tys: list typ)
  : option tsofmem :=
  store_args_rec_fmem m (Vptr sp Ptrofs.zero) 0 args tys.

Definition not_alloc_instr (i : instruction) : Prop :=
  match i with
  | Pallocframe _ _ _ => False
  | _ => True
  end.

(** local step of the x86-TSO module. 
    
    Figure 19 in supplemental text presents some of them, and here is the 
    full definition of the x86TSO thread local semantics.
 *)
Inductive tsofstep :
  core -> tsofmem -> footprint -> core -> tsofmem -> Prop :=
| tso_exec_step_internal:
    forall b ofs (f: function) i rs bm rs' bm' lf fp,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i -> not_alloc_instr i ->
      exec_instr_TSO f i rs bm = Next rs' bm' ->
      exec_instr_TSO_fp f i rs bm = fp ->
      tsofstep (Core_State rs lf) bm fp (Core_State rs' lf) bm'

| tso_exec_step_internal_allocframe :
    forall b ofs (f : function) (rs: regset) bm rs' bm' bm2 bm3
      stk lf fp sz ofs_ra ofs_link sp
      (Hrs': rs' = nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pallocframe sz ofs_ra ofs_link) ->
      tsoalloc bm 0 sz (bm', stk) ->
      sp = Vptr stk Ptrofs.zero ->
      tsostorev Mptr bm' (Val.offset_ptr sp ofs_link) rs#RSP = Some bm2 ->
      tsostorev Mptr bm2 (Val.offset_ptr sp ofs_ra) rs#RA = Some bm3 ->
      fp = FP.union (tsoalloc_fp stk 0 sz)
                    (FP.union (storev_fp Mptr (Val.offset_ptr sp ofs_link))
                              (storev_fp Mptr (Val.offset_ptr sp ofs_ra))) ->
      tsofstep (Core_State rs lf) bm fp (Core_State rs' lf) bm3
                 
| tso_exec_step_builtin:
    forall b ofs f ef args fp res rs bm vargs vres rs' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      rs RSP <> Vundef->
      eval_builtin_args ge rs (rs RSP) bm args vargs ->
      MemOpFP.eval_builtin_args_fp ge rs (rs RSP) args fp ->
      i64ext_sem ef vargs vres ->
      rs' = nextinstr_nf
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      tsofstep (Core_State rs lf) bm fp (Core_State rs' lf) bm
               
| tso_exec_step_to_external:
    forall b ef args rs bm lf fp,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs bm (ef_sig ef) args ->
      extcall_arguments_fp rs (ef_sig ef) fp ->
      tsofstep (Core_State rs lf) bm fp (Core_CallstateOut ef args rs lf) bm

| tso_exec_step_i64ext:
    forall b ef args res rs bm rs' lf,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      i64ext_sem ef args res ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
      tsofstep (Core_CallstateOut ef args rs lf) bm empfp (Core_State rs' lf) bm

(*NOTE [loader]*)
| exec_initialize_call: 
    forall bm args tys retty bm1 stk bm2 fb z fp1 fp2 fp,
      args_len_rec args tys = Some z -> 
      tsoalloc bm 0 (4*z) (bm1, stk) ->
      tsoalloc_fp stk 0 (4*z) = fp1 ->
      store_args_fmem bm1 stk args tys = Some bm2 ->
      store_args_fp stk tys = fp2 ->
      FP.union fp1 fp2 = fp ->
      let rs0 := (Pregmap.init Vundef) 
                   #PC <- (Vptr fb Ptrofs.zero)
                   #RA <- Vzero 
                   #RSP <- (Vptr stk Ptrofs.zero) in
      tsofstep (Core_CallstateIn fb args tys retty) bm 
           fp (Core_State rs0 (mk_load_frame stk retty)) bm2
. 

End x86TSO_Semantics.

(** [tsostep] is applied by x86TSO global semantics *)
Inductive tsostep 
          (ge: genv) (fl: MemAux.freelist) :
  core -> buffer * gmem -> footprint -> core -> buffer * gmem -> Prop :=
| TSOstep :
    forall c b gm fm fp c' tsofm' b' gm',
      embed gm fl fm ->
      tsofstep ge c (mktsofmem b fm) fp c' tsofm' ->
      gm' = strip (fmemory tsofm') ->
      b' = tbuffer tsofm' ->
      tsostep ge fl c (b, gm) fp c' (b', gm').


(** tso step properties... *)

Lemma tsostep_not_halted:
  forall ge fl tc x fp tc' x',
    tsostep ge fl tc x fp tc' x' ->
    halt tc = None.
Proof.
  clear. intros.
  inv H; inv H1; simpl; auto.
  all: destruct lf; simpl; rewrite H; simpl; auto.
Qed.

Lemma tsostep_not_atext:
  forall ge fl tc x fp tc' x',
    tsostep ge fl tc x fp tc' x' ->
    at_external ge tc = None.
Proof.
  clear. intros.
  inv H. inv H1; simpl; auto.
  apply helpers.i64ext_extcall in H3. inv H3. inv H1; auto.
Qed.
