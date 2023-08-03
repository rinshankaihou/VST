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

(* An adapted version of CompCert file [x86/Asm.v],
   with support for our interaction semantics. *)

Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import Asm.

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory InteractionSemantics.

Require Import loadframe.

Require Import ASM_local.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** * Abstract syntax *)
(** Same as ASM_local *)

(** * Operational semantics *)
Open Scope asm.

(** builtin args *)
Section EVAL_BUILTIN_ARG.

Context {A: Type}.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

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
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
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

Section RELSEM.
  
Variable ge: genv.
(** Performing a comparison *)

(** Integer comparison between x and y:
-       ZF = 1 if x = y, 0 if x != y
-       CF = 1 if x <u y, 0 if x >=u y
-       SF = 1 if x - y is negative, 0 if x - y is positive
-       OF = 1 if x - y overflows (signed), 0 if not
-       PF is undefined
*)

Definition compare_ints (x y: val) (rs: regset) (m: mem): regset :=
  rs #ZF  <- (Val.cmpu (Mem.valid_pointer m) Ceq x y)
     #CF  <- (Val.cmpu (Mem.valid_pointer m) Clt x y)
     #SF  <- (Val.negative (Val.sub x y))
     #OF  <- (Val.sub_overflow x y)
     #PF  <- Vundef.

Definition check_compare_ints (x y: val) (m: mem) : bool :=
(*
  let weak_valid_ptr := fun b ofs => (Mem.valid_pointer m b ofs) || (Mem.valid_pointer m b (ofs - 1)) in
  match x, y with
  | Vint n1, Vint n2 => true
  | Vint n1, Vptr b2 ofs2 => Int.eq n1 Int.zero && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
  | Vptr b1 ofs1, Vint n2 => Int.eq n2 Int.zero && weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if eq_block b1 b2
    then weak_valid_ptr b1 (Ptrofs.unsigned ofs1) && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
    else Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) && Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2)
  | _, _ => false
  end.
*)
  if (Val.cmpu_bool (Mem.valid_pointer m) Ceq x y)
  then true
  else false.

Definition compare_longs (x y: val) (rs: regset) (m: mem): regset :=
  rs #ZF  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq x y))
     #CF  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt x y))
     #SF  <- (Val.negativel (Val.subl x y))
     #OF  <- (Val.subl_overflow x y)
     #PF  <- Vundef.

(** Floating-point comparison between x and y:
-       ZF = 1 if x=y or unordered, 0 if x<>y
-       CF = 1 if x<y or unordered, 0 if x>=y
-       PF = 1 if unordered, 0 if ordered.
-       SF and 0F are undefined
*)

Definition compare_floats (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vfloat x, Vfloat y =>
      rs #ZF  <- (Val.of_bool (negb (Float.cmp Cne x y)))
         #CF  <- (Val.of_bool (negb (Float.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float.cmp Ceq x y || Float.cmp Clt x y || Float.cmp Cgt x y)))
         #SF  <- Vundef
         #OF  <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs
  end.

Definition compare_floats32 (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vsingle x, Vsingle y =>
      rs #ZF  <- (Val.of_bool (negb (Float32.cmp Cne x y)))
         #CF  <- (Val.of_bool (negb (Float32.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float32.cmp Ceq x y || Float32.cmp Clt x y || Float32.cmp Cgt x y)))
         #SF  <- Vundef
         #OF  <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _ => Stuck
    end
  end.

Definition exec_load (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) :=
  match Mem.loadv chunk m (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) :=
  match Mem.storev chunk m (eval_addrmode ge a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf (undef_regs destroyed rs)) m'
  | None => Stuck
  end.

Definition exec_load_fp (chunk: memory_chunk) (a: addrmode) (rs: regset) :=
  loadv_fp chunk (eval_addrmode ge a rs).

Definition exec_store_fp (chunk: memory_chunk) (a: addrmode) (rs: regset) :=
  storev_fp chunk (eval_addrmode ge a rs).


(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual IA32 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the IA32 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the IA32 code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.

    Concerning condition flags, the comparison instructions set them
    accurately; other instructions (moves, [lea]) preserve them;
    and all other instruction set those flags to [Vundef], to reflect
    the fact that the processor updates some or all of those flags,
    but we do not need to model this precisely.
*)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n))) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n))) m
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero))) m
  | Pmovl_rm rd a =>
      exec_load Mint32 m a rs rd
  | Pmovq_rm rd a =>
      exec_load Mint64 m a rs rd
  | Pmovl_mr a r1 =>
      exec_store Mint32 m a rs r1 nil
  | Pmovq_mr a r1 =>
      exec_store Mint64 m a rs r1 nil
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n))) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64 m a rs r1 nil
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n))) m
  | Pmovss_fm rd a =>
      exec_load Mfloat32 m a rs rd
  | Pmovss_mf a r1 =>
      exec_store Mfloat32 m a rs r1 nil
  | Pfldl_m a =>
      exec_load Mfloat64 m a rs ST0
  | Pfstpl_m a =>
      exec_store Mfloat64 m a rs ST0 (ST0 :: nil)
  | Pflds_m a =>
      exec_load Mfloat32 m a rs ST0
  | Pfstps_m a =>
      exec_store Mfloat32 m a rs ST0 (ST0 :: nil)
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1 nil
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1 nil
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1)))) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1)))) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1)))) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1)))) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1)))) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1)))) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge a rs))) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge a rs))) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd))) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n)))) m
  | Paddq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n)))) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1))) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1))) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n)))) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1))) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1))) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1))) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1))) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31))))) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63))))) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1))) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n)))) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1))) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n)))) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero)) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero))) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1))) m 
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n)))) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd))) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd))) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX))) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX))) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n)))) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX))) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX))) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n)))) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX))) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX))) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n)))) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n)))))) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n)))) m
  | Pcmpl_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true =>
      if check_compare_ints (rs r1) (rs r2) m
      then Next (nextinstr (compare_ints (rs r1) (rs r2) rs m)) m
      else Stuck
    end
  | Pcmpq_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true =>  Next (nextinstr (compare_longs (rs r1) (rs r2) rs m)) m
    end
  | Pcmpl_ri r1 n =>
    match check_vundef (rs r1)(Vint n) with
    | false => Stuck
    | true =>
      if check_compare_ints (rs r1) (Vint n) m
      then Next (nextinstr (compare_ints (rs r1) (Vint n) rs m)) m
      else Stuck
    end
  | Pcmpq_ri r1 n =>
    match check_vundef (rs r1)(Vlong n) with
    | false => Stuck
    | true => Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m)) m
    end
  | Ptestl_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true =>  Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m)) m
    end
  | Ptestq_rr r1 r2 =>
    match check_vundef (rs r1)(rs r2) with
    | false => Stuck
    | true => Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m)) m
    end
  | Ptestl_ri r1 n =>
    match check_vundef (rs r1)(Vint n) with
    | false => Stuck
    | true =>  Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m)) m
    end
  | Ptestq_ri r1 n =>
      match check_vundef (rs r1)(Vlong n) with
    | false => Stuck
    | true => Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m)) m
      end
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1))) m
      | Some false => Next (nextinstr rs) m
      | None => Next (nextinstr (rs#rd <- Vundef)) m
      end
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs)))) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd))) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd))) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero))) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1))) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1))) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1))) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1))) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd))) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd))) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs)) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero))) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label f lbl rs m
  | Pjmp_s id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label f lbl rs m
      | Some _, Some _ => Next (nextinstr rs) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_s id sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pcall_r r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs r)) m
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load (if Archi.ptr64 then Many64 else Many32) m a rs rd
  | Pmov_mr_a a r1 =>
      exec_store (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil
  | Pmovsd_fm_a rd a =>
      exec_load Many64 m a rs rd
  | Pmovsd_mf_a a r1 =>
      exec_store Many64 m a rs r1 nil
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Ptrofs.zero in
      match Mem.storev Mptr m1 (Val.offset_ptr sp ofs_link) rs#RSP with
      | None => Stuck
      | Some m2 =>
          match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
          | None => Stuck
          | Some m3 => Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m3
          end
      end
  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
          | None => Stuck
          | Some sp =>
              match rs#RSP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => Stuck
                  | Some m' => Next (nextinstr (rs#RSP <- sp #RA <- ra)) m'
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
  | Psubq_ri _ _
             
  | Plock_movl_rm _ _
  | Plock_xchg _ _
  | Plock_cmpxchg _ _
  | Plock_dec _
  | Pjns _ => Stuck
  end.


Definition exec_locked_instr (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** same as movl_rm *)
  | Plock_movl_rm rd r2 =>
    exec_load Mint32 m r2 rs rd
  (** exchange contents of a and rd *)
  | Plock_xchg a rd =>
    match Mem.loadv Mint32 m (eval_addrmode ge a rs) with
    | Some v =>
      match Mem.storev Mint32 m (eval_addrmode ge a rs) (rs rd) with
      | Some m' =>
        (** TODO: Should this instruction invalidate some registers? *)
        Next (nextinstr (rs#rd <- v)) m'
      | _ => Stuck
      end
    | _ => Stuck
    end
  (** CAS *)
  | Plock_cmpxchg a rd =>
    match Mem.loadv Mint32 m (eval_addrmode ge a rs) with
    | Some v =>
      match Val.cmpu_bool (Mem.valid_pointer m) Ceq v (rs RAX) with
      | Some true =>
        match Mem.storev Mint32 m (eval_addrmode ge a rs) (rs rd) with
        | Some m' =>
          (** TODO: Should this instruction invalidate some registers? *)
          Next (nextinstr ((rs# (CR ZF) <- Vtrue))) m'
        | _ => Stuck
        end

      | Some false =>
        Next (nextinstr ((rs # (CR ZF) <- Vfalse) # RAX <- v)) m
             
      | None => Stuck
      end
    | _ => Stuck
    end
  | _ => Stuck
  end.

(** cmp footprint should be moved somewhere other than Cop_fp.v *)
Require Cop_fp.

Definition compare_ints_fp (x y: val) (m: mem) : footprint :=
  FP.union (Cop_fp.cmpu_bool_fp_total m Ceq x y)
           (Cop_fp.cmpu_bool_fp_total m Clt x y).

Definition compare_longs_fp (x y: val) (m: mem) : footprint :=
  FP.union (Cop_fp.cmplu_bool_fp_total m Ceq x y)
           (Cop_fp.cmplu_bool_fp_total m Clt x y).

               
(** footprint of [exec_instr] *)
Definition exec_instr_fp (f: function) (i: instruction) (rs: regset) (m: mem) : footprint :=
  match i with
  (** Moves *)
  | Pmovl_rm rd a =>
    exec_load_fp Mint32 a rs
  | Pmovq_rm rd a =>
    exec_load_fp Mint64 a rs
  | Pmovl_mr a r1 =>
    exec_store_fp Mint32 a rs
  | Pmovq_mr a r1 =>
    exec_store_fp Mint64 a rs
  | Pmovsd_fm rd a =>
    exec_load_fp Mfloat64 a rs
  | Pmovsd_mf a r1 =>
    exec_store_fp Mfloat64 a rs
  | Pmovss_fm rd a =>
    exec_load_fp Mfloat32 a rs
  | Pmovss_mf a r1 =>
    exec_store_fp Mfloat32 a rs
  | Pfldl_m a =>
    exec_load_fp Mfloat64 a rs
  | Pfstpl_m a =>
    exec_store_fp Mfloat64 a rs
  | Pflds_m a =>
    exec_load_fp Mfloat32 a rs
  | Pfstps_m a =>
    exec_store_fp Mfloat32 a rs
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
    exec_store_fp Mint8unsigned a rs
  | Pmovw_mr a r1 =>
    exec_store_fp Mint16unsigned a rs
  | Pmovzb_rm rd a =>
    exec_load_fp Mint8unsigned a rs
  | Pmovsb_rm rd a =>
    exec_load_fp Mint8signed a rs
  | Pmovzw_rm rd a =>
    exec_load_fp Mint16unsigned a rs
  | Pmovsw_rm rd a =>
    exec_load_fp Mint16signed a rs
  (** Integer arithmetic *)
  | Pcmpl_rr r1 r2 =>
    compare_ints_fp (rs r1) (rs r2) m
  | Pcmpq_rr r1 r2 =>
    compare_longs_fp (rs r1) (rs r2) m
  | Pcmpl_ri r1 n =>
    compare_ints_fp (rs r1) (Vint n) m
  | Pcmpq_ri r1 n =>
    compare_longs_fp (rs r1) (Vlong n) m
  | Ptestl_rr r1 r2 =>
    compare_ints_fp (Val.and (rs r1) (rs r2)) Vzero m
  | Ptestq_rr r1 r2 =>
    compare_longs_fp (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) m
  | Ptestl_ri r1 n =>
    compare_ints_fp (Val.and (rs r1) (Vint n)) Vzero m
  | Ptestq_ri r1 n =>
    compare_longs_fp (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) m
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
    exec_load_fp (if Archi.ptr64 then Many64 else Many32) a rs
  | Pmov_mr_a a r1 =>
    exec_store_fp (if Archi.ptr64 then Many64 else Many32) a rs
  | Pmovsd_fm_a rd a =>
    exec_load_fp Many64 a rs
  | Pmovsd_mf_a a r1 =>
    exec_store_fp Many64 a rs 
  (** Pseudo-instructions *)
  | Pallocframe sz ofs_ra ofs_link =>
    let (m1, stk) := Mem.alloc m 0 sz in
    let sp := Vptr stk Ptrofs.zero in
    FP.union (alloc_fp m 0 sz)
             (FP.union (storev_fp Mptr (Val.offset_ptr sp ofs_link))
                       (storev_fp Mptr (Val.offset_ptr sp ofs_ra)))
  | Pfreeframe sz ofs_ra ofs_link =>
    match rs#RSP with
    | Vptr stk ofs =>
      FP.union (FP.union (loadv_fp Mptr (Val.offset_ptr rs#RSP ofs_ra))
                         (loadv_fp Mptr (Val.offset_ptr rs#RSP ofs_link)))
               (free_fp stk 0 sz)
    | _ => empfp
    end
      
  | _ => empfp
          
  end.

Definition exec_locked_instr_fp (i: instruction) (rs: regset) (m: mem) : footprint :=
  match i with
  (** same as movl_rm *)
  | Plock_movl_rm rd r2 =>
    exec_load_fp Mint32 r2 rs
  (** exchange contents of a and rd *)
  | Plock_xchg a rd =>
    FP.union (loadv_fp Mint32 (eval_addrmode ge a rs))
             (storev_fp Mint32 (eval_addrmode ge a rs))
  (** CAS *)
  | Plock_cmpxchg a rd =>
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
  end.

(** extcall args *)
Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs (IR RSP)) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.


(** Execution of the instruction at [rs#PC]. *)
Inductive step: core -> mem -> footprint -> core -> mem -> Prop :=
| exec_step_internal:
    forall b ofs (f: function) i rs m rs' m' lf fp,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      exec_instr_fp f i rs m = fp ->
      step (Core_State rs lf) m fp (Core_State rs' lf) m'
| exec_step_builtin:
    forall b ofs f ef args fp res rs m vargs vres rs' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      rs RSP <> Vundef->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      MemOpFP.eval_builtin_args_fp ge rs (rs RSP) args fp ->
      i64ext_sem ef vargs vres ->
      rs' = nextinstr_nf
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (Core_State rs lf) m fp (Core_State rs' lf) m 
| exec_step_to_external:
    forall b ef args rs m lf fp,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      extcall_arguments_fp rs (ef_sig ef) fp ->
      step (Core_State rs lf) m fp (Core_CallstateOut ef args rs lf) m
| exec_step_i64ext:
    forall b ef args res rs m rs' lf,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      i64ext_sem ef args res ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
      step (Core_CallstateOut ef args rs lf) m empfp (Core_State rs' lf) m
(*NOTE [loader]*)
| exec_initialize_call: 
    forall m args tys retty m1 stk m2 fb z fp1 fp2 fp,
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      alloc_fp m 0 (4*z) = fp1 ->
      store_args_fmem m1 stk args tys = Some m2 ->
      store_args_fp stk tys = fp2 ->
      FP.union fp1 fp2 = fp ->
      let rs0 := (Pregmap.init Vundef) 
                   #PC <- (Vptr fb Ptrofs.zero)
                   #RA <- Vzero 
                   #RSP <- (Vptr stk Ptrofs.zero) in
      step (Core_CallstateIn fb args tys retty) m 
           fp (Core_State rs0 (mk_load_frame stk retty)) m2
(*           
| exec_step_to_lock:
    forall b ofs (f: function) i rs m lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      lock_prefixed i ->
      step (Core_State rs lf) m empfp (Core_LockState rs LOCK lf) m
           
| exec_step_locked:
    forall b ofs (f: function) i rs m rs' m' lf fp,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_locked_instr i rs m = Next rs' m' ->
      exec_locked_instr_fp i rs m = fp ->
      step (Core_LockState rs STEP lf) m fp (Core_LockState rs' UNLOCK lf) m' *)
.

End RELSEM.


(** * Core step relation *)

(** To build core step on GMemory from Fstep on FMemory, we define these two relations to 
    embed / strip freelists *)
Require Import MemAux ValRels.

Inductive step_gmem (ge: genv) (fl: freelist): core -> gmem -> FP.t -> core -> gmem -> Prop :=
  Step1_intro: forall c gm m fp c' gm' m',
    embed gm fl m ->
    step ge c m fp c' m' ->
    strip m' = gm' ->
    step_gmem ge fl c gm fp c' gm'.

(** Execution of whole programs. *)
Definition init_genv (cu: Asm_comp_unit) (ge G: genv) : Prop :=
  G = ge /\ ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).

Definition init_mem : genv -> gmem -> Prop := init_gmem_generic.

(** init_core, at_external, after_external, halted same as ASM_local *)

Definition AsmLang : Language :=
  Build_Language fundef unit genv Asm_comp_unit core 
                 init_core step_gmem at_external after_external halted
                 CUAST.internal_fn init_genv init_mem.
