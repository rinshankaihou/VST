(* An adapted version of CompCert file [x86/Asm.v],
   with support for our interaction semantics. *)

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

(** Abstract syntax and semantics for IA32 assembly language *)
(** This is a modified version of IA32 assembly *)

Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import Asm.


Require Import CUAST Footprint MemOpFP ValFP Op_fp String val_casted helpers.
Require IS_local.

Require Import loadframe.

(** load frame for x86 asm need only recording the initial stack pointer and return type *)

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)           (**r pointer to argument frame *)
           (retty: option typ),  (**r return type *)
      load_frame.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** * Abstract syntax *)

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions for types:
- [b]: 8 bits
- [w]: 16 bits ("word")
- [l]: 32 bits ("longword")
- [q]: 64 bits ("quadword")
- [d] or [sd]: FP double precision (64 bits)
- [s] or [ss]: FP single precision (32 bits)

  Naming conventions for operands:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: ireg) (r1: ireg)       (**r [mov] (integer) *)
  | Pmovl_ri (rd: ireg) (n: int)
  | Pmovq_ri (rd: ireg) (n: int64)
  | Pmov_rs (rd: ireg) (id: ident)
  | Pmovl_rm (rd: ireg) (a: addrmode)
  | Pmovq_rm (rd: ireg) (a: addrmode)
  | Pmovl_mr (a: addrmode) (rs: ireg)
  | Pmovq_mr (a: addrmode) (rs: ireg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pmovss_fi (rd: freg) (n: float32)   (**r [movss] (single 32-bit float) *)
  | Pmovss_fm (rd: freg) (a: addrmode)
  | Pmovss_mf (a: addrmode) (r1: freg)
  | Pfldl_m (a: addrmode)               (**r [fld] double precision *)
  | Pfstpl_m (a: addrmode)              (**r [fstp] double precision *)
  | Pflds_m (a: addrmode)               (**r [fld] simple precision *)
  | Pfstps_m (a: addrmode)              (**r [fstp] simple precision *)
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pmovzl_rr (rd: ireg) (rs: ireg)     (**r [movzl] (32-bit zero-extension) *)
  | Pmovsl_rr (rd: ireg) (rs: ireg)     (**r [movsl] (32-bit sign-extension) *)
  | Pmovls_rr (rd: ireg)                (** 64 to 32 bit conversion (pseudo) *)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg)  (**r conversion to single float *)
  | Pcvtss2sd_ff (rd: freg) (r1: freg)  (**r conversion to double float *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  | Pcvttss2si_rf (rd: ireg) (r1: freg) (**r single to signed int *)
  | Pcvtsi2ss_fr (rd: freg) (r1: ireg)  (**r signed int to single *)
  | Pcvttsd2sl_rf (rd: ireg) (r1: freg) (**r double to signed long *)
  | Pcvtsl2sd_fr (rd: freg) (r1: ireg)  (**r signed long to double *)
  | Pcvttss2sl_rf (rd: ireg) (r1: freg) (**r single to signed long *)
  | Pcvtsl2ss_fr (rd: freg) (r1: ireg)  (**r signed long to single *)
  (** Integer arithmetic *)
  | Pleal (rd: ireg) (a: addrmode)
  | Pleaq (rd: ireg) (a: addrmode)
  | Pnegl (rd: ireg)
  | Pnegq (rd: ireg)
  | Paddl_ri (rd: ireg) (n: int)
  | Paddq_ri (rd: ireg) (n: int64)
  | Psubl_rr (rd: ireg) (r1: ireg)
  | Psubq_rr (rd: ireg) (r1: ireg)
  | Pimull_rr (rd: ireg) (r1: ireg)
  | Pimulq_rr (rd: ireg) (r1: ireg)
  | Pimull_ri (rd: ireg) (n: int)
  | Pimulq_ri (rd: ireg) (n: int64)
  | Pimull_r (r1: ireg)
  | Pimulq_r (r1: ireg)
  | Pmull_r (r1: ireg)
  | Pmulq_r (r1: ireg)
  | Pcltd
  | Pcqto
  | Pdivl (r1: ireg)
  | Pdivq (r1: ireg)
  | Pidivl (r1: ireg)
  | Pidivq (r1: ireg)
  | Pandl_rr (rd: ireg) (r1: ireg)
  | Pandq_rr (rd: ireg) (r1: ireg)
  | Pandl_ri (rd: ireg) (n: int)
  | Pandq_ri (rd: ireg) (n: int64)
  | Porl_rr (rd: ireg) (r1: ireg)
  | Porq_rr (rd: ireg) (r1: ireg)
  | Porl_ri (rd: ireg) (n: int)
  | Porq_ri (rd: ireg) (n: int64)
  | Pxorl_r (rd: ireg)                  (**r [xor] with self = set to zero *)
  | Pxorq_r (rd: ireg)
  | Pxorl_rr (rd: ireg) (r1: ireg)
  | Pxorq_rr (rd: ireg) (r1: ireg)
  | Pxorl_ri (rd: ireg) (n: int)
  | Pxorq_ri (rd: ireg) (n: int64)
  | Pnotl (rd: ireg)
  | Pnotq (rd: ireg)
  | Psall_rcl (rd: ireg)
  | Psalq_rcl (rd: ireg)
  | Psall_ri (rd: ireg) (n: int)
  | Psalq_ri (rd: ireg) (n: int)
  | Pshrl_rcl (rd: ireg)
  | Pshrq_rcl (rd: ireg)
  | Pshrl_ri (rd: ireg) (n: int)
  | Pshrq_ri (rd: ireg) (n: int)
  | Psarl_rcl (rd: ireg)
  | Psarq_rcl (rd: ireg)
  | Psarl_ri (rd: ireg) (n: int)
  | Psarq_ri (rd: ireg) (n: int)
  | Pshld_ri (rd: ireg) (r1: ireg) (n: int)
  | Prorl_ri (rd: ireg) (n: int)
  | Prorq_ri (rd: ireg) (n: int)
  | Pcmpl_rr (r1 r2: ireg)
  | Pcmpq_rr (r1 r2: ireg)
  | Pcmpl_ri (r1: ireg) (n: int)
  | Pcmpq_ri (r1: ireg) (n: int64)
  | Ptestl_rr (r1 r2: ireg)
  | Ptestq_rr (r1 r2: ireg) 
  | Ptestl_ri (r1: ireg) (n: int)
  | Ptestq_ri (r1: ireg) (n: int64)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
  (** Floating-point arithmetic *)
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *)
  | Padds_ff (rd: freg) (r1: freg)
  | Psubs_ff (rd: freg) (r1: freg)
  | Pmuls_ff (rd: freg) (r1: freg)
  | Pdivs_ff (rd: freg) (r1: freg)
  | Pnegs (rd: freg)
  | Pabss (rd: freg)
  | Pcomiss_ff (r1 r2: freg)
  | Pxorps_f (rd: freg)	              (**r [xor] with self = set to zero *)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  | Pjmp_s (symb: ident) (sg: signature)
  | Pjmp_r (r: ireg) (sg: signature)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)   (**r pseudo *)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  | Pcall_s (symb: ident) (sg: signature)
  | Pcall_r (r: ireg) (sg: signature)
  | Pret
  (** Saving and restoring registers *)
  | Pmov_rm_a (rd: ireg) (a: addrmode)  (**r like [Pmov_rm], using [Many64] chunk *)
  | Pmov_mr_a (a: addrmode) (rs: ireg)  (**r like [Pmov_mr], using [Many64] chunk *)
  | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *)
  | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *)
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pallocframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pfreeframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pbuiltin(ef: external_function)(args: list (builtin_arg preg))(res: builtin_res preg)
  (** Instructions not generated by [Asmgen] -- TO CHECK *)
  | Padcl_ri (rd: ireg) (n: int)
  | Padcl_rr (rd: ireg) (r2: ireg)
  | Paddl_mi (a: addrmode) (n: int)
  | Paddl_rr (rd: ireg) (r2: ireg)
  | Pbsfl (rd: ireg) (r1: ireg)
  | Pbsfq (rd: ireg) (r1: ireg)
  | Pbsrl (rd: ireg) (r1: ireg)
  | Pbsrq (rd: ireg) (r1: ireg)
  | Pbswap64 (rd: ireg)
  | Pbswap32 (rd: ireg)
  | Pbswap16 (rd: ireg)
  | Pcfi_adjust (n: int)
  | Pfmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pmaxsd (rd: freg) (r2: freg)
  | Pminsd (rd: freg) (r2: freg)
  | Pmovb_rm (rd: ireg) (a: addrmode)
  | Pmovsq_mr  (a: addrmode) (rs: freg)
  | Pmovsq_rm (rd: freg) (a: addrmode)
  | Pmovsb
  | Pmovsw
  | Pmovw_rm (rd: ireg) (ad: addrmode)
  | Prep_movsl
  | Psbbl_rr (rd: ireg) (r2: ireg)
  | Psqrtsd (rd: freg) (r1: freg)
  | Psubl_ri (rd: ireg) (n: int)
  | Psubq_ri (rd: ireg) (n: int64)

             
  (** instruction with lock prefix, for sc_atomic *)
  (** (.., NULL)   --noop--> (.., locked) *)
  (** (.., locked) --xchg--> (.., unlock) *)
  (** (.., unlock) --noop--> (.., NULL) *)

  (** for sc_load *)
  (** MOV is sufficient for sc load, if sc stores are done with lock prefix.
      This pseudo instruction would be translated to MOV *)
  | Plock_movl_rm (rd: ireg) (r2: addrmode)
  (** for sc_store *)
  | Plock_xchg (a: addrmode) (rs: ireg)
  (** for sc_cas *)
  | Plock_cmpxchg (a: addrmode) (rs: ireg)
  (** lock dec, for spinlock impl *)
  | Plock_dec (a: addrmode)
  (** jump if negative, for spinlock impl *)
  | Pjns (l:label)
.

Definition lock_prefixed (i: instruction) : Prop :=
  match i with
  | Plock_movl_rm _ _ => True
  | Plock_xchg _ _ => True
  | Plock_cmpxchg _ _ => True
  | _ => False
  end.

Lemma lock_prefixed_dec:
  forall i, {lock_prefixed i} + {~ lock_prefixed i}.
Proof.
  destruct i; simpl; auto.
Defined.

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
Definition genv := Genv.t fundef unit.

(** * Operational semantics *)
Open Scope asm.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

Definition eval_addrmode32 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.add  (match base with
             | None => Vint Int.zero
             | Some r => rs r
            end)
  (Val.add (match ofs with
             | None => Vint Int.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mul (rs r) (Vint (Int.repr sc))
             end)
           (match const with
            | inl ofs => Vint (Int.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode64 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.addl (match base with
             | None => Vlong Int64.zero
             | Some r => rs r
            end)
  (Val.addl (match ofs with
             | None => Vlong Int64.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mull (rs r) (Vlong (Int64.repr sc))
             end)
           (match const with
            | inl ofs => Vlong (Int64.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 a rs else eval_addrmode32 a rs.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

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
  match Mem.loadv chunk m (eval_addrmode a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) :=
  match Mem.storev chunk m (eval_addrmode a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf (undef_regs destroyed rs)) m'
  | None => Stuck
  end.

Definition exec_load_fp (chunk: memory_chunk) (a: addrmode) (rs: regset) :=
  loadv_fp chunk (eval_addrmode a rs).

Definition exec_store_fp (chunk: memory_chunk) (a: addrmode) (rs: regset) :=
  storev_fp chunk (eval_addrmode a rs).


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
Definition check_vundef (v1 v2:val):bool:=
  match v1 with
  | Vundef => false
  | _ => match v2 with
        |Vundef => false
        |_ => true
        end
  end.
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
      Next (nextinstr (rs#rd <- (eval_addrmode32 a rs))) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 a rs))) m
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
    match Mem.loadv Mint32 m (eval_addrmode a rs) with
    | Some v =>
      match Mem.storev Mint32 m (eval_addrmode a rs) (rs rd) with
      | Some m' =>
        (** TODO: Should this instruction invalidate some registers? *)
        Next (nextinstr (rs#rd <- v)) m'
      | _ => Stuck
      end
    | _ => Stuck
    end
  (** CAS *)
  | Plock_cmpxchg a rd =>
    match Mem.loadv Mint32 m (eval_addrmode a rs) with
    | Some v =>
      match Val.cmpu_bool (Mem.valid_pointer m) Ceq v (rs RAX) with
      | Some true =>
        match Mem.storev Mint32 m (eval_addrmode a rs) (rs rd) with
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

(** TODO: should be moved to Footprint.v ? *)
Definition of_optfp (ofp: option footprint) : footprint :=
  match ofp with
  | Some fp => fp
  | None => empfp
  end.

Definition compare_ints_fp (x y: val) (m: mem) : footprint :=
  FP.union (cmpu_bool_fp_total m Ceq x y)
           (cmpu_bool_fp_total m Clt x y).

(*
Goal forall c x y m1 m2, Val.cmplu (Mem.valid_pointer m1) c x y =
                    Val.cmplu (Mem.valid_pointer m2) c x y.
Proof.
  unfold Val.cmplu, Val.cmplu_bool. auto.
Qed.
 *)

Definition compare_longs_fp (x y: val) (m: mem) : footprint :=
  FP.union (cmplu_bool_fp_total m Ceq x y)
           (cmplu_bool_fp_total m Clt x y).



               
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
    FP.union (loadv_fp Mint32 (eval_addrmode a rs))
             (storev_fp Mint32 (eval_addrmode a rs))
  (** CAS *)
  | Plock_cmpxchg a rd =>
    match Mem.loadv Mint32 m (eval_addrmode a rs) with
    | Some v =>
      match Val.cmpu_bool (Mem.valid_pointer m) Ceq v (rs RAX) with
      | Some true =>
        FP.union (loadv_fp Mint32 (eval_addrmode a rs))
                 (FP.union (cmpu_bool_fp_total m Ceq v (rs RAX))
                           (storev_fp Mint32 (eval_addrmode a rs)))
      | _ => FP.union (loadv_fp Mint32 (eval_addrmode a rs)) (cmpu_bool_fp_total m Ceq v (rs RAX))
      end
    | _ => loadv_fp Mint32 (eval_addrmode a rs)
    end
  | _ => empfp
  end.


(** footprint for loading external call arguments *)
Inductive extcall_arg_fp (rs: regset) : loc -> footprint -> Prop :=
| extcall_arg_reg_fp: forall r,
    extcall_arg_fp rs (R r) empfp
| extcall_arg_stack_fp: forall ofs ty bofs fp,
    bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
    loadv_fp (chunk_of_type ty) (Val.offset_ptr (rs (IR RSP)) (Ptrofs.repr bofs)) = fp->
    extcall_arg_fp rs (S Outgoing ofs ty) fp.

Inductive extcall_arg_pair_fp (rs: regset) : rpair loc -> footprint -> Prop :=
| extcall_arg_one_fp: forall l fp,
    extcall_arg_fp rs l fp ->
    extcall_arg_pair_fp rs (One l) fp
| extcall_arg_twolong_fp: forall hi lo fp1 fp2 fp,
    extcall_arg_fp rs hi fp1 ->
    extcall_arg_fp rs lo fp2 ->
    FP.union fp1 fp2 = fp ->
    extcall_arg_pair_fp rs (Twolong hi lo) fp.

Inductive load_arguments_fp (rs: regset) : list (rpair loc) -> footprint -> Prop :=
| load_arguments_nil_fp:
    load_arguments_fp rs nil empfp
| load_arguments_cons_fp:
    forall pl pll fp1 fp2 fp,
      extcall_arg_pair_fp rs pl fp1 ->
      load_arguments_fp rs pll fp2 ->
      FP.union fp1 fp2 = fp ->
      load_arguments_fp rs (pl :: pll) fp.

Definition extcall_arguments_fp
          (rs: regset) (sg: signature) (fp: footprint) : Prop :=
  load_arguments_fp rs (loc_arguments sg) fp.

(** Execution of the instruction at [rs#PC]. *)

Inductive lock_signal : Type :=
| LOCK
| STEP
| UNLOCK.

Inductive core: Type :=
| Core_State: regset -> load_frame -> core
(*Auxiliary state: for marshalling arguments INTO memory*)
| Core_CallstateIn: 
    forall (f: block)                (**r pointer to function to call *)
      (args: list val)          (**r arguments passed to initial_core *)
      (tys: list typ)           (**r argument types *)
      (retty: option typ),      (**r return type *)       
      core
(*Auxiliary state: for marshalling arguments OUT OF memory*)
| Core_CallstateOut: 
    forall (f: external_function)    (**r external function to be called *)
      (vals: list val)          (**r at_external arguments *)
      (rs: regset)              (**r register state *)
      (loader: load_frame),     (**r program loader frame *)
      core
(*Auxiliary state: for lock prefixed instructions *)
| Core_LockState:
    forall (rs: regset)
      (locked: lock_signal)
      (loader: load_frame),
      core
.

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
      eval_builtin_args_fp ge rs (rs RSP) args fp ->      
      i64ext ef ->
      external_call ef ge vargs m E0 vres m ->
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
      i64ext ef ->
      external_call ef ge args m E0 res m ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
      step (Core_CallstateOut ef args rs lf) m empfp (Core_State rs' lf) m
(*NOTE [loader]*)
| exec_initialize_call: 
    forall m args tys retty m1 stk m2 fb z fp1 fp2 fp,
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      alloc_fp m 0 (4*z) = fp1 ->
      store_args m1 stk args tys = Some m2 ->
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

(** Execution of whole programs. *)
Definition Asm_comp_unit := @comp_unit_generic fundef unit.

Definition init_genv (cu: Asm_comp_unit) (ge G: genv): Prop :=
  ge = G /\ globalenv_generic cu ge.

Definition init_mem : genv -> mem -> Prop := init_mem_generic.


(** Copied from compcomp *)
Definition fundef_init (fb: block) (sig: signature) (args: list val) : option core :=
  let tyl := sig_args sig in
  if wd_args args tyl 
  then Some (Core_CallstateIn fb args tyl (sig_res sig))
  else None.


Definition init_core (ge : Genv.t fundef unit) (fnid: ident) (args: list val): option core :=
  match Genv.find_symbol ge fnid with
  | Some fb => match Genv.find_funct_ptr ge fb with
              | Some cfd =>
                match cfd with
                | Internal fd =>
                  fundef_init fb (fn_sig fd) args
                | External _ => None
                end
              | None => None
              end
  | None => None
  end.

Require GAST.

Definition at_external (ge: Genv.t fundef unit) (c: core) :
  option (ident * signature * list val) :=
  match c with
  | Core_CallstateOut (EF_external name sig) args rs lf =>
    match invert_symbol_from_string ge name with
    (** following operational semantics of LTL, get arguments from locset & function signature *)
    | Some fnid =>
      if peq fnid GAST.ent_atom || peq fnid GAST.ext_atom
      then None
      else Some (fnid, sig, args)
    | _ => None
    end
(*      
  | Core_LockState rs LOCK lf =>
    Some (GAST.ent_atom, GAST.ent_atom_sg, nil)
  | Core_LockState rs UNLOCK lf =>
    Some (GAST.ext_atom, GAST.ext_atom_sg, nil)
*)
  | _ => None
 end.

Definition after_external (c: core) (vret: option val) : option core :=
  match c with
  | Core_CallstateOut (EF_external name sig)  args rs lf => 
   match vret, sig_res sig with
     None, None =>
     Some (Core_State ((set_pair (loc_external_result sig) Vundef rs) # PC <- (rs RA)) lf)
   | Some res, Some ty =>
     if val_has_type_func res ty
     then Some (Core_State ((set_pair (loc_external_result sig) res rs) # PC <- (rs RA)) lf)
     else None
   | _, _ => None
   end
(*     
  | Core_LockState rs LOCK lf =>
    match vret with
    | None => Some (Core_LockState rs STEP lf)
    | _ => None
    end
  | Core_LockState rs UNLOCK lf =>
    match vret with
    | None => Some (Core_State rs lf)
    | _ => None
    end
*)
  | _ => None
  end.

(*
int => AX => IR RAX
float => FP0 => ST0
long => DX AX => RDX RAX
single => FP0 => ST0
any32 => AX => IR RAX
any64 => X0 => FR XMM0
none => AX => IR RAX
 *)

Definition halted (c : core): option val :=
  match c with
  | Core_State rs (mk_load_frame fb sigres) =>
    if Val.cmp_bool Ceq rs#PC Vzero
    then match (loc_result (mksignature nil sigres cc_default)) with
         | One r => Some (rs (preg_of r))
         | Twolong r1 r2 => Some (Val.longofwords (rs (preg_of r1)) (rs (preg_of r2)))
         end
    else None
  | _ => None
  end.

Definition Asm_IS :=
  IS_local.Build_sem_local fundef unit genv Asm_comp_unit core init_genv init_mem
                           init_core halted step at_external after_external.

