(** This file defines the instantiation of object [Ro], [Go] and [Io] for spin-lock, 
which are corresponding to the definitions in Figure 21 in submission #115 
supplemental text.  *)
From mathcomp.ssreflect Require Import fintype ssrnat.     
Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import Asm.

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe.

Require CminorLang.
Require SpecLang.
Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO. 

Require Import Coq.Lists.Streams.

Require Import RGRels ClientSim.
Require Import code.

(** * Object Invirant *)
(** [unlock state] : 
it says that the value of lock L is zero and there exists only one buffer item 
in buffers, which will update the value of lock L to one; or the value of lock L 
is one and there is no buffer item in buffers will change its value. It can be 
viewed as ([I_buffered] \/ [I_available]) defined in Figure 21 in submission #115 
supplemental text  *)
Definition unlock_st (L : block) (M : gmem) (tm : tsomem) : Prop :=
  load (Mint32) M L 0%Z = Some (Vint Int.one) /\
  (
    (exists t bf1 bf2,
        tm.(tso_buffers) t =
        bf1 ++ (BufferedStore Mint32 L 0%Z (Vint Int.one)) :: bf2
        /\ (forall t' ofs, t <> t' -> ~ in_buffer (tm.(tso_buffers) t') L ofs)
        /\ (forall ofs, ~ in_buffer (bf1 ++ bf2) L ofs)
        /\ (load_tsomem (Mint32) tm L 0%Z = Some (Vint Int.zero))
    ) \/
    (load_tsomem (Mint32) tm L 0 = Some (Vint Int.one) /\
     (forall t ofs, ~ in_buffer (tso_buffers tm t) L ofs))
  ).

(** [lock state] : 
it says that the value of lock L is zero and there is no buffer item in buffers 
will change its value. It can be viewed as the definition of [I_unavailable] in 
Figure 21 in submission #115 supplemental text *)
Definition lock_st (L : block) (M : gmem) (tm : tsomem) : Prop :=
  load (Mint32) M L 0%Z = Some (Vint Int.zero) /\
  (forall t, ~ (exists ofs, in_buffer (tso_buffers tm  t) L ofs)) /\
  (load_tsomem (Mint32) tm L 0%Z = Some (Vint Int.zero)). 

(** [object invariant] : 
the state of lock variable L is in [lock] or [unlock] state, and corresponds to `Io` 
in Figure 21 in submission #115 supplemental text. *)
Definition obj_inv (ge : genv) : stInv :=
  fun (M : gmem) (bm : tsomem) =>
    exists L, Genv.find_symbol ge lock_L_ident = Some L /\
              (lock_st L M bm \/ unlock_st L M bm) /\
              (forall n, exists M', store (Mint32) M L 0%Z (Vint n) = Some M') /\
              (forall n, exists bm', store_tsomem (Mint32) bm L 0%Z (Vint n) =
                                     Some bm') /\ unbuffer_safe bm /\
              (forall ofs, 0 <= ofs < size_chunk Mint32 ->
                      obj_mem M L ofs) /\
              (forall ofs, 0 <= ofs < size_chunk Mint32 ->
                      exists p,
                        (GMem.mem_access (get_gm bm)) !! L ofs Memperm.Cur =
                        Some p /\ Memperm.perm_order p Memperm.Writable) /\
              (forall ofs k p, (ofs >= size_chunk Mint32 \/ ofs < 0) ->
                      ~ GMem.perm M L ofs k p /\ ~ GMem.perm (memory bm) L ofs k p
              ).

(** * lock Guarantee *)
(** [lock_succ] : 
it describles the state transition when the thread achieves the lock. It changes 
the value of lock L from 1 to 0 (Corresponding to the definition of G_lock in 
Figure 21 in submission #115 supplemental text).
*)
Definition lock_succ (L : block) (t : tid) : stRel :=
  fun (M : gmem) (bm : tsomem) (M' : gmem) (bm' : tsomem) =>
    (
      load (Mint32) M L 0%Z = Some (Vint Int.one) /\
      load_tsomem (Mint32) bm L 0 = Some (Vint Int.one)
    ) /\
    (
      Some bm' = store_tsomem (Mint32) bm L 0 (Vint Int.zero) /\
      store (Mint32) M L 0%Z (Vint Int.zero) = Some M' 
    ).

(** [lock_fail] : 
it describles the state transition when the thread fails to get the lock. 
Because the program state does not change when lock fails. It can be view 
as transition Id defined in Figure 21 in submission #115 supplemental text.
*)
Definition lock_fail (L : block) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    load_tsomem (Mint32) tm L 0 = Some (Vint Int.zero) /\ M = M' /\
    Some tm' = store_tsomem (Mint32) tm L 0 (Vint Int.zero).

(** [Id] : corresponding to the transition Id defined in Figure 21 in submission 
#115 supplemental text *)
Definition Id (ge : genv) (M : gmem) (bm : tsomem) (M' : gmem) (bm' : tsomem) :
  Prop :=
  M = M' /\ bm = bm' /\ obj_inv ge M bm.

(** [G_lock] : lock_succ \/ lock_fail *)
Definition G_lock (ge : genv) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    exists L, Genv.find_symbol ge lock_L_ident = Some L /\
    obj_inv ge M tm /\ obj_inv ge M' tm' /\
    (lock_succ L t M tm M' tm' \/ lock_fail L t M tm M' tm').

(** [G_alloc] : 
it describles the state transition when executing memory allocation. It requires 
the low-level and high-level program allocate the same block. The memory allocation
isn't shown in paper, but we consider it in Coq proof *)
Definition G_alloc (ge : genv) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    exists b,
      obj_inv ge M tm /\ obj_inv ge M' tm' /\
      Some M' = alloc M b 0 0 /\
      append_t_buffer t tm (BufferedAlloc b 0 0) = tm' /\
      ~ In b (GMem.validblocks M) /\
      (forall t', ~ (exists ofs, in_buffer (tso_buffers tm t') b ofs))
      /\ ~ In b (GMem.validblocks (memory tm)).

(** * unlock Guarantee *)
Definition unlock_succ (L : block) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    (load (Mint32) M L 0%Z = Some (Vint Int.zero) /\
     load_tsomem (Mint32) tm L 0%Z = Some (Vint Int.zero)) /\
    (store (Mint32) M L 0%Z (Vint Int.one) = Some M' /\
     append_t_buffer t tm (BufferedStore Mint32 L 0 (Vint Int.one)) = tm'
    ).

(** [G_unlock] : 
it describles the state transition when the thread releases the lock. It changes 
the value of lock L from 1 to 0. The low-level x86-tso program doesn't modify 
variable L in memory directly, but pushs the write operation to buffer instead. 
It corresponding to the definition of G_unlock in Figure 21 in submission #115 
supplemental text *)
Definition G_unlock (ge : genv) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    exists L, Genv.find_symbol ge lock_L_ident = Some L /\
    obj_inv ge M tm /\ obj_inv ge M' tm' /\
    unlock_succ L t M tm M' tm'.

(** G client *)
Definition Gclt (ge : genv) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    exists L, Genv.find_symbol ge lock_L_ident = Some L /\
    exists v, load (Mint32) M L 0 = Some v /\
              load (Mint32) M' L 0 = Some v /\
              obj_inv ge M tm /\ obj_inv ge M' tm' /\
              (forall t, ~ (exists ofs, in_buffer (tso_buffers tm t) L ofs) ->
                         ~ (exists ofs, in_buffer (tso_buffers tm' t) L ofs)).

(** Object G *)
Definition Gobj (ge : genv) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    G_lock ge t M tm M' tm' \/ G_unlock ge t M tm M' tm' \/ Id ge M tm M' tm' \/
    G_alloc ge t M tm M' tm'.
    
(** * Object Rely *)
(** Corresponding to the R_buffer defined in Figure 21 in submission #115 
supplemental text *)
Definition Robj (ge : genv) (t : tid) : stRel :=
  fun (M : gmem) (tm : tsomem) (M' : gmem) (tm' : tsomem) =>
    exists t', t <> t' /\
               (
                 Gclt ge t' M tm M' tm' \/ Gobj ge t' M tm M' tm').

(** * Match State *)

Section MatchState.

  Variable sge : Genv.t SpecLang.F SpecLang.V.
  Variable ge : genv.

  Local Notation Sskip := SpecLang.Sskip.
  Local Notation Sassign := SpecLang.Sassign.
  Local Notation Sloadv := SpecLang.Sloadv.
  Local Notation Sstorev := SpecLang.Sstorev.
  Local Notation Sseq := SpecLang.Sseq.
  Local Notation Swhile := SpecLang.Swhile.
  Local Notation Satom := SpecLang.Satom.
  Local Notation Sassert := SpecLang.Sassert.

  Definition lock_spec_fn : SpecLang.stmt :=
    Sseq
    (Sseq (Sassign r Int.zero)
      (Sseq (Sassign x Int.zero)
      (Sseq (
        Swhile (SpecLang.BEq r Int.zero)
               (Satom (Sseq (Sloadv r lock_L_ident) (Sstorev x lock_L_ident)))
         ) Sskip))) Sskip.

  Definition lock_spec_while_cont : SpecLang.cont :=
    SpecLang.Kseq
          (SpecLang.Swhile (SpecLang.BEq r Int.zero)
             (SpecLang.Satom
                (SpecLang.Sseq (SpecLang.Sloadv r lock_L_ident)
                   (SpecLang.Sstorev x lock_L_ident))))
          (SpecLang.Kseq SpecLang.Sskip
             (SpecLang.Kseq SpecLang.Sskip SpecLang.Kstop)).

  (** ** Lock Acquire function Match State  *) 
  Inductive lock_match_state :
    tid -> SpecLang.core * gmem -> core * tsomem -> Prop :=
  | lock_init_match :
      forall t sc sm tc tm,
        Some tc = init_core ge lock_acquire_ident nil ->
        Some sc = SpecLang.init_core sge lock_acquire_ident nil ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)
                         
  | lock_label_match : (* lock : *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 0) -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 0))
                   lock_acquire_tso_fnbody.(fn_code) = Some (Plabel lock_lbl) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | mov_Laddr_match : (* movl $L RCX  *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 1) -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 1))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pmov_rs RCX lock_L_ident) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | set_lock_val : (* movl $0, RDX *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 2) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> 
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 2))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pmovl_ri RDX Int.zero) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | lock_acquire_label : (* lock_acquire *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 3) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RDX = Vzero ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 3))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Plabel lock_acquire_lbl) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | get_cmp_val : (* movl $1, %eax *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 4) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RDX = Vzero -> 
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 4))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pmovl_ri RAX Int.one) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | lock_cmpxchg_match : (* lock cmpxchg %edx, [%ecx] *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 5) -> rs RA = Vzero -> 
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RAX = Vone -> rs RDX = Vzero ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 5))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Plock_cmpxchg (Addrmode (Some RCX) None (inl 0%Z)) RDX) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | jne_enter_ZF_1_match : (* je enter [ZF = 1] *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> rs ZF = Vint Int.one ->
        lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 6) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RDX = Vzero ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 6))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pjcc Cond_e enter_lbl) -> te r = Vone ->
        sc = SpecLang.State SpecLang.Sskip lock_spec_while_cont te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | jne_enter_ZF_0_match : (* je enter [ZF = 0] *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> rs ZF = Vint Int.zero ->
        lf = mk_load_frame b' None -> 
        rs PC = Vptr b (Ptrofs.repr 6) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RDX = Vzero ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 6))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pjcc Cond_e enter_lbl) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | spin_label_match : (* spin : *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 7) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RDX = Vzero ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 7))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Plabel spin_lbl) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | get_lock_var : (* mov [RCX] RBX *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 8) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RDX = Vzero ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 8))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pmovl_rm RBX (Addrmode (Some RCX) None (inl 0%Z))) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | cmp_Lvar_match : (* cmp RBX, $0 *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 9) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RDX = Vzero ->
        (rs RBX = Vone \/ rs RBX = Vzero) ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 9))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pcmpl_ri RBX (Int.zero)) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | je_spin_match : (* je spin *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 10) -> rs RA = Vzero -> rs RDX = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> (rs ZF = Vone \/ rs ZF = Vzero) ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 10))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pjcc Cond_e spin_lbl) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | jmp_lock_match : (* jmp lock_acquire *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 11) -> rs RA = Vzero -> rs RDX = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 11))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pjmp_l lock_acquire_lbl) ->
        sc = SpecLang.State lock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | enter_label_match : (* enter : *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 12) -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 12))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Plabel enter_lbl) ->
        te r = Vone ->
        sc = SpecLang.State SpecLang.Sskip lock_spec_while_cont te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | set_ret_val : (* mov $0 RAX *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 13) -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 13))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pmovl_ri RAX (Int.zero)) -> te r = Vone ->
        sc = SpecLang.State SpecLang.Sskip lock_spec_while_cont te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)
                         
  | lock_retl_match : (* retl *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 14) -> rs RAX = Vzero -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_acquire_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 14))
                   lock_acquire_tso_fnbody.(fn_code) =
        Some (Pret) -> te r = Vone ->
        sc = SpecLang.State SpecLang.Sskip lock_spec_while_cont te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm)

  | lock_halt_match :
      forall t rs lf sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vzero -> rs RAX = Vzero ->
        sc = SpecLang.State SpecLang.Sskip SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        lock_match_state t (sc, sm) (tc, tm).

  Definition unlock_spec_fn : SpecLang.stmt :=
    Sseq 
      (Satom
        (
          Sseq (Sloadv r lock_L_ident)
          (Sseq (Sassign x (Int.one))
          (Sseq (Sassert (SpecLang.BEq r Int.zero)) (Sstorev x lock_L_ident)
          ))
        )) Sskip.
  
  (** ** Lock Release function Match State  *) 
  Inductive unlock_match_state :
    tid -> SpecLang.core * gmem -> core * tsomem -> Prop :=
  | unlock_init_match :
      forall t sc sm tc tm,
        Some tc = init_core ge lock_release_ident nil ->
        Some sc = SpecLang.init_core sge lock_release_ident nil ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm)
  | unlock_label_match : (* unlock : *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 0) -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_release_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 0))
                   lock_release_tso_fnbody.(fn_code) =
        Some (Plabel unlock_lbl) ->
        sc = SpecLang.State unlock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm)

  | get_lock_addr_match : (* mov $L RCX *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 1) -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_release_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 1))
                   lock_release_tso_fnbody.(fn_code) =
        Some (Pmov_rs RCX lock_L_ident) ->
        sc = SpecLang.State unlock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm)

  | mov_one_match : (* mov 1 RDX *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 2) -> rs RA = Vzero ->
        rs RCX = Vptr L (Ptrofs.repr 0) ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        Genv.find_funct_ptr ge b = Some (Internal lock_release_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 2))
                   lock_release_tso_fnbody.(fn_code) =
        Some (Pmovl_ri RDX (Int.one)) ->
        sc = SpecLang.State unlock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm)

  | unlock_step_match : (* mov RDX [RCX] *)
      forall t rs lf b sc sm tc tm te b' L,
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 3) ->
        rs RCX = Vptr L (Ptrofs.repr 0) -> rs RA = Vzero ->
        Some L = Genv.find_symbol ge lock_L_ident ->
        rs RDX = Vint Int.one ->
        Genv.find_funct_ptr ge b = Some (Internal lock_release_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 3))
                   lock_release_tso_fnbody.(fn_code) =
        Some (Pmovl_mr (Addrmode (Some RCX) None (inl 0%Z)) RDX) ->
        sc = SpecLang.State unlock_spec_fn SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm)

  | unlock_set_ret_val_match : (* mov $0 RAX *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 4) -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_release_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 4))
                   lock_release_tso_fnbody.(fn_code) =
        Some (Pmovl_ri RAX (Int.zero)) ->
        sc = SpecLang.State SpecLang.Sskip
                            (SpecLang.Kseq SpecLang.Sskip SpecLang.Kstop) te ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm)
      
  | unlock_retl_match : (* retl *)
      forall t rs lf b sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vptr b (Ptrofs.repr 5) -> rs RAX = Vzero -> rs RA = Vzero ->
        Genv.find_funct_ptr ge b = Some (Internal lock_release_tso_fnbody) ->
        find_instr (Ptrofs.unsigned (Ptrofs.repr 5))
                   lock_release_tso_fnbody.(fn_code) =
        Some (Pret) ->
        sc = SpecLang.State SpecLang.Sskip
                            (SpecLang.Kseq SpecLang.Sskip SpecLang.Kstop) te ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm)

  | unlock_halt_match :
      forall t rs lf sc sm tc tm te b',
        tc = Core_State rs lf -> lf = mk_load_frame b' None ->
        rs PC = Vzero -> rs RAX = Vzero ->
        sc = SpecLang.State SpecLang.Sskip SpecLang.Kstop te ->
        obj_inv ge sm tm ->
        unlock_match_state t (sc, sm) (tc, tm).

  Inductive obj_match_state :
    tid -> SpecLang.core * gmem -> core * tsomem -> Prop :=
  | obj_lock_match :
      forall t sc sm tc tm,
        lock_match_state t (sc, sm) (tc, tm) ->
        obj_match_state t (sc, sm) (tc, tm)

  | obj_unlock_match :
      forall t sc sm tc tm,
        unlock_match_state t (sc, sm) (tc, tm) ->
        obj_match_state t (sc, sm) (tc, tm).
    
End MatchState. 