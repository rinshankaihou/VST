(** This file presents the syntax and semantics of CImp, which is a simple 
imperative language defined for writting the code specification. 

The specification of spin-lock, shown in Figure 10(a) in paper, 
is implemented by CImp. *)

(* From mathcomp.ssreflect Require Import fintype ssrnat. *)
Require Import Coqlib Maps (*Axioms*).
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import (*Locations Stacklayout*) Conventions.
(*
Require Import Asm.
*)
Require Import CUAST FMemOpFP ValFP (*Op_fp String val_casted helpers*).

Require Import Footprint GMemory FMemory .
Require Import Integers Floats FMemPerm.
Require Import GAST GlobDefs ETrace Blockset.
(*Require Import loadframe.*)

(*Require CminorLang.
Require Import ASM_local.
Require Import AsmLang.*)

Require Import Coq.Lists.Streams.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

(** ** Syntax *)
(** Bool expression *)
Inductive bexpr : Type :=
| BEq (r: ident) (n: Int.int).

(** Statement *)
Inductive stmt : Type :=
| Sskip
| Sassign (r: ident) (n: Int.int)
| Sloadv (r: ident) (gvar: ident)
| Sstorev (r: ident) (gvar: ident)
| Sseq (s1 s2: stmt)
| Swhile (b: bexpr) (s: stmt)
| Satom (s: stmt)
| Sassert (b: bexpr).

(** Function *)
Record function : Type :=
  {
    fn_sig: signature;
    fn_body: stmt;
  }.

(** ** Semantics *)
Definition fundef : Type := AST.fundef function.
Definition genv : Type := Genv.t fundef unit.

Definition F: Type := fundef.
Definition V: Type := unit.
Definition G: Type := genv.

Definition tmp : Type := ident -> val.
Definition init_tmp : tmp := fun _ => Vundef.

Inductive eval_bexpr (te: tmp) : bexpr -> val -> Prop :=
| Eval_btrue: forall r n,
    te r = Vint n ->
    eval_bexpr te (BEq r n) Vtrue
| Eval_bfalse: forall r n,
    te r <> Vint n ->
    eval_bexpr te (BEq r n) Vfalse.

Inductive cont : Type :=
| Kstop
| Kseq: stmt -> cont -> cont.

Inductive core : Type :=
| CallStateIn (s : stmt)
| State (s: stmt) (k: cont) (te: tmp)
| EntAtomState (s: stmt) (k0: cont) (te: tmp)
| AtomState (s: stmt) (k: cont) (k0: cont) (te: tmp)
| ExtAtomState (k0: cont) (te: tmp).


(** load/store operations for accessing location without Cur permissions 
    TODO: move to somewhere else?...
*)
Definition loadmax (m: mem) (b: block) : option val :=
  if Mem.range_perm_dec m b 0 (size_chunk Mint32) Memperm.Max Memperm.Readable
  then Some (decode_val Mint32 (Mem.getN (size_chunk_nat Mint32) 0 (Mem.mem_contents m) !! b))
  else None.

Program Definition storemax (m: mem) (b: block) (v: val) : option mem :=
  if Mem.range_perm_dec m b 0 (size_chunk Mint32) Memperm.Max Memperm.Writable then 
    Some (Mem.mkmem (PMap.set b
                              (Mem.setN (encode_val Mint32 v) 0 (PMap.get b m.(Mem.mem_contents)))
                              m.(Mem.mem_contents))
                    (m.(Mem.mem_access))
                    (m.(Mem.validblocks))
                    (m.(Mem.freelist))
                    (m.(Mem.nextblockid))
                    _ _ _ _ _)
  else None.
Next Obligation. apply Mem.freelist_wd. auto. Qed.
Next Obligation. apply Mem.valid_wd. auto. Qed.
Next Obligation. apply Mem.access_max. Qed.
Next Obligation. apply Mem.invalid_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite Mem.setN_default. apply Mem.contents_default.
  apply Mem.contents_default.
Qed.

Definition loadmax_fp (b: block) : footprint := load_fp Mint32 b 0.
Definition storemax_fp (b: block) : footprint := store_fp Mint32 b 0.

(** Semantics *)
Section Semantics.
  
  Variable ge: genv.
  
  Inductive normalstep : stmt -> cont -> tmp -> mem ->
                         footprint ->
                         stmt -> cont -> tmp -> mem -> Prop :=
  | Sassign_step: forall r n k te m te',
      te' = (fun r' => if peq r' r then Vint n else te r') ->
      normalstep (Sassign r n) k te m empfp Sskip k te' m
  | Sloadv_step: forall r gvar b k te m v fp te',
      Genv.find_symbol ge gvar = Some b ->
      loadmax m b = Some v ->
      fp = loadmax_fp b ->
      te' = (fun r' => if peq r' r then v else te r') ->
      normalstep (Sloadv r gvar) k te m fp Sskip k te' m
  | Sstorev_step: forall r gvar b k te m v fp m',
      Genv.find_symbol ge gvar = Some b ->
      te r = v ->
      storemax m b v = Some m' ->
      fp = storemax_fp b ->
      normalstep (Sstorev r gvar) k te m fp Sskip k te m'
  | Swhile_true: forall b s k te m,
      eval_bexpr te b Vtrue ->
      normalstep (Swhile b s) k te m empfp s (Kseq (Swhile b s) k) te m
  | Swhile_false: forall b s k te m,
      eval_bexpr te b Vfalse ->
      normalstep (Swhile b s) k te m empfp Sskip k te m
  | Sassert_step: forall b k te m,
      eval_bexpr te b Vtrue ->
      normalstep (Sassert b) k te m empfp Sskip k te m
  | Sseq_step: forall s s' te m k,
      normalstep (Sseq s s') k te m empfp s (Kseq s' k) te m
  | Sskip_seq: forall s te m k,
      normalstep Sskip (Kseq s k) te m empfp s k te m. 

  Inductive fstep : core -> mem -> footprint -> core -> mem -> Prop := 
  | Normalstep: forall s k te m fp s' k' te' m',
      normalstep s k te m fp s' k' te' m' ->
      fstep (State s k te) m fp (State s' k' te') m'
  | EntAtomstep: forall s k te m,
      fstep (State (Satom s) k te) m empfp (EntAtomState s k te) m
  | Atomstep: forall s k te m fp s' k' te' m' k0,
      normalstep s k te m fp s' k' te' m' ->
      fstep (AtomState s k k0 te) m fp (AtomState s' k' k0 te') m'
  | ExtAtomstep: forall k0 te m,
      fstep (AtomState Sskip Kstop k0 te) m empfp (ExtAtomState k0 te) m
  | Callinstep: forall s stk fp m m',
      Mem.alloc m 0 0 = (m', stk) ->
      alloc_fp m 0 0 = fp ->
      fstep (CallStateIn s) m fp (State s Kstop init_tmp) m'.

End Semantics.

Definition at_external (ge: genv) (c: core) : option (ident * signature * list val) :=
  match c with
  | EntAtomState s cont te => Some (ent_atom, ent_atom_sg, nil)
  | ExtAtomState cont te => Some (ext_atom, ext_atom_sg, nil)
  | _ => None
  end.

Definition after_external (c: core) (ov: option val) : option core :=
  match c, ov with
  | EntAtomState s k0 te, None => Some (AtomState s Kstop k0 te)
  | ExtAtomState k0 te, None => Some (State Sskip k0 te)
  | _, _ => None
  end.

Inductive step (ge: genv) (fl: MemAux.freelist): core -> gmem -> FP.t -> core -> gmem -> Prop :=
  Step_intro: forall c gm m fp c' gm' m',
    embed gm fl m ->
    fstep ge c m fp c' m' ->
    strip m' = gm' ->
    step ge fl c gm fp c' gm'.

Definition fundef_init (cfd: fundef) (args: list val) : option core :=
  match cfd with
  | Internal fd =>
    match args with
    | nil => Some (CallStateIn (fn_body fd))
    | _ => None
    end
  | External _=> None
  end.

Definition init_core (ge: genv) (fnid: ident) (args: list val): option core :=
  generic_init_core fundef_init ge fnid args.

Definition halt (c: core) : option val :=
  match c with
  | State Sskip Kstop te => Some Vzero
  | _ => None
  end.

Require Import TSOMem.

(** InteractionSemantics instantiation *)
Definition comp_unit : Type := @comp_unit_generic fundef unit.
Definition internal_fn: comp_unit -> list ident := CUAST.internal_fn.
Definition init_genv (cu: comp_unit) (ge G: Genv.t F V): Prop :=
  G = ge /\
  ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).

(* speclang init gmem *)
Definition read_as_zero_gm {F V: Type} (ge: Genv.t F V)
           (m: gmem) (b: block) (ofs len: Z) : Prop :=
  forall chunk p,
  ofs <= p -> p + size_chunk chunk <= ofs + len ->
  (align_chunk chunk | p) ->
  load chunk m b p =
  Some (match chunk with
        | Mint8unsigned | Mint8signed | Mint16unsigned | Mint16signed | Mint32 => Vint Int.zero
        | Mint64 => Vlong Int64.zero
        | Mfloat32 => Vsingle Float32.zero
        | Mfloat64 => Vfloat Float.zero
        | Many32 | Many64 => Vundef
        end).

Fixpoint load_store_init_data_gm {F V: Type} (ge: Genv.t F V)
         (m: gmem) (b: block) (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
    load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
    /\ load_store_init_data_gm ge m b (p + 1) il'
  | Init_int16 n :: il' =>
    load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
    /\ load_store_init_data_gm ge m b (p + 2) il'
  | Init_int32 n :: il' =>
    load Mint32 m b p = Some(Vint n)
    /\ load_store_init_data_gm ge m b (p + 4) il'
  | Init_int64 n :: il' =>
    load Mint64 m b p = Some(Vlong n)
    /\ load_store_init_data_gm ge m b (p + 8) il'
  | Init_float32 n :: il' =>
    load Mfloat32 m b p = Some(Vsingle n)
    /\ load_store_init_data_gm ge m b (p + 4) il'
  | Init_float64 n :: il' =>
    load Mfloat64 m b p = Some(Vfloat n)
    /\ load_store_init_data_gm ge m b (p + 8) il'
  | Init_addrof symb ofs :: il' =>
    (exists b', Genv.find_symbol ge symb = Some b' /\ load Mptr m b p = Some(Vptr b' ofs))
    /\ load_store_init_data_gm ge m b (p + size_chunk Mptr) il'
  | Init_space n :: il' =>
    read_as_zero_gm ge m b p n
    /\ load_store_init_data_gm ge m b (p + Zmax n 0) il'
  end.

Definition globals_initialized_fmem_speclang
           {F V: Type} (ge: Genv.t F V) (fm: FMemory.Mem.mem) : Prop :=
  forall b gd,
    Genv.find_def ge b = Some gd ->
    match gd with
    | Gfun _ =>
      FMemory.Mem.perm fm b 0 Memperm.Cur Memperm.Nonempty /\
      (forall ofs k p, FMemory.Mem.perm fm b ofs k p -> ofs = 0 /\ p = Memperm.Nonempty)
    | Gvar v =>
      FMemory.Mem.range_perm fm b 0 (init_data_list_size (gvar_init v))
                             Memperm.Max (permission_convert (Genv.perm_globvar v))
      (* variables in object memory don't have current permission *)
      /\ (forall ofs, 0 <= ofs < init_data_list_size (gvar_init v) ->
                (Mem.mem_access fm) !! b ofs Memperm.Cur = None)
      /\
      (forall ofs k p,
          FMemory.Mem.perm fm b ofs k p ->
          0 <= ofs < init_data_list_size (gvar_init v)
          /\ Memperm.perm_order (permission_convert (Genv.perm_globvar v)) p)
      /\
      (gvar_volatile v = false ->
       load_store_init_data_gm ge (strip fm) b 0 (gvar_init v))
      /\
      (gvar_volatile v = false ->
       loadbytes (strip fm) b 0 (init_data_list_size (gvar_init v)) =
       Some (Genv.bytes_of_init_data_list ge (gvar_init v)))
    end.

Record init_fmem_speclang (ge : Genv.t F V) (m : mem) : Prop :=
  Build_init_fmem_speclang
    {
      globdef_initialized_fm : globals_initialized_fmem_speclang ge m;
      dom_match_fm : forall b : positive,
          Plt b (Genv.genv_next ge) <-> Mem.valid_block m b;
      reach_closed_fm : MemClosures.reach_closed (strip m) (Mem.valid_block m)
    }.

(** We can use [init_gmem] to initialize the memory of CImp module. 
The initialization is a little different with other module, 
because the object memory use [Max] permission and doesn't have [Cur] permission. *)
Definition init_gmem (ge : Genv.t F V) (gm : gmem) :=
  exists fm, strip fm = gm /\ init_fmem_speclang ge fm.

Definition speclang : InteractionSemantics.Language :=
  InteractionSemantics.Build_Language F V G comp_unit core 
                                      init_core step at_external after_external halt 
                                      internal_fn init_genv init_gmem.