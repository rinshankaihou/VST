(** This file gives the definitions of the TSO memory and some operations 
on tso memory *)
(** The TSO model is defined following the approach of CompCertTSO *)

From mathcomp.ssreflect Require Import fintype ssrnat. 
Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import Asm.

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory.
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe.

Require Import Coq.Lists.Streams InteractionSemantics.
Require Import Zwf.

Set Implicit Arguments.
 
Definition perm_dec (gm : gmem) (b : block) (ofs : Z)
           (k : Memperm.perm_kind) (p : Memperm.permission) :=
  Mem.perm_order'_dec (Maps.PMap.get b (GMem.mem_access gm) ofs k) p.

Definition range_perm (m : gmem) (b : block) (lo : Z)
           (hi : Z) (k : Memperm.perm_kind) (p : Memperm.permission) :=
  forall ofs : Z, lo <= ofs < hi -> Mem.perm_order' ((GMem.mem_access m) !! b ofs k) p.

Theorem range_perm_dec :
  forall (m : gmem) (b : block) (lo : Z)
           (hi : Z) (k : Memperm.perm_kind) (p : Memperm.permission),
  {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. Lia.lia.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. Lia.lia.
  right; red; intros. elim n. red; intros; apply H0; Lia.lia.
  right; red; intros. elim n. apply H0. Lia.lia.
  left; red; intros. lia.
Qed.
Definition valid_access m chunk b ofs p:=
  range_perm m b ofs (ofs + size_chunk chunk) Memperm.Max p /\
  (align_chunk chunk|ofs).

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Memperm.Max p).
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk)).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

(** There are three types of buffer item : 
  1. [Alloc]
  2. [Free]
  3. [Store]
*)
Inductive buffer_item : Type :=
| BufferedAlloc : block -> Z -> Z -> buffer_item
| BufferedFree : block -> Z -> Z -> buffer_item
| BufferedStore : memory_chunk -> block -> Z -> val -> buffer_item.

Definition loadbytes (m : gmem) (b : block) (ofs n : Z) :=
  if range_perm_dec m b ofs (ofs + n) Memperm.Max Memperm.Readable then
    Some (Mem.getN (Z.to_nat n) ofs (GMem.mem_contents m) !! b)
  else
    None.

(** 
Here, we define [load], [store], [alloc] and [free] operations on GMemory.
- [load]  : read a memory chunk at a given address in GMemory.
- [store] : store a memory chunk at a given address in GMemory.   
- [alloc] : alloc a fresh memory block in GMemory.
- [free]  : invalidate a memory block in GMemory.
 *)

(** Load a value from GMemory. *)
Definition load (c : memory_chunk) (m : gmem) (b : block) (ofs : Z) :=
  if valid_access_dec m c b ofs Memperm.Readable
  then Some (decode_val c (Mem.getN (size_chunk_nat c) ofs (GMem.mem_contents m) !! b))
  else None.

(** Store a value in GMemory. *)
Program Definition store (c : memory_chunk) (m: gmem)
        (b: block) (ofs : Z) (v: val) : option gmem :=
if valid_access_dec m c b ofs Memperm.Writable
             then 
               Some (GMem.mk_gmem (PMap.set b
                                            (Mem.setN (encode_val c v) ofs
                                  (PMap.get b m.(GMem.mem_contents)))
                                            m.(GMem.mem_contents))
                                  (m.(GMem.mem_access))
                                  (m.(GMem.validblocks))
                                  _ _ _)
else None.
Next Obligation. apply GMem.access_max. Qed.
Next Obligation. apply GMem.invalid_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite Mem.setN_default. apply GMem.contents_default.
  apply GMem.contents_default.
Qed.
(** Alloc a block in GMemory. *)
Program Definition alloc (m: gmem)(b:block) (lo hi: Z) :=
 Some  (GMem.mk_gmem (PMap.set b (ZMap.init Undef) m.(GMem.mem_contents))
         (PMap.set b (fun ofs k => if zle lo ofs && zlt ofs hi then Some Memperm.Freeable else None) m.(GMem.mem_access))
         (b :: m.(GMem.validblocks))
         _ _ _).
Next Obligation.
  rewrite PMap.gsspec. destruct peq;try apply GMem.access_max.
  destruct (zle lo ofs && zlt ofs hi);constructor.
Qed.
Next Obligation.
  rewrite PMap.gsspec;destruct peq.
  contradict H;auto.
  apply GMem.invalid_noaccess;auto.
Qed.
Next Obligation.
  rewrite PMap.gsspec;destruct peq;auto.
  apply GMem.contents_default.
Qed.
Local Notation "a # b" := (PMap.get b a) (at level 1).
Program Definition unchecked_free (m:gmem)(b:block)(lo hi:Z):=
  GMem.mk_gmem
    m.(GMem.mem_contents)
        (PMap.set b
                  (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(GMem.mem_access)#b ofs k)
                  m.(GMem.mem_access))
        (m.(GMem.validblocks))
_ _ _.
Next Obligation.
  rewrite PMap.gsspec;destruct peq;try apply GMem.access_max.
  destruct (zle lo ofs && zlt ofs hi);try constructor.
  apply GMem.access_max.
Qed.
Next Obligation.
  rewrite PMap.gsspec;destruct peq;try apply GMem.invalid_noaccess;auto.
  destruct (zle lo ofs && zlt ofs hi) ;auto;try apply GMem.invalid_noaccess;auto;congruence.
Qed.
Next Obligation.
  apply GMem.contents_default.
Qed.
(** Free a segment of memory in GMemory. *)
Definition free (m: gmem) (b: block) (lo hi: Z): option gmem :=
  if range_perm_dec m b lo hi Memperm.Max Memperm.Freeable
  then Some(unchecked_free m b lo hi)
  else None.

(** * TSO Memory Model *)
(** [apply_buffer_item] : applies a given buffer item to the given memory state. *)
Definition apply_buffer_item (bi: buffer_item) (gm: gmem) : option gmem :=
  match bi with
  | BufferedAlloc b lo hi => alloc gm b lo hi
  | BufferedFree b lo hi => free gm b lo hi
  | BufferedStore chunk b ofs v => store chunk gm b ofs v
  end.

Definition buffer_item_eq (i i':buffer_item) : {i = i'} + {i <> i'}.
Proof.
  decide equality;try apply zeq;try apply peq;try apply Val.eq;try apply chunk_eq.
Qed.
Definition buffer : Type := list buffer_item.
Definition buffer_eq (i i':buffer): {i=i'} + {i<>i'}.
Proof. decide equality. apply buffer_item_eq. Qed.
(** [buffers] : the collection of thread buffers and corresponding to the definition 
of [B] defined in Figure 17 in submission #15 supplemental text *)
Definition buffers : Type := tid -> buffer.

(** [tsomem] : consists of each thread's buffer and global memory. *)
Record tsomem: Type :=
  mktsomem {
      tso_buffers : buffers;
      memory : gmem;
    }.

(** [tsomem_init] : in the initial state, each thread's buffer is empty. *)
Definition tsomem_init (gm: gmem) : tsomem := mktsomem (fun _ => nil) gm.

(** [tupdate] : updates the buffer of given thread with the given buffer.  *)
Definition tupdate (t: tid) (b': buffer) (B: buffers) : buffers :=
  fun t' => if peq t' t then b' else B t'.

(** Buffer item is applied by global semantics. *)
Definition unbuffer (tm: tsomem) (t: tid) : option tsomem :=
  let b := tso_buffers tm t in
  let gm := memory tm in
  match b with
  | bi :: b' =>
    match apply_buffer_item bi gm with
    | Some gm' => Some (mktsomem (tupdate t b' (tso_buffers tm)) gm')
    | None => None
    end
  | nil => None
  end.

(** State is [unbuffer_safe] if all possible unbufferings succeed. *)
Inductive unbuffer_safe: tsomem -> Prop :=
| unbuffer_safe_unbuffer :
    forall tso
           (ABIS: forall t bi b,
               tso.(tso_buffers) t = bi :: b ->
               exists m', apply_buffer_item bi tso.(memory) = Some m')
           (UNBS: forall t bi b m',
               tso.(tso_buffers) t = bi :: b ->
               apply_buffer_item bi tso.(memory) = Some m' ->
               unbuffer_safe (mktsomem (tupdate t b tso.(tso_buffers))
                                       m')),
      unbuffer_safe tso.

(** Module local view : [buffer] + [fmemory]. *)
Record tsofmem: Type :=
  mktsofmem {
      tbuffer : buffer;
      fmemory : mem;
    }.

(** [buffer_insert] : adds a given buffer item to the end of the buffer. *)
Definition buffer_insert (tfm : tsofmem) (bi : buffer_item) :=
  mktsofmem (tfm.(tbuffer) ++ bi :: nil) tfm.(fmemory).

Definition optbind (A B : Type) (g : A -> option B) (f : option A) : option B :=
  match f with
    | None => None
    | Some v => g v
  end.
(** 
[apply_buffer] : 
corresponds to the 'apply_buffer' defined in 
submission #115 supplemental text in Figure 19 on page 20. 
It applies a given buffer item to the given memory state. 
The buffer is applied from left to right (i.e., starting with the head).
*)
Fixpoint apply_buffer (b : list buffer_item) (gm : gmem) : option gmem :=
  match b with
  | nil => Some gm
  | bi :: rest =>
    optbind (fun gm' => apply_buffer rest gm') (apply_buffer_item bi gm)
  end.

Definition tso_valid_pointer (tfm : tsofmem) (b : block) (ofs : Z) : bool :=
  match tfm with
  | mktsofmem bf fm =>
    match apply_buffer bf (strip fm) with
    | Some gm' =>
      proj_sumbool (perm_dec gm' b ofs Memperm.Cur Memperm.Nonempty)
    | _ => false
    end
  end.

(** [tsoupd] : updates the buffer of the given thread t with b' 
and the goal memory with gm' in tso memory. *)
Definition tsoupd (tm: tsomem) (t: tid) (b': buffer) (gm': gmem) : tsomem :=
  mktsomem (tupdate t b' (tso_buffers tm)) gm'.

(** Here, we define [alloc], [free], [load] and [store] operations on TSO memory : 
- [tsoalloc] : alloc a fresh block in TSO memory. It doesn't take effect immediately, but is inserted into buffer first.
- [tsofree]  : invalidate a segment of memory in TSO memory. It doesn't take effect immediately, but is inserted into buffer first.
- [tsoload]  : load a memory chunk from TSO memory. Note that we do not buffer reads; reads are satisfied directly from buffers, or from the main memory if the buffer of the reading thread does not contain a corresponding write.  
- [tsostore] : store a memory chunk in TSO memory. It doesn't take effect immediately, but is inserted into buffer first. 
*)
Inductive tsoalloc : tsofmem -> Z -> Z -> tsofmem * block -> Prop :=
| TSOAlloc :
    forall bf fm lo hi fm' gm',
      apply_buffer bf (strip fm) = Some gm' ->
      embed gm' (Mem.freelist fm) fm' ->
      tsoalloc (mktsofmem bf fm) lo hi
               (buffer_insert (mktsofmem bf fm)
                              (BufferedAlloc (Mem.nextblock fm') lo hi),
                Mem.nextblock fm').

Definition tsofree (tfm : tsofmem) (b : block) (lo hi : Z) : option tsofmem :=
  Some (buffer_insert tfm (BufferedFree b lo hi)).

Definition tsoload (c : memory_chunk) (tfm : tsofmem)
           (b : block) (ofs : Z) : option val :=
  match tfm with
  | mktsofmem bf fm =>
    match apply_buffer bf (strip fm) with
    | Some gm => load c gm b ofs
    | None => None
    end
  end.

Definition tsoloadv (c : memory_chunk) (tfm : tsofmem)
           (addr : val) : option val :=
  match addr with
  | Vundef => None
  | Vint _ => None
  | Vlong _ => None
  | Vfloat _ => None
  | Vsingle _ => None
  | Vptr b ofs => tsoload c tfm b (Integers.Ptrofs.unsigned ofs)
  end.

Definition tsostore (c : memory_chunk) (tfm : tsofmem) (b : block) (ofs : Z)
           (v : val) :=
  Some (buffer_insert tfm (BufferedStore c b ofs v)).

Definition tsostorev (c : memory_chunk) (tfm : tsofmem) (addr v : val) :=
  match addr with
  | Vundef => None
  | Vint _ => None
  | Vlong _ => None
  | Vfloat _ => None
  | Vsingle _ => None
  | Vptr b ofs => tsostore c tfm b (Integers.Ptrofs.unsigned ofs) v
  end.

Fixpoint get_buffer_b (bf : buffer) : list block :=
  match bf with
  | nil => nil
  | bi :: bf' =>
    match bi with
    | BufferedAlloc b _ _ => b :: get_buffer_b bf'
    | BufferedFree b _ _ => b :: get_buffer_b bf'
    | BufferedStore _ b _ _ => b :: get_buffer_b bf'
    end
  end.

Inductive in_buffer_item : buffer_item -> block -> Z -> Prop :=
| in_alloc_bi: forall b ofs lo hi,
    in_buffer_item (BufferedAlloc b lo hi) b ofs
| in_free_bi: forall b ofs lo hi,
    lo <= ofs < hi ->
    in_buffer_item (BufferedFree b lo hi) b ofs
| in_store_bi: forall b ofs chunk ofs' v,
    ofs' <= ofs < ofs' + (size_chunk chunk) ->
    in_buffer_item (BufferedStore chunk b ofs' v) b ofs.

Inductive in_buffer (buf: buffer) (b: block) (ofs: Z) : Prop :=
| in_buffer_intro: forall bi,
    In bi buf ->
    in_buffer_item bi b ofs ->
    in_buffer buf b ofs.

Definition wfbi (bi : buffer_item) : Prop :=
  match bi with
  | BufferedAlloc b lo hi => lo < hi
  | BufferedFree b lo hi => lo < hi 
  | _ => True
  end.

Definition wfbis (bis : list buffer_item) : Prop :=
  forall bi, In bi bis -> wfbi bi.

(** * Auxiliary operation *)
Definition get_tsom_b (t : tid) (tm : tsomem) : list block :=
  match tm with
  | mktsomem bfs gm => get_buffer_b (bfs t)
  end.

Definition load_tsomem (c : memory_chunk) (tm : tsomem)
           (b : block) (pos : Z) : option val :=
  match tm with
  | mktsomem bfs gm => load c gm b pos
  end.

Definition store_tsomem (c : memory_chunk) (tm : tsomem)
           (b : block) (pos : Z) (v : val) : option tsomem :=
  match tm with
  | mktsomem bfs gm =>
    match store c gm b pos v with
    | Some gm' => Some (mktsomem bfs gm')
    | None => None
    end
  end.

(** Apply the whole content of the thread buffer *)
Definition append_t_buffer (t : tid) (tm : tsomem) (bi: buffer_item) : tsomem :=
  let bf := tm.(tso_buffers) t in
  let gm := memory tm in
  mktsomem (tupdate t (bf++(bi::nil)) tm.(tso_buffers)) gm.

(** Get gmem from [tsomem] *)
Definition get_gm (tm : tsomem) :=
  match tm with
  | mktsomem bf m => m
  end.

Definition no_perm (m : gmem) (b : block) (ofs : Z) :=
  (GMem.mem_access m) !! b ofs Memperm.Max = None /\
  (GMem.mem_access m) !! b ofs Memperm.Cur = None.

Definition inrange (b : block) (ofs : Z) (sz : Z) :=
  fun b' ofs' => if Pos.eq_dec b b' then
                   if (zle ofs ofs') && (zlt ofs' (ofs + sz)%Z) then
                     true
                   else
                     false
                 else
                   false.

Definition outrange (b : block) (ofs : Z) (sz : Z) :=
  fun b' ofs' => if Pos.eq_dec b b' then
                   if (zle ofs ofs') && (zlt ofs' (ofs + sz)%Z) then
                     false
                   else
                     true
                 else
                   true.

Definition gmem_loc_content_eq (P : Locs.t) (m m' : gmem) :=
  forall b ofs0, Locs.belongsto P b ofs0 ->
          ZMap.get ofs0 (GMem.mem_contents m) !! b =
          ZMap.get ofs0 (GMem.mem_contents m') !! b.

Definition gmem_loc_perm_eq (P : Locs.t) (m m' : gmem) :=
  forall b ofs0 k, Locs.belongsto P b ofs0 ->
            (GMem.mem_access m) !! b ofs0 k = (GMem.mem_access m') !! b ofs0 k.

Definition gmem_loc_eq (P : Locs.t) (m m' : gmem) :=
  gmem_loc_content_eq P m m' /\ gmem_loc_perm_eq P m m'.

Local Notation footprint := FP.t.
Definition bi_footprint (bi: buffer_item) : footprint :=
  match bi with
  | BufferedAlloc b lo hi => uncheck_alloc_fp b lo hi
  | BufferedFree b lo hi => free_fp b lo hi
  | BufferedStore chunk b ofs v => store_fp chunk b ofs
  end.

Definition unbuf_locality_1 (bi : buffer_item) (m m' : gmem) :=
  apply_buffer_item bi m = Some m' ->
  forall m0,
    MemPre m m0 (bi_footprint bi) ->
    exists m0', apply_buffer_item bi m0 = Some m0' /\ MemPost m' m0' (bi_footprint bi).


