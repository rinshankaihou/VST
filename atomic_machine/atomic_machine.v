(** * Sequentially consistent atomic machine

    This file lifts a sequential semantics to a sequentially consistent
    concurrent machine with a lambda-Rust-style reader/writer race detector
    (the [rw_map]) and SC atomic operations.

    A machine configuration is <<(tp, m, μ)>>, where [tp] is a thread pool,
    [m] is memory, and [μ] is a reader/writer state map. A sequential step has
    two phases: [Core_Try] takes one thread step, reserves its memory events in
    [μ], and records those events as pending. A thread with pending events can
    only take [Core_Commit], which finishes the events and releases their
    reservations. A failed reservation models a data race. *)

From Stdlib Require Import List.
Import ListNotations.

Require Import stdpp.gmap.

(** ** Reader/writer states

    The state of one memory byte, as in lambda-Rust: [Rst n] means [n]
    threads are between Try and Commit of a step that reads the byte;
    [Wst] means some thread is mid-step on a write to it. *)


Section RWMap.

  Context {Loc : Type}.
  Context {LocEqDec : EqDecision Loc}.
  Context {LocCountable : @Countable Loc _}.

  Inductive rw_state : Type :=
  | Rst (n : nat)
  | Wst.

  Variant mem_ev : Type :=
  | Read (l : Loc)
  | Write (l : Loc)
  | Alloc (l : Loc)
  | Free (l : Loc).

  Definition rw_map := gmap Loc rw_state.

  Implicit Types (μ : rw_map) (oμ : option rw_map) (l : Loc)
    (ev : mem_ev) (evs : list mem_ev).

  Definition initial_rw : rw_map := ∅.

  Definition rsv_Alloc μ l : option rw_map :=
    match μ !! l with
    | None => Some $ <[l := Rst 0]> μ
    | _ => None
    end.

  (** Reservation does not remove a location: a pending [fin_Read] may still
      need it. *)
  Definition rsv_Free μ : option rw_map :=
    mret μ.

  Definition rsv_Write μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Rst O => Some $ <[l := Wst]> μ
    | _ => None
    end.

  Definition rsv_Read μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Rst n => Some $ <[l := Rst (S n)]> μ
    | _ => None
    end.

  Definition fin_Alloc μ : option rw_map := mret μ.

  Definition fin_Free μ l : option rw_map :=
    match μ !! l with
    | Some _ => Some $ delete l μ
    | _ => None
    end.

  Definition fin_Write μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Wst => Some $ <[l := Rst O]> μ
    | _ => None
    end.

  Definition fin_Read μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Rst (S n) => Some $ <[l := Rst n]> μ
    | _ => None
    end.

  Lemma rsv_Write_fin_Write μ l μ' :
    rsv_Write μ l = Some μ' ->
    fin_Write μ' l = Some μ.
  Proof.
    unfold rsv_Write.
    destruct (μ !! l) as [[n |] |] eqn:Hlookup;
      simpl; try discriminate.
    destruct n; simpl; try discriminate.
    intros Hreserve. inversion Hreserve; subst μ'; clear Hreserve.
    unfold fin_Write. rewrite (lookup_insert_eq μ l Wst). simpl.
    rewrite (insert_insert μ l l (Rst 0) Wst).
    destruct (decide (l = l)); [| contradiction].
    f_equal. apply (insert_id μ l (Rst 0)). exact Hlookup.
  Qed.

  Lemma rsv_Read_fin_Read μ l μ' :
    rsv_Read μ l = Some μ' ->
    fin_Read μ' l = Some μ.
  Proof.
    unfold rsv_Read.
    destruct (μ !! l) as [[n |] |] eqn:Hlookup;
      simpl; try discriminate.
    intros Hreserve. inversion Hreserve; subst μ'; clear Hreserve.
    unfold fin_Read. rewrite (lookup_insert_eq μ l (Rst (S n))). simpl.
    rewrite (insert_insert μ l l (Rst n) (Rst (S n))).
    destruct (decide (l = l)); [| contradiction].
    f_equal. apply (insert_id μ l (Rst n)). exact Hlookup.
  Qed.

  Definition rsv_ev ev oμ : option rw_map :=
    μ ← oμ;
    match ev with
    | Read l => rsv_Read μ l
    | Write l => rsv_Write μ l
    | Alloc l => rsv_Alloc μ l
    | Free l => rsv_Free μ
    end.

  Definition fin_ev ev oμ : option rw_map :=
    μ ← oμ;
    match ev with
    | Read l => fin_Read μ l
    | Write l => fin_Write μ l
    | Alloc _ => fin_Alloc μ
    | Free l => fin_Free μ l
    end.

  (** Reserve memory events by updating the reader/writer map. *)
  Definition rsv evs μ : option rw_map :=
    foldr rsv_ev (Some μ) evs.

  (** Finish memory events, releasing reservations where appropriate. *)
  Definition fin evs μ : option rw_map :=
    foldr fin_ev (Some μ) evs.

End RWMap.


Section Memory.
  Class MemMixin {Loc Val : Type} {LocEqDec : EqDecision Loc} {LocCountable : Countable Loc} {Mem : Type} {Layout : Type} : Type := {
    load : Mem -> Loc -> Layout -> option Val;
    store : Mem -> Loc -> Layout -> Val -> option Mem;
    layout_to_locs : Loc -> Layout -> list Loc
  }.

End Memory.

Section AtomicMachine.

  Context `{mem_inst: !@MemMixin Loc Val LocEqDec LocCountable Mem Layout}.

  Local Notation mem_ev := (mem_ev(Loc:=Loc)).
  Local Notation rw_map := (rw_map(Loc:=Loc)).

  Inductive atomic_op : Type :=
  | ALoad : Layout -> Loc -> atomic_op
  | AStore : Layout -> Loc -> Val -> atomic_op
  | ACAS : Layout -> Loc -> Val (* expected val *) ->
          Val (* new val*) -> atomic_op.

  Class sqlang {mem_inst : @MemMixin Loc Val LocEqDec LocCountable Mem Layout} : Type := {
    (** Thread-local state. *)
    sqlang_thrd_st : Type;
    (** Events emitted by the underlying sequential semantics. *)
    sqlang_true_val : Val;
    sqlang_false_val : Val;
    sqlang_step :
      sqlang_thrd_st -> Mem -> list mem_ev -> sqlang_thrd_st -> Mem -> Prop;

    (** A pending atomic operation and its return-value continuation. *)
    sqlang_at_external :
      sqlang_thrd_st -> option (atomic_op * (option Val -> sqlang_thrd_st));

    (** Values transferred by atomic memory operations must be defined. *)
    sqlang_val_defined : Val -> Prop;

    (** Value (in)equality for CAS.  The suspended thread state remains an
        argument so a typed source language can recover the comparison type
        from the declaration which was decoded by [sqlang_at_external]. *)
    sqlang_ValEq : sqlang_thrd_st -> Mem -> Val -> Val -> Prop;
    sqlang_ValNEq : sqlang_thrd_st -> Mem -> Val -> Val -> Prop;
  }.

  Context {MemMixinInst : @MemMixin Loc Val _ _ Mem Layout}.
  Context {L : sqlang}.

  Local Notation C := sqlang_thrd_st.
  Local Notation at_external := sqlang_at_external.
  Local Notation Vtrue := sqlang_true_val.
  Local Notation Vfalse := sqlang_false_val.
  Local Notation ValDefined := sqlang_val_defined.
  Local Notation ValEq := sqlang_ValEq.
  Local Notation ValNEq := sqlang_ValNEq.

  Implicit Types (μ : rw_map) (oμ : option rw_map) (l : Loc)
    (ev : mem_ev) (evs : list mem_ev) (ly : Layout).

  Inductive tstate : Type :=
  | Running (c : C) (T : list mem_ev)
  | StuckState.

  Definition tpool := gmap nat tstate.

  (** No non-atomic write in progress anywhere in ls. *)
  Definition readable μ (ls : list Loc) : Prop :=
    Forall (fun l => μ !! l <> Some Wst) ls.

  (** No non-atomic access at all in ls. *)
  Definition writable μ (ls : list Loc) : Prop :=
    Forall (fun l => μ !! l = Some (Rst 0)) ls.

  Inductive at_step : tpool -> Mem -> rw_map -> tpool -> Mem -> rw_map -> Prop :=

  | Core_Try : forall tp m μ i c T c' m' μ'
      (Hget : tp !! i = Some (Running c []))
      (Hstep : sqlang_step c m T c' m')
      (Hreserve : rsv T μ = Some μ'),
      at_step tp m μ (<[i := Running c' T]> tp) m' μ'

  | Core_Commit : forall tp m μ i c T μ'
      (Hget : tp !! i = Some (Running c T))
      (Hne : T <> [])
      (Hcommit : fin T μ = Some μ'),
      at_step tp m μ (<[i := Running c []]> tp) m μ'

  | SC_Read : forall tp m μ i c ly l v K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c = Some (ALoad ly l, K))
      (Hmu : readable μ (layout_to_locs l ly))
      (Hload : load m l ly = Some v)
      (Hdefined : ValDefined v),
      at_step tp m μ (<[i := Running (K $ Some v) []]> tp) m μ

  | SC_Write : forall tp m μ i c ly l v m' K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c = Some (AStore ly l v, K))
      (Hmu : writable μ (layout_to_locs l ly))
      (Hstore : store m l ly v = Some m')
      (Hdefined : ValDefined v),
      at_step tp m μ (<[i := Running (K None) []]> tp) m' μ

  | SC_Cas_Suc : forall tp m μ i c ly l v_exp v_new v_cur m' K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c = Some (ACAS ly l v_exp v_new, K))
      (Hmu : writable μ (layout_to_locs l ly))
      (Hload : load m l ly = Some v_cur)
      (Hdefined_cur : ValDefined v_cur)
      (Heq : ValEq c m v_cur v_exp)
      (Hstore : store m l ly v_new = Some m')
      (Hdefined_new : ValDefined v_new),
      at_step tp m μ (<[i := Running (K $ Some Vtrue) []]> tp) m' μ

  | SC_Cas_Fail : forall tp m μ i c ly l v_exp v_new v_cur K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c = Some (ACAS ly l v_exp v_new, K))
      (Hmu : readable μ (layout_to_locs l ly))
      (Hload : load m l ly = Some v_cur)
      (Hdefined_cur : ValDefined v_cur)
      (Hneq : ValNEq c m v_cur v_exp),
      at_step tp m μ (<[i := Running (K $ Some Vfalse) []]> tp) m μ

  (** The comparison succeeded, but the write reservation failed. *)
  | SC_Cas_Stuck : forall tp m μ i c ly l v_exp v_new v_cur K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c = Some (ACAS ly l v_exp v_new, K))
      (Hload : load m l ly = Some v_cur)
      (Hdefined_cur : ValDefined v_cur)
      (Heq : ValEq c m v_cur v_exp)
      (Ho : ~ writable μ (layout_to_locs l ly)),
      at_step tp m μ (<[i := StuckState]> tp) m μ.

End AtomicMachine.
