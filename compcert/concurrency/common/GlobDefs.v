(* This file is partly adapted from file [linking.v] of Compositional CompCert,
   including definitions and properties of [Core.t] and [CallStack.t].
   In [Core.t], we have additional field for recording the corresponding freelists 
   of the runtime module.
   In [CallStack.t], we removed the constaints from its definitions, 
   hoping to make the semantics cleaner.
   The constraints (or invariants) on callstacks are presented separately in [ThreadPool.inv_cs].

   In this file we add additional construct for freelists, thread pool, etc.. *)

Require Import Coqlib Maps.
Require Import mathcomp.ssreflect.fintype.
Require Import AST Values Globalenvs.
Require Import Blockset GMemory MemClosures MemAux InteractionSemantics GAST Injections.
Require Import Lists.Streams Lia.

(** * Definitions of global runtime states*)

(** This file defines the runtime global states. 
    The global world consists of:
- [GlobEnv]: environment containing module code and freelists
- [ProgConfig]: runtime state 
 *)


(** thread id *)
Definition tid : Type := positive.
(** freelist if *)
Definition fid : Type := positive.
(** module id *)
Definition mid : Type := nat.

(** ** The freelists of all threads and runtime modules *) 
Module FLists.

  (** Freelists consists of
- [flist_content]: mapping from freelist id [fid] to the actual freelists of type [Stream block]
- [thread_flmap]: a stream of freelist ids allocated for each thread *)
  
  Record t: Type :=
    { flist_content: fid -> freelist;
      thread_flmap: tid -> nat -> fid;
    }.

  (** We always assume freelists are [wd], i.e.
- [flist_norep]: each freelist itself has no duplicated block
- [flist_disj]: any two freelists are disjoint
- [thread_fl_norep]: threads' freelist id stream is not duplicated
- [thread_fl_disj]: threads are not assigned with have duplicated freelists 
      In this way, any two different runtime [Core.t]s could be guaranteed assigned with disjoint freelist.
   *)
  Record wd (fls: t) : Prop :=
    {
      flist_norep: forall f, norep (flist_content fls f);      
      flist_disj: forall f1 f2, f1 <> f2 ->
                                disj (flist_content fls f1) (flist_content fls f2);
      thread_fl_norep: forall t n1 n2, n1 <> n2 ->
                                       thread_flmap fls t n1 <>
                                       thread_flmap fls t n2;
      thread_fl_disj: forall t1 t2 n1 n2, t1 <> t2 ->
                                          (thread_flmap fls t1 n1) <>
                                          (thread_flmap fls t2 n2);
    }.

  (** *** Initial Freelists *)
  (** mapping blocks to countable freelists.. *)
  (**     0   1   2   3   4  ..
     0   1   2   4   7   11 ..
     1   3   5   8   12 ..
     2   6   9   13 ..
     3   10  14 ..
     4   15 ..
   *)

  Definition fid_to_freelist_func (base: block) (fid: positive) (n: nat) : block :=
    let: row := (Pos.to_nat fid - 1)%nat in
    let: col := n in
    (Pos.of_nat ((row + col + 2) * (row + col + 1) / 2 - col)%nat + base - 1)%positive.

  Lemma arith_result2:
    forall m n,
      ((m + n + 2) * (m + n + 1) / 2  > n)%nat .
  Proof.
    induction m.
    (* m = 0 *)
    intro. rewrite Nat.add_0_l.
    induction n. simpl. lia.
    do 2 rewrite plus_Snm_nSm. rewrite mult_comm.
    replace 3%nat with (1 + 2)%nat by Lia.lia.
    rewrite plus_assoc. rewrite Nat.mul_add_distr_l.
    rewrite Nat.div_add; lia.
    (* induction on m *)
    intro.
    rewrite plus_Snm_nSm. rewrite <- Nat.add_assoc.
    rewrite plus_Snm_nSm. rewrite <- Nat.add_assoc. rewrite plus_Snm_nSm.
    do 2 rewrite Nat.add_assoc.
    replace 3%nat with (1 + 2)%nat by Lia.lia.
    rewrite plus_assoc. rewrite Nat.mul_add_distr_r.
    rewrite mult_comm. rewrite plus_comm. rewrite mult_comm. rewrite plus_comm.
    rewrite Nat.div_add; lia.
  Qed.

  Lemma div2_plus_1:
    forall y x:nat, (x / 2 - y = (x - 2 * y) / 2)%nat.
  Proof.
    induction y; intro. 
    rewrite Nat.mul_0_r, 2 Nat.sub_0_r. auto.
    replace (x / 2 - S y)%nat with (x / 2 - y - 1)%nat by lia. rewrite IHy. clear.
    replace ((x - 2 * y) / 2 - 1)%nat with ((x - 2 * y - 2)/2)%nat.
    replace (2 * S y)%nat with (2 * (y + 1))%nat by lia.
    rewrite Nat.mul_add_distr_l. rewrite Nat.mul_1_r, Nat.sub_add_distr. auto.
    assert (forall x, (x / 2 - 1 = (x - 2) / 2)%nat).
    { clear. intro.
      induction x. simpl. auto.
      destruct x. simpl. lia.
      destruct x. simpl. lia.
      replace (S (S (S x)) - 2)%nat with (S x) by lia.
      replace (S (S x) - 2)%nat with x in IHx by lia.
      destruct (Even.even_or_odd x).
      (* even *)
      assert (Even.even (S (S x))) by (apply Even.even_S, Even.odd_S; auto).
      do 2 rewrite <- Nat.div2_div.
      rewrite <- Div2.even_div2; auto. rewrite Nat.div2_div. rewrite IHx.
      rewrite <- Div2.even_div2; auto. symmetry. apply Nat.div2_div.
      (* odd *)
      assert (Even.odd (S (S x))) by (apply Even.odd_S, Even.even_S; auto).
      do 2 rewrite <- Nat.div2_div.
      rewrite <- (Div2.odd_div2 x); auto.
      rewrite <- Div2.odd_div2; auto.
    }
    rewrite H. auto.
  Qed.

  
  Lemma arith_aux:
    forall x1 y1 x2 y2, (x1 + y1 < x2 + y2 ->
                   (x1 + y1 + 2) * (x1 + y1 + 1) / 2 - y1 <
                   (x2 + y2 + 2) * (x2 + y2 + 1) / 2 - y2)%nat.
  Proof.
    intros m1 n1 m2 n2 H.
    pose proof (arith_result2 m2 n2).
    assert ((m2 + n2 + 2) * (m2 + n2 + 1) / 2 - n2 >
            (m2 + n2 + 2) * (m2 + n2 + 1) / 2 - (m2 + n2 + 1))%nat by lia.
    assert ((m2 + n2 + 2) * (m2 + n2 + 1) / 2 - (m2 + n2 + 1) =
            (m2 + n2 + 2 - 2) * (m2 + n2 + 1) / 2)%nat.
    { clear H H0 H1. 
      rewrite div2_plus_1.
      rewrite Nat.mul_sub_distr_r. auto.
    }
    rewrite H2 in H1; clear H2.
    replace (m2 + n2 + 2 - 2)%nat with (m2 + n2)%nat in H1 by lia.
    assert ((m2 + n2) * (m2 + n2 + 1) / 2 >= (m1 + n1 + 1) * (m1 + n1 + 2) / 2)%nat.
    { generalize H; clear; intro.
      assert (m2 + n2 >= m1 + n1 + 1)%nat by lia.
      apply Nat.div_le_mono; [lia|].
      apply Nat.mul_le_mono; lia. }
    assert ((m1 + n1 + 1) * (m1 + n1 + 2) / 2 >=
            (m1 + n1 + 1) * (m1 + n1 + 2) / 2 - n1)%nat by lia.
    eapply Nat.le_lt_trans. 2: eauto.
    eapply Nat.le_trans. rewrite (Nat.mul_comm). apply H3. auto.
  Qed.
    
    
  Lemma arith_result1:
    forall m1 n1 m2 n2,
      m1 <> m2 \/ n1 <> n2 ->
      ((m1 + n1 + 2) * (m1 + n1 + 1) / 2 - n1)%nat <>
      ((m2 + n2 + 2) * (m2 + n2 + 1) / 2 - n2)%nat.
  Proof.
    intros.
    pose proof (arith_result2 m1 n1).
    pose proof (arith_result2 m2 n2).

    (* whether m1 + n1 = m2 + n2 ? *)
    destruct (Nat.eq_dec (m1 + n1) (m2 + n2)).
    (* if eq, by arith_result2, n1 = n2 *) 
    rewrite e in *. intro.
    assert (n1 = n2) by lia.
    destruct H; try congruence.
    subst. apply H. generalize e; clear; intro. lia.
    (* if neq, it is either m1 + n1 > m2 + n2, or .. *)
    destruct (Nat.le_decidable (m1 + n1) (m2 + n2)).
    assert (m1 + n1  < m2 + n2 )%nat by lia; clear n H2.
    (* by m1 + n1 < m2 + n1, and arith_2,
       ((m2 + n2 + 2) * .. / 2 - n2 
       >  (...)/2 - (m2 + n2 + 1)
       >=? (...)/2 - (m1 + n1 + 1) *)
    apply arith_aux in H3. lia.
    assert (m2 + n2 < m1 + n1)%nat by lia; clear n H2.
    apply arith_aux in H3. lia.
  Qed.
      
  
  
  CoFixpoint func_to_stream {A: Type} (func: nat -> A) (base: nat): Stream A :=
    Cons (func base) (func_to_stream func (S base)).


  (** in case we need it for cofix *)
  Definition frob {A: Type} (s: Stream A) : Stream A :=
    match s with
    | Cons h t => Cons h t
    end.
  
  Theorem frob_eq: forall A (s: Stream A), s = frob s.
  Proof. destruct s. auto. Qed.
      
  Lemma freelist_func_stream_S:
    forall A n (func: nat -> A) base,
      Str_nth (S n) (func_to_stream func base) =
      Str_nth n (func_to_stream func (S base)).
  Proof.
    intros. unfold func_to_stream. unfold Str_nth. simpl. auto.
  Qed.
    
  Lemma freelist_func_stream_eq:
    forall A n (func: nat -> A) base,
      Str_nth n (func_to_stream func base) = func (n + base)%nat.
  Proof.
    intros. generalize dependent base.
    induction n. auto.
    intro. rewrite freelist_func_stream_S. rewrite IHn.
    rewrite Nat.add_comm. simpl. rewrite Nat.add_comm. auto.
  Qed.
  
    
  Definition init_flist_content (base: block) : fid -> freelist :=
    fun f: fid =>
      func_to_stream (fid_to_freelist_func base f) 0.
      

  (** norep in each inital freelist *)
  Lemma init_freelist_norep:
    forall base f, norep (init_flist_content base f).
  Proof.
    intros. constructor.
    unfold init_flist_content, fid_to_freelist_func.
    intros. do 2 rewrite  freelist_func_stream_eq.
    remember ((Pos.to_nat f - 1 + (n1 + 0) + 2) * (Pos.to_nat f - 1 + (n1 + 0) + 1) / 2 - (n1 + 0))%nat as x.
    remember ((Pos.to_nat f - 1 + (n2 + 0) + 2) * (Pos.to_nat f - 1 + (n2 + 0) + 1) / 2 - (n2 + 0))%nat as y.
    rewrite Nat.add_0_r in Heqx.
    rewrite Nat.add_0_r in Heqy.
    assert (x <> y).
    { subst. apply arith_result1. auto. }
    assert (x > 0)%nat.
    { subst. clear. pose proof (arith_result2 (Pos.to_nat f - 1) n1). Lia.lia. }
    assert (y > 0)%nat.
    { subst. clear. pose proof (arith_result2 (Pos.to_nat f - 1) n2). Lia.lia. }
    clear Heqx Heqy H.
    
    intro.
    assert (tmp: forall a b c: positive, (a + c - 1)%positive = (b + c - 1)%positive -> a = b).
    { clear. intros. rewrite <- (Pos.add_cancel_r _ _ 1) in H.
      do 2 rewrite Pos.sub_add in H; try lia. }
    apply tmp in H. clear tmp.
    apply H0. clear H0.
    pose proof (Nat2Pos.inj_compare x y).
    rewrite <- Pos.compare_eq_iff in H.
    rewrite H in H0.
    apply Nat.compare_eq_iff. apply H0; Lia.lia.
  Qed.

  (** disj among freelists *)
  Lemma init_freelist_disj:
    forall base f1 f2, f1 <> f2 -> disj (init_flist_content base f1) (init_flist_content base f2).
  Proof.
    intros. constructor. intros.
    unfold init_flist_content, fid_to_freelist_func. do 2 rewrite freelist_func_stream_eq.
    remember ((Pos.to_nat f1 - 1 + (n1 + 0) + 2) * (Pos.to_nat f1 - 1 + (n1 + 0) + 1) / 2 - (n1 + 0))%nat as x.
    remember ((Pos.to_nat f2 - 1 + (n2 + 0) + 2) * (Pos.to_nat f2 - 1 + (n2 + 0) + 1) / 2 - (n2 + 0))%nat as y.
    rewrite Nat.add_0_r in Heqx.
    rewrite Nat.add_0_r in Heqy.
    assert (x > 0)%nat.
    { subst. clear. pose proof (arith_result2 (Pos.to_nat f1 - 1) n1). Lia.lia. }
    assert (y > 0)%nat.
    { subst. clear. pose proof (arith_result2 (Pos.to_nat f2 - 1) n2). Lia.lia. }
    assert (tmp1: forall x y, (Pos.to_nat x - 1)%nat = (Pos.to_nat y - 1)%nat -> x = y).
    { clear. intros. lia. }
    assert (x <> y).
    { subst. apply arith_result1. left. intro. apply H. clear H. apply tmp1. auto. }
    clear Heqx Heqy H.
    
    intro.
    assert (tmp: forall a b c: positive, (a + c - 1)%positive = (b + c - 1)%positive -> a = b).
    { clear. intros. rewrite <- (Pos.add_cancel_r _ _ 1) in H.
      do 2 rewrite Pos.sub_add in H; try lia. }
    apply tmp in H. clear tmp.
    apply H2. clear H2 tmp1. 
    pose proof (Nat2Pos.inj_compare x y).
    rewrite <- Pos.compare_eq_iff in H.
    rewrite H in H2.
    apply Nat.compare_eq_iff. apply H2; Lia.lia.
  Qed.
    
  (* mapping fids to countable fid streams *)
  Definition tid_to_fid_stream (i: tid) (n: nat) : fid :=
    let: row := (Pos.to_nat i - 1)%nat in
    let: col := n in
    Pos.of_nat ((row + col + 2) * (row + col + 1) / 2 - col)%nat.


  Lemma tid_to_fid_stream_disj:
    forall i1 i2 n1 n2,
      i1 <> i2 \/ n1 <> n2 ->
      tid_to_fid_stream i1 n1 <> tid_to_fid_stream i2 n2.
  Proof.
    intros.
    unfold tid_to_fid_stream.
    assert ((Pos.to_nat i1 - 1 <> Pos.to_nat i2 - 1)%nat \/ n1 <> n2).
    { destruct H; auto. left.
      intro. apply H.
      rewrite <- Pos.compare_eq_iff.
      rewrite Pos2Nat.inj_compare.
      rewrite Nat.compare_eq_iff.
      lia. }
    eapply arith_result1 in H0. clear H.
    intro. apply Nat2Pos.inj_iff in H. auto.
    clear. pose proof (arith_result2 (Pos.to_nat i1 - 1)%nat n1). lia.
    clear. pose proof (arith_result2 (Pos.to_nat i2 - 1)%nat n2). lia.    
  Qed.

  Definition init: block -> t :=
    fun base : block => Build_t (init_flist_content base) tid_to_fid_stream.
        
  Theorem init_wd:
    forall b, wd (init b).
  Proof.
    intros.
    unfold init.
    constructor; simpl.
    (* norep in freelists *)
    apply init_freelist_norep.
    (* norep among freelists *)
    apply init_freelist_disj.
    (* norep in thread's freelist stream *)
    intros. apply tid_to_fid_stream_disj; auto.
    intros. apply tid_to_fid_stream_disj; auto.
  Qed.


  Definition get_block (fl: freelist) (n: nat) : block := Str_nth n fl.
  Definition get_fl (x: t) (f:fid) : freelist := x.(flist_content) f.
  
  Definition get_tfid (x: t) (i: tid) (n: nat) : fid := (x.(thread_flmap) i n).

  (* Interfaces, get freelist or block of a thread *)
  Definition get_tfl (x: t) (i: tid) (n: nat) : freelist := get_fl x (get_tfid x i n).

  Definition get_tfblock (x: t) (i: tid) (n: nat) (bid: nat) : block :=
    get_block (get_tfl x i n) bid.

  Definition bbelongsto (x: t) (i: tid) (b: block) : Prop :=
    exists n bid, get_tfblock x i n bid = b.

  Definition fbelongsto (x: t) (i: tid) (f: fid) : Prop :=
    exists n, get_tfid x i n = f.

  Definition bbelongstof (x: t) (f: fid) (b: block) : Prop :=
    exists n, get_block (get_fl x f) n = b.
  
  Theorem freelist_norepeat:
    forall x f, wd x -> norep (flist_content x f).
  Proof. intros. apply flist_norep. auto. Qed.
  
  Theorem freelist_disjoint:
    forall x f1 f2, wd x -> f1 <> f2 -> disj (flist_content x f1) (flist_content x f2).
  Proof. intros. apply flist_disj; auto. Qed.
  
  Theorem thread_freelist_norepeat:
    forall x i nf, wd x -> norep (get_tfl x i nf).
  Proof. intros; apply flist_norep; auto. Qed.

  Theorem thread_freelist_disj:
    forall x i1 i2 nf1 nf2, wd x -> i1 <> i2 -> disj (get_tfl x i1 nf1) (get_tfl x i2 nf2).
  Proof. intros. apply flist_disj. auto. apply (thread_fl_disj x); auto. Qed.

End FLists.
        

(** ** The global environment for all modules *)
(** The environment consists of the runtime ModSems of each module and 
    pre-allocated freelists *)

Module GlobEnv.

  (** - [M] : number of modules *)
  (** - [modules] : runtime ModSems, which is original module instrumented with initialized module's runtime environments *)
  (** - [ge_bound] : the bound for blocks bound to global definitions *)
  (** - [freelists] : the initialized freelists for runtime [Core.t]s *)
  Record t: Type :=
    {
      M: nat;
      modules: 'I_M -> ModSem.t;
      (* find module *)
      get_mod: ident -> option 'I_M;
      (* globenv bound *)
      ge_bound: block;
      (* freelists for threads *)
      freelists: FLists.t;
    }.

  (* Invariants *)
  Record wd (GE: t) : Prop :=
    {
      wd_fl: FLists.wd GE.(freelists)
      ;
      (** Global environments are disjoint. I.e., function/global variables of different modules 
          are bounded to disjoint memory blocks *)
      ge_inj: forall (i1 i2: 'I_(M GE)) Mod1 Mod2 id1 id2 b,
          ~ Nat.eq i1 i2 ->
          (modules GE) i1 = Mod1 ->
          (modules GE) i2 = Mod2 ->          
          let: ge1 := ModSem.ge Mod1 in
          let: ge2 := ModSem.ge Mod2 in
          Genv.find_symbol ge1 id1 = Some b ->
          Genv.find_symbol ge2 id2 = Some b ->
          id1 = id2
      ;
      (** Global environments are consistent. I.e., same ident is mapped to the same block in 
          all [ge]s *)
      ge_consist: forall (i1 i2: 'I_(M GE)) Mod1 Mod2 id b1 b2,
          (modules GE) i1 = Mod1 ->
          (modules GE) i2 = Mod2 ->
          let: ge1 := ModSem.ge Mod1 in
          let: ge2 := ModSem.ge Mod2 in
          Genv.find_symbol ge1 id = Some b1 ->
          Genv.find_symbol ge2 id = Some b2 ->
          b1 = b2
      ;
      (** genv_next of global environments eq to ge_bound *)
      ge_bound_consist:
        forall i Mod, modules GE i = Mod ->
                 let: ge := ModSem.ge Mod in
                 Genv.genv_next ge = ge_bound GE;
             
      (** No conflict definitions.
          [TODO] is it necessary?
       *)
    }.

  Definition det (GE: t) : Prop :=
    forall ix, mod_det (modules GE ix).

  Definition mods_wd (GE: t) : Prop :=
    forall ix, mod_wd (modules GE ix).
  
  (** The [GE] is properly initialized from [cus] if [init cus GE] *)
  Record init {NL: nat} {L: @langs NL} (cus: cunits L) (GE: t): Prop :=
    {
      (** Amount of runtime semantic modules is equal to amount of compilation units *)
      mod_num: (M GE) = length cus
      ;
      (** All runtime semantic modules ([ModSem.t]) are properly initialized w.r.t. its language*)
      ge_init: forall (i: 'I_(M GE)),
          (exists cui, nth_error cus i = Some cui /\
                       let: Mod:= (modules GE) i in
                       ModSem.init_modsem (L (lid L cui)) (cu L cui) Mod)
      ;
      (** No conflict definitions.
          [TODO] is it necessary?
       *)
      (** Domain of [get_mod] contains all internal functions *)
      (** since get_mod is a function, 
          wd implies internal function sets of
          different cunits are disjoint. *)
      get_mod_init:
        forall id mid,
          (get_mod GE id) = Some mid <->
          snd (@fold_left (nat * (option nat)) (cunit L)
                          (fun ir cui => let (i, res) := ir in
                                      if res then (S i, res)
                                      else if In_dec peq id (internal_fn (L (lid L cui)) (cu L cui))
                                           then (S i, Some i)
                                           else (S i, res))
                          cus (0%nat, None))
          = Some (nat_of_ord mid)
      ;
      
      (*    get_mod_wd:
        forall id (i: 'I_(M GE)) cui,
          nth_error cus i = Some cui ->
          In id (internal_fn (L (lid L cui)) (cu L cui)) ->
          get_mod GE id = Some i 
      ;*)
      ge_wd: wd GE;
          
    }.

  Inductive init_mem: t -> gmem -> Prop :=
  | Init_mem : forall GE gm,
      (* globval blocks are properly initialized *)
      (forall i,
          let: Mod := modules GE i in
          let: l := ModSem.lang Mod in
          let: ge := ModSem.ge Mod in
          init_gmem l ge gm) ->
      (* freelists are free *)
      (forall fi,
          no_overlap (FLists.get_fl (freelists GE) fi) (valid_block_bset gm)) ->
      init_mem GE gm.

End GlobEnv.



(** **  [Core.t] *)
(** 
    The type [Core.t] gives runtime states of dynamic module invocations. 

- [i : 'I_N]:
      A natural between [0..n-1] that maps this core back to the
      translation unit numbered [i] from which it was invoked. 
- [c : (cores i).(C)]:
      Runtime states of module [i]. 
- [sg : signature]:
      Type signature of the function that this core was spawned to handle. 
- [F : fid]:
      the freelist assigned to this runtime core.
*)
(** 
    A [Core] is a runtime local state of some core semantics, 
    including module id and the signature of the function spawning the core 
*)
Module Core.
  Section Core.
    Context {ge: GlobEnv.t}.
    
    Record t : Type :=
      {
        i : 'I_ge.(GlobEnv.M);

        c : (ge.(GlobEnv.modules) i).(ModSem.lang).(core);
        sg : signature;
        
        F : fid;
      }.

    Inductive update
              (x: t)
              (c': (ge.(GlobEnv.modules) x.(i)).(ModSem.lang).(core))
      : t -> Prop :=
      Update: forall x',
        x' = Build_t x.(i) c' x.(sg) x.(F) -> update x c' x'.

  End Core.
End Core.



(** ** [CallStack.t] *)
(** The type [CallStack.t] gives the thread runtime stack of spawned cores *)
Module CallStack.
  Section CallStack.
    Context {ge: GlobEnv.t}.

    Definition t : Type := list (@Core.t ge).

    (* an empty call stack for thread i *)
    Definition emp_cs : t := nil.
    (* push a new core (function call) *)
    Definition push (c: Core.t) (cs: t) : t := c :: cs.
    (* pop the top core (function return) *)
    Definition pop (cs: t) : option t :=
      match cs with
      | nil => None
      | c :: cs' => Some cs'
      end.
    (* get the top core *)
    Definition top (cs: t) : option Core.t :=
      match cs with
      | nil => None
      | c :: cs' => Some c
      end.
    (* update top of call stack *)
    Inductive update : t -> Core.t -> t -> Prop :=
      Update : forall c cs cc c',
        Core.update c cc c' ->
        update (c::cs) c' (c'::cs).

    Definition is_emp (cs: t) : Prop := cs = nil.
    
  End CallStack.
End CallStack.

(** ** [ThreadPool.t] *)
(** The type [ThreadPool.t] gives the threadpool definition *)
Module ThreadPool.
  Section ThreadPool.
    Context {ge: GlobEnv.t}.

    Record t : Type :=
      {
        content: PMap.t (option (@CallStack.t ge));
        next_tid: tid;
        (* the next fid num for each thread *)
        next_fmap: tid -> nat;
      }.

    Definition emp: t := Build_t (PMap.init None) 1%positive (fun _ => 0%nat).
      
    Definition spawn (thdp: t)
               (mid: 'I_(GlobEnv.M ge))
               (c: core (ModSem.lang (GlobEnv.modules ge mid)))
               (sg: signature) : t :=
      let: nf := (thdp.(next_fmap) thdp.(next_tid)) in
      let: f := FLists.get_tfid (GlobEnv.freelists ge) (thdp.(next_tid)) nf in
      let: c := Core.Build_t mid c sg f in
      Build_t (PMap.set thdp.(next_tid) (Some (c::nil)) thdp.(content))
              (Pos.succ thdp.(next_tid))
              (fun i => if peq i thdp.(next_tid) then (S (thdp.(next_fmap) i))
                        else thdp.(next_fmap) i).

    Definition push (thdp: t) (i: tid)
               (mid: 'I_(GlobEnv.M ge))
               (c: core (ModSem.lang (GlobEnv.modules ge mid)))
               (sg: signature) : option t :=
      let: ocs := PMap.get i thdp.(content) in
      match ocs with
      | None => None
      | Some cs =>
        let: nf := (thdp.(next_fmap) i) in
        let: f := FLists.get_tfid (GlobEnv.freelists ge) i nf in
        let: c := Core.Build_t mid c sg f in
        Some
          (Build_t (PMap.set i (Some (CallStack.push c cs)) thdp.(content))
                   (thdp.(next_tid))
                   (fun i' => if peq i i' then (S (thdp.(next_fmap) i))
                             else thdp.(next_fmap) i')
          )
      end.


        
    Definition pop (thdp: t) (i: tid) : option t :=
      let: ocs := PMap.get i thdp.(content) in
      match ocs with
      | None => None
      | Some cs =>
        match CallStack.pop cs with
        | None => None
        | Some cs' =>
          Some (Build_t (PMap.set i (Some cs') thdp.(content))
                        (thdp.(next_tid)) (thdp.(next_fmap)))
        end
      end.

    Definition get_cs (thdp: t) (i: tid) : option CallStack.t :=
      PMap.get i thdp.(content).
    
    Definition get_top (thdp: t) (i: tid) : option Core.t :=
      match get_cs thdp i with
      | Some cs => CallStack.top cs
      | None => None
      end.

    Inductive update (thdp: t) (i: tid) (c: Core.t) : t -> Prop :=
      Update : forall cs cs' thdp',
        get_cs thdp i = Some cs ->
        CallStack.update cs c cs' ->
        thdp' = Build_t (PMap.set i (Some cs') thdp.(content))
                        (thdp.(next_tid)) (thdp.(next_fmap)) ->
        update thdp i c thdp'.

    
    (* The initial threadpool w.r.t. a collection of entries *)
    Inductive init : entries -> t -> Prop :=
    | init_nil : init nil emp
    | init_cons :
        forall funid m_id,
          GlobEnv.get_mod ge funid = Some m_id ->
          forall e thdp cc,
            init e thdp ->
            let: Mod := GlobEnv.modules ge m_id in
            let: l := ModSem.lang Mod in
            let: Ge := ModSem.Ge Mod in
            l.(init_core) Ge funid nil = Some cc ->
            let: thdp':= spawn thdp m_id cc signature_main in
            init (funid :: e) thdp'.
        
    Definition valid_tid (TP:t) (i:tid) := Plt i (next_tid TP).

    (*
      Program Definition upd (TP: t) (i: tid) (cs: CallStack.t) : option t :=
      if plt i (@next_tid TP) then
      Some (Build_t (PMap.set i (Some cs) (@tp TP)) (@next_tid TP) _ _)
      else None.
      Next Obligation.
      rewrite PMap.gsspec. destruct peq.
      subst. contradiction.
      apply (tp_finite TP); auto.
      Qed.
      Next Obligation.
      rewrite PMap.gsspec.
      destruct peq; eauto.
      apply (tp_valid TP) in H0; auto.
      Qed.
     *)  
    Inductive halted : t -> tid -> Prop :=
    | Halted : forall TP i cs,
        get_cs TP i = Some cs -> CallStack.is_emp cs ->
        halted TP i.
                          
    (* invariants on the fid of call stacks *)            
    Record inv_cs (cs: CallStack.t) (i: tid) (next: nat) : Prop :=
      {
        (* - fid in cores belongsto thread i's fid map *)
        fid_belongsto: forall c,
            In c cs ->
            FLists.fbelongsto (ge.(GlobEnv.freelists)) i c.(Core.F);
        (* - fid are valid w.r.t. [next] *)
        fid_valid: forall c,
            In c cs ->
            exists n, (n < next)%nat /\
                      FLists.get_tfid (ge.(GlobEnv.freelists)) i n = c.(Core.F);
        (* - fid of each core are not equal *)
        fid_disjoint:
          forall n1 n2 (core1 core2: @Core.t ge),
            nth_error cs n1 = Some core1 ->
            nth_error cs n2 = Some core2 ->
            (Core.F core1) = (Core.F core2) ->
            n1 = n2;
      }.

    Lemma cs_upd_inv_cs:
      forall (cs: @CallStack.t ge) c cs' i f,
        inv_cs cs i f ->
        CallStack.update cs c cs' ->
        inv_cs cs' i f.
    Proof.
      intros.
      destruct H, H0; subst.
      destruct H; subst; simpl in *.
      destruct c; simpl in *.
      remember {| Core.i := i0; Core.c := c; Core.sg := sg; Core.F := F |} as c0.
      constructor; intros; simpl in *.
      { destruct H.
        specialize (fid_belongsto0 c0).
        subst; simpl in *. apply fid_belongsto0; auto.
        apply fid_belongsto0; auto. }
      { destruct H.
        specialize (fid_valid0 c0).
        subst; simpl in *; apply fid_valid0; auto.
        apply fid_valid0; auto. }
      { specialize (fid_disjoint0 n1 n2).
        destruct n1; destruct n2; simpl in *; auto; subst.
        eapply fid_disjoint0 in H0; eauto. inversion H. subst. auto.
        eapply fid_disjoint0 in H; eauto. inversion H0. subst. auto.
        eapply fid_disjoint0; eauto. }
    Qed.

    Lemma cs_push_inv_cs:
      forall cs ix cc sg cs' i nf,
        GlobEnv.wd ge ->
        inv_cs cs i nf ->
        CallStack.push
          {|Core.i := ix; Core.c := cc; Core.sg := sg;
            Core.F := FLists.get_tfid (GlobEnv.freelists ge) i nf |} cs
        = cs' ->
        inv_cs cs' i (S nf).
    Proof.
      intros cs ix cc sg cs' i nf Hwdge. intros.
      unfold CallStack.push in H0. 
      destruct H; constructor; intros; subst; simpl in *.
      { destruct H. subst. simpl. eexists; eauto.
        apply fid_belongsto0; auto. }
      { destruct H. subst. exists nf. auto.
        apply fid_valid0 in H; destruct H as (nf'&H&H').
        exists nf'; split; auto. }
      { destruct n1; destruct n2; auto; simpl in *.
        inversion H; subst; clear H; simpl in *. exfalso.
        apply nth_error_in in H1. apply fid_valid0 in H1. destruct H1 as (n&Hneq&H1).
        rewrite <- H1 in H2. clear H1. assert (nf <> n) by Lia.lia.
        destruct (GlobEnv.wd_fl _ Hwdge). eapply thread_fl_norep; eauto.
        inversion H1; subst; clear H1; simpl in *. exfalso.
        apply nth_error_in in H. apply fid_valid0 in H. destruct H as (n&Hneq&H).
        rewrite <- H in H2. clear H. assert (nf <> n) by Lia.lia.
        destruct (GlobEnv.wd_fl _ Hwdge). eapply thread_fl_norep; eauto.
        
        apply (fid_disjoint0 _ _ _ _ H) in H1; auto. }
    Qed.

    Lemma cs_pop_inv_cs:
      forall cs cs' i nf,
        inv_cs cs i nf ->
        CallStack.pop cs = Some cs' ->
        inv_cs cs' i nf.
    Proof.
      intros. unfold CallStack.pop in H0. destruct cs; try discriminate.
      inversion H0; clear H0; subst.
      destruct H; constructor; intros; auto.
      apply fid_belongsto0; auto. apply in_cons; auto.
      apply fid_valid0; auto. apply in_cons; auto.
      specialize (fid_disjoint0 (S n1) (S n2)); simpl in *.
      assert (S n1 = S n2) by (eapply fid_disjoint0; eauto).
      Lia.lia.
    Qed.
      
    (* invariants *)
    Record inv (thdp: t) : Prop :=
      {
        tp_finite: forall i,
            Pos.ge i thdp.(next_tid) -> PMap.get i thdp.(content) = None;
        tp_valid: forall i,
            Plt i thdp.(next_tid) -> exists cs, PMap.get i thdp.(content) = Some cs;
        (* default val is none *)
        thdp_default: fst thdp.(content) = None;
        (* inv on callstacks and freelists hold *)
        cs_inv: forall i cs,
          PMap.get i thdp.(content) = Some cs ->
          inv_cs cs i (thdp.(next_fmap) i);
      }.

    Lemma emp_inv: inv emp.
    Proof.
      unfold emp. constructor; intros; simpl in *; auto.
      rewrite PMap.gi.
      simpl in H. induction i; inversion H.
      rewrite PMap.gi in H. discriminate.
    Qed.

    Lemma spawn_inv:
      forall tp mid c sg tp',
        spawn tp mid c sg = tp' ->
        inv tp ->
        inv tp'.
    Proof.
      unfold spawn; simpl. 
      intros. subst. inversion H0.
      constructor; subst; simpl in *; intros.
      { rewrite PMap.gsspec. destruct peq; subst. lia.
        apply tp_finite0. lia. }
      { rewrite PMap.gsspec. destruct peq; eauto.
        apply tp_valid0. apply Plt_succ_inv in H. destruct H; congruence. }
      { auto. }
      { rewrite PMap.gsspec in H. destruct peq; subst; auto.
        inv H. clear. constructor; simpl; intros; auto.
        inv H; simpl. unfold FLists.fbelongsto. eauto. inversion H0.
        inv H; simpl. unfold FLists.fbelongsto. eauto. inversion H0.
        do 2 try destruct n1; do 2 try destruct n2; simpl in *; auto; try discriminate.
      }
    Qed.

    Lemma init_inv:
      forall el tp,
        init el tp ->
        inv tp.
    Proof.
      intros. induction H.
      apply emp_inv.
      eapply spawn_inv; eauto.
    Qed.
      
    Lemma upd_top_inv:
      forall tp i c cc c' tp',
        inv tp ->
        get_top tp i = Some c ->
        Core.update c cc c' ->
        update tp i c' tp' ->
        inv tp'.
    Proof.
      intros.
      destruct H, H2; subst.
      constructor; intros; simpl in *; auto.
      { rewrite PMap.gsspec. destruct peq.
        subst. apply tp_finite0 in H3. unfold get_cs in H. congruence.
        apply tp_finite0; auto. }
      { rewrite PMap.gsspec. destruct peq.
        eexists; eauto.
        apply tp_valid0; auto. }
      { rewrite PMap.gsspec in H3. unfold get_cs in *.
        destruct peq; subst. inversion H3. subst. clear H3.
        apply cs_inv0 in H. eapply cs_upd_inv_cs; eauto.
        apply cs_inv0 in H3. auto.
      }
    Qed.

    Lemma push_inv:
      forall tp i ix cc sg tp',
        GlobEnv.wd ge ->
        inv tp ->
        push tp i ix cc sg = Some tp' ->
        inv tp'.
    Proof.
      intros tp i ix cc sg tp' Hwdge; intros. unfold push in H0.
      destruct H. remember ((content tp) !! i) as tpi.
      destruct tpi; try congruence. inversion H0; clear H0. 
      constructor; intros; subst; simpl in *.
      { rewrite PMap.gsspec. destruct peq.
        subst. apply tp_finite0 in H. congruence.
        apply tp_finite0; auto. }
      { rewrite PMap.gsspec. destruct peq.
        subst. eexists; eauto. apply tp_valid0; auto. }
      { auto. }
      { rewrite PMap.gsspec in H. destruct peq.
        inversion H; subst; clear H.
        destruct peq; try congruence.
        eapply cs_push_inv_cs; eauto.
        destruct peq; try congruence.
        apply cs_inv; auto. constructor; auto. }
    Qed.

    Lemma pop_inv:
      forall tp i tp',
        inv tp ->
        pop tp i = Some tp' ->
        inv tp'.
    Proof.
      unfold pop; intros.
      destruct H.
      remember ((content tp) !! i) as tpi.
      destruct tpi; try congruence.
      remember (CallStack.pop t0) as ocs.
      destruct ocs; try congruence.
      inversion H0; clear H0. subst.
      destruct t0. inversion Heqocs. symmetry in Heqocs.
      constructor; intros; subst; simpl in *.
      { rewrite PMap.gsspec. destruct peq.
        subst. apply tp_finite0 in H. congruence.
        apply tp_finite0; auto. }
      { rewrite PMap.gsspec. destruct peq.
        subst. eexists; eauto. apply tp_valid0; auto. }
      { auto. }
      { rewrite PMap.gsspec in H. destruct peq.
        inversion H; inversion Heqocs; subst; clear H Heqocs.
        eapply cs_pop_inv_cs; eauto.

        apply cs_inv; auto. constructor; auto. }
    Qed.

    Record inv_mem (thdp: t) (gm: gmem) : Prop :=
      {
        tp_valid_freelist_free:
          forall i n,
            (n >= (next_fmap thdp) i)%nat ->
            no_overlap (FLists.get_tfl (GlobEnv.freelists ge) i n) (valid_block_bset gm);
      }.
            
    Lemma push_top_fid:
      forall thdp i mid c sg thdp' C,
        push thdp i mid c sg = Some thdp' ->
        get_top thdp' i = Some C ->
        let nf := (thdp.(next_fmap) i) in
        let f := FLists.get_tfid (GlobEnv.freelists ge) i nf in
        Core.F C = f.
    Proof.
      intros.
      unfold push, get_top, get_cs, CallStack.top in *.
      repeat match goal with
             | H: Some _ = Some _ |- _ => inversion H; clear H; subst
             | H: match ?x with _ => _ end = _ |- _ =>
               destruct x eqn:? ; simpl in *; try (inversion H; fail); subst; simpl in *
             end.
      simpl in *. rewrite PMap.gsspec in Heqo. destruct peq; try congruence.
      inversion Heqo. simpl. auto.
    Qed.
    
  End ThreadPool.
End ThreadPool.

(** ** Atomic bit *)
Inductive Bit : Type :=
| O : Bit
| I : Bit.

(** ** Runtime state *)
(** Runtime state consists of 
    - [thread_pool]: mapping from thread id to runtime callstack 
    - [cur_tid]: the current thread that is running
    - [gm]: the global emmory state
    - [atom_bit]: abstract state for modeling atomic blocks
*)
Record ProgConfig {GE: GlobEnv.t}: Type :=
  {
    thread_pool : @ThreadPool.t GE;
    cur_tid : tid;
    gm : gmem;
    atom_bit : Bit;
  }.

(** ** Initial state *)
(** This property checks if runtime ModSems are properly generated and
   runtime Cores are properly initialized *)
(** 1. ge of each ModSem are properly initialized, without conflict *)
(**    note that we need [print], [ent_atom], and [exit_atom], we require these idents are not conflicted *)
(** 2. global vars are properly initialized in gm, freelists are free in gm *)
(** 3. cores are initialized from entries, inv |- threadpool  *)
(** 4. all freelist are wd and free *)
(** 5. initial gms are reach-closed on its domain (valid_blocks) *)
(** 6. the initialized [cur_tid] is valid and the [atom_bit] set to [O] *)
Inductive init_config
          {NL: nat} {L: @langs NL} (p: @prog NL L)
          (m:gmem) (GE: GlobEnv.t) (pc: @ProgConfig GE) (t: tid): Prop :=
  Init_config:
    (* 1. *)
    GlobEnv.init (fst p) GE ->
    (* 2. *)
    GlobEnv.init_mem GE m ->
    (* 3. *)
    ThreadPool.init (snd p) (pc.(thread_pool)) ->
    (* 4. *)
    FLists.wd (GlobEnv.freelists GE) ->
    (forall fi, no_overlap (FLists.get_fl (GlobEnv.freelists GE) fi) (valid_block_bset m)) ->
    (* 5. *)
    reach_closed m (valid_block_bset m) ->
    (* 6. cur_tid and atomBit *)
    cur_tid pc = t ->
    Plt t (ThreadPool.next_tid pc.(thread_pool)) ->
    (atom_bit pc) = O ->
    (gm pc) = m ->
    init_config p m GE pc t.

Lemma init_config_GE_wd:
  forall NL L (p:@prog NL L) gm GE pc t,
    init_config p gm GE pc t ->
    GlobEnv.wd GE.
Proof.
  inversion 1.
  inversion H0.
  auto.
Qed.

(** ** Final state *)
(** A state is final state if all threads are halted *)
Inductive final_state {ge: GlobEnv.t} : @ProgConfig ge -> Prop :=
| Final_state : forall pc TP,
    thread_pool pc = TP ->
    (forall i, ThreadPool.valid_tid TP i -> ThreadPool.halted TP i) ->
    final_state pc.



(** ** Realtion on initial memories *)
(** We require:
- sgm injects tgm w.r.t. some block inject function
- domain of sgm tgm matches
- locs of sgm tgm matches
 *)
Record InitRel (mu: Mu) (SGE TGE: GlobEnv.t) (sgm tgm: gmem) : Prop :=
  {
    ir_inject: GMem.Binject_weak (inj mu) sgm tgm;
    ir_mu_wd: Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu);
    ir_shared_src: SharedSrc mu = fun b => Plt b (GlobEnv.ge_bound SGE);
    ir_shared_tgt: SharedTgt mu = fun b => Plt b (GlobEnv.ge_bound TGE);
    ir_ge_bound: GlobEnv.ge_bound SGE = GlobEnv.ge_bound TGE;
    
    ir_senv_init_inj:
      forall (m: 'I_(GlobEnv.M SGE)) (n: 'I_(GlobEnv.M TGE)),
        nat_of_ord m = nat_of_ord n ->
        let Modm := GlobEnv.modules SGE m in
        let Modn := GlobEnv.modules TGE n in
        let sge := ModSem.ge Modm in
        let tge := ModSem.ge Modn in
        (forall id, option_rel (fun b b' => inj mu b = Some b')
                          (Senv.find_symbol sge id) (Senv.find_symbol tge id));
    
    ir_shared_src_valid: forall b, GMem.valid_block sgm b <-> Injections.SharedSrc mu b;
    ir_shared_tgt_valid: forall b, GMem.valid_block tgm b <-> Injections.SharedTgt mu b;
    
  }.


Definition res_has_type (res: val) (sg: signature) : Prop :=
  Val.has_type res (proj_sig_res sg).

Definition res_sg (sg: signature) (res: val) : val :=
  (* match (sg.(sig_res)) with
  | None => None
  | Some _ => Some res
  end. *)
  res.

Definition not_pointer (v: val) : Prop :=
  match v with
  | Vptr _ _ => False
  | Vundef => False
  | _ => True
  end.