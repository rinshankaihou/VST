(* Extended the original CompCert's correctness proof for supporting concurrency. *)

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

(** Correctness proof for Cminor generation. *)

Require Import Coq.Program.Equality FSets Permutation.
Require Import FSets FSetAVL Orders Mergesort.
Require Import Coqlib Maps Ordered Errors Integers Floats.
Require Intv.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Csharpminor Switch Cminor Cminorgen.


Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        Op_fp CminorLang Cminor_op_footprint cminorgen.

Require Import  Cop  Csharpminor Csharpminor_local Cminor Cminor_local  Cop_fp_local infp.

Local Open Scope error_monad_scope.
Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.
Ltac inv_eq:=
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; inversion H ;subst
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;subst;try contradiction;try discriminate.
Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Definition match_prog (p: Csharpminor_local.comp_unit) (tp: Cminor_local.cminor_comp_unit) :=
  match_comp_unit_gen (fun f tf => transl_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  intros. apply match_transform_partial_cunit; auto.
Qed.

Section TRANSLATION.

Variable prog: Csharpminor_local.comp_unit.
Variable tprog: cminor_comp_unit.
Variable ge : Csharpminor.genv.
Variable tge : Cminor.genv.
Hypothesis TRANSL: match_prog prog tprog.
Hypothesis SGEINIT: globalenv_generic prog ge.
Hypothesis TGEINIT: globalenv_generic tprog tge.
Hypothesis S_EQ: ge.(Genv.genv_next) = tge.(Genv.genv_next).
Lemma ge_match: ge_match_strict ge tge.
Proof. eapply match_cu_ge_match_strict; eauto. Qed.
Lemma genv_match: Genv.match_genvs (match_globdef  (fun f tf => transl_fundef f = OK tf) eq) ge tge.
Proof. eapply match_cu_match_genv; eauto. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. destruct genv_match. auto. Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. eapply match_cu_senv_preserved; eauto. Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Csharpminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
    Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof.
  destruct genv_match.
  unfold fundef,Csharpminor.fundef in *.
  unfold Genv.find_funct_ptr, Genv.find_def; intros.
  inv_eq.
  specialize (mge_defs b).
  inv mge_defs.
  rewrite <-H0 in Heqo. inv Heqo.
  rewrite <- H in Heqo. inv Heqo.
  inv H2. eauto.
Qed.
Lemma functions_translated:
  forall (v: val) (f: Csharpminor.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
    Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof.
   destruct v; simpl; intros; try discriminate. 
   destruct Ptrofs.eq_dec; [|discriminate]. 
   apply function_ptr_translated; auto.
Qed.

Lemma sig_preserved_body:
  forall f tf cenv size,
  transl_funbody cenv size f = OK tf ->
  tf.(fn_sig) = Csharpminor.fn_sig f.
Proof.
  intros. unfold transl_funbody in H. monadInv H; reflexivity.
Qed.

Lemma sig_preserved:
  forall f tf,
  transl_fundef f = OK tf ->
  Cminor.funsig tf = Csharpminor.funsig f.
Proof.
  intros until tf; destruct f; simpl.
  unfold transl_function. destruct (build_compilenv f).
  case (zle z Ptrofs.max_unsigned); simpl bind; try congruence.
  intros. monadInv H. simpl. eapply sig_preserved_body; eauto.
  intro. inv H. reflexivity.
Qed.

(** * Derived properties of memory operations *)

Lemma load_freelist:
  forall fbl chunk m b ofs m',
  (forall b' lo hi, In (b', lo, hi) fbl -> b' <> b) ->
  Mem.free_list m fbl = Some m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction fbl; intros.
  simpl in H0. congruence.
  destruct a as [[b' lo] hi].
  generalize H0. simpl. case_eq (Mem.free m b' lo hi); try congruence.
  intros m1 FR1 FRL.
  transitivity (Mem.load chunk m1 b ofs).
  eapply IHfbl; eauto. intros. eapply H. eauto with coqlib.
  eapply Mem.load_free; eauto. left. apply sym_not_equal. eapply H. auto with coqlib.
Qed.

Lemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
Proof.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed.

Lemma nextblock_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi].
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.nextblock m0). eauto. eapply Mem.nextblock_free; eauto.
Qed.

Lemma free_list_freeable:
  forall l m m',
  Mem.free_list m l = Some m' ->
  forall b lo hi,
  In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  destruct H0. inv H.
  eauto with mem.
  red; intros. eapply Mem.perm_free_3; eauto. exploit IHl; eauto.
Qed.

Lemma nextblock_storev:
  forall chunk m addr v m',
  Mem.storev chunk m addr v = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold Mem.storev; intros. destruct addr; try discriminate.
  eapply Mem.nextblock_store; eauto.
Qed.

(** * Correspondence between C#minor's and Cminor's environments and memory states *)

(** In C#minor, every variable is stored in a separate memory block.
  In the corresponding Cminor code, these variables become sub-blocks
  of the stack data block.  We capture these changes in memory via a
  memory injection [f]:
  [f b = Some(b', ofs)] means that C#minor block [b] corresponds
  to a sub-block of Cminor block [b] at offset [ofs].

  A memory injection [f] defines a relation [Val.inject f] between
  values and a relation [Mem.inject f] between memory states.  These
  relations will be used intensively in our proof of simulation
  between C#minor and Cminor executions. *)

(** ** Matching between Cshaprminor's temporaries and Cminor's variables *)
Definition match_temps (f: meminj) (le: Csharpminor.temp_env) (te: env) : Prop :=
  forall id v, le!id = Some v -> exists v', te!(id) = Some v' /\ Val.inject f v v'.

Lemma match_temps_invariant:
  forall f f' le te,
  match_temps f le te ->
  inject_incr f f' ->
  match_temps f' le te.
Proof.
  intros; red; intros. destruct (H _ _ H1) as [v' [A B]]. exists v'; eauto.
Qed.

Lemma match_temps_assign:
  forall f le te id v tv,
  match_temps f le te ->
  Val.inject f v tv ->
  match_temps f (PTree.set id v le) (PTree.set id tv te).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  inv H1. exists tv; auto.
  eauto.
Qed.

(** ** Matching between C#minor's variable environment and Cminor's stack pointer *)

Inductive match_var (f: meminj) (sp: block): option (block * Z) -> option Z -> Prop :=
  | match_var_local: forall b sz ofs,
      Val.inject f (Vptr b Ptrofs.zero) (Vptr sp (Ptrofs.repr ofs)) ->
      match_var f sp (Some(b, sz)) (Some ofs)
  | match_var_global:
      match_var f sp None None.

(** Matching between a C#minor environment [e] and a Cminor
  stack pointer [sp]. The [lo] and [hi] parameters delimit the range
  of addresses for the blocks referenced from [te]. *)

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (sp: block)
                 (lo hi: block) : Prop :=
  mk_match_env {

(** C#minor local variables match sub-blocks of the Cminor stack data block. *)
    me_vars:
      forall id, match_var f sp (e!id) (cenv!id);

(** [lo, hi] is a proper interval. *)
    me_low_high:
      Ple lo hi;

(** Every block appearing in the C#minor environment [e] must be
  in the range [lo, hi]. *)
    me_bounded:
      forall id b sz, PTree.get id e = Some(b, sz) -> Ple lo b /\ Plt b hi;

(** All blocks mapped to sub-blocks of the Cminor stack data must be
    images of variables from the C#minor environment [e] *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists sz, PTree.get id e = Some(b, sz);

(** All C#minor blocks below [lo] (i.e. allocated before the blocks
  referenced from [e]) must map to blocks that are below [sp]
  (i.e. allocated before the stack data for the current Cminor function). *)
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> Plt b lo -> Plt tb sp
  }.

Ltac geninv x :=
  let H := fresh in (generalize x; intro H; inv H).

Lemma match_env_invariant:
  forall f1 cenv e sp lo hi f2,
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  (forall b delta, f2 b = Some(sp, delta) -> f1 b = Some(sp, delta)) ->
  (forall b, Plt b lo -> f2 b = f1 b) ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. destruct H. constructor; auto.
(* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
(* bounded *)
  intros. eauto.
(* below *)
  intros. rewrite H2 in H; eauto.
Qed.

(** [match_env] and external calls *)

Remark inject_incr_separated_same:
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b, Mem.valid_block m1 b -> f2 b = f1 b.
Proof.
  intros. case_eq (f1 b).
  intros [b' delta] EQ. apply H; auto.
  intros EQ. case_eq (f2 b).
  intros [b'1 delta1] EQ1. exploit H0; eauto. intros [C D]. contradiction.
  auto.
Qed.

Remark inject_incr_separated_same':
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b b' delta,
  f2 b = Some(b', delta) -> Mem.valid_block m1' b' -> f1 b = Some(b', delta).
Proof.
  intros. case_eq (f1 b).
  intros [b'1 delta1] EQ. exploit H; eauto. congruence.
  intros. exploit H0; eauto. intros [C D]. contradiction.
Qed.

Lemma match_env_external_call:
  forall f1 cenv e sp lo hi f2 m1 m1',
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  Ple hi (Mem.nextblock m1) -> Plt sp (Mem.nextblock m1') ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. apply match_env_invariant with f1; auto.
  intros. eapply inject_incr_separated_same'; eauto.
  intros. eapply inject_incr_separated_same; eauto. red. destruct H. xomega.
Qed.

(** [match_env] and allocations *)

Lemma match_env_alloc:
  forall f1 id cenv e sp lo m1 sz m2 b ofs f2,
  match_env f1 (PTree.remove id cenv) e sp lo (Mem.nextblock m1) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_env f2 cenv (PTree.set id (b, sz) e) sp lo (Mem.nextblock m2).
Proof.
  intros until f2; intros ME ALLOC CENV INCR SAME OTHER ENV.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  inv ME; constructor.
(* vars *)
  intros. rewrite PTree.gsspec. destruct (peq id0 id).
  (* the new var *)
  subst id0. rewrite CENV. constructor. econstructor. eauto.
  rewrite Ptrofs.add_commut; rewrite Ptrofs.add_zero; auto.
  (* old vars *)
  generalize (me_vars0 id0). rewrite PTree.gro; auto. intros M; inv M.
  constructor; eauto.
  constructor.
(* low-high *)
  rewrite NEXTBLOCK; xomega.
(* bounded *)
  intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inv H. rewrite NEXTBLOCK; xomega.
  exploit me_bounded0; eauto. rewrite NEXTBLOCK; xomega.
(* inv *)
  intros. destruct (eq_block b (Mem.nextblock m1)).
  subst b. rewrite SAME in H; inv H. exists id; exists sz. apply PTree.gss.
  rewrite OTHER in H; auto. exploit me_inv0; eauto.
  intros [id1 [sz1 EQ]]. exists id1; exists sz1. rewrite PTree.gso; auto. congruence.
(* incr *)
  intros. rewrite OTHER in H. eauto. unfold block in *; xomega.
Qed.

(** The sizes of blocks appearing in [e] are respected. *)

Definition match_bounds (e: Csharpminor.env) (m: mem) : Prop :=
  forall id b sz ofs p,
  PTree.get id e = Some(b, sz) -> Mem.perm m b ofs Max p -> 0 <= ofs < sz.

Lemma match_bounds_invariant:
  forall e m1 m2,
  match_bounds e m1 ->
  (forall id b sz ofs p,
   PTree.get id e = Some(b, sz) -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_bounds e m2.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

(** ** Permissions on the Cminor stack block *)

(** The parts of the Cminor stack data block that are not images of
    C#minor local variable blocks remain freeable at all times. *)

Inductive is_reachable_from_env (f: meminj) (e: Csharpminor.env) (sp: block) (ofs: Z) : Prop :=
  | is_reachable_intro: forall id b sz delta,
      e!id = Some(b, sz) ->
      f b = Some(sp, delta) ->
      delta <= ofs < delta + sz ->
      is_reachable_from_env f e sp ofs.

Definition padding_freeable (f: meminj) (e: Csharpminor.env) (tm: mem) (sp: block) (sz: Z) : Prop :=
  forall ofs,
  0 <= ofs < sz -> Mem.perm tm sp ofs Cur Freeable \/ is_reachable_from_env f e sp ofs.

Lemma padding_freeable_invariant:
  forall f1 e tm1 sp sz cenv lo hi f2 tm2,
  padding_freeable f1 e tm1 sp sz ->
  match_env f1 cenv e sp lo hi ->
  (forall ofs, Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b hi -> f2 b = f1 b) ->
  padding_freeable f2 e tm2 sp sz.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [A | A].
  left; auto.
  right. inv A. exploit me_bounded; eauto. intros [D E].
  econstructor; eauto. rewrite H2; auto.
Qed.

(** Decidability of the [is_reachable_from_env] predicate. *)

Lemma is_reachable_from_env_dec:
  forall f e sp ofs, is_reachable_from_env f e sp ofs \/ ~is_reachable_from_env f e sp ofs.
Proof.
  intros.
  set (pred := fun id_b_sz : ident * (block * Z) =>
                 match id_b_sz with
                 | (id, (b, sz)) =>
                      match f b with
                           | None => false
                           | Some(sp', delta) =>
                               if eq_block sp sp'
                               then zle delta ofs && zlt ofs (delta + sz)
                               else false
                      end
                 end).
  destruct (List.existsb pred (PTree.elements e)) eqn:?.
  (* yes *)
  rewrite List.existsb_exists in Heqb.
  destruct Heqb as [[id [b sz]] [A B]].
  simpl in B. destruct (f b) as [[sp' delta] |] eqn:?; try discriminate.
  destruct (eq_block sp sp'); try discriminate.
  destruct (andb_prop _ _ B).
  left. apply is_reachable_intro with id b sz delta.
  apply PTree.elements_complete; auto.
  congruence.
  split; eapply proj_sumbool_true; eauto.
  (* no *)
  right; red; intro NE; inv NE.
  assert (existsb pred (PTree.elements e) = true).
  rewrite List.existsb_exists. exists (id, (b, sz)); split.
  apply PTree.elements_correct; auto.
  simpl. rewrite H0. rewrite dec_eq_true.
  unfold proj_sumbool. destruct H1. rewrite zle_true; auto. rewrite zlt_true; auto.
  congruence.
Qed.

(** * Correspondence between global environments *)

(** Global environments match if the memory injection [f] leaves unchanged
  the references to global symbols and functions. *)
Inductive match_globalenvs (f: meminj) (bound: block): Prop :=
| mk_match_globalenvs
    (GNEXT: bound=ge.(Genv.genv_next))
    (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
    (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
    (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
    (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
    (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Remark inj_preserves_globals:
  forall f hi,
  match_globalenvs f hi ->
  meminj_preserves_globals ge f.
Proof.
  intros. inv H.
  split. intros. apply DOMAIN. eapply SYMBOLS. eauto.
  split. intros. apply DOMAIN. eapply VARINFOS. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed.

(** * Invariant on abstract call stacks  *)

(** Call stacks represent abstractly the execution state of the current
  C#minor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a C#minor
  function and its Cminor translation. *)

Inductive frame : Type :=
  Frame(cenv: compilenv)
       (tf: Cminor.function)
       (e: Csharpminor.env)
       (le: Csharpminor.temp_env)
       (te: Cminor.env)
       (sp: block)
       (lo hi: block).

Definition callstack : Type := list frame.

(** Matching of call stacks imply:
- matching of environments for each of the frames
- matching of the global environments
- separation conditions over the memory blocks allocated for C#minor local variables;
- separation conditions over the memory blocks allocated for Cminor stack data;
- freeable permissions on the parts of the Cminor stack data blocks
  that are not images of C#minor local variable blocks.
*)
Inductive match_callstack (f: meminj) (m: mem) (tm: mem):
                          callstack -> block -> block -> Prop :=
  | mcs_nil:
      forall hi bound tbound,
      match_globalenvs f hi ->
      Ple hi bound -> Ple hi tbound ->
      match_callstack f m tm nil bound tbound
  | mcs_cons:
      forall cenv tf e le te sp lo hi cs bound tbound
        (BOUND: Ple hi bound)
        (TBOUND: Plt sp tbound)
        (MTMP: match_temps f le te)
        (MENV: match_env f cenv e sp lo hi)
        (BOUND: match_bounds e m)
        (PERM: padding_freeable f e tm sp tf.(fn_stackspace))
        (MCS: match_callstack f m tm cs lo sp)
        (PLT:~ Plt sp (Genv.genv_next ge)),
        match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound.


Lemma match_callstack_ple_ge:
  forall f m tm cs b tb,
    match_callstack f m tm cs b tb->
    Ple (Genv.genv_next ge) b.
Proof.
  induction cs.
  intros. inv H. inv H0. auto.
  intros. inv H. eapply IHcs in MCS.
  eapply Ple_trans;eauto.
  inv MENV. eapply Ple_trans;eauto.
Qed.
(** [match_callstack] implies [match_globalenvs]. *)

Lemma match_callstack_match_globalenvs:
  forall f m tm cs bound tbound,
  match_callstack f m tm cs bound tbound ->
  exists hi, match_globalenvs f hi.
Proof.
  induction 1; eauto.
Qed.

(** Invariance properties for [match_callstack]. *)

Lemma match_callstack_invariant:
  forall f1 m1 tm1 f2 m2 tm2 cs bound tbound,
  match_callstack f1 m1 tm1 cs bound tbound ->
  inject_incr f1 f2 ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall sp ofs, Plt sp tbound -> Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b bound -> f2 b = f1 b) ->
  (forall b b' delta, f2 b = Some(b', delta) -> Plt b' tbound -> f1 b = Some(b', delta)) ->
  match_callstack f2 m2 tm2 cs bound tbound.
Proof.
  induction 1; intros.
  (* base case *)
  econstructor; eauto.
  inv H. constructor; intros; eauto.
  eapply IMAGE; eauto. eapply H6; eauto. xomega.
  (* inductive case *)
  assert (Ple lo hi) by (eapply me_low_high; eauto).
  econstructor; eauto.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto.
    intros. apply H3. xomega.
  eapply match_bounds_invariant; eauto.
    intros. eapply H1; eauto.
    exploit me_bounded; eauto. xomega.
  eapply padding_freeable_invariant; eauto.
    intros. apply H3. xomega.
  eapply IHmatch_callstack; eauto.
    intros. eapply H1; eauto. xomega.
    intros. eapply H2; eauto. xomega.
    intros. eapply H3; eauto. xomega.
    intros. eapply H4; eauto. xomega.
Qed.

Lemma match_callstack_incr_bound:
  forall f m tm cs bound tbound bound' tbound',
  match_callstack f m tm cs bound tbound ->
  Ple bound bound' -> Ple tbound tbound' ->
  match_callstack f m tm cs bound' tbound'.
Proof.
  intros. inv H.
  econstructor; eauto. xomega. xomega.
  constructor; auto. xomega. xomega.
Qed.

(** Assigning a temporary variable. *)

Lemma match_callstack_set_temp:
  forall f cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
  Val.inject f v tv ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  match_callstack f m tm (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H0. constructor; auto.
  eapply match_temps_assign; eauto.
Qed.

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the C#minor side)
  and simultaneously freeing the Cminor stack data block. *)

Lemma in_blocks_of_env:
  forall e id b sz,
  e!id = Some(b, sz) -> In (b, 0, sz) (blocks_of_env e).
Proof.
  unfold blocks_of_env; intros.
  change (b, 0, sz) with (block_of_binding (id, (b, sz))).
  apply List.in_map. apply PTree.elements_correct. auto.
Qed.

Lemma in_blocks_of_env_inv:
  forall b lo hi e,
  In (b, lo, hi) (blocks_of_env e) ->
  exists id, e!id = Some(b, hi) /\ lo = 0.
Proof.
  unfold blocks_of_env; intros.
  exploit list_in_map_inv; eauto. intros [[id [b' sz]] [A B]].
  unfold block_of_binding in A. inv A.
  exists id; intuition. apply PTree.elements_complete. auto.
Qed.

Lemma match_callstack_freelist:
  forall f cenv tf e le te sp lo hi cs m m' tm,
  Mem.inject f m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  exists tm',
  Mem.free tm sp 0 tf.(fn_stackspace) = Some tm'
  /\ match_callstack f m' tm' cs (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f m' tm'.
Proof.
  intros until tm; intros INJ FREELIST MCS. inv MCS. inv MENV.
  assert ({tm' | Mem.free tm sp 0 (fn_stackspace tf) = Some tm'}).
  apply Mem.range_perm_free.
  red; intros.
  exploit PERM; eauto. intros [A | A].
  auto.
  inv A. assert (Mem.range_perm m b 0 sz Cur Freeable).
  eapply free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
  replace ofs with ((ofs - delta) + delta) by Lia.lia.
  eapply Mem.perm_inject; eauto. apply H3. Lia.lia.
  destruct X as  [tm' FREE].
  exploit nextblock_freelist; eauto. intro NEXT.
  exploit Mem.nextblock_free; eauto. intro NEXT'.
  assert(R:match_callstack f m' tm' cs (Mem.nextblock m') (Mem.nextblock tm') /\ Mem.inject f m' tm').
  split;auto.
  rewrite NEXT; rewrite NEXT'.
  apply match_callstack_incr_bound with lo sp; try Lia.lia.
  apply match_callstack_invariant with f m tm; auto.
  intros. eapply perm_freelist; eauto.
  intros. eapply Mem.perm_free_1; eauto. left; unfold block; xomega. xomega. xomega.
  eapply Mem.free_inject; eauto.
  intros. exploit me_inv0; eauto. intros [id [sz A]].
  exists 0; exists sz; split.
  eapply in_blocks_of_env; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_max. eauto.
  destruct R as [MCS' MINJ'].
  exists tm'. Esimpl;auto.
Qed.

  
(** Preservation of [match_callstack] by external calls. *)

Lemma match_callstack_external_call:
  forall f1 f2 m1 m2 m1' m2',
  Mem.unchanged_on (loc_unmapped f1) m1 m2 ->
  Mem.unchanged_on (loc_out_of_reach f1 m1) m1' m2' ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  forall cs bound tbound,
  match_callstack f1 m1 m1' cs bound tbound ->
  Ple bound (Mem.nextblock m1) -> Ple tbound (Mem.nextblock m1') ->
  match_callstack f2 m2 m2' cs bound tbound.
Proof.
  intros until m2'.
  intros UNMAPPED OUTOFREACH INCR SEPARATED MAXPERMS.
  induction 1; intros.
(* base case *)
  apply mcs_nil with hi; auto.
  inv H. constructor; auto.
  intros.  case_eq (f1 b1).
  intros [b2' delta'] EQ. rewrite (INCR _ _ _ EQ) in H. inv H. eauto.
  intro EQ. exploit SEPARATED; eauto. intros [A B]. elim B. red. xomega.
(* inductive case *)
  constructor. auto. auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto.
  red in SEPARATED. intros. destruct (f1 b) as [[b' delta']|] eqn:?.
  exploit INCR; eauto. congruence.
  exploit SEPARATED; eauto. intros [A B]. elim B. red. xomega.
  intros. assert (Ple lo hi) by (eapply me_low_high; eauto).
  destruct (f1 b) as [[b' delta']|] eqn:?.
  apply INCR; auto.
  destruct (f2 b) as [[b' delta']|] eqn:?; auto.
  exploit SEPARATED; eauto. intros [A B]. elim A. red. xomega.
  eapply match_bounds_invariant; eauto.
  intros. eapply MAXPERMS; eauto. red. exploit me_bounded; eauto. xomega.
  (* padding-freeable *)
  red; intros.
  destruct (is_reachable_from_env_dec f1 e sp ofs).
  inv H3. right. apply is_reachable_intro with id b sz delta; auto.
  exploit PERM; eauto. intros [A|A]; try contradiction.
  left. eapply Mem.perm_unchanged_on; eauto.
  red; intros; red; intros. elim H3.
  exploit me_inv; eauto. intros [id [lv B]].
  exploit BOUND0; eauto. intros C.
  apply is_reachable_intro with id b0 lv delta; auto; Lia.lia.
  eauto with mem.
  (* induction *)
  eapply IHmatch_callstack; eauto. inv MENV; xomega. xomega.  xomega.  
Qed.

(** [match_callstack] and allocations *)

Lemma match_callstack_alloc_right:
  forall f m tm cs tf tm' sp le te cenv (PROMEM:~Plt sp (Genv.genv_next ge)),
  match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  Mem.inject f m tm ->
  match_temps f le te ->
  (forall id, cenv!id = None) ->
  match_callstack f m tm'
      (Frame cenv tf empty_env le te sp (Mem.nextblock m) (Mem.nextblock m) :: cs)
      (Mem.nextblock m) (Mem.nextblock tm').
Proof.
  intros.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  constructor.
  xomega.
  unfold block in *; xomega.
  auto.
  constructor; intros.
    rewrite H3. rewrite PTree.gempty. constructor.
    xomega.
    rewrite PTree.gempty in H4; discriminate.
    eelim Mem.fresh_block_alloc; eauto. eapply Mem.valid_block_inject_2; eauto.
    rewrite RES. change (Mem.valid_block tm tb). eapply Mem.valid_block_inject_2; eauto.
  red; intros. rewrite PTree.gempty in H4. discriminate.
  red; intros. left. eapply Mem.perm_alloc_2; eauto.
  eapply match_callstack_invariant with (tm1 := tm); eauto.
  rewrite RES; auto.
  intros. eapply Mem.perm_alloc_1; eauto.
  auto. 
Qed.

Lemma match_callstack_alloc_left:
  forall f1 m1 tm id cenv tf e le te sp lo cs sz m2 b f2 ofs (PROMEM:~Plt sp (Genv.genv_next ge)) ,
  match_callstack f1 m1 tm
    (Frame (PTree.remove id cenv) tf e le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_callstack f2 m2 tm
    (Frame cenv tf (PTree.set id (b, sz) e) le te sp lo (Mem.nextblock m2) :: cs)
    (Mem.nextblock m2) (Mem.nextblock tm).
Proof.
  intros. inv H.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  assert (LO: Ple lo (Mem.nextblock m1)) by (eapply me_low_high; eauto).
  constructor.
  xomega.
  auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_alloc; eauto.
  red; intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inversion H. subst b0 sz0 id0. eapply Mem.perm_alloc_3; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_alloc_4; eauto.
  exploit me_bounded; eauto. unfold block in *; xomega.
  red; intros. exploit PERM; eauto. intros [A|A]. auto. right.
  inv A. apply is_reachable_intro with id0 b0 sz0 delta; auto.
  rewrite PTree.gso. auto. congruence.
  eapply match_callstack_invariant with (m1 := m1); eauto.
  intros. eapply Mem.perm_alloc_4; eauto.
  unfold block in *; xomega.
  intros. apply H4. unfold block in *; xomega.
  intros. destruct (eq_block b0 b).
  subst b0. rewrite H3 in H. inv H. xomegaContradiction.
  rewrite H4 in H; auto.
  auto.
Qed.

(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of Csharpminor
  local variables as sub-blocks of the Cminor stack data.  This is the most difficult part of the proof. *)

Definition cenv_remove (cenv: compilenv) (vars: list (ident * Z)) : compilenv :=
  fold_right (fun id_lv ce => PTree.remove (fst id_lv) ce) cenv vars.

Remark cenv_remove_gso:
  forall id vars cenv,
  ~In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = PTree.get id cenv.
Proof.
  induction vars; simpl; intros.
  auto.
  rewrite PTree.gro. apply IHvars. intuition. intuition.
Qed.

Remark cenv_remove_gss:
  forall id vars cenv,
  In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = None.
Proof.
  induction vars; simpl; intros.
  contradiction.
  rewrite PTree.grspec. destruct (PTree.elt_eq id (fst a)). auto.
  destruct H. intuition. eauto.
Qed.

Definition cenv_compat (cenv: compilenv) (vars: list (ident * Z)) (tsz: Z) : Prop :=
  forall id sz,
  In (id, sz) vars ->
  exists ofs,
      PTree.get id cenv = Some ofs
   /\ Mem.inj_offset_aligned ofs sz
   /\ 0 <= ofs
   /\ ofs + Zmax 0 sz <= tsz.

Definition cenv_separated (cenv: compilenv) (vars: list (ident * Z)) : Prop :=
  forall id1 sz1 ofs1 id2 sz2 ofs2,
  In (id1, sz1) vars -> In (id2, sz2) vars ->
  PTree.get id1 cenv = Some ofs1 -> PTree.get id2 cenv = Some ofs2 ->
  id1 <> id2 ->
  ofs1 + sz1 <= ofs2 \/ ofs2 + sz2 <= ofs1.

Definition cenv_mem_separated (cenv: compilenv) (vars: list (ident * Z)) (f: meminj) (sp: block) (m: mem) : Prop :=
  forall id sz ofs b delta ofs' k p,
  In (id, sz) vars -> PTree.get id cenv = Some ofs ->
  f b = Some (sp, delta) ->
  Mem.perm m b ofs' k p ->
  ofs <= ofs' + delta < sz + ofs -> False.

Lemma match_callstack_alloc_variables_rec:
  forall tm sp tf cenv le te lo cs,
  Mem.valid_block tm sp ->
  fn_stackspace tf <= Ptrofs.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  alloc_variables e1 m1 vars e2 m2 ->
  forall f1 mu (AGMU:proper_mu ge tge f1 mu)(PROMEM:~ Plt sp (Genv.genv_next ge)),
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars f1 sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  match_callstack f1 m1 tm
    (Frame (cenv_remove cenv vars) tf e1 le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.inject f1 m1 tm ->
  exists f2,
    match_callstack f2 m2 tm
      (Frame cenv tf e2 le te sp lo (Mem.nextblock m2) :: cs)
      (Mem.nextblock m2) (Mem.nextblock tm)
  /\ Mem.inject f2 m2 tm /\ proper_mu ge tge f2 mu.
Proof.
  intros until cs; intros VALID REPRES STKSIZE STKPERMS.
  induction 1; intros f1 mu AGMU PROMEM NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ.
  (* base case *)
  simpl in MCS. exists f1; auto.
  (* inductive case *)
  simpl in NOREPET. inv NOREPET.
  exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.nextblock_alloc; eauto. intros NB.
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit Mem.alloc_left_mapped_inject.
    eexact MINJ.
    eexact H.
    eexact VALID.
    instantiate (1 := ofs). zify. Lia.lia.
    intros. exploit STKSIZE; eauto. Lia.lia.
    intros. apply STKPERMS. zify. Lia.lia.
    replace (sz - 0) with sz by Lia.lia. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. Lia.lia.
  intros [f2 [A [B [C D]]]].
  assert(E:proper_mu ge tge f2 mu).
  {
    inv AGMU.
    econstructor;eauto.
    unfold inject_incr in *;auto.
    unfold sep_inject in *;intros.
    destruct (peq b' (Mem.nextblock m)).
    Focus 2.
    apply D in n. rewrite n in H2. eauto.

    subst b'.
    rewrite H2 in C;inv C.
    unfold Bset.inj_to_meminj in H1.
    inv_eq.
    apply match_callstack_match_globalenvs in MCS as [? MCS].
    inv MCS.
    inv proper_mu_inject.
    inv inj_weak.
    apply inj_range' in Heqo as ?.
    
    inv proper_mu_ge_init_inj.
    rewrite mu_shared_tgt in H5.
    unfold Bset.belongsto in H5.
    contradiction.
  }
  exploit (IHalloc_variables f2); eauto.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b b1); intros P.
    subst b. rewrite C in H5; inv H5.
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    Lia.lia.
    eapply SEP2. apply in_cons; eauto. eauto.
    rewrite D in H5; eauto. eauto. auto.
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply match_callstack_alloc_left; eauto.
    rewrite cenv_remove_gso; auto.
    apply UNBOUND with sz; auto with coqlib.
Qed.

Lemma match_callstack_alloc_variables:
  forall tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te mu (AGMU:proper_mu ge tge f1 mu)(PROMEM:~ Plt sp (Genv.genv_next ge)),
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Ptrofs.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack f2 m2 tm2 (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2 /\ proper_mu ge tge f2 mu.
Proof.
  intros.
  eapply match_callstack_alloc_variables_rec; eauto.
  eapply Mem.valid_new_block; eauto.
  intros. eapply Mem.perm_alloc_3; eauto.
  intros. apply Mem.perm_implies with Freeable; auto with mem. eapply Mem.perm_alloc_2; eauto.
  red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto.
  intros. apply PTree.gempty.
  eapply match_callstack_alloc_right; eauto.
  intros. destruct (In_dec peq id (map fst vars)).
  apply cenv_remove_gss; auto.
  rewrite cenv_remove_gso; auto.
  destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto.
  eapply Mem.alloc_right_inject; eauto.
Qed.

(** Properties of the compilation environment produced by [build_compilenv] *)

Remark block_alignment_pos:
  forall sz, block_alignment sz > 0.
Proof.
  unfold block_alignment; intros.
  destruct (zlt sz 2). Lia.lia.
  destruct (zlt sz 4). Lia.lia.
  destruct (zlt sz 8); Lia.lia.
Qed.

Remark assign_variable_incr:
  forall id sz cenv stksz cenv' stksz',
  assign_variable (cenv, stksz) (id, sz) = (cenv', stksz') -> stksz <= stksz'.
Proof.
  simpl; intros. inv H.
  generalize (align_le stksz (block_alignment sz) (block_alignment_pos sz)).
  assert (0 <= Zmax 0 sz). apply Zmax_bound_l. Lia.lia.
  Lia.lia.
Qed.

Remark assign_variables_incr:
  forall vars cenv sz cenv' sz',
  assign_variables (cenv, sz) vars = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'.
  simpl; intros. inv H. Lia.lia.
Opaque assign_variable.
  destruct a as [id s]. simpl. intros.
  destruct (assign_variable (cenv, sz) (id, s)) as [cenv1 sz1] eqn:?.
  apply Zle_trans with sz1. eapply assign_variable_incr; eauto. eauto.
Transparent assign_variable.
Qed.

Remark inj_offset_aligned_block:
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) sz.
Proof.
  intros; red; intros.
  apply Z.divide_trans with (block_alignment sz).
  unfold align_chunk.  unfold block_alignment.
  generalize Zone_divide; intro.
  generalize Zdivide_refl; intro.
  assert (2 | 4). exists 2; auto.
  assert (2 | 8). exists 4; auto.
  assert (4 | 8). exists 2; auto.
  destruct (zlt sz 2).
  destruct chunk; simpl in *; auto; lia.
  destruct (zlt sz 4).
  destruct chunk; simpl in *; auto; lia.
  destruct (zlt sz 8).
  destruct chunk; simpl in *; auto; lia.
  destruct chunk; simpl; auto.
  apply align_divides. apply block_alignment_pos.
Qed.

Remark inj_offset_aligned_block':
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) (Zmax 0 sz).
Proof.
  intros.
  replace (block_alignment sz) with (block_alignment (Zmax 0 sz)).
  apply inj_offset_aligned_block.
  rewrite Zmax_spec. destruct (zlt sz 0); auto.
  transitivity 1. reflexivity. unfold block_alignment. rewrite zlt_true. auto. Lia.lia.
Qed.

Lemma assign_variable_sound:
  forall cenv1 sz1 id sz cenv2 sz2 vars,
  assign_variable (cenv1, sz1) (id, sz) = (cenv2, sz2) ->
  ~In id (map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ (id, sz) :: nil) sz2
  /\ cenv_separated cenv2 (vars ++ (id, sz) :: nil).
Proof.
  unfold assign_variable; intros until vars; intros ASV NOREPET POS COMPAT SEP.
  inv ASV.
  assert (LE: sz1 <= align sz1 (block_alignment sz)). apply align_le. apply block_alignment_pos.
  assert (EITHER: forall id' sz',
             In (id', sz') (vars ++ (id, sz) :: nil) ->
             In (id', sz') vars /\ id' <> id \/ (id', sz') = (id, sz)).
    intros. rewrite in_app in H. destruct H.
    left; split; auto. red; intros; subst id'. elim NOREPET.
    change id with (fst (id, sz')). apply in_map; auto.
    simpl in H. destruct H. auto. contradiction.
  split; red; intros.
  apply EITHER in H. destruct H as [[P Q] | P].
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  exists ofs.
  split. rewrite PTree.gso; auto.
  split. auto. split. auto. zify; Lia.lia.
  inv P. exists (align sz1 (block_alignment sz)).
  split. apply PTree.gss.
  split. apply inj_offset_aligned_block.
  split. Lia.lia.
  Lia.lia.
  apply EITHER in H; apply EITHER in H0.
  destruct H as [[P Q] | P]; destruct H0 as [[R S] | R].
  rewrite PTree.gso in *; auto. eapply SEP; eauto.
  inv R. rewrite PTree.gso in H1; auto. rewrite PTree.gss in H2; inv H2.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs1) by congruence. subst ofs.
  left. zify; Lia.lia.
  inv P. rewrite PTree.gso in H2; auto. rewrite PTree.gss in H1; inv H1.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs2) by congruence. subst ofs.
  right. zify; Lia.lia.
  congruence.
Qed.

Lemma assign_variables_sound:
  forall vars' cenv1 sz1 cenv2 sz2 vars,
  assign_variables (cenv1, sz1) vars' = (cenv2, sz2) ->
  list_norepet (map fst vars' ++ map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ vars') sz2 /\ cenv_separated cenv2 (vars ++ vars').
Proof.
  induction vars'; simpl; intros.
  rewrite app_nil_r. inv H; auto.
  destruct a as [id sz].
  simpl in H0. inv H0. rewrite in_app in H6.
  rewrite list_norepet_app in H7. destruct H7 as [P [Q R]].
  destruct (assign_variable (cenv1, sz1) (id, sz)) as [cenv' sz'] eqn:?.
  exploit assign_variable_sound.
    eauto.
    instantiate (1 := vars). tauto.
    auto. auto. auto.
  intros [A B].
  exploit IHvars'.
    eauto.
    instantiate (1 := vars ++ ((id, sz) :: nil)).
    rewrite list_norepet_app. split. auto.
    split. rewrite map_app. apply list_norepet_append_commut. simpl. constructor; auto.
    rewrite map_app. simpl. red; intros. rewrite in_app in H4. destruct H4.
    eauto. simpl in H4. destruct H4. subst y. red; intros; subst x. tauto. tauto.
    generalize (assign_variable_incr _ _ _ _ _ _ Heqp). Lia.lia.
    auto. auto.
  rewrite app_ass. auto.
Qed.

Remark permutation_norepet:
  forall (A: Type) (l l': list A), Permutation l l' -> list_norepet l -> list_norepet l'.
Proof.
  induction 1; intros.
  constructor.
  inv H0. constructor; auto. red; intros; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.
  inv H. simpl in H2. inv H3. constructor. simpl; intuition. constructor. intuition. auto.
  eauto.
Qed.

Lemma build_compilenv_sound:
  forall f cenv sz,
  build_compilenv f = (cenv, sz) ->
  list_norepet (map fst (Csharpminor.fn_vars f)) ->
  cenv_compat cenv (Csharpminor.fn_vars f) sz /\ cenv_separated cenv (Csharpminor.fn_vars f).
Proof.
  unfold build_compilenv; intros.
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  assert (cenv_compat cenv vars2 sz /\ cenv_separated cenv vars2).
    change vars2 with (nil ++ vars2).
    eapply assign_variables_sound.
    eexact H.
    simpl. rewrite app_nil_r. apply permutation_norepet with (map fst vars1); auto.
    apply Permutation_map. auto.
    Lia.lia.
    red; intros. contradiction.
    red; intros. contradiction.
  destruct H1 as [A B]. split.
  red; intros. apply A. apply Permutation_in with vars1; auto.
  red; intros. eapply B; eauto; apply Permutation_in with vars1; auto.
Qed.

Lemma assign_variables_domain:
  forall id vars cesz,
  (fst (assign_variables cesz vars))!id <> None ->
  (fst cesz)!id <> None \/ In id (map fst vars).
Proof.
  induction vars; simpl; intros.
  auto.
  exploit IHvars; eauto. unfold assign_variable. destruct a as [id1 sz1].
  destruct cesz as [cenv stksz]. simpl.
  rewrite PTree.gsspec. destruct (peq id id1). auto. tauto.
Qed.

Lemma build_compilenv_domain:
  forall f cenv sz id ofs,
  build_compilenv f = (cenv, sz) ->
  cenv!id = Some ofs -> In id (map fst (Csharpminor.fn_vars f)).
Proof.
  unfold build_compilenv; intros.
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  generalize (assign_variables_domain id vars2 (PTree.empty Z, 0)).
  rewrite H. simpl. intros. destruct H1. congruence.
  rewrite PTree.gempty in H1. congruence.
  apply Permutation_in with (map fst vars2); auto.
  apply Permutation_map. apply Permutation_sym; auto.
Qed.

(** Initialization of C#minor temporaries and Cminor local variables. *)

Lemma create_undef_temps_val:
  forall id v temps, (create_undef_temps temps)!id = Some v -> In id temps /\ v = Vundef.
Proof.
  induction temps; simpl; intros.
  rewrite PTree.gempty in H. congruence.
  rewrite PTree.gsspec in H. destruct (peq id a).
  split. auto. congruence.
  exploit IHtemps; eauto. tauto.
Qed.

Fixpoint set_params' (vl: list val) (il: list ident) (te: Cminor.env) : Cminor.env :=
  match il, vl with
  | i1 :: is, v1 :: vs => set_params' vs is (PTree.set i1 v1 te)
  | i1 :: is, nil => set_params' nil is (PTree.set i1 Vundef te)
  | _, _ => te
  end.

Lemma bind_parameters_agree_rec:
  forall f vars vals tvals le1 le2 te,
  bind_parameters vars vals le1 = Some le2 ->
  Val.inject_list f vals tvals ->
  match_temps f le1 te ->
  match_temps f le2 (set_params' tvals vars te).
Proof.
Opaque PTree.set.
  induction vars; simpl; intros.
  destruct vals; try discriminate. inv H. auto.
  destruct vals; try discriminate. inv H0.
  simpl. eapply IHvars; eauto.
  red; intros. rewrite PTree.gsspec in *. destruct (peq id a).
  inv H0. exists v'; auto.
  apply H1; auto.
Qed.

Lemma set_params'_outside:
  forall id il vl te, ~In id il -> (set_params' vl il te)!id = te!id.
Proof.
  induction il; simpl; intros. auto.
  destruct vl; rewrite IHil.
  apply PTree.gso. intuition. intuition.
  apply PTree.gso. intuition. intuition.
Qed.

Lemma set_params'_inside:
  forall id il vl te1 te2,
  In id il ->
  (set_params' vl il te1)!id = (set_params' vl il te2)!id.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct vl; destruct (List.in_dec peq id il); auto;
  repeat rewrite set_params'_outside; auto;
  assert (a = id) by intuition; subst a; repeat rewrite PTree.gss; auto.
Qed.

Lemma set_params_set_params':
  forall il vl id,
  list_norepet il ->
  (set_params vl il)!id = (set_params' vl il (PTree.empty val))!id.
Proof.
  induction il; simpl; intros.
  auto.
  inv H. destruct vl.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
Qed.

Lemma set_locals_outside:
  forall e id il,
  ~In id il -> (set_locals il e)!id = e!id.
Proof.
  induction il; simpl; intros.
  auto.
  rewrite PTree.gso. apply IHil. tauto. intuition.
Qed.

Lemma set_locals_inside:
  forall e id il,
  In id il -> (set_locals il e)!id = Some Vundef.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss.
  rewrite PTree.gsspec. destruct (peq id a). auto. auto.
Qed.

Lemma set_locals_set_params':
  forall vars vals params id,
  list_norepet params ->
  list_disjoint params vars ->
  (set_locals vars (set_params vals params)) ! id =
  (set_params' vals params (set_locals vars (PTree.empty val))) ! id.
Proof.
  intros. destruct (in_dec peq id vars).
  assert (~In id params). apply list_disjoint_notin with vars; auto. apply list_disjoint_sym; auto.
  rewrite set_locals_inside; auto. rewrite set_params'_outside; auto. rewrite set_locals_inside; auto.
  rewrite set_locals_outside; auto. rewrite set_params_set_params'; auto.
  destruct (in_dec peq id params).
  apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto.
  rewrite set_locals_outside; auto.
Qed.

Lemma bind_parameters_agree:
  forall f params temps vals tvals le,
  bind_parameters params vals (create_undef_temps temps) = Some le ->
  Val.inject_list f vals tvals ->
  list_norepet params ->
  list_disjoint params temps ->
  match_temps f le (set_locals temps (set_params tvals params)).
Proof.
  intros; red; intros.
  exploit bind_parameters_agree_rec; eauto.
  instantiate (1 := set_locals temps (PTree.empty val)).
  red; intros. exploit create_undef_temps_val; eauto. intros [A B]. subst v0.
  exists Vundef; split. apply set_locals_inside; auto. auto.
  intros [v' [A B]]. exists v'; split; auto.
  rewrite <- A. apply set_locals_set_params'; auto.
Qed.

(** The main result in this section. *)

Theorem match_callstack_function_entry:
  forall fn cenv tf m e m' tm tm' sp f cs args targs le mu (AGMU:proper_mu ge tge f mu)(PROMEM:~Plt sp (Genv.genv_next ge)),
  build_compilenv fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Ptrofs.max_unsigned ->
  list_norepet (map fst (Csharpminor.fn_vars fn)) ->
  list_norepet (Csharpminor.fn_params fn) ->
  list_disjoint (Csharpminor.fn_params fn) (Csharpminor.fn_temps fn) ->
  alloc_variables Csharpminor.empty_env m (Csharpminor.fn_vars fn) e m' ->
  bind_parameters (Csharpminor.fn_params fn) args (create_undef_temps fn.(fn_temps)) = Some le ->
  Val.inject_list f args targs ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let te := set_locals (Csharpminor.fn_temps fn) (set_params targs (Csharpminor.fn_params fn)) in
  exists f',
     match_callstack f' m' tm'
                     (Frame cenv tf e le te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f' m' tm' /\ proper_mu ge tge f' mu.
Proof.
  intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply match_callstack_alloc_variables; eauto.
  intros. eapply build_compilenv_domain; eauto.
  eapply bind_parameters_agree; eauto.
Qed.

(** * Compatibility of evaluation functions with respect to memory injections. *)

Remark val_inject_val_of_bool:
  forall f b, Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; constructor.
Qed.

Remark val_inject_val_of_optbool:
  forall f ob, Val.inject f (Val.of_optbool ob) (Val.of_optbool ob).
Proof.
  intros; destruct ob; simpl. destruct b; constructor. constructor.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ Val.inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ Val.inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vlong ?x) _ ] =>
      exists (Vlong x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.

(** Compatibility of [eval_unop] with respect to [Val.inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  Val.inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct op; simpl; intros.
  all: try(inv H;inv H0;simpl in *;try TrivialExists;unfold option_map in *;inv_eq;inv H2; TrivialExists;try constructor; fail).
Qed.

(** Compatibility of [eval_binop] with respect to [Val.inject]. *)

Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  Mem.inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct op; simpl; intros; inv H.
  all: try(TrivialExists;inv H0;inv H1;constructor;fail).
- TrivialExists. apply Val.add_inject; auto.
- TrivialExists. apply Val.sub_inject; auto.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H4. TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H4. TrivialExists.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H4. TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H4. TrivialExists.
- TrivialExists; inv H0; inv H1; simpl; auto.

  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- (* cmp *)
  TrivialExists. inv H0; inv H1; simpl in *; try discriminate; auto.
  inv H4. eexists; split; [eauto|]. apply val_inject_val_of_bool.
- (* cmpu *)
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  replace (Val.cmpu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  simpl in *. TrivialExists. inv H4. apply val_inject_val_of_bool.
  symmetry. eapply Val.cmpu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  discriminate.
- (* cmpf *)
  inv H0; inv H1; simpl in *; try discriminate; auto.
  inv H4; TrivialExists. apply val_inject_val_of_bool.
- (* cmpfs *)
  inv H0; inv H1; simpl in *; try discriminate; auto.
  inv H4; TrivialExists. apply val_inject_val_of_bool.
- (* cmpl *)
  unfold Val.cmpl in *. inv H0; inv H1; simpl in H4; inv H4.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
- (* cmplu *)
  unfold Val.cmplu in *.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  simpl in H4; inv H4.
  replace (Val.cmplu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
  symmetry. eapply Val.cmplu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  discriminate.
Qed.


(** * Correctness of Cminor construction functions *)

(** Correctness of the variable accessor [var_addr] *)

Lemma var_addr_correct:
  forall cenv id f tf e le te sp lo hi m cs tm b,
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  eval_var_addr ge e id b ->
  exists tv,
     eval_expr tge (Vptr sp Ptrofs.zero) te tm (var_addr cenv id) tv
  /\ Val.inject f (Vptr b Ptrofs.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f sp e!id cenv!id).
    inv H. inv MENV. auto.
  inv H1; inv H0; try congruence.
  (* local *)
  exists (Vptr sp (Ptrofs.repr ofs)); split.
  constructor. simpl. rewrite Ptrofs.add_zero_l; auto.
  congruence.
  (* global *)
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  exists (Vptr b Ptrofs.zero); split.
  constructor. simpl. unfold Genv.symbol_address. 
  rewrite symbols_preserved. rewrite H2. auto.
  econstructor; eauto.
Qed.

(** * Semantic preservation for the translation *)

(** The proof of semantic preservation uses simulation diagrams of the
  following form:
<<
       e, m1, s ----------------- sp, te1, tm1, ts
          |                                |
         t|                                |t
          v                                v
       e, m2, out --------------- sp, te2, tm2, tout
>>
  where [ts] is the Cminor statement obtained by translating the
  C#minor statement [s].  The left vertical arrow is an execution
  of a C#minor statement.  The right vertical arrow is an execution
  of a Cminor statement.  The precondition (top vertical bar)
  includes a [mem_inject] relation between the memory states [m1] and [tm1],
  and a [match_callstack] relation for any callstack having
  [e], [te1], [sp] as top frame.  The postcondition (bottom vertical bar)
  is the existence of a memory injection [f2] that extends the injection
  [f1] we started with, preserves the [match_callstack] relation for
  the transformed callstack at the final state, and validates a
  [outcome_inject] relation between the outcomes [out] and [tout].
*)

(** ** Semantic preservation for expressions *)

Remark bool_of_val_inject:
  forall f v tv b,
  Val.bool_of_val v b -> Val.inject f v tv -> Val.bool_of_val tv b.
Proof.
  intros. inv H0; inv H; constructor; auto.
Qed.

Lemma transl_constant_correct:
  forall f sp cst v,
  Csharpminor.eval_constant cst = Some v ->
  exists tv,
     eval_constant tge sp (transl_constant cst) = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct cst; simpl; intros; inv H.
  exists (Vint i); auto.
  exists (Vfloat f0); auto.
  exists (Vsingle f0); auto.
  exists (Vlong i); auto.
Qed.
Lemma transl_expr_correct:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_expr ge e le m a v ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tv,
     eval_expr tge (Vptr sp Ptrofs.zero) te tm ta tv
  /\ Val.inject f v tv.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  (* Etempvar *)
  inv MATCH. exploit MTMP; eauto. intros [tv [A B]].
  exists tv; split. constructor; auto. auto.
  (* Eaddrof *)
  eapply var_addr_correct; eauto.
  (* Econst *)
  exploit transl_constant_correct; eauto. intros [tv [A B]].
  exists tv; split; eauto. constructor; eauto.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit eval_unop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split; auto. econstructor; eauto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit Mem.loadv_inject; eauto. intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto. auto.
Qed.


Lemma AGMU_Tgt_plt:
  forall b mu (AGMU:proper_mu ge tge inject_id mu)(S_EQ:Genv.genv_next ge = Genv.genv_next tge),
    Bset.belongsto (Injections.SharedTgt mu) b ->
    Plt b (Genv.genv_next ge).
Proof.
  intros.
  inv AGMU. inv proper_mu_ge_init_inj.
  rewrite mu_shared_tgt in H.
  unfold Bset.belongsto in H.
  rewrite S_EQ;auto.
Qed.


Lemma store_fp_match:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
                            (Frame cenv tf e le te sp lo hi :: cs)
                            (Mem.nextblock m) (Mem.nextblock tm)),
    forall b ofs b' ofs' chunk,
      Val.inject f (Vptr b ofs)(Vptr b' ofs')->
      fp_match (Genv.genv_next tge) (FMemOpFP.store_fp chunk b (Ptrofs.unsigned ofs))(FMemOpFP.store_fp chunk b' (Ptrofs.unsigned ofs')).
Proof.
  rewrite <- S_EQ.
  unfold fp_match,FMemOpFP.store_fp,in_fps;simpl;intros.
  Esimpl;intros;inv H1.
  unfold FMemOpFP.range_locset,Locs.belongsto in *.
  destruct eq_block;try discriminate;subst b0.
  apply match_callstack_match_globalenvs in MATCH as [? MATCH].
  inv MATCH. 
  inv H. apply IMAGE in H5 as R;auto;subst.
  exploit DOMAIN;try apply H0.
  intro R';rewrite H5 in R';inv R'.
  destruct eq_block;try contradiction.
  rewrite Ptrofs.add_zero in *. auto.
Qed.
Lemma storev_fp_match:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
                            (Frame cenv tf e le te sp lo hi :: cs)
                            (Mem.nextblock m) (Mem.nextblock tm)),
    forall b ofs b' ofs' chunk,
      Val.inject f (Vptr b ofs)(Vptr b' ofs')->
      fp_match (Genv.genv_next tge) (FMemOpFP.storev_fp chunk (Vptr b ofs))(FMemOpFP.storev_fp chunk (Vptr b' ofs')).
Proof. unfold FMemOpFP.storev_fp. apply store_fp_match. Qed.

Lemma transl_expr_fp_correct:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
                            (Frame cenv tf e le te sp lo hi :: cs)
                            (Mem.nextblock m) (Mem.nextblock tm)),
  forall a fp,
    Csharpminor_local.eval_expr_fp ge e le m a fp ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tfp,
    eval_expr_fp tge (Vptr sp Ptrofs.zero) te tm ta tfp /\
    fp_match (Genv.genv_next tge) fp tfp.
Proof.
  unfold fp_match.
  induction 3;intros.
  monadInv TR.
  Esimpl;eauto. econstructor;eauto.
  intros. apply in_fps_emp. 
  {
    exists empfp. split.
    monadInv TR.
    eapply var_addr_correct in H as ?;eauto;Hsimpl.
    unfold var_addr in *.
    destruct (cenv ! id) eqn:?;inv H0;econstructor;eauto.
    intros. apply in_fps_emp.
  }
  {
    exists empfp. split.
    monadInv TR.
    eapply transl_constant_correct in H;eauto;Hsimpl.
    econstructor;eauto.
    intros. apply in_fps_emp.
    Unshelve. auto.
  }
  {
    monadInv TR.
    eapply IHeval_expr_fp in EQ as ?;eauto.
    Hsimpl;Esimpl;eauto.
    eapply transl_expr_correct in H as ?;eauto;Hsimpl.
    eapply eval_unop_compat in H1 as ?;eauto;Hsimpl.
    econstructor;eauto.
  }
  {
    monadInv TR.
    eapply IHeval_expr_fp1 in EQ as ?;eauto.
    eapply IHeval_expr_fp2 in EQ1 as ?;eauto;Hsimpl.
    eapply transl_expr_correct in H as ?;eauto.
    eapply transl_expr_correct in H1 as ?;eauto;Hsimpl.
    eapply eval_binop_compat in H3 as ?;eauto;Hsimpl.
    enough(exists tfp', eval_binop_fp op x4 x3 tm = Some tfp' /\
                   forall b ofs,
                     Plt b (Genv.genv_next ge)->
                     in_fps b ofs fp3 tfp').
    {
      Hsimpl.
      Esimpl.
      econstructor;eauto.
      intros.
      specialize (H8 _ ofs H17).
      specialize (H7 _ ofs H17). rewrite<- S_EQ in H17.
      specialize (H16 _ ofs H17).
      apply in_fps_union;try apply in_fps_union;auto.
    }
    
    unfold eval_binop,eval_binop_fp, Cminor_op_footprint.eval_binop_fp in *.
    destruct op eqn:?;inv H4.
    all: try(exists empfp;split;[reflexivity|intros;apply in_fps_emp];fail).
      
    all: try(inv H11;inv H12;try discriminate;inv_eq;exists empfp;split;[reflexivity|intros;apply in_fps_emp]).

    eexists;split;eauto.
    apply match_callstack_match_globalenvs in MATCH as MATCHG.
    destruct MATCHG. inv H4.
    rewrite S_EQ in IMAGE,DOMAIN.
    intros.
    eapply cmpu_fp_infps;eauto.
    rewrite S_EQ in H4;auto.
  }
  {
    monadInv TR.
    eapply transl_expr_correct in H as ?;eauto.
    Hsimpl.
    eapply Mem.loadv_inject in H1 as ?;eauto.
    Hsimpl.
    specialize (IHeval_expr_fp _ EQ).
    Hsimpl.
    eexists;split.
    econstructor;eauto.
    intros.
    apply match_callstack_match_globalenvs in MATCH as MATCHG.
    destruct MATCHG as [? MATCHG].
    inv MATCHG.
    apply in_fps_union;auto.
    
    unfold Mem.loadv in H1.
    destruct v1 eqn:?;inv H1.
    inv H3.
    unfold FMemOpFP.loadv_fp in *.
    unfold FMemOpFP.load_fp in *.
    unfold in_fps;simpl;Esimpl;intro R;inv R.
    unfold FMemOpFP.range_locset in *.
    destruct eq_block;try discriminate.
    subst b2.
    eapply IMAGE in H11 as ?;eauto;subst .
    exploit DOMAIN;eauto;try rewrite S_EQ;eauto;intro R;rewrite H11 in R;inv R.
    rewrite Ptrofs.add_zero in *.
    unfold Locs.belongsto.
    destruct eq_block;try contradiction.
    auto.
    congruence.
  }
Qed.

Lemma transl_exprlist_correct:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_exprlist ge e le m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge (Vptr sp Ptrofs.zero) te tm ta tv
  /\ Val.inject_list f v tv.
Proof.
  induction 3; intros; monadInv TR.
  exists (@nil val); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.
Lemma transl_exprlist_fp_correct:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
                            (Frame cenv tf e le te sp lo hi :: cs)
                            (Mem.nextblock m) (Mem.nextblock tm)),
  forall a fp,
    Csharpminor_local.eval_exprlist_fp ge e le m a fp ->
    forall v,
      Csharpminor.eval_exprlist ge e le m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tfp,
    eval_exprlist_fp tge (Vptr sp Ptrofs.zero) te tm ta tfp /\
    fp_match (Genv.genv_next tge) fp tfp.
Proof.
  unfold fp_match.
  induction 3;intros;monadInv TR.
  eexists. split. econstructor.
  intros. apply in_fps_emp. 
  exploit transl_expr_fp_correct;eauto. intro. Hsimpl.
  inv H2.
  exploit IHeval_exprlist_fp;eauto. intro. Hsimpl.
  eapply transl_expr_correct in H6;eauto.
  eapply transl_exprlist_correct in H8;eauto.
  Hsimpl.
  eexists;split. econstructor;eauto.
  intros.
  apply in_fps_union;auto.
Qed.
Lemma fp_match_FPMatch':
  forall fp tfp mu f hi
    (H:fp_match (Genv.genv_next tge) fp tfp) 
    (AGMU:proper_mu ge tge f mu)
    (MGE:match_globalenvs f hi),
    Injections.FPMatch' mu fp tfp.
Proof.
  unfold fp_match;intros; inv AGMU;inv proper_mu_ge_init_inj;inv MGE; constructor;constructor;intros;pose proof H0 as R;rewrite mu_shared_tgt in H0;unfold Bset.belongsto in H0;try eapply H in H0 as ?;eauto;destruct H2 as (?&?&?&?);unfold Bset.inject_block; [unfold FP.ge_cmps|unfold FP.ge_reads|unfold FP.ge_writes|unfold FP.ge_frees]; apply proper_mu_inject in R as [? R];exploit proper_mu_inject_incr;unfold Bset.inj_to_meminj;try rewrite R;eauto;intro R2;apply IMAGE in R2;auto; subst;try congruence;  eexists;split;eauto; apply belongsto_union;left;eauto;rewrite S_EQ;auto.
Qed.    
(** ** Semantic preservation for statements and functions *)

Inductive match_cont: Csharpminor.cont -> Cminor.cont -> compilenv -> exit_env -> callstack -> Prop :=
  | match_Kstop: forall cenv xenv,
      match_cont Csharpminor.Kstop Kstop cenv xenv nil
  | match_Kseq: forall s k ts tk cenv xenv cs,
      transl_stmt cenv xenv s = OK ts ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq s k) (Kseq ts tk) cenv xenv cs
  | match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
      transl_stmt cenv xenv s1 = OK ts1 ->
      match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq (Csharpminor.Sseq s1 s2) k)
                 (Kseq ts1 tk) cenv xenv cs
  | match_Kblock: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kblock k) (Kblock tk) cenv (true :: xenv) cs
  | match_Kblock2: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont k (Kblock tk) cenv (false :: xenv) cs
  | match_Kcall: forall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv',
      transl_funbody cenv sz fn = OK tfn ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kcall optid fn e le k)
                 (Kcall optid tfn (Vptr sp Ptrofs.zero) te tk)
                 cenv' nil
                 (Frame cenv tfn e le te sp lo hi :: cs).

Inductive match_states: meminj->Csharpminor_local.core*mem -> Cminor_local.core*mem -> Prop :=
  | match_state:
      forall fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (NGE: ~ Plt sp (Genv.genv_next ge))
      (MK: match_cont k tk cenv xenv cs),
      match_states f (Csharpminor_local.Core_State fn s k e le, m)
                   (Core_State tfn ts tk (Vptr sp Ptrofs.zero) te, tm)
  | match_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (NGE: ~ Plt sp (Genv.genv_next ge))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs),
      match_states f (Csharpminor_local.Core_State fn (Csharpminor.Sseq s1 s2) k e le, m)
                   (Core_State tfn ts1 tk (Vptr sp Ptrofs.zero) te, tm)
  | match_callstate:
      forall fd args k m tfd targs tk tm f cs cenv
      (TR: transl_fundef fd = OK tfd)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: Val.inject_list f args targs),
      match_states f (Csharpminor_local.Core_Callstate fd args k,m)
                   (Core_Callstate tfd targs tk,tm)
  | match_returnstate:
      forall v k m tv tk tm f cs cenv
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: Val.inject f v tv),
      match_states f (Csharpminor_local.Core_Returnstate v k,m)
                   (Core_Returnstate tv tk,tm).

Remark val_inject_function_pointer:
  forall bound v fd f tv,
  Genv.find_funct ge v = Some fd ->
  match_globalenvs f bound ->
  Val.inject f v tv ->
  tv = v.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H.
  assert (f b = Some(b, 0)). inv H0. apply DOMAIN. eapply FUNCTIONS; eauto.
  inv H1. rewrite H2 in H5; inv H5. reflexivity.
Qed.

Lemma match_call_cont:
  forall k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  match_cont (Csharpminor.call_cont k) (call_cont tk) cenv nil cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma match_is_call_cont:
  forall tfn te sp tm k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    star (step tge) (Core_State tfn Sskip tk sp te) tm
               empfp (Core_State tfn Sskip tk' sp te) tm
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
Proof.
  induction 1; simpl; intros; try contradiction.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
  exploit IHmatch_cont; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply star_left; eauto. constructor. traceEq. auto.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
Qed.

Fixpoint seq_left_depth (s: Csharpminor.stmt) : nat :=
  match s with
  | Csharpminor.Sseq s1 s2 => S (seq_left_depth s1)
  | _ => O
  end.

Definition measure (S: Csharpminor_local.core) : nat :=
  match S with
  | Csharpminor_local.Core_State fn s k e le => seq_left_depth s
  | _ => O
  end.

Definition inj_mu (f:meminj)(mu:Injections.Mu):Prop:=
  forall b,
    Plt b (Genv.genv_next ge) ->
    f b = Bset.inj_to_meminj (Injections.inj mu) b.

Definition MS i mu fp fp' cm cm' :Prop:= exists f,
  match_states f cm cm' /\
  Injections.FPMatch' mu fp fp' /\
  let (c, m) := cm in
  let (c', m') := cm' in
  measure c = i /\
  (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
  (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
  (proper_mu ge tge f mu) /\
  (MemClosures_local.unmapped_closed mu m m').

(** Properties of [switch] compilation *)

Inductive lbl_stmt_tail: lbl_stmt -> nat -> lbl_stmt -> Prop :=
  | lstail_O: forall sl,
      lbl_stmt_tail sl O sl
  | lstail_S: forall c s sl n sl',
      lbl_stmt_tail sl n sl' ->
      lbl_stmt_tail (LScons c s sl) (S n) sl'.

Lemma switch_table_default:
  forall sl base,
  exists n,
     lbl_stmt_tail sl n (select_switch_default sl)
  /\ snd (switch_table sl base) = (n + base)%nat.
Proof.
  induction sl; simpl; intros.
- exists O; split. constructor. Lia.lia.
- destruct o.
  + destruct (IHsl (S base)) as (n & P & Q). exists (S n); split.
    constructor; auto.
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. Lia.lia.
  + exists O; split. constructor.
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. auto.
Qed.

Lemma switch_table_case:
  forall i sl base dfl,
  match select_switch_case i sl with
  | None =>
      switch_target i dfl (fst (switch_table sl base)) = dfl
  | Some sl' =>
      exists n,
         lbl_stmt_tail sl n sl'
      /\ switch_target i dfl (fst (switch_table sl base)) = (n + base)%nat
  end.
Proof.
  induction sl; simpl; intros.
- auto.
- destruct (switch_table sl (S base)) as [tbl1 dfl1] eqn:ST.
  destruct o; simpl.
  rewrite dec_eq_sym. destruct (zeq i z).
  exists O; split; auto. constructor.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. Lia.lia.
  auto.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. Lia.lia.
  auto.
Qed.

Lemma switch_table_select:
  forall i sl,
  lbl_stmt_tail sl
                (switch_target i (snd (switch_table sl O)) (fst (switch_table sl O)))
                (select_switch i sl).
Proof.
  unfold select_switch; intros.
  generalize (switch_table_case i sl O (snd (switch_table sl O))).
  destruct (select_switch_case i sl) as [sl'|].
  intros (n & P & Q). replace (n + O)%nat with n in Q by Lia.lia. congruence.
  intros E; rewrite E.
  destruct (switch_table_default sl O) as (n & P & Q).
  replace (n + O)%nat with n in Q by Lia.lia. congruence.
Qed.

Inductive transl_lblstmt_cont(cenv: compilenv) (xenv: exit_env): lbl_stmt -> cont -> cont -> Prop :=
  | tlsc_default: forall k,
      transl_lblstmt_cont cenv xenv LSnil k (Kblock (Kseq Sskip k))
  | tlsc_case: forall i s ls k ts k',
      transl_stmt cenv (switch_env (LScons i s ls) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv ls k k' ->
      transl_lblstmt_cont cenv xenv (LScons i s ls) k (Kblock (Kseq ts k')).

Lemma switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall f sp e m,
      plus (step tge) (Core_State f s k sp e) m empfp (Core_State f body k' sp e)m).
Proof.
  induction ls; intros.
- monadInv H. econstructor; split.
  econstructor.
  intros. eapply plus_two. constructor. constructor. auto.
- monadInv H.
  exploit IHls; eauto. intros [k' [A B]].
  econstructor; split.
  econstructor; eauto.
  intros. eapply plus_star_trans. eauto.
  eapply star_left. constructor. apply star_one. constructor.
  reflexivity. traceEq.
Qed.

Lemma switch_ascent:
  forall f sp e m cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall k k1,
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  star (step tge) (Core_State f (Sexit n) k1 sp e) m
             empfp (Core_State f (Sexit O) k2 sp e) m
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction 1; intros.
- exists k1; split; auto. apply star_refl.
- inv H0. exploit IHlbl_stmt_tail; eauto. intros (k2 & P & Q).
  exists k2; split; auto.
  eapply star_left. constructor. eapply star_left. constructor. eexact P.
  eauto. auto.
Qed.

Lemma switch_match_cont:
  forall cenv xenv k cs tk ls tk',
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk' ->
  match_cont (Csharpminor.Kseq (seq_of_lbl_stmt ls) k) tk' cenv (false :: switch_env ls xenv) cs.
Proof.
  induction ls; intros; simpl.
  inv H0. apply match_Kblock2. econstructor; eauto.
  inv H0. apply match_Kblock2. eapply match_Kseq2. auto. eauto.
Qed.

Lemma switch_match_states:
  forall fn k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz ls body tk'
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject f m tm)
    (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S,
  plus (step tge) (Core_State tfn (Sexit O) tk' (Vptr sp Ptrofs.zero) te) tm empfp S tm /\ match_states f (Csharpminor_local.Core_State fn (seq_of_lbl_stmt ls) k e le, m) (S,tm).
Proof.
  intros. inv TK.
  - econstructor; split. eapply plus_two. constructor. constructor. auto.
    eapply match_state; eauto.
    inv MCS. auto.
  - econstructor; split. eapply plus_left. constructor. apply star_one. constructor. auto.
    simpl. eapply match_state_seq; eauto.
    inv MCS. auto.
    simpl. eapply switch_match_cont; eauto.
Qed.

Lemma transl_lblstmt_suffix:
  forall cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall body ts, transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  exists body', exists ts', transl_lblstmt cenv (switch_env ls' xenv) ls' body' = OK ts'.
Proof.
  induction 1; intros.
- exists body, ts; auto.
- monadInv H0. eauto.
Qed.

(** Commutation between [find_label] and compilation *)

Section FIND_LABEL.

Variable lbl: label.
Variable cenv: compilenv.
Variable cs: callstack.

Lemma transl_lblstmt_find_label_context:
  forall xenv ls body ts tk1 tk2 ts' tk',
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  transl_lblstmt_cont cenv xenv ls tk1 tk2 ->
  find_label lbl body tk2 = Some (ts', tk') ->
  find_label lbl ts tk1 = Some (ts', tk').
Proof.
  induction ls; intros.
- monadInv H. inv H0. simpl. rewrite H1. auto.
- monadInv H. inv H0. simpl in H6. eapply IHls; eauto.
  replace x with ts0 by congruence. simpl. rewrite H1. auto.
Qed.

Lemma transl_find_label:
  forall s k xenv ts tk,
  transl_stmt cenv xenv s = OK ts ->
  match_cont k tk cenv xenv cs ->
  match Csharpminor.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end

with transl_lblstmt_find_label:
  forall ls xenv body k ts tk tk1,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk1 ->
  find_label lbl body tk1 = None ->
  match Csharpminor.find_label_ls lbl ls k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end.
Proof.
  intros. destruct s; try (monadInv H); simpl; auto.
  (* seq *)
  exploit (transl_find_label s1). eauto. eapply match_Kseq. eexact EQ1. eauto.
  destruct (Csharpminor.find_label lbl s1 (Csharpminor.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.
  (* ifthenelse *)
  exploit (transl_find_label s1). eauto. eauto.
  destruct (Csharpminor.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.
  (* loop *)
  apply transl_find_label with xenv. auto. econstructor; eauto. simpl. rewrite EQ; auto.
  (* block *)
  apply transl_find_label with (true :: xenv). auto. constructor; auto.
  (* switch *)
  simpl in H. destruct (switch_table l O) as [tbl dfl]. monadInv H.
  exploit switch_descent; eauto. intros [k' [A B]].
  eapply transl_lblstmt_find_label. eauto. eauto. eauto. reflexivity.
  (* return *)
  destruct o; monadInv H; auto.
  (* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.
  apply transl_find_label with xenv; auto.

  intros. destruct ls; monadInv H; simpl.
  (* nil *)
  inv H1. rewrite H2. auto.
  (* cons *)
  inv H1. simpl in H7.
  exploit (transl_find_label s). eauto. eapply switch_match_cont; eauto.
  destruct (Csharpminor.find_label lbl s (Csharpminor.Kseq (seq_of_lbl_stmt ls) k)) as [[s' k''] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'; intuition.
  eapply transl_lblstmt_find_label_context; eauto.
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
  intro. eapply transl_lblstmt_find_label. eauto. auto. eauto.
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
Qed.

End FIND_LABEL.

Lemma transl_find_label_body:
  forall cenv xenv size f tf k tk cs lbl s' k',
  transl_funbody cenv size f = OK tf ->
  match_cont k tk cenv xenv cs ->
  Csharpminor.find_label lbl f.(Csharpminor.fn_body) (Csharpminor.call_cont k) = Some (s', k') ->
  exists ts', exists tk', exists xenv',
     find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
  /\ transl_stmt cenv xenv' s' = OK ts'
  /\ match_cont k' tk' cenv xenv' cs.
Proof.
  intros. monadInv H. simpl.
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0.
  instantiate (1 := lbl). rewrite H1. auto.
Qed.

Ltac resolvfp:=
  match goal with
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: fp_match _ ?fp1 ?fp2, H2: proper_mu _ _ _ _ ,H3: match_callstack _ _ _ _ _ _|- _ =>
    apply match_callstack_match_globalenvs in H3 as ?;Hsimpl;
    exploit fp_match_FPMatch';try apply H;try apply H2;eauto;intro;clear H; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; auto; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) ?fp1' => 
    eapply Injections.fp_match_union_S'; auto; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union ?fp1 _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union (FP.union ?fp1 _) _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union (FP.union ?fp1' _) _) (FP.union (FP.union ?fp1 _) _)=> 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp1 ?fp') =>
    rewrite FP.union_comm_eq; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp' _) =>
    apply FP.subset_union_subset; auto
  | |- Injections.FPMatch' _ _ empfp => apply Injections.fp_match_emp'
  | H: FP.subset ?fp1 ?fp2 |- Injections.FPMatch' _ ?fp2 ?fp1 =>
    apply Injections.fp_match_subset_T' with fp2; try exact H; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) ?fp2 =>
    apply Injections.fp_match_union_S'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union ?fp2 _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union'; resolvfp                                          
  | H: (forall b, Bset.belongsto (FP.blocks ?fp2) _ -> ~ Injections.SharedTgt ?mu _)
    |- Injections.FPMatch' _ _ ?fp2 =>
    apply Injections.fp_match_local_block; auto                                          
  | |- FP.subset ?fp ?fp => apply FP.subset_refl
  | H: fp_inject _ ?fp ?fp', H': proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp' =>
    eapply fp_inject_fp_match; inv H'; eauto
  | H: fp_inject inject_id ?fp ?fp'|- FP.subset ?fp' ?fp =>
    apply fp_inject_id_fp_subset
  | H: proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp => inv H; eapply fp_match_id; eauto
  | _ => idtac
  end.

Ltac eresolvfp:= resolvfp; eauto.

Ltac resvalid:=
  match goal with
  (** valid blocks *)
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.free ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_free_1; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.alloc ?m1 _ _ = (?m2,_)
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_alloc; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.store _ ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.store_valid_block_1; eauto
  (** Mem inv *)
  | H1: Mem.store _ ?m1 _ _ _ = Some ?m2,
        H2: Mem.store _ ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.store_val_inject_unmapped_closed_preserved;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.free ?m1 _ _ _ = Some ?m2,
        H2: Mem.free ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.alloc ?m1 _ _ = (?m2, _),
        H2: Mem.alloc ?m1' _ _ = (?m2', _),
            H3: proper_mu _ _ _ _
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto;
      try (eapply Mem.alloc_unchanged_on; eauto; fail)
  | _ => idtac
  end.
Ltac invMS :=
  match goal with
  | H: MS _ _ _ _  ?cm1 ?cm2 |- _ =>
    destruct cm1 as [sc Hm]; destruct cm2 as [tc Lm];
    unfold MS in H; simpl in H;
    destruct H as [f0 [MS [FPMATCH [EQI [SVALID [TVALID [AGMU RCPRESV]]]]]]]
  | H: MS _ _ _ _  ?cm1 ?cm2 |- _ =>
    unfold MS in H; simpl in H;
    destruct H as [f0 [MS [FPMATCH [EQI [SVALID [TVALID [AGMU RCPRESV]]]]]]]
  end.
Ltac splitMS :=
  eexists; constructor; auto;
  [econstructor; eresolvfp |
   split; [eresolvfp|
           split; [auto|
                   split; [try resvalid; auto |
                           split; [try resvalid; auto
                                  |split; [auto|
                                           try resvalid; eauto]]]]]];auto.

Lemma match_bounds_rely:
  forall f mu Hm Hm' e cenv sp lo hi
    (PLGE: Ple (Genv.genv_next ge) lo)
    (PLE: Ple hi (Mem.nextblock Hm))
    (MENV: match_env f cenv e sp lo hi)
    (MB:match_bounds e Hm)
    (AGMU:proper_mu ge tge f mu)
    (HRELY:LDefs.Rely (Injections.SharedSrc mu) Hm Hm'),
    match_bounds e Hm'.
Proof.
  unfold match_bounds.
  intros.
  inv MENV.
  eapply me_bounded0 in H as ?.
  destruct H1.
  inv HRELY.
  inv H3.
  eapply MB;eauto.
  eapply unchanged_on_perm;eauto.
  intro.
  inv AGMU.
  inv proper_mu_ge_init_inj.
  rewrite mu_shared_src in H3.
  unfold Bset.belongsto in H3.
  eapply Ple_trans in H1;eauto.
  eapply Plt_Ple_trans in H3;eauto.
  apply Plt_ne in H3;contradiction.
  unfold Mem.valid_block.
  eapply Plt_Ple_trans;eauto.
Qed.

Lemma inject_rely:
  forall f mu Hm Lm Hm' Lm'
    (AGMU:proper_mu ge tge f mu)
    (HRELY:LDefs.Rely (Injections.SharedSrc mu) Hm Hm')
    (LRELY:LDefs.Rely (Injections.SharedTgt mu) Lm Lm')
    (INV:LDefs.Inv mu Hm' Lm')
    (MINJ:Mem.inject f Hm Lm),
    Mem.inject f Hm' Lm'.
Proof.
  intros.
  inv AGMU;inv HRELY;inv LRELY.
  eapply MemClosures_local.sep_inject_rely_inject;eauto.
Qed.
Lemma match_callstack_rely:
  forall f mu Hm Lm Hm' Lm' cs b tb
    (MCS:match_callstack f Hm Lm cs b tb)
    (PLE:Ple b (Mem.nextblock Hm))
    (AGMU:proper_mu ge tge f mu)
    (HRELY:LDefs.Rely (Injections.SharedSrc mu) Hm Hm')
    (LRELY:LDefs.Rely (Injections.SharedTgt mu) Lm Lm')
    (INV:LDefs.Inv mu Hm' Lm')
    (MINJ:Mem.inject f Hm Lm)
    (MINJ':Mem.inject f Hm' Lm'),
    match_callstack f Hm' Lm' cs b tb.
Proof.
  induction cs;intros.
  inv MCS. econstructor;eauto.

  inv MCS. exploit IHcs;eauto.
  inv MENV. eapply Ple_trans;eauto. eapply Ple_trans;eauto.
  intro.
  econstructor;eauto.
  eapply match_callstack_ple_ge in H as ?.
  
  eapply match_bounds_rely in BOUND0;try apply MENV;eauto.
  eapply Ple_trans;eauto.

  eapply padding_freeable_invariant;eauto.
  intros.
  inv LRELY.
  inv H1.
  eapply unchanged_on_perm;eauto.
  intro.
  contradict PLT.
  inv AGMU. inv proper_mu_ge_init_inj.
  rewrite mu_shared_tgt in H1;unfold Bset.belongsto in H1. rewrite S_EQ. auto.
  revert H0;clear;intro.
  destruct Lm.
  unfold Mem.perm in H0. simpl in *.
  unfold Mem.perm_order' in H0.
  destruct (mem_access !! sp ofs Cur) eqn:?;try contradiction.
  unfold Mem.valid_block. simpl.
  destruct (plt sp nextblock);auto.
  eapply nextblock_noaccess in n;eauto. rewrite Heqo in n. inv n.
Qed.
Lemma unmapped_closed_alloc_variables:
  forall vars e e2 mu Hm Lm Hm' 
    (SVALID: forall b0 : block,  Bset.belongsto (Injections.SharedSrc mu) b0 -> Mem.valid_block Hm b0)
    (TVALID: forall b0 : block,  Bset.belongsto (Injections.SharedTgt mu) b0 -> Mem.valid_block Lm b0)
    (AGMU: Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu)),
    MemClosures_local.unmapped_closed mu Hm Lm ->
    alloc_variables e Hm vars e2 Hm' ->
    MemClosures_local.unmapped_closed mu Hm' Lm.
Proof.
  induction vars;intros.
  inv H0. auto.
  inv H0.
  assert(SVALID': forall b, Bset.belongsto (Injections.SharedSrc mu) b-> Mem.valid_block m1 b).
  resvalid.
  eapply unmapped_closed_alloc_1 in H5;eauto.
Qed.
Lemma TRANSF_local_ldsim:
  @local_ldsim Csharpminor_IS Cminor_IS ge tge ge tge.
Proof.
  econstructor.
  instantiate(1:=fun b =>MS).
  instantiate(1:=lt).

  econstructor;eauto.
  apply lt_wf.
  intros;invMS;eapply proper_mu_inject;eauto.
  intros;invMS;eapply proper_mu_ge_init_inj;eauto.
  apply ge_match.
  {
    intros mu fid args args' score GE_INIT_INJ INJID GARG ARGREL INITCORE.
    unfold init_core_local in *. simpl in *.
    unfold init_core.
    
    unfold Csharpminor_local.init_core in INITCORE.
    unfold generic_init_core in INITCORE |- *.
    erewrite symbols_preserved.
    destruct Genv.find_symbol eqn:?;[|inv INITCORE].
    destruct (Genv.find_funct_ptr ge b) eqn:?;[|inv INITCORE].
    
    apply function_ptr_translated in Heqo0 as ?.
    destruct H as [tf[Heqo' FUNDEFMATCH]].
    rewrite Heqo'.
    destruct f eqn:?;[|inv INITCORE].
    unfold Csharpminor_local.fundef_init in INITCORE.
    destruct ( val_has_type_list_func args (sig_args (Csharpminor.funsig (Internal f0))) &&  vals_defined args && zlt (4 * (2 * Zlength args)) Int.max_unsigned) eqn:?;inv INITCORE.
    assert(wd_args args (sig_args (Csharpminor.funsig (Internal f0))) = true).
    auto. clear Heqb0.
    unfold fundef_init.
    erewrite sig_preserved;eauto.
    pose proof FUNDEFMATCH as R.
    monadInv R.
    erewrite wd_args_inject;eauto.
    eexists;split;eauto.
    intros sm0 tm0 INITSM INITTM MEMINITINJ sm tm [HRELY LRELY MINJ].
    exists O.
    assert (args' = args).
    { generalize ARGREL GARG MEMINITINJ; clear. revert args'. induction args; intros args' REL G MEMREL; inv REL.
      auto. inv G. f_equal. inv H1; auto. inv MEMREL. apply inj_inject_id in H. inv H. rewrite Ptrofs.add_zero; auto.
      contradiction. apply IHargs; auto. }
    subst.

    splitMS.
    unfold inj_mu;auto.

    Focus 2.
    apply match_Kstop.
    {
      econstructor 1 with(hi:=Genv.genv_next ge).
      Focus 2.
      inv HRELY. rewrite EQNEXT.
      inv INITSM. rewrite dom_match.
      apply Ple_refl.
      Focus 2.
      inv LRELY. rewrite EQNEXT.
      inv INITTM. rewrite S_EQ,dom_match.
      apply Ple_refl.

      econstructor;auto.
      + intros.
        assert(Mem.valid_block sm0 b0).
        unfold Mem.valid_block. inv INITSM. congruence.
        inv MEMINITINJ.
        eapply dom_eq_src in H1.
        inv wd_mu_init.
        eapply inj_dom in H1. Hsimpl.
        assert(Bset.inj_to_meminj (Injections.inj mu) b0 = Some (x0,0)).
        unfold Bset.inj_to_meminj. rewrite H1. auto.
        apply INJID in H2 as ?. inv H3. auto.
      + intros.
        eapply INJID in H0 ;inv H0;auto.
      + intros.
        eapply Genv.genv_symb_range;eauto.
      + intros.
        rewrite Genv.find_funct_ptr_iff in H0.
        eapply Genv.genv_defs_range;eauto.
      + intros.
        rewrite Genv.find_var_info_iff in H0.
        eapply Genv.genv_defs_range;eauto.
    }
    
    constructor.
    inv MEMINITINJ. inv HRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_src; auto.
    inv MEMINITINJ. inv LRELY. unfold Mem.valid_block in *. intros. rewrite EQNEXT. apply dom_eq_tgt; auto.
    inv MEMINITINJ; econstructor; eauto. intro.
    intros ? ? ? ? ?. exploit inj_inject_id. exact H0. intro. inv H1.
    intro A. inv A. auto.
    apply MemClosures_local.reach_closed_unmapped_closed. inv LRELY. auto.

    Unshelve.
    apply (PTree.empty Z).
  }
  {
    simpl.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm Hfp' Hcore' Hm' MS STEP.
    revert i mu Hfp Lfp Lcore Lm MS.
    pose proof STEP as STEP_bk.
    induction STEP;intros;invMS;inv MS;simpl.
    {
      right;exists (seq_left_depth s).
      monadInv TR; dependent induction MK.
      Esimpl. constructor. econstructor;eauto.
      eresolvfp.  splitMS;auto.

      Esimpl. constructor. econstructor;eauto.
      eresolvfp.
      eexists. split;eauto.
      eapply match_state_seq;eauto.
      split. eresolvfp. eauto.
      exploit IHMK;eauto.
      intro. Hsimpl. Esimpl;eauto. rewrite<- FP.emp_union_fp with (fp:=x).
      econstructor 2;eauto.  constructor.
    }
    {
      right;exists 0%nat.
      monadInv TR; dependent induction MK.
      Esimpl. constructor. econstructor;eauto.
      eresolvfp. splitMS.

      exploit IHMK;eauto.
      intro;Hsimpl.
      Esimpl;eauto.  rewrite<- FP.emp_union_fp with (fp:=x).
      econstructor 2;eauto.
      constructor.
    }
    {
      right;exists 0%nat.
      monadInv TR.
      eapply match_callstack_freelist in MCS as ?;eauto.
      Hsimpl.
      eapply match_is_call_cont in MK as ?;eauto.
      Hsimpl.
      Esimpl.
      eapply plus_right;eauto.
      econstructor;eauto.

      eresolvfp.
      Lemma freelist_free_fpmatch:
        forall mu f0 e sp tfn
          (AGMU: proper_mu ge tge f0 mu)
          (NGE: ~ Plt sp (Genv.genv_next ge)),
           Injections.FPMatch' mu (FMemOpFP.free_list_fp (blocks_of_env e))
                               (FMemOpFP.free_fp sp 0 (fn_stackspace tfn)).
      Proof.
        unfold FMemOpFP.free_fp.
        constructor;simpl;try apply FMemOpFP.emp_loc_match.
        unfold FMemOpFP.range_locset. constructor;intros.
        inv H0. inv_eq. unfold Bset.belongsto in H.
        inv AGMU. inv proper_mu_ge_init_inj.
        rewrite mu_shared_tgt in H.
        contradiction.
      Qed.
      eapply freelist_free_fpmatch;eauto.
      splitMS.
      eapply freelist_free_fpmatch;eauto.
      {
        intros.
        eapply proper_mu_inject in H7 as [];eauto.
        eapply proper_mu_inject_incr in AGMU as ?.
        exploit H8. unfold Bset.inj_to_meminj;rewrite H7; eauto.
        intro;  eapply Mem.valid_block_inject_1;eauto.
      }
      assert(R:
          forall b lo hi,
            In (b,lo,hi) (blocks_of_env e) ->
            ~ Plt b (Genv.genv_next ge) /\  lo = 0).
      {
        intros.
        eapply in_blocks_of_env_inv in H7 as [?[]];subst.
        inv MCS.
        inv MENV.
        apply  match_callstack_ple_ge in MCS0 as ?.
        apply me_bounded0 in H7 as [].
        xomega.
      }
      assert(R2:
               forall b lo hi,
                 In (b,lo,hi)(blocks_of_env e) ->
                 exists delta,
                 f0 b = Some (sp,delta)).
      {
        intros.
        inv MCS.
        inv MENV.
        eapply in_blocks_of_env_inv in H7 as [?[]];subst.
        specialize (me_vars0 x1).
        inv me_vars0;try congruence.
        rewrite H7 in H8;inv H8.
        inv H10. eauto.
      }
      eapply freelist_free_unmapped_closed;eauto.
    }
    {
      right;exists 0%nat.
      monadInv TR.
      eapply transl_expr_correct in H as ?;eauto.
      eapply transl_expr_fp_correct in H0 as ?;eauto.
      Hsimpl.
      Esimpl.
      econstructor. econstructor;eauto.
      eresolvfp.
      splitMS.
      eapply match_callstack_set_temp;eauto.
    }
    {
      right;exists 0%nat.
      monadInv TR.
      eapply transl_expr_correct in H as ?;eauto.
      eapply transl_expr_fp_correct in H0 as ?;eauto.
      eapply transl_expr_correct in H1 as ?;eauto.
      eapply transl_expr_fp_correct in H2 as ?;eauto.
      Hsimpl.
      eapply Mem.storev_mapped_inject in H3 as ?;eauto.
      Hsimpl.
      apply nextblock_storev in H12 as R1.
      apply nextblock_storev in H3 as R2.
      unfold Mem.storev in *.
      inversion H11;subst;try discriminate.
      eapply storev_fp_match in MCS as ?;eauto.
      
      Esimpl.
      econstructor. econstructor;eauto.
      eresolvfp.
      repeat eapply Injections.fp_match_union';eauto.
      unfold MS.
      Esimpl;eauto.
      econstructor;eauto.
      rewrite R1,  R2.
      eapply match_callstack_invariant;eauto.
      intros. eapply Mem.perm_store_2; eauto.
      intros. eapply Mem.perm_store_1; eauto.
      eresolvfp.
      repeat eapply Injections.fp_match_union';eauto.
      resvalid.
      resvalid.

      inv AGMU.
      eapply MemClosures_local.store_val_inject_unmapped_closed_preserved; eauto.
      erewrite<- Mem.address_inject';eauto.
      instantiate(1:=chunk).
      Transparent Mem.store.
      unfold Mem.store in H3.
      inv H3.
      destruct (Mem.valid_access_dec);try discriminate.
      inv H17.
      unfold Mem.valid_access in *.
      unfold Mem.range_perm in *.
      unfold Mem.perm in *. simpl in *.
      destruct v0.
      split;auto.
      intros.
      eapply H3 in H17;eauto.
      unfold Mem.perm_order' in *.
      inv_eq;constructor.
      Opaque Mem.store.
    }
    {
      right;exists 0%nat.
      monadInv TR.
      exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
      eapply transl_expr_correct in H as ?;eauto.
      eapply transl_expr_fp_correct in H0 as ?;eauto.
      Hsimpl.
      assert(x2 = vf).
         exploit match_callstack_match_globalenvs; eauto. intros [bnd MG].
         eapply val_inject_function_pointer; eauto.
      subst x2. 
      eapply transl_exprlist_correct in H1 as ?;eauto.
      eapply transl_exprlist_fp_correct in H2 as ?;eauto.
      Hsimpl.
      Esimpl.
      econstructor;eauto.
      econstructor;eauto.
      apply sig_preserved; eauto.
      eresolvfp.
      splitMS.
      eapply match_Kcall;eauto.
      red;auto.
      Unshelve.
      apply (PTree.empty Z).
    }
    {
      right;exists (seq_left_depth s1).
      monadInv TR.
      Esimpl.
      econstructor;eauto. econstructor.
      eresolvfp.
      splitMS.
      constructor;auto.
    }
    {
      left.
      exists (seq_left_depth s1).
      split;auto.
      splitMS.
    }
    {
      right;eexists.
      monadInv TR.
      eapply transl_expr_correct in H as ?;eauto.
      eapply transl_expr_fp_correct in H0 as ?;eauto.
      Hsimpl.
      eapply bool_of_val_inject in H1 as ?;eauto.
      Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      splitMS.
      destruct b;auto.
    }
    {
      right.
      monadInv TR.
      Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      splitMS.
      constructor;auto.
      simpl. rewrite EQ. auto.
    }
    {
      right.
      monadInv TR.
      Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      splitMS.
      econstructor;eauto.
    }
    {
      monadInv TR.
      right.
      clear STEP_bk.
      dependent induction MK.
      + Esimpl. constructor. econstructor;eauto.
        eresolvfp.
        instantiate(1:=O).
        splitMS;auto.
      + exploit IHMK;eauto. intro.
        Hsimpl.
        Esimpl;eauto.
        eapply plus_left. constructor. apply plus_star;eauto.
        eresolvfp.
      + exploit IHMK;eauto;intro;Hsimpl.
        Esimpl;eauto.
        eapply plus_left. constructor. apply plus_star;eauto.
        eresolvfp.
    }
    {
      right;monadInv TR.
      clear STEP_bk.
      dependent induction MK.
      + Esimpl. constructor. econstructor;eauto.
        eresolvfp.
        instantiate(1:=O).
        splitMS;auto.
      + exploit IHMK;eauto. intro.
        Hsimpl.
        Esimpl;eauto.
        eapply plus_left. constructor. apply plus_star;eauto.
        eresolvfp.
    }
    {
      right;monadInv TR.
      clear STEP_bk.
      dependent induction MK.
      + Esimpl. constructor. econstructor;eauto.
        eresolvfp.
        instantiate(1:=O).
        splitMS;auto.
      + exploit IHMK;eauto. intro.
        Hsimpl.
        Esimpl;eauto.
        eapply plus_left. constructor. apply plus_star;eauto.
        eresolvfp.
    }
    {
      simpl in TR. destruct (switch_table cases O) as [tbl dfl] eqn:STBL. monadInv TR.
      
      exploit transl_expr_correct; eauto.
      intros [tv [EVAL VINJ]].
      exploit transl_expr_fp_correct;eauto.
      intros [tfp[EVALFP MATCH]].
      assert (SA: switch_argument islong tv n).
      { inv H1; inv VINJ;constructor. }
       exploit switch_descent; eauto. intros [k1 [A B]].
      exploit switch_ascent; eauto. eapply (switch_table_select n).
      rewrite STBL; simpl. intros [k2 [C D]].
      exploit transl_lblstmt_suffix; eauto. eapply (switch_table_select n).
      simpl. intros [body' [ts' E]].
      exploit switch_match_states; eauto. intros [T2 [F G]].
      
      right.
      Esimpl.
      eapply plus_star_trans. eapply B.
      eapply star_left. econstructor; eauto.
      eapply star_trans. eexact C.
      apply plus_star. eexact F.
      reflexivity. reflexivity. traceEq.
      eresolvfp.

      unfold MS.
      Esimpl;eauto.
      eresolvfp.
    }
    {
      right;exists O;monadInv TR.
      exploit match_callstack_freelist;eauto. intro.
      Hsimpl.

      Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      eapply freelist_free_fpmatch;eauto.
      splitMS.
      eapply match_call_cont;eauto.
      eapply freelist_free_fpmatch;eauto.
      intros.
      unfold Bset.belongsto in H3.
      inversion AGMU;subst.
      apply proper_mu_inject in H3 as ?.
      destruct H4.
      exploit proper_mu_inject_incr.
      unfold Bset.inj_to_meminj.
      rewrite H4. eauto.
      intro.
      eapply Mem.valid_block_inject_1;eauto.
      assert(R:
          forall b lo hi,
            In (b,lo,hi) (blocks_of_env e) ->
            ~ Plt b (Genv.genv_next ge) /\  lo = 0).
      {
        intros.
        eapply in_blocks_of_env_inv in H3 as [?[]];subst.
        inv MCS.
        inv MENV.
        apply  match_callstack_ple_ge in MCS0 as ?.
        apply me_bounded0 in H3 as [].
        xomega.
      }
      assert(R2:
               forall b lo hi,
                 In (b,lo,hi)(blocks_of_env e) ->
                 exists delta,
                 f0 b = Some (sp,delta)).
      {
        intros.
        inv MCS.
        inv MENV.
        eapply in_blocks_of_env_inv in H3 as [?[]];subst.
        specialize (me_vars0 x0).
        inv me_vars0;try congruence.
        rewrite H3 in H4;inv H4.
        inv H6. eauto.
      }
      eapply freelist_free_unmapped_closed;eauto.
    }
    {
      right;exists O;monadInv TR.
      exploit match_callstack_freelist;eauto. intro.
      exploit transl_expr_correct;eauto;intro.
      exploit transl_expr_fp_correct;eauto;intro.
      Hsimpl.

      Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      eapply freelist_free_fpmatch;eauto.
      splitMS.
      eapply match_call_cont;eauto.
      eapply freelist_free_fpmatch;eauto.
      intros.
      unfold Bset.belongsto in H9.
      inv AGMU.
      apply proper_mu_inject in H9 as ?.
      destruct H10.
      exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H10;eauto.
      intro.
      eapply Mem.valid_block_inject_1;eauto.
      assert(R:
          forall b lo hi,
            In (b,lo,hi) (blocks_of_env e) ->
            ~ Plt b (Genv.genv_next ge) /\  lo = 0).
      {
        intros.
        eapply in_blocks_of_env_inv in H9 as [?[]];subst.
        inv MCS.
        inv MENV.
        apply  match_callstack_ple_ge in MCS0 as ?.
        apply me_bounded0 in H9 as [].
        xomega.
      }
      assert(R2:
               forall b lo hi,
                 In (b,lo,hi)(blocks_of_env e) ->
                 exists delta,
                 f0 b = Some (sp,delta)).
      {
        intros.
        inv MCS.
        inv MENV.
        eapply in_blocks_of_env_inv in H9 as [?[]];subst.
        specialize (me_vars0 x3).
        inv me_vars0;try congruence.
        rewrite H9 in H10;inv H10.
        inv H12. eauto.
      }
      eapply freelist_free_unmapped_closed;eauto.
    }
    {
      monadInv TR.
      right;Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      splitMS.
    }
    {
      monadInv TR;right.
      exploit transl_find_label_body; eauto.
      intro;Hsimpl.
      Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      splitMS.
    }
    {
      monadInv TR. generalize EQ; clear EQ; unfold transl_function.
      caseEq (build_compilenv f). intros ce sz BC.
      destruct (zle sz Ptrofs.max_unsigned); try congruence.
      intro TRBODY.
      generalize TRBODY; intro TMP. monadInv TMP.
      
      set (tf := mkfunction (Csharpminor.fn_sig f)
                            (Csharpminor.fn_params f)
                            (Csharpminor.fn_temps f)
                            sz
                            x0) in *.
      caseEq (Mem.alloc Lm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
      assert(R2:Ple (Genv.genv_next ge)(Mem.nextblock m)).
      {
        unfold Ple.
        apply Pos.le_nlt.
        intro.
        inv AGMU.
        inv proper_mu_ge_init_inj.
        assert(Injections.SharedSrc mu (Mem.nextblock m)).
        rewrite mu_shared_src;auto.
        apply SVALID in H6.
        apply Plt_ne in H6. contradiction.
      }
      assert(R:~ Plt sp (Genv.genv_next ge)).
      {
        apply Mem.alloc_result in ALLOC'.
        subst sp.
        intro.
        inv AGMU.
        inv proper_mu_ge_init_inj.
        exploit TVALID.
        rewrite mu_shared_tgt.
        unfold Bset.belongsto.
        rewrite<- S_EQ.
        eauto.
        intro.
        unfold Mem.valid_block in H6.
        apply Plt_ne in H6.
        contradiction.
      }
     
      exploit match_callstack_function_entry; eauto.
      simpl; eauto. simpl; auto.
      intros [?[]].
      right.
      Esimpl.
      constructor. econstructor;eauto.
      eresolvfp.
      {
        unfold MemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp.
        constructor;simpl;try apply FMemOpFP.emp_loc_match.
        constructor;intros.
        inv H8. destruct peq;try discriminate;subst.
        apply TVALID in H7. unfold Mem.valid_block in H7.
        apply Plt_ne in H7.
        contradiction.
      }
      destruct H6.
      assert(SVALID':  forall b : block,  Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m1 b).
      {
        intros.
        unfold Bset.belongsto in H6.
        inv p.
        apply proper_mu_inject in H6 as ?.
        destruct H7.
        exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj. rewrite H7;eauto.
        intro.
        eapply Mem.valid_block_inject_1;eauto.
      }
      splitMS.

      inv MK; simpl in ISCC; contradiction || econstructor; eauto.
      {
        unfold MemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp.
        constructor;simpl;try apply FMemOpFP.emp_loc_match.
        constructor;intros.
        inv H7. destruct peq;try discriminate;subst.
        apply TVALID in H6. unfold Mem.valid_block in H6.
        apply Plt_ne in H6.
        contradiction.
      }
     
      inv AGMU.
      eapply unmapped_closed_alloc_2;eauto.
      eapply unmapped_closed_alloc_variables in H2;eauto.
    }
    {
      inv MK.
      simpl.
      right.
      inversion MCS;subst.
      Esimpl.

      constructor.  econstructor;eauto.
      eresolvfp.
      instantiate(1:=O).
      unfold set_optvar;simpl.
      
      destruct optid;splitMS.
      eapply match_callstack_set_temp;eauto.
    }
  }
  { (*at_ext*)
    simpl.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm f sg argSrc MS ATEXT RC GARG.
    exists O.
    unfold at_external,Csharpminor_local.at_external in *.
    destruct Hcore; try discriminate. destruct f0; try discriminate. destruct e; try discriminate. 
    destruct (invert_symbol_from_string) eqn:SYMBNAME;try discriminate.
    destruct peq; try discriminate. destruct peq; try discriminate. simpl in *.
    inv ATEXT. invMS. inv MS. monadInv TR.

    erewrite match_genvs_invert_symbol_from_string_preserved;eauto using genv_match.
    destruct peq; try contradiction. destruct peq; try contradiction. simpl.
    eexists;split;eauto. Esimpl;eauto.
    {
      simpl in *. unfold LDSimDefs.arg_rel.
      revert targs AGMU GARG ARGSINJ ; clear.
      (** should be extracted as a lemma ... *)
      induction argSrc; intros args' AGMU GARG LD. simpl. inv LD. auto. inv LD. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto.
      eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H0; eauto. 
      intro. rewrite H1 in H;inv H.
      econstructor. unfold Bset.inj_to_meminj; rewrite H0. eauto. rewrite Ptrofs.add_zero; auto. 
    }
    inv AGMU. eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_injection'';eauto.
    unfold LDefs.Inv.
    inv AGMU.
    eapply MemClosures_local.sep_inject_rc_inject;eauto.
    splitMS.

    intros.
    inv H.
    Focus 2.
    inv H0. simpl. auto.

    induction f1;simpl;intros.
    monadInv H0;auto.
    monadInv H0.
    destruct e;auto.
  }
  { (*after_ext*)
    simpl. unfold after_external_local,Csharpminor_local.after_external,after_external.
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MS GRES AFTEXT RESREL.
    destruct Hcore; try discriminate. destruct f; try discriminate. destruct e;try discriminate.
    invMS. inv MS.
    monadInv TR.
    exists (match oresTgt with Some v => Core_Returnstate v tk | None => Core_Returnstate Vundef tk end).
    split.
    inv_eq.
    inv_eq;auto.
    rewrite Heqb. auto.

    inv_eq. auto.

    intros Hm' Lm' [HRELY LRELY INV].
    exists O. 

    unfold LDSimDefs.ores_rel in RESREL.
    
    destruct oresSrc eqn:?;inv AFTEXT; destruct oresTgt eqn:?;try contradiction.
    {
      inv_eq.
     
      exploit inject_rely;eauto. intro.
      splitMS.

      inversion HRELY. rewrite EQNEXT.
      inversion LRELY. rewrite EQNEXT0.
      eapply match_callstack_rely;eauto.
      apply Ple_refl.
      inv RESREL;try constructor.   econstructor;eauto.
      inv AGMU;apply proper_mu_inject_incr in H0;auto.
      intros ? S; apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT. auto.
      intros ? T; apply TVALID in T;unfold Mem.valid_block in *;inv LRELY;rewrite EQNEXT;auto.

      inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
    }
    {
      inv_eq.
      exploit inject_rely;eauto. intro.
      splitMS.

      inversion HRELY. rewrite EQNEXT.
      inversion LRELY. rewrite EQNEXT0.
      eapply match_callstack_rely;eauto.
      apply Ple_refl.
      intros ? S; apply SVALID in S. unfold Mem.valid_block in *. inv HRELY. rewrite EQNEXT. auto.
      intros ? T; apply TVALID in T;unfold Mem.valid_block in *;inv LRELY;rewrite EQNEXT;auto.
      inv AGMU.
      inv LRELY. eapply MemClosures_local.reach_closed_unmapped_closed; eauto.
    }
  }
  { (*halt*)
    simpl.
    unfold halted,Csharpminor_local.halted.
    intros i mu Hfp Lfp Hcore Hm Lcore Lm resSrc MS HALT RC GRES.
    destruct Hcore; try discriminate.
    destruct k;try discriminate.
    inv HALT.
    invMS. inv MS.
    inv MK.
    exists tv. split;eauto.
    split;auto.
    {
      unfold LDSimDefs.G_arg in GRES.
      destruct resSrc eqn:?;try contradiction;unfold LDSimDefs.res_rel;inv RESINJ;try constructor.
      inv AGMU.
      apply proper_mu_inject in GRES as [].
      exploit proper_mu_inject_incr.
      unfold Bset.inj_to_meminj.
      rewrite H;eauto.
      intro. rewrite H1 in H0;inv H0.
      econstructor;eauto.
      unfold Bset.inj_to_meminj. rewrite H;auto.
    }
    split.
    inv AGMU. eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_injection'';eauto.
    split. auto.
    inv AGMU.
    eapply MemClosures_local.sep_inject_rc_inject;eauto.
  }
Qed.
End TRANSLATION.

