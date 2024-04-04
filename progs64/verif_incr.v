(* Do not edit this file, it was generated automatically *)
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.SC_atomics.
Require Import VST.atomics.verif_lock.
Require Import VST.progs64.incr.

From diaframe Require Import defs weakestpre.
From diaframe Require Export spec_notation.
From diaframe Require Import proofmode_base.
From diaframe.lib Require Import iris_hints.

Import LiftNotation.

Unset Universe Polymorphism.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section mpred.

(* box up concurrentGS? *)
Context `{!VSTGS unit Σ, !cinvG Σ, !inG Σ (excl_authR natO), !atomic_int_impl (Tstruct _atom_int noattr)}.
#[local] Instance concurrent_ext_spec : ext_spec unit := concurrent_ext_spec _ (ext_link_prog prog).

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Definition ghost_auth (g : gname) (n : nat) : mpred := own g (●E n : excl_authR natO).
Definition ghost_frag (g : gname) (n : nat) : mpred := own g (◯E n : excl_authR natO).

Definition cptr_lock_inv (g1 g2 : gname) (ctr : val) := ∃ z : nat, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr z)) ctr ∗
  ∃ x : nat, ∃ y : nat, ⌜(z = x + y)%nat⌝ ∧ ghost_auth g1 x ∗ ghost_auth g2 y.

Definition incr_spec :=
 DECLARE _incr
  WITH sh1 : share, sh : Qp, h : lock_handle, g1 : gname, g2 : gname, left : bool, n : nat, gv: globals
  PRE [ ]
         PROP  (readable_share sh1)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_frag (if left then g1 else g2) n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_frag (if left then g1 else g2) (n+1)%nat).

Definition read_spec :=
 DECLARE _read
  WITH sh1 : share, sh : Qp, h : lock_handle, g1 : gname, g2 : gname, n1 : nat, n2 : nat, gv: globals
  PRE [ ]
         PROP  (readable_share sh1)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_frag g1 n1; ghost_frag g2 n2)
  POST [ tuint ]
         PROP ()
         RETURN (Vint (Int.repr (n1 + n2)%nat))
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_frag g1 n1; ghost_frag g2 n2).

Definition thread_lock_R sh1 (sh : Qp) h (g1 g2 : gname) (ctr : val) :=
  field_at sh1 t_counter [StructField _lock] (ptr_of h) ctr ∗ lock_inv sh h (cptr_lock_inv g1 g2 ctr) ∗ ghost_frag g1 1.

Definition thread_lock_inv sh1 sh h g1 g2 ctr ht :=
  self_part sh ht ∗ thread_lock_R sh1 sh h g1 g2 ctr.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * Qp * lock_handle * lock_handle * gname * gname * globals
  PRE [ tptr tvoid ]
         let '(sh1, sh, h, ht, g1, g2, gv) := x in
         PROP  (readable_share sh1; ptr_of ht = y)
         PARAMS (y) GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
                lock_inv sh h (cptr_lock_inv g1 g2 (gv _c));
                ghost_frag g1 0;
                lock_inv sh ht (thread_lock_inv sh1 sh h g1 g2 (gv _c) ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; freelock_spec;
  spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Instance ctr_inv_exclusive : forall g1 g2 p,
ExclusiveProp (cptr_lock_inv g1 g2 p).
Proof.
  unfold cptr_lock_inv, ExclusiveProp; intros.
  iIntros "((% & ? & ?) & (% & ? & ?))".
  rewrite !field_at_field_at_; iApply (field_at__conflict with "[$]"); auto.
  { simpl; lia. }
Qed.
#[local] Hint Resolve ctr_inv_exclusive : core.

Instance thread_inv_exclusive : forall sh1 sh h g1 g2 p,
ExclusiveProp (thread_lock_R sh1 sh h g1 g2 p).
Proof.
  unfold cptr_lock_inv, ExclusiveProp; intros.
  iIntros "((? & ? & g1) & (? & ? & g2))".
  iDestruct (own_valid_2 with "g1 g2") as %[]%@excl_auth_frag_op_valid.
Qed.
#[local] Hint Resolve thread_inv_exclusive : core.

Lemma ghost_var_inj : forall g x y, ghost_auth g x ∗ ghost_frag g y ⊢ ⌜x = y⌝.
Proof.
  intros; iIntros "(a & f)".
  iDestruct (own_valid_2 with "a f") as %H%@excl_auth_agree; done.
Qed.

Lemma ghost_var_incr : forall g1 g2 x y n (left : bool), ghost_auth g1 x ∗ ghost_auth g2 y ∗ ghost_frag (if left then g1 else g2) n ⊢
  |==> ⌜(if left then x else y) = n⌝ ∧ ghost_auth (if left then g1 else g2) (n+1)%nat ∗ ghost_frag (if left then g1 else g2) (n+1)%nat ∗
       ghost_auth (if left then g2 else g1) (if left then y else x).
Proof.
  destruct left.
  - iIntros "(a & $ & f)".
    iDestruct (ghost_var_inj with "[$a $f]") as %->.
    iMod (own_update_2 with "a f") as "($ & $)"; last done.
    apply @excl_auth_update.
  - iIntros "($ & a & f)".
    iDestruct (ghost_var_inj with "[$a $f]") as %->.
    iMod (own_update_2 with "a f") as "($ & $)"; last done.
    apply @excl_auth_update.
Qed.

Definition wp {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} (E:coPset) (Delta: tycontext) (c: statement) (Q: ret_assert): assert :=
  ∃ P: assert, ⌜@semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q⌝ ∧ P.

(* Notation wp OK_ty Σ VSTGS0 Espec cs E Delta c Q := (∃ P: assert, ⌜@semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q⌝ ∧ P). *)
Definition wp_spec: forall {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} (E:coPset) (Delta: tycontext) P c Q,
  (P ⊢ @wp OK_ty Σ VSTGS0 Espec cs E Delta c Q) <-> @semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q.
Proof.
  intros.
  split; intros.
  + eapply semax_pre.
    - rewrite bi.and_elim_r H //.
    - unfold wp.
      apply semax_extract_exists.
      clear P H.
      intros P.
      apply semax_extract_prop.
      auto.
  + unfold wp.
    iIntros; iExists P; iSplit; auto.
Qed.
Opaque wp.
Ltac into_wp := rewrite <- wp_spec.

Typeclasses Opaque locald_denote.
Arguments locald_denote : simpl never.

Global Instance into_and_local {Σ'} p P Q : IntoAnd p (@local Σ' (`(and) P Q)) (local P) (local Q).
Proof. by rewrite /IntoAnd local_lift2_and. Qed.

(* for diaframe *)
Global Instance into_sep_local  {Σ'} P Q: IntoSep (@local Σ' (`(and) P Q)) (local P) (local Q).
Proof. rewrite /IntoSep. rewrite local_lift2_and. iIntros "[#$ #$]". Qed.

Global Instance into_sep_careful_local  {Σ'} P Q: IntoSepCareful (@local Σ' (`(and) P Q)) (local P) (local Q).
Proof. rewrite /IntoSepCareful local_lift2_and. iIntros "[#$ #$]". Qed.

(* maybe turn this into something more general, but we need to prove BiPositive mpred *)
Global Instance into_sep_careful_affine_local  {Σ'} P Q: IntoSepCareful (<affine> @local Σ' (`(and) P Q)) (<affine> local P) (<affine> local Q).
Proof. rewrite /IntoSepCareful local_lift2_and // bi.affinely_and. iIntros "[#$ #$]". Qed.

Global Instance into_sep_careful_local_foldr_and  {Σ'} P Qs: IntoSepCareful (@local Σ' (foldr (` and) (` True%type) (map locald_denote (P::Qs)))) 
                                                                         (local (locald_denote P)) (local (foldr (` and) (` True%type) (map locald_denote Qs))).
Proof. rewrite /IntoSepCareful. simpl. rewrite local_lift2_and. iIntros "[#$ #$]". Qed.

Global Instance comine_sep_as_local  {Σ'} P: CombineSepAs (@local Σ' (liftx True%type)) 
                                                          (local (locald_denote P))
                                                          (local (foldr (` and) (` True%type) (map locald_denote [P]))).
Proof. rewrite /CombineSepAs. rewrite !local_lift2_and. iIntros "[#? #?]"; iFrame "#". Qed.

Global Instance comine_sep_as_local_2  {Σ'} P Qs: CombineSepAs (@local Σ' (foldr (` and) (` True%type) (map locald_denote Qs)))
                                                               (local (locald_denote P))
                                                               (local (foldr (` and) (` True%type) (map locald_denote (P::Qs)))).
Proof. rewrite /CombineSepAs. rewrite !local_lift2_and. iIntros "[#? #?]"; iFrame "#". Qed.

(* SEP *)
Global Instance into_sep_careful_SEP {A Σ'} P Q R: IntoSepCareful (@SEPx A Σ' (P::Q::R)) (SEPx [P]) (SEPx (Q::R)).
Proof. rewrite /IntoSepCareful. iIntros "[$ $]". Qed.

(* P is singleton *)
(* Global Instance combine_sep_as_SEP_1 {A Σ'} P Q R: CombineSepAs (SEPx [P]) (SEPx (Q::R)) (@SEPx A Σ' (P::Q::R)).
Proof. rewrite /CombineSepAs /SEPx -!embed_sep /fold_right_sepcon bi.sep_emp //. Qed. *)

Global Instance combine_sep_as_SEP {A Σ'} P Q R: CombineSepAs (SEPx (Q::R)) (SEPx [P]) (@SEPx A Σ' (P::Q::R)).
Proof. rewrite /CombineSepAs /SEPx -!embed_sep /fold_right_sepcon bi.sep_emp. rewrite [_ ∗ P]bi.sep_comm //. Qed.

From iris.proofmode Require Import base coq_tactics reduction tactics string_ident.

Tactic Notation "iSelect2" open_constr(pat1) open_constr(pat2) tactic1(tac) :=
lazymatch goal with
| |- context[ environments.Esnoc ?Es ?x pat1 ] =>
  lazymatch iTypeOf x with
  | Some (_,?T) => unify T pat1;
    lazymatch Es with
    | context [ environments.Esnoc _ ?y pat2 ] =>
      lazymatch iTypeOf y with
      | Some (_,?T) => unify T pat2; tac x y
      end
    end
  end
end.

Tactic Notation "_iCombine" constr(H1) constr(H2):=
iCombine [H1;H2] as "?".

Tactic Notation "combine" open_constr(pat1) open_constr(pat2):=
  iSelect2 pat1 pat2 
  ltac:(fun x y => iRename x into "__VerySecretName1";
                   iRename y into "__VerySecretName2"; 
                   iCombine "__VerySecretName1" "__VerySecretName2" as "?";
                   try iClear "__VerySecretName1 __VerySecretName2").
  
Typeclasses Opaque SEPx.
Typeclasses Opaque local. (* do same thing as sepx so it is always LOCALx*)
Typeclasses Opaque field_at.
Set Nested Proofs Allowed.

Global Instance combine_sep_as_PQR {Σ'} (Q: list localdef) R: CombineSepAs (SEPx R)
  (<affine> @local Σ' (foldr (liftx and) (liftx True%type) (map locald_denote Q)))
  (PROP () (LOCALx Q (SEPx R))).
Proof. rewrite /CombineSepAs /PROPx /LOCALx /SEPx. iIntros "($ & #$)". Qed.

Ltac from_wp :=
  repeat combine (local _) (local _);
  repeat combine (SEPx _) (SEPx _);
  repeat combine (SEPx _) (local _);
  iStopProof;
  rewrite -> wp_spec.


(* see goal is _⊢acquire, iAssert acquire_hint so have context, can use diaframe to figure out args *)

Definition ArgsWrap {Σ'} {T:Type} : T -> @assert Σ' := fun (args:T) => ⌜(forall (l:@list nat), rev (rev l) = l)⌝%type.
Instance Persistent_ArgsWrap: forall {Σ'} {T:Type} (args:T), Persistent (@ArgsWrap Σ' T args).
Proof. intros. apply _. Qed.
(* Instance Absorbing_ArgsWrap: forall {Σ'} {T:Type} (args:T), Absorbing (@ArgsWrap Σ' T args).
Proof. intros. apply _. Qed.
Instance Affine_ArgsWrap: forall {Σ'} {T:Type} (args:T), Affine (@ArgsWrap Σ' T args).
Proof. intros. unfold ArgsWrap. unfold Affine. iIntros "%?". apply _. Qed. *)

Arguments ArgsWrap : simpl never.

Global Instance acquire_hint  (sh:Qp) (h:lock_handle) (R:mpred) :
  HINT1  (@SEPx mpred.environ_index Σ [lock_inv sh h R])%assert5 (* this should be Pre of acquire_spec *) ✱ [True]  
    ⊫ [id] ; (<absorb> @ArgsWrap Σ (Qp * lock_handle * mpred) (sh, h, R)).
Proof. intros. iSteps.  iPureIntro. apply rev_involutive. Qed.
Opaque ArgsWrap.
Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.


  (* into_wp; iSteps.
evar (__forward_call_arg: (Qp * lock_handle * mpred)%type).
iAssert  (ArgsWrap __forward_call_arg) as "#__forward_call_arg"; unfold __forward_call_arg.
iSteps.
iClear "__forward_call_arg".
(* Ltac move_local_to_sep_context:=
  repeat iSelect (local _) (fun x => iDestruct x as "-#?");
  repeat rewrite bi.affinely_elim. *)

  (* move_local_to_sep_context. *)
  
from_wp.



(* TODO setup proper instance for rewrite under semax 
   rewrite bi.intuitionistically_elim. *)

forward_call (sh, h, cptr_lock_inv g1 g2 (gv _c)). *)


  forward_call (sh, h, (cptr_lock_inv g1 g2 (gv _c))).

  (* should be able to do this automatically with a hint about command  *)
  unfold cptr_lock_inv at 2.
  Intros z x y.
  forward.
  forward.
  forward.
  
  (* gather_SEP (ghost_auth g1 x) (ghost_auth g2 y) (ghost_frag _ n).
  viewshift_SEP 0 (⌜(if left then x else y) = n⌝ ∧
    ghost_auth (if left then g1 else g2) (n+1)%nat ∗
    ghost_frag (if left then g1 else g2) (n+1)%nat ∗
    ghost_auth (if left then g2 else g1) (if left then y else x)).
  { go_lowerx.
    iIntros "(? & _)".
    by iMod (ghost_var_incr with "[$]"). }
  Intros. *)
  
  forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  {
  Typeclasses Opaque cptr_lock_inv.
  (* TODO maybe write an instance for affine and ExclusiveProp? *)
  Global Instance lock_prop_hint {prop:bi} (P:prop):
  ExclusiveProp P ->
    HINT (empty_hyp_first) ✱ [-; emp] ⊫ [id] ; (<affine> (P ∗ P -∗ False)) ✱ [emp]. 
    Proof. rewrite empty_hyp_first_eq. unfold ExclusiveProp. intros->. iSteps as "H". Qed.
  
  iSteps.

  destruct left.

  Global Instance ghost_auth_update g1 x n n':
      HINT (ghost_auth g1 x ∗ ghost_frag g1 n) ✱ [-; emp] ⊫ [bupd]; (ghost_frag g1 (n')%nat) ✱ [ghost_auth g1 (n')%nat].
  Proof.
    iStep as "a f". iDestruct (ghost_var_inj with "[$a $f]") as %->.
    iMod (own_update_2 with "a f") as "($ & $)"; last done.
    apply @excl_auth_update.
  Qed.

  Global Instance close_cinv_hint z'  (n n' x y: nat) g1 g2 _c (gv:globals):
  n' = (x + 1)%nat ->
  z' = Int.repr (n' + y)%nat -> (* (Int.add (Int.repr z) (Int.repr 1)) *)
    HINT (field_at Ews t_counter (DOT _ctr) (Vint z') (gv _c)) ✱ 
      [-; ghost_auth g1 x ∗ ghost_auth g2 y ∗ ghost_frag g1 n]
      ⊫ [bupd]; cptr_lock_inv g1 g2 (gv _c) ✱ [ghost_frag g1 (n')].
  Proof. intros -> ->. iStep as "H1 H2 H3 H4". unfold cptr_lock_inv.
  iSteps.
  iExists (x+1). iExists y. 
  
iStepDebug.

  iStep.
   iDestruct (ghost_var_inj with "[$H2 $H4]") as %->.
   iAssert (|==>ghost_auth g1 (n+1) ∗ ghost_frag g1 (n+1))  with "[H2 H4]" as "> [H2 $]".
   iMod (own_update_2 with "H2 H4") as "($ & $)"; last done.
   apply @excl_auth_update.
   iFrame.
   done.
   
   
   iModIntro.
  iExists  (n + 1 + y).  iFrame "H1".  (n+1), y. Admitted.



  Hint Extern 1 (_ = Int.repr _) => by rewrite add_repr; rep_lia : typeclass_instances.


  iStepDebug.
  Set Typeclasses Debug.
  solveStep. 
  (* FIXME
    1.1-1.1-1.1-1: (Int.add (Int.repr z) (Int.repr 1) = Int.repr ?n')
    1.1-1.1-1.1-1: looking for (Int.add (Int.repr z) (Int.repr 1) = Int.repr ?n') with backtracking*)


  forward_call.
  
  (sh, h, cptr_lock_inv g1 g2 (gv _c)).
    unfold Frame; instantiate (1 := [ghost_frag (if left then g1 else g2) (n+1)%nat;
      field_at sh1 t_counter (DOT _lock) (ptr_of h) (gv _c)]); simpl.
    destruct left.
    - Exists (n+1)%nat y; subst; entailer!.
      rewrite !Nat2Z.inj_add //.
    - Exists x (n+1)%nat; entailer!.
      rewrite !Nat2Z.inj_add //. }
  forward.
  cancel.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward.
  forward_call (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z x y.
  forward.
  assert_PROP (x = n1 /\ y = n2) as Heq.
  { sep_apply ghost_var_inj.
    sep_apply (ghost_var_inj g2).
    entailer!. }
  forward.
  forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists z x y; entailer!. }
  destruct Heq as [-> ->]; forward.
  entailer!.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  forward_call (sh1, sh, h, g1, g2, true, 0, gv).
  simpl.
  forward_call release_self (sh, ht, thread_lock_R sh1 sh h g1 g2 (gv _c)).
  { lock_props.
    unfold thread_lock_R at 2; unfold thread_lock_inv; cancel. }
  forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  rename a into gv.
  set (ctr := gv _c).
  forward.
  ghost_alloc (fun g => own g (●E O ⋅ ◯E O : excl_authR natO)).
  { apply excl_auth_valid. }
  Intro g1.
  ghost_alloc (fun g => own g (●E O ⋅ ◯E O : excl_authR natO)).
  { apply excl_auth_valid. }
  Intro g2.
  sep_apply (library.create_mem_mgr gv).
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv g1 g2 ctr).
  Intros lock.
  forward.
  forward.
  forward_call release_simple (1%Qp, lock, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    rewrite !own_op /cptr_lock_inv /ghost_auth.
    Exists O O O.
    unfold_data_at (data_at _ _ _ _); entailer!. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (gv, fun lockt => thread_lock_inv sh2 (1/2)%Qp lock g1 g2 ctr lockt).
  Intros lockt.
  sep_apply lock_inv_isptr; Intros.
  forward_spawn _thread_func (ptr_of lockt) (sh2, (1/2)%Qp, lock, lockt, g1, g2, gv).
  { rewrite -{3}Qp.half_half -frac_op -lock_inv_share_join.
    rewrite -{1}Qp.half_half -frac_op -lock_inv_share_join.
    erewrite <- field_at_share_join; try apply Hsh; auto.
    subst ctr; entailer!. }
  { simpl; auto. }
  forward_call (sh1, (1/2)%Qp, lock, g1, g2, false, 0, gv).
  forward_call ((1/2)%Qp, lockt, thread_lock_inv sh2 (1/2)%Qp lock g1 g2 (gv _c) lockt).
  unfold thread_lock_inv at 2; unfold thread_lock_R; Intros.
  simpl.
  forward_call (sh1, (1/2)%Qp, lock, g1, g2, 1, 1, gv).
  (* We've proved that t is 2! *)
  forward.
  forward_call ((1/2)%Qp, lock, cptr_lock_inv g1 g2 (gv _c)).
  forward_call freelock_self ((1/2)%Qp, (1/2)%Qp, lockt, thread_lock_R sh2 (1/2) lock g1 g2 (gv _c)).
  { unfold thread_lock_inv, selflock; cancel. }
  { rewrite frac_op Qp.half_half //. }
  forward.
  forward_call freelock_simple (lock, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.
    rewrite -{2}Qp.half_half -frac_op -lock_inv_share_join.
    subst ctr; cancel. }
  forward.
Qed.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl.
  destruct x; simpl.
  monPred.unseal.
  Intros h.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; unfold liftx; simpl; unfold lift.
  monPred.unseal; Intros.
  destruct ret; unfold eval_id in H0; simpl in H0; subst; simpl; [|contradiction].
  saturate_local; auto. }
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.

End mpred.
