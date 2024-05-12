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

(* explicitly gain Delta from semax *)
Definition wp_spec_Delta: forall {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} (E:coPset) (Delta: tycontext) P c Q,
  (ENTAIL Delta, P ⊢ @wp OK_ty Σ VSTGS0 Espec cs E Delta c Q) <-> @semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q.
Proof.
  intros. rewrite wp_spec.
  split; apply semax_pre.
  - done. 
  - iSteps.
Qed.
Opaque wp.

Ltac into_ipm := rewrite <- wp_spec_Delta.

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

Global Instance combine_sep_as_fold_right_sep_con {prop:bi} (P: prop) (Q: list prop): CombineSepAs (fold_right_sepcon Q) (fold_right_sepcon [P]) (fold_right_sepcon $ P::Q).
Proof. rewrite /CombineSepAs. simpl. iSteps. Qed.

From iris.proofmode Require Import base coq_tactics reduction tactics string_ident.

(* select 2 different hyps that match pat1 and pat2 respectively *)
Tactic Notation "iSelect2" open_constr(pat1) open_constr(pat2) tactic1(tac) :=
lazymatch goal with
| |- context[ environments.Esnoc _ ?x pat1 ] =>
  lazymatch iTypeOf x with
  | Some (_,?T) => unify T pat1;
    match goal with
    | |- context[ environments.Esnoc ?Es ?y pat2 ] =>
      lazymatch iTypeOf y with
      | Some (_,?T) => (assert_fails (unify x y)); unify T pat2; tac x y
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
Typeclasses Opaque tc_environ.
Set Nested Proofs Allowed.

Global Instance combine_sep_as_PQR {Σ'} (Q: list localdef) R: CombineSepAs (SEPx R)
  (<affine> @local Σ' (foldr (liftx and) (liftx True%type) (map locald_denote Q)))
  (PROP () (LOCALx Q (SEPx R))).
Proof. rewrite /CombineSepAs /PROPx /LOCALx /SEPx. iIntros "($ & #$)". Qed.


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


Global Instance semax_mono: ∀ {OK_ty : Type} {Σ' : gFunctors} {VSTGS0 : VSTGS OK_ty Σ'} 
{OK_spec : ext_spec OK_ty} {CS : compspecs} (E : coPset) (Delta : tycontext),
  Proper (bi_entails ==> eq ==> equiv ==> flip impl)
         (semax E Delta).
Proof. intros. rewrite /Proper /respectful /flip /impl. intros ?????->??->. by apply ConseqFacts.semax_pre_simple. Qed.

Lemma add_PROPx : forall {Σ} Q R, (LOCALx Q (SEPx R) ⊣⊢ PROP ( ) @LOCALx Σ Q (SEPx R))%assert5.
Proof. intros. unfold PROPx; simpl. rewrite bi.True_and //. Qed.

Global Instance comine_sep_as_Delta_PQR {Σ'} P Q R Delta:
CombineSepAs (<affine> local (tc_environ Delta)) 
             (@PROPx _ Σ' P (LOCALx Q (SEPx R)))
             (local (tc_environ Delta) ∧ (PROPx P (LOCALx Q (SEPx R)))).
Proof. rewrite /CombineSepAs. rewrite -bi.persistent_and_affinely_sep_l. rewrite comm //. Qed.

Ltac from_ipm :=
  match goal with 
  | |- envs_entails _ (wp _ _ _ _) =>
      (* if goal is wp, Delta is already in wp and redundant *)
      iSelect (local (tc_environ _)) (fun x => iClear x)
  | _ => 
      (* otherwise, keep it, move to spatial context for merging *)
    idtac
  end;
  (* combine LOCALs, base case and then recurive case *)
  combine (local (liftx True%type)) (local (locald_denote _));
  repeat combine (local (foldr (liftx and) _ _)) (local (locald_denote _));
  (* combine SEPs *)
  repeat combine (SEPx _) (SEPx _);
  (* move LOCAL to spatial context, combine with SEP *)
  iSelect (local (foldr (liftx and) _ _ )) (fun x => iDestruct x as "-#?");
  combine (SEPx _) (<affine> local (foldr (liftx and) _ _ ));
  lazymatch goal with
  | |- envs_entails _ (wp _ _ _ _) => idtac
  | _ => iSelect (local (tc_environ _)) (fun x => iDestruct x as "-#?");
          combine (<affine> local (tc_environ _)) (PROPx _ _)
  end;
  iStopProof;
  lazymatch goal with
  | |- _ ⊢ wp _ _ _ _ =>
      rewrite -> ?wp_spec
  | _ => idtac
  end
  .

Typeclasses Opaque cptr_lock_inv.
(* TODO maybe write an instance for affine and ExclusiveProp? *)
Global Instance lock_prop_hint {prop:bi} (P:prop):
ExclusiveProp P ->
  HINT (empty_hyp_first) ✱ [-; emp] ⊫ [id] ; (<affine> (P ∗ P -∗ False))%assert5 ✱ [emp]. 
  Proof. rewrite empty_hyp_first_eq. unfold ExclusiveProp, SEPx, fold_right_sepcon. intros->. iSteps as "H". Qed.
Global Instance lock_prop_hint2 (P:mpred)  E:
ExclusiveProp P ->
  HINT (empty_hyp_first) ✱ [-; emp] ⊫ [id] ; (|={E}=> <affine> (P ∗ P -∗ False))%assert5 ✱ [emp]. 
  Proof. rewrite empty_hyp_first_eq. unfold ExclusiveProp, SEPx, fold_right_sepcon, BiAbd. simpl. intros.
    rewrite !bi.sep_emp.
    rewrite -(fupd_intro E _). rewrite H. iSteps. Qed.
(* TODO as a normalization step for calculating offset? make the thing in vint to vint (f ... g (some_nat)) *)
(* rewrite add_repr.
assert (Z.of_nat z + 1 = Z.of_nat (z + 1))%Z as -> by lia. *)

(* user decides which side *)

Global Instance ghost_auth_update g1 x n n':
    HINT (ghost_auth g1 x ∗ ghost_frag g1 n) ✱ [-; emp] ⊫ [bupd]; (ghost_frag g1 (n')%nat) ✱ [ghost_auth g1 (n')%nat].
Proof.
  iStep as "a f". iDestruct (ghost_var_inj with "[$a $f]") as %->.
  iMod (own_update_2 with "a f") as "($ & $)"; last done.
  apply @excl_auth_update.
Qed.

Lemma SEP_entails_SEP  {Σ'} {heap: heapGS Σ'} (R R': list (@mpred Σ' heap)):
  (fold_right_sepcon R ⊢ fold_right_sepcon R')
  -> SEPx R ⊢ @SEPx environ_index Σ' R'.
Proof.
  intros. iStartProof (@mpred Σ' heap). iIntros (i).
    unfold SEPx. rewrite H. iSteps. Qed.


Global Instance close_cinv_update_g1_hint (x1 x2 δx y z: nat) g1 g2 _c (gv:globals):
HINT field_at Ews t_counter (DOT _ctr) (Vint (Int.add (Int.repr (Z.of_nat z)) (Int.repr 1))) (gv _c) ✱ 
  [-; ghost_auth g1 x1 ∗ ghost_frag g1 x2 ∗ ghost_auth g2 y ∗ □⌜(Z.of_nat δx=1∧x1+y=z)%nat⌝ ]
  ⊫ [bupd]; cptr_lock_inv g1 g2 (gv _c) ✱ [□⌜(Z.of_nat δx=1∧x1+y=z)%nat⌝  ∗ ghost_frag g1 (x2+δx)].
Proof.
(* intros H; inversion H. *)
iStep as "●g1  ◯g1 ●g2 _ _ ctr". unfold cptr_lock_inv.
iDestruct (ghost_var_inj with "[$●g1 $◯g1]") as %<-.
iAssert (|==>ghost_auth g1 (x1+δx) ∗ ghost_frag g1 (x1+δx)) with "[●g1 ◯g1]" as "> [●g1 ◯g1]".
iMod (own_update_2 with "●g1 ◯g1") as "($ & $)"; last done.
apply @excl_auth_update.
rewrite add_repr. replace 1%Z with (Z.of_nat (Z.to_nat 1)) by lia. rewrite -Nat2Z.inj_add.
iFrame. iSteps.
Qed.

Lemma into_fold_right_sepcon_singleton : forall {Σ:gFunctors} (P: iProp Σ),
  P ⊣⊢ fold_right_sepcon [P].
Proof. intros. iSteps. Qed.

Ltac into_fold_right_sepcons Γs :=
lazymatch Γs with
|  Esnoc ?Γs' _ (fold_right_sepcon _) => idtac
|  Esnoc ?Γs' _ ?P => rewrite [(X in (Esnoc Γs' _ X))](into_fold_right_sepcon_singleton P);
                      into_fold_right_sepcons Γs'
| _ => idtac 
end.

(* assume in ipm, change every hyp in the sep context to "fold_right_sepcon [hyp]" *)
Ltac into_fold_right_sepcons_Γs :=
match goal with
| |- envs_entails (Envs _ ?Γs _) _ =>
  into_fold_right_sepcons Γs
end.


Lemma change_SEP `{!VSTGS unit Σ} E d P Q (R: list mpred) (R' R'': list mpred):
  (fold_right_sepcon R ⊢  |={E}=> fold_right_sepcon $ (R'++ R'')) ->
    local (tc_environ d) ∧ PROPx P $ LOCALx Q $ SEPx R ⊢ PROPx P $ LOCALx Q $ |={E}=> (SEPx $ R'++R'').
Proof. intros. go_lowerx. rewrite H //. Qed.
 (* TRIAL 2, try to prove directly *)

(* todo try and merge change_SEP, semax_pre_fupd and semax_pre_SEP_fupd *)
Lemma semax_change_pre_for_forward_call:
  forall {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} E Delta P Q R R' R'' c Post,
      (fold_right_sepcon R ⊢ |={E}=> fold_right_sepcon $ (R'++ R'')) ->
      @semax OK_ty Σ VSTGS0 Espec cs E Delta (PROPx P $ LOCALx Q $ SEPx (R'++R'')) c Post -> semax E Delta (PROPx P $ LOCALx Q $ SEPx R) c Post.
Proof.
intros until 1.
apply semax_pre_fupd. go_lowerx. rewrite H //.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.

  into_ipm; iSteps. 
  from_ipm.


  forward_call (sh, h, (cptr_lock_inv g1 g2 (gv _c))).

  (* should be able to do this automatically with a hint about command  *)
  unfold cptr_lock_inv at 2.
  Intros z x y.
  forward.
  forward.
  forward.




destruct left.
*

  (* forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)). *)

  (* lock_specs.release_spec mk_funspec *)


 (* from get_function_witness_type *)
 Ltac pose_witness_type (*ts*) Σ A witness :=
  (unify A (ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             exfalso)
 ||
 let TA := constr:(ofe_car (@dtfr Σ A)) in
  let TA' := eval cbv [dtfr dependent_type_functor_rec constOF idOF prodOF discrete_funOF
      ofe_morOF sigTOF list.listOF oFunctor_car ofe_car] in TA
 in let TA'' := eval simpl in TA'
  in match type of witness with ?T => 
       (unify T TA''; let ARG:=fresh "ARG" in pose witness as ARG)
      + (fail "Type of witness does not match type required by funspec WITH clause.
Witness value: " witness "
Witness type: " T "
Funspec type: " TA'')
     end.

  (* from prove_call_setup *)
 Ltac get_pre_sep_of_spec subsumes witness :=
 prove_call_setup1 subsumes
 ;
 [ .. | 
 match goal with |- @call_setup1 _ ?Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _  -> _ =>
 pose_witness_type (*ts*) Σ A witness
 end
 ]
 .


(* from forward_call i.e. new_fwd_call. *)
Ltac vstep_call :=
  try lazymatch goal with
        | |- semax _ _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
        end;
  repeat lazymatch goal with
    | |- semax _ _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
        rewrite <- seq_assoc
  end
  (* lazymatch goal with |- semax _ ?Delta _ (Ssequence ?C _) _ =>
    lazymatch C with context [Scall _ _ _] =>
           new_fwd_call'
      end
  end. *)
  .

Ltac change_pre_sep_with fpre_sep :=
eapply (semax_change_pre_for_forward_call _ _ _ _ _ fpre_sep);
[
cbn;
iSteps;
into_fold_right_sepcons_Γs;
repeat (combine (fold_right_sepcon _) (fold_right_sepcon _));
iStopProof; rewrite -fupd_intro; f_equal
| simpl app].

vstep_call.


prove_call_setup1 release_simple.

Ltac pose_ewitness Σ A :=
  (unify A (ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
              exfalso)
  ||
  let TA := constr:(ofe_car (@dtfr Σ A)) in
  let TA' := eval cbv [dtfr dependent_type_functor_rec constOF idOF prodOF discrete_funOF
      ofe_morOF sigTOF list.listOF oFunctor_car ofe_car] in TA in
  let TA'' := eval simpl in TA' in
  let ARG_TYPE := fresh "ARG_TYPE" in
  pose TA'' as ARG_TYPE
      .

match goal with |- @call_setup1 _ ?Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _  -> _ =>
pose_ewitness Σ A 
end.

Opaque lock_handle.

pose (nat, (bool, nat)) as ty.

From Ltac2 Require Import Ltac2.
Ltac2 rec evar_tuple (arg: constr) : constr :=
  lazy_match! arg with
  | prod ?a ?b =>
    let evar_a :=  (evar_tuple a) in
    let evar_b :=  (evar_tuple b) in 
    constr:(prod $evar_a $evar_b)
  | ?a =>
    let arg_i := Fresh.fresh (Fresh.Free.of_ids []) ident:(arg) in
    (ltac1:(a arg |- evar (arg: a)) (Ltac1.of_constr a) (Ltac1.of_ident arg_i));
    (Control.hyp arg_i)
  end.



Ltac2 rec evar_tuple (wit_ident: constr) : constr :=
  Message.print (Message.of_constr wit_ident);
  lazy_match! wit_ident with
  | prod ?a ?b =>
    Message.print (Message.of_string "a");
    let evar_a :=  (evar_tuple a) in
    let evar_b :=  (evar_tuple b) in 
    constr:(prod $evar_a $evar_b)
  | ?a =>
    Message.print (Message.of_string "b");
    let arg_i := Fresh.fresh (Fresh.Free.of_ids []) ident:(arg) in
    (ltac1:(a arg |- evar (arg: a)) (Ltac1.of_constr a) (Ltac1.of_ident arg_i));
    (Control.hyp arg_i)
  end.

  pose (1+1) as def.
  Ltac2 
  
  let setup := fresh "SETUP" in
  intro setup;
  destruct setup as [_  [Hsub _]];
match goal with | Hsub : (funspec_sub _ (mk_funspec _ _ _ _ ?fpre _)) |- _ =>
  match fpre with λne _ : ?arg_type, _ =>
  let arg_type := eval cbn in arg_type in
  idtac "arg_type is" arg_type;
  let arg_evar := ltac2:(evar_tuple (Option.get (Ltac1.to_constr ltac1val:(arg_type)))) in
  pose arg_evar
  end
end.
  (* let fpre1 := eval cbn in (fpre) in *)
  let fpre_name := fresh "fpre" in
  pose fpre as fpre_name end; clear Hsub.





  ltac2:(lazy_match! goal with | [fpre := λne _ : ?arg_type, _ |- _] =>
let bndr := Constr.Binder.make (Some ident:(witttt)) constr:(arg_type) in
           Message.print (Message.of_constr (Constr.Binder.type bndr)) end).
    pose ARG_TYPE as HH;
    ltac2:(evar_tuple @HH) end.
    idtac ARG_TYPE end.
    

ltac2: (Message.print (Message.of_constr  &ARG_TYPE1)).
ltac:(idtac ARG_TYPE1).
ltac2:(Constr.Binder.make (Some ident:(emm)) constr:(I)).



Ltac evar_tuple' A :=
  match A with
  | prod ?A ?B =>
    evar_tuple' A;
    evar_tuple' B
  | ?A =>
    let arg_i := fresh "arg" in
    evar (arg_i: A)
  end.
  lazymatch goal with | ARG_TYPE1 := ?X |- _ =>
    let x := evar_tuple' X in idtac x
  end.

pose (arg, arg0, arg1) as ARGS.
pose (fpre ARGS) as fpre'; simpl in fpre'.

match goal with | fpre' := context[SEPx ?fpre_sep] |- _ =>
  let fpre_sep_name := fresh "fpre_sep" in
  pose fpre_sep as fpre_sep_name
end.

eapply (semax_change_pre_for_forward_call _ _ _ _ _ fpre_sep).
-
  subst fpre_sep. subst arg. subst arg0. subst arg1.
cbn;
iSteps.
into_fold_right_sepcons_Γs.
repeat (combine (fold_right_sepcon _) (fold_right_sepcon _));
iStopProof. rewrite -fupd_intro; f_equal.
- simpl app.
 subst arg. subst arg0. subst arg1.  


match goal with | fpre := context[SEPx ?fpre_sep] |- _ =>
  change_pre_sep_with fpre_sep end.


get_pre_sep_of_spec release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)); simpl.


(* TODO give SETUP a new name *)
let SETUP := fresh "SETUP" in
intro SETUP; destruct SETUP as [_  [Hsub _]];
match goal with | Hsub : (funspec_sub _ (mk_funspec _ _ _ _ ?fpre _)) |- _ =>
  let fpre := eval cbn in (fpre ARG) in
  let fpre_name := fresh "fpre" in
  pose fpre as fpre_name end;
match goal with | fpre := context[SEPx ?fpre_sep] |- _ =>
  change_pre_sep_with fpre_sep end.

forward_call release_simple ARG.
entailer!!.

(* forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)). *)

forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)). entailer!!.

* 
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
