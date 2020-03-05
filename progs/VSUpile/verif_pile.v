Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import pile.
Require Import spec_stdlib.
Require Import spec_pile.
Require Import spec_pile_private.

Section Pile_VSU.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p 
      /\ (p=nullval <-> sigma=nil)
       /\ Forall (Z.le 0) sigma).
Proof.
intros.
revert p; induction sigma; 
  unfold listrep; fold listrep; intros.
  entailer!; intuition.
Intros y. entailer!.
split.
split; intro. subst p. destruct H0; contradiction. discriminate.
constructor; auto. omega.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep; fold listrep;
 intros; entailer!; auto with valid_pointer.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma prep_local_facts:
  forall sigma p,
   prep sigma p |-- !! (isptr p /\ Forall (Z.le 0) sigma).
Proof.
intros.
unfold prep.
Intros q.
entailer!.
Qed.
Hint Resolve prep_local_facts : saturate_local.

Lemma prep_valid_pointer:
  forall sigma p,
   prep sigma p |-- valid_pointer p.
Proof. 
 intros.
 unfold prep. Intros x.
 entailer!; auto with valid_pointer.
Qed.
Hint Resolve prep_valid_pointer : valid_pointer.

Definition pilefreeable (p: val) : mpred :=
            malloc_token Ews tpile p.

Definition PILE: PilePredicates := Build_PilePredicates prep prep_local_facts prep_valid_pointer pilefreeable.

Definition PILEPRIV: PilePrivatePredicates := Build_PilePrivatePredicates PILE (eq_refl _).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       (LAMBDAx [gv] [Vint (Int.repr (sizeof t))]
       (SEP (mem_mgr gv)))
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

  Definition Pile_ASI: funspecs := PileASI PILE.

  Definition pile_imported_specs:funspecs := spec_stdlib.specs.

  Definition pile_internal_specs: funspecs := surely_malloc_spec::Pile_ASI.

  Definition PileVprog: varspecs. mk_varspecs prog. Defined.
  Definition PileGprog: funspecs := pile_imported_specs ++ pile_internal_specs.

Lemma body_surely_malloc: semax_body PileVprog PileGprog f_surely_malloc surely_malloc_spec.
Proof.
start_function.
forward_call (malloc_spec_sub t) gv.
Intros p.
if_tac.
{ subst.
  forward_if False.
  - forward_call 1. contradiction.
  - inv H2. }
forward_if True.
+ contradiction.
+ forward. entailer!.
+ forward. Exists p. entailer!.
Qed.

Lemma body_Pile_new: semax_body PileVprog PileGprog f_Pile_new (Pile_new_spec PILE).
Proof.
start_function.
forward_call (tpile, gv).
split3; simpl; auto; computable.
Intros p.
repeat step!.
simpl spec_pile.pilerep.
unfold prep, listrep, pile_freeable.
repeat step!.
Qed.

Lemma body_Pile_add: semax_body PileVprog PileGprog f_Pile_add (Pile_add_spec PILE).
Proof.
start_function.
forward_call (tlist, gv).
split3; simpl; auto; computable.
Intros q.
simpl spec_pile.pilerep; unfold prep.
Intros head.
forward.
forward.
forward.
forward.
simpl pilerep; unfold prep.
Exists q.
unfold listrep at 2; fold listrep.
Exists head.
entailer!.
Qed.

Lemma body_Pile_count: semax_body PileVprog PileGprog f_Pile_count (Pile_count_spec PILE).
Proof.
start_function.
simpl pilerep; unfold prep. Intros head.
forward.
unfold Sfor.
forward.
forward_loop (EX r:val, EX s2: list Z,
   PROP(0 <= sumlist s2 <= sumlist sigma)
   LOCAL(temp _c (Vint (Int.repr (sumlist sigma - sumlist s2)));
              temp _p p; temp _q r)
   SEP (data_at Ews tpile head p; 
          listrep s2 r -* listrep sigma head;
          listrep s2 r))%assert
   break: 
  (PROP()
   LOCAL(temp _c (Vint (Int.repr (sumlist sigma))); temp _p p)
   SEP (data_at Ews tpile head p; 
          listrep sigma head))%assert.
-
Exists head sigma.
entailer!. rewrite Z.sub_diag. auto.
apply wand_sepcon_adjoint. cancel.
-
Intros r s2.
forward_if (r<>nullval).
forward.
entailer!.
subst r.
forward.
entailer!.
assert (s2=nil) by intuition; subst s2.
simpl. rewrite Z.sub_0_r; auto.
sep_apply (modus_ponens_wand (listrep s2 nullval)).
cancel.
Intros.
destruct s2.
assert_PROP False; [ | contradiction]. {
 entailer!. assert (r=nullval) by intuition; subst r. congruence.
}
unfold listrep at 3; fold listrep.
Intros r'.
forward.
forward. {
 entailer!.
 simpl in H0.
 clear - H0 H H2 H9.
 rewrite (Int.signed_repr z) by rep_omega.
 rewrite (Int.signed_repr) by rep_omega.
 assert (0 <= sumlist s2). {
 clear - H9. induction s2; simpl; auto. omega.
 inv H9. apply IHs2 in H2. omega.
 }
 rep_omega.
}
forward.
Exists r' s2.
entailer!.
simpl. split.
simpl in H0.
 assert (0 <= sumlist s2). {
 clear - H9. induction s2; simpl; auto. omega.
 inv H9. apply IHs2 in H2. omega.
 }
 rep_omega.
 f_equal; f_equal; omega.
apply -> wand_sepcon_adjoint.
match goal with |- _ * ?A * ?B * ?C |-- _ => 
 assert (A * B * C |-- listrep(z::s2) r) end.
unfold listrep at 2; fold listrep. Exists r'. entailer!.
sep_apply H10.
sep_apply modus_ponens_wand.
auto.
 -
forward.
simpl pilerep; unfold prep.
Exists head.
cancel.
Qed.

Lemma body_Pile_free: semax_body PileVprog PileGprog f_Pile_free (Pile_free_spec PILE).
Proof.
start_function.
simpl pilerep; unfold prep. 
simpl pile_freeable. unfold pilefreeable. Intros head.
forward.
forward_while (EX q:val, EX s2: list Z,
   PROP ( )
   LOCAL (temp _q q; temp _p p; gvars gv)
   SEP (data_at Ews tpile head p; 
       listrep s2 q; malloc_token Ews tpile p;
   mem_mgr gv))%assert.
{ Exists head sigma; entailer!. }
{ entailer!. }
{ destruct s2.
   assert_PROP False; [|contradiction]. unfold listrep. entailer!.
  unfold listrep; fold listrep.
  Intros y.
  forward.
  forward_call (free_spec_sub (Tstruct _list noattr)) (q, gv).
  rewrite if_false by (intro; subst; contradiction).
  cancel.
  forward.
  Exists (y, s2).
  entailer!. cancel. }
subst.
assert_PROP (p<>nullval). entailer!.
forward_call (free_spec_sub (Tstruct _pile noattr))  (p, gv).
rewrite if_false by auto.
cancel.
forward.
rewrite (proj1 H0) by auto.
unfold listrep.
entailer!.
Qed.

  Definition PileComponent: @Component NullExtension.Espec PileVprog _ 
      nil pile_imported_specs prog Pile_ASI pile_internal_specs.
  Proof. 
    mkComponent.
    + solve_SF_internal body_surely_malloc.
    + solve_SF_internal body_Pile_new.
    + solve_SF_internal body_Pile_add.
    + solve_SF_internal body_Pile_count.
    + solve_SF_internal body_Pile_free.
  Qed.

  Definition PileVSU: @VSU NullExtension.Espec PileVprog _ 
      nil pile_imported_specs prog Pile_ASI.
  Proof. eexists; apply PileComponent. Qed.

  Definition PilePrivateComponent: @Component NullExtension.Espec PileVprog _ 
      nil pile_imported_specs prog (PilePrivateASI PILEPRIV) pile_internal_specs.
  Proof. 
    mkComponent.
    + solve_SF_internal body_surely_malloc.
    + solve_SF_internal body_Pile_new.
    + solve_SF_internal body_Pile_add.
    + solve_SF_internal body_Pile_count.
    + solve_SF_internal body_Pile_free.
  Qed.

Definition PilePrivateVSU: @VSU NullExtension.Espec PileVprog _ 
      nil pile_imported_specs prog (PilePrivateASI PILEPRIV).
  Proof. eexists; apply PileComponent. Qed.
End Pile_VSU.
