(* Inspired by:
   Subjective Auxiliary State for Coarse-Grained Concurrency, Ley-Wild and Nanevski, POPL 2013. *)

(* Require Import VST.concurrency.conclib. *)
(* Require Import VST.concurrency.lock_specs. *)
(* Require Import VST.atomics.SC_atomics. *)
(* Require Import VST.atomics.verif_lock. *)
Require Import iris_ora.algebra.frac_auth.
Require Import iris.algebra.numbers.
Require Import VST.zlist.sublist.
Require Import VST.progs64.incrN.

From diaframe Require Import defs.
From diaframe Require Import proofmode_base tactics.
From VST.vstep Require Import vstep ora_hints vst_hints.

Require Import VST.atomics.verif_lock_atomic.
Import LiftNotation.

Unset Universe Polymorphism.

Set Nested Proofs Allowed.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section proofs.

Context `{!VSTGS unit Σ, !cinvG Σ, !atomic_int_impl (Tstruct _atom_int noattr), !inG Σ (frac_authR natR)}.
(* #[local] Instance concurrent_ext_spec : ext_spec _ := concurrent_ext_spec _ (ext_link_prog prog). *)

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition ghost_ref n g := own g (●F n : frac_authR _).
Definition ghost_part sh n g := own g (◯F{sh} n : frac_authR _).
Definition ghost_both sh n1 n2 g := own g (●F n1 ⋅ ◯F{sh} n2 : frac_authR _).

Definition t_counter := Tstruct _counter noattr.

Definition cptr_lock_inv g ctr :=
  ∃ z : nat, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr (Z.of_nat z))) ctr ∗ ghost_ref z g.

Definition ctr_handle sh h g ctr n := lock_inv sh h (cptr_lock_inv g ctr) ∗ ghost_part sh n g.

Definition init_ctr_spec :=
 DECLARE _init_ctr
  WITH gv: globals
  PRE [ ]
         PROP  ()
         PARAMS ()
         GLOBALS (gv)
         SEP   (library.mem_mgr gv; data_at_ Ews t_counter (gv _c))
  POST [ tvoid ]
    ∃ h : lock_handle, ∃ g : gname,
         PROP ()
         LOCAL ()
         SEP (library.mem_mgr gv; ctr_handle 1 h g (gv _c) O;
              field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c)
              ).

Definition dest_ctr_spec :=
 DECLARE _dest_ctr
  WITH h : lock_handle, g : gname, v : nat, gv : globals
  PRE [ ]
         PROP  ()
         PARAMS ()
         GLOBALS (gv)
         SEP (field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c);
              ctr_handle 1 h g (gv _c) v)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (data_at Ews t_counter (vint (Z.of_nat v), ptr_of h) (gv _c)).

Definition incr_spec :=
 DECLARE _incr
  WITH sh1 : share, sh : Qp, h : lock_handle, g : gname, n : nat, gv: globals
  PRE [ ]
         PROP  (readable_share sh1)
         PARAMS ()
         GLOBALS (gv)
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
              ctr_handle sh h g (gv _c) n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
              ctr_handle sh h g (gv _c) (S n)).


Definition thread_lock_R sh1 sh g ctr lockc :=
  field_at sh1 t_counter [StructField _lock] (ptr_of lockc) ctr ∗ ctr_handle sh lockc g ctr 1%nat.

Definition thread_lock_inv sh1 tsh sh g ctr lockc lockt :=
  selflock (thread_lock_R sh1 sh g ctr lockc) tsh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * Qp * lock_handle * Qp * lock_handle * gname * globals
  PRE [ tptr tvoid ]
         let '(sh1, tsh, ht, sh, h, g, gv) := x in
         PROP  (readable_share sh1; ptr_of ht = y)
         PARAMS (y)
         GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); 
                ctr_handle sh h g (gv _c) O;
                lock_inv tsh ht (thread_lock_inv sh1 tsh sh g (gv _c) h ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  freelock_spec; spawn_spec; init_ctr_spec; dest_ctr_spec; incr_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_exclusive : forall lg p,
  exclusive_mpred (cptr_lock_inv lg p).
Proof.
  intros; unfold cptr_lock_inv.
  iIntros "((% & ? & ?) & (% & ? & ?))".
  rewrite !field_at_field_at_; iApply (field_at__conflict with "[$]"); auto.
  { simpl; lia. }
Qed.
#[local] Hint Resolve ctr_inv_exclusive : core.

Lemma thread_inv_exclusive : forall sh1 sh g p l,
  sh1 <> Share.bot -> exclusive_mpred (thread_lock_R sh1 sh g p l).
Proof.
  intros; unfold thread_lock_R.
  iIntros "((? & ? & ?) & (? & ? & ?))".
  rewrite !field_at_field_at_; iApply (field_at__conflict with "[$]"); auto.
  { simpl; lia. }
Qed.
#[local] Hint Resolve thread_inv_exclusive : core.

Lemma ctr_handle_share_join : forall sh1 sh2 h g ctr v1 v2,
  ctr_handle sh1 h g ctr v1 ∗ ctr_handle sh2 h g ctr v2 ⊣⊢ ctr_handle (sh1 ⋅ sh2) h g ctr (v1 + v2)%nat.
Proof.
  intros; unfold ctr_handle.
  rewrite -lock_inv_share_join /ghost_part frac_auth_frag_op own_op.
  apply bi.equiv_entails_2; cancel.
Qed.


Class TypeSizePositive c_type gfs :=
  type_size_positive : (0 < sizeof (nested_field_type c_type gfs))%Z.
Hint Extern 4 (TypeSizePositive _ _) => rewrite /TypeSizePositive //; lia : typeclass_instances.

Global Instance field_at_exclusive c_type gfs v1 v2 i:
TypeSizePositive c_type gfs ->
MergableConsume (field_at Ews c_type gfs v1 i) true
  (λ p Pin Pout,
    TCAnd (TCEq Pin $ field_at Ews c_type gfs v2 i) $
           TCEq Pout (False:mpred)).
Proof.
  intros.
  rewrite /MergableConsume => p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim field_at_conflict //=.
  auto.
Qed.



(* Global Definition split_struct_2_fields (cs:compspecs) c_def sh ct l v1 v2 vs i f1 f2 sh2 be ed :
  TCEq (PTree.get i cs.(cenv_cs)) (Some c_def) ->
  TCEq (co_members c_def) [f1; f2] ->
    (∃ v' : reptype ct,
    ∃ v1': reptype (nested_field_type ct (DOT name_member f1)),
    ∃ v2': reptype (nested_field_type ct (DOT name_member f2)),
    JMeq (v1, v2) v' ->
    JMeq v1 v1' ->
    JMeq v2 v2' -> 
(HINT data_at sh ct v' l ✱ [-; emp]
      ⊫ [id]; field_at sh ct (DOT (name_member f1)) v1' l ✱
    [spacer sh2 be ed vs ∗ field_at sh ct (DOT (name_member f2)) v2' l] )%I )%type. *)

    (* (reptype (nested_field_type t gfs)) *)




Class TCJMeq {A:Type} (a:A)  {B:Type} (b:B) := tcjmeq : @JMeq A a B b.
Example test_TCJMeq: TCJMeq (reptype (nested_field_type t_counter (DOT _ctr))) val.
Proof. Fail tc_solve. Abort.
Hint Extern 10 (TCJMeq _ _) => unfold TCJMeq; apply JMeq_refl : typeclass_instances.
Example test_TCJMeq: TCJMeq (reptype (nested_field_type t_counter (DOT _ctr))) val.
Proof. tc_solve. Qed.

Inductive TC_lia (P:Prop) : Prop :=  | tceq_lia  : P -> TC_lia P.
Existing Class TC_lia.
Global Hint Mode TC_lia + : typeclass_instances.
Hint Extern 10 (TC_lia _) => constructor; lia : typeclass_instances.
Example test_TC_lia: forall z:nat, TC_lia (0 <= Z.of_nat z)%Z.
Proof. intros. tc_solve. Qed.

Lemma eq_TCEq {A} (x y : A) : x = y -> TCEq x y.
Proof. intros ->. apply _. Qed.
Global Instance TCEq_find_z (z:Z) (n:nat) :
  TCEq n (Z.to_nat z) ->
  TC_lia (0 <= z)%Z ->
  TCEq (Z.of_nat n) z%Z.
Proof. intros -> H. inversion H. apply eq_TCEq. lia. Qed.

Global Instance TCJMeq_refl {A} (v:A): @TCJMeq A v A v.
Proof. tc_solve. Qed.
Global Instance TCJMeq_refl_vint (z1 z2:Z): TCEq z1 z2 -> TCJMeq (vint z1) (vint z2).
Proof. intros ->. tc_solve. Qed.
    
Global Instance field_at_unify_val sh t gfs (v1 v2: reptype (nested_field_type t gfs)) (v1' v2': val) l:
  TCJMeq v1 v1' ->
  TCEq v1' v2' ->
  TCJMeq v2 v2' ->
  HINT field_at sh t gfs v1 l ✱ [-; emp]
  ⊫ [id]; field_at sh t gfs v2 l ✱ [ emp ].
Proof. intros H1 -> H2. unfold TCJMeq in *. iSteps. 
       pose proof (JMeq_eq (JMeq_trans H1 (JMeq_sym H2))) as ->.
       iSteps.
Qed.

 Ltac2 Set vstep_specs as old_vstep_specs :=
  fun _ => 
           (constr:(_makelock), constr:(funspec_sub_refl_dep))::
           (constr:(_release), constr:(funspec_sub_refl_dep))::
           (constr:(_release), constr:(release_inv_deferred))::[]
           (* (constr:(_release), constr:(release_simple2)):: *)
           (* (constr:(_acquire), constr:(funspec_sub_refl_dep)):: *)
           (* (constr:(_spawn), constr:(funspec_sub_refl_dep)):: *)
           (* (old_vstep_specs ()) *)
           .

Lemma body_init_ctr: semax_body Vprog Gprog f_init_ctr init_ctr_spec.
Proof.

  ltac2:(vsteps ()).
  repeat EExists.
  entailer.
  ltac2:(aSteps ()).
  iStopProof. iStep as "a b c d".
 
  

  forward_call  (x).
  ghost_alloc (ghost_both 1 O O).
  { by apply frac_auth_valid. }
  Intros g.
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv g (gv _c)).
  Intros h.
  forward.
  forward.
  forward_call release_simple (1%Qp, h, cptr_lock_inv g (gv _c)).
  {
    iStep.
    iSplitL.
    - iSplitR.
      + iModIntro.  iSteps.
      +
        ltac2:(aSteps ()).

Qed.



Require Import Coq.Program.Equality.
Lemma body_dest_ctr: semax_body Vprog Gprog f_dest_ctr dest_ctr_spec.
Proof.
  ltac2:(vstep ()).
  ltac2:(vstep ()).
  entailer.
  iSteps.
  
  
  Search is_pointer_or_null.
  apply isptr_is_pointer_or_null. 
  
  unfold isptr. destruct h. subst.
  destruct p.  simpl. unfold ptr_of.  simp simpl. done. (left is_pointer_or_null_dec) auto.
  unfold ctr_handle. Intros.
  ltac2:(vsteps ()).
  
  start_function.
  unfold ctr_handle; Intros.
  forward.
  forward_call (1%Qp, h, cptr_lock_inv g (gv _c)).
  forward.
  forward_call freelock_simple (h, cptr_lock_inv g (gv _c)).
  { lock_props; cancel. }
  unfold cptr_lock_inv.
  Intros z.
  entailer!.
  iIntros "(? & ref & ? & ? & part)".
  iDestruct (own_valid_2 with "ref part") as %Hv%frac_auth_agree.
  inv Hv.
  unfold_data_at (data_at _ _ _ _); iFrame.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  unfold ctr_handle; Intros.
  forward.
  forward_call (sh, h, cptr_lock_inv g (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  forward.
  gather_SEP (ghost_part _ _ _) (ghost_ref _ _).
  viewshift_SEP 0 (ghost_part sh (S n) g ∗ ghost_ref (S z) g).
  { go_lowerx.
    iIntros "((part & ref) & _)".
    iMod (own_update_2 with "ref part") as "($ & $)"; last done.
    apply frac_auth_update, nat_local_update; lia. }
  Intros; forward_call release_simple (sh, h, cptr_lock_inv g (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists (S z).
    rewrite Nat2Z.inj_succ.
    entailer!. }
  forward.
  unfold ctr_handle; cancel.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh1, sh, h, g, O, gv).
  forward_call release_self (tsh, ht, thread_lock_R sh1 sh g (gv _c) h).
  { lock_props.
    unfold thread_lock_inv, selflock, thread_lock_R; cancel. }
  forward.
Qed.

Local Open Scope Z.

Definition N := 5.
Definition N_frac := (/ pos_to_Qp (Z.to_pos (N + 1)))%Qp.

Global Instance namespace_inhabitant : Inhabitant namespace := nroot.

Opaque Qp.div Qp.mul.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  fold N.
  sep_apply (library.create_mem_mgr gv).
  forward_call gv.
  Intros x; destruct x as (h, g); simpl.
  (* need to split off shares for the locks and ghost here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  destruct (split_shares (Z.to_nat N) Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  rewrite -> Z2Nat.id in * by (unfold N; lia).
  assert_PROP (field_compatible (tarray (tptr t_lock) N) [] v_thread_lock) by entailer!.
  assert (N <= Int.max_signed) by computable.
  forward_for_simple_bound N (∃ i : Z, ∃ sh : share, ∃ ll : list lock_handle,
    PROP (sepalg_list.list_join sh0 (sublist i N shs) sh;
          Zlength ll = i; Forall isptr (map ptr_of ll))
    LOCAL (lvar _thread_lock (tarray (tptr t_lock) N) v_thread_lock; gvars gv)
    SEP (library.mem_mgr gv; field_at sh t_counter (DOT _lock) (ptr_of h) (gv _c);
         spacer Ews 4 8 (gv _c); ctr_handle (pos_to_Qp (Z.to_pos (N - i + 1)) * N_frac)%Qp h g (gv _c) O;
         [∗ list] j ∈ seq 0 (Z.to_nat i), lock_inv (1/2) (Znth (Z.of_nat j) ll)
           (thread_lock_inv (Znth (Z.of_nat j) shs) (1/2) N_frac g (gv _c) h (Znth (Z.of_nat j) ll));
         data_at Tsh (tarray (tptr t_lock) N) (map ptr_of ll ++ repeat Vundef (Z.to_nat (N - i))) v_thread_lock; has_ext tt))%assert.
  { Exists Ews (@nil lock_handle).
    rewrite -> !sublist_same by auto; rewrite Qp.mul_inv_r; entailer!. }
  { (* first loop *)
    forward_call (gv, fun ht => thread_lock_inv (Znth i shs) (1/2) N_frac g (gv _c) h ht).
    Intros ht.
    forward.
    assert_PROP (0 <= i < Zlength (map ptr_of ll ++ repeat Vundef (Z.to_nat (N - i)))) as Hi.
    { entailer!. rewrite -> Zlength_app, Zlength_map, Zlength_repeat, Zplus_minus by lia; auto. }
    forward.
    { rewrite -> upd_Znth_same by auto; entailer!. }
    rewrite -> upd_Znth_same by auto.
    assert (readable_share (Znth (Zlength ll) shs)) as Hshi by (apply Forall_Znth; auto; lia).
    rewrite -> sublist_next in H7 by lia; inv H7.
    destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H13) H15) as (sh' & ? & Hsh').
    sep_apply lock_inv_isptr; Intros.
    forward_spawn _thread_func (ptr_of ht) (Znth (Zlength ll) shs, (1/2)%Qp, ht, N_frac, h, g, gv).
    { rewrite -{1}Qp.half_half -frac_op -lock_inv_share_join.
      erewrite <- field_at_share_join; try apply Hsh'.
      replace (pos_to_Qp (Z.to_pos _)) with (1 + pos_to_Qp (Z.to_pos (N - Zlength ll)))%Qp.
      rewrite Qp.mul_add_distr_r Qp.mul_1_l -frac_op.
      rewrite -(ctr_handle_share_join _ _ _ _ _ O O).
      entailer!.
      { rewrite -> (Z2Pos.inj_add _ 1) by lia.
        rewrite !pos_to_Qp_add; f_equal; lia. } }
    { simpl; auto. }
    Exists sh' (ll ++ [ht]); entailer!.
    { split; [autorewrite with sublist; auto | rewrite map_app Forall_app; repeat constructor; auto]. }
    rewrite !sep_assoc; apply bi.sep_mono.
    - unfold ctr_handle.
      replace (Z.to_pos (N - (Zlength ll + 1) + 1)) with (Z.to_pos (N - Zlength ll)) by lia; cancel.
      rewrite -> Z2Nat.inj_add by lia. rewrite Nat.add_comm seq_S big_sepL_app /=.
      rewrite -> Z2Nat.id, app_Znth2, Zminus_diag, Znth_0_cons by (tauto || lia); cancel.
      rewrite Zlength_correct Nat2Z.id; apply big_sepL_mono; intros ?? (-> & ?)%lookup_seq.
      assert (Z.of_nat k < Zlength ll) by (rewrite Zlength_correct; apply inj_lt; auto).
      rewrite app_Znth1 //.
    - rewrite -> upd_complete_gen' by tauto; autorewrite with sublist; apply derives_refl. }
  rewrite !sublist_nil Zminus_diag; Intros shx ll.
  inv H6.
  forward_for_simple_bound N (∃ i : Z, ∃ sh : share,
    PROP (sepalg_list.list_join shx (sublist 0 i shs) sh)
    LOCAL (lvar _thread_lock (tarray (tptr t_lock) N) v_thread_lock; gvars gv)
    SEP (library.mem_mgr gv; field_at sh t_counter (DOT _lock) (ptr_of h) (gv _c);
         spacer Ews 4 8 (gv _c); ctr_handle (pos_to_Qp (Z.to_pos (i + 1)) * N_frac)%Qp h g (gv _c) (Z.to_nat i);
         [∗ list] j ∈ seq (Z.to_nat i) (Z.to_nat N - Z.to_nat i), lock_inv (1/2) (Znth (Z.of_nat j) ll)
           (thread_lock_inv (Znth j shs) (1/2) N_frac g (gv _c) h (Znth j ll));
         data_at Tsh (tarray (tptr t_lock) N) (map ptr_of ll) v_thread_lock; has_ext tt))%assert.
  { rewrite -> !sublist_nil, app_nil_r by (auto; lia).
    Exists shx; entailer!.
    { constructor. }
    apply derives_refl. }
  { (* second loop *)
    forward.
    { entailer!. apply isptr_is_pointer_or_null, Forall_Znth; auto.
      rewrite Zlength_map; simpl in *; replace (Zlength ll) with N; auto. }
    Opaque N.
    destruct (Z.to_nat N - Z.to_nat i)%nat eqn: Hsub; [lia|].
    rewrite -cons_seq /= Z2Nat.id; last lia.
    forward_call ((1/2)%Qp, Znth i ll, thread_lock_inv (Znth i shs) (1/2) N_frac g (gv _c) h (Znth i ll)).
    { rewrite -> Znth_map by (simpl in *; lia); entailer!. }
    { cancel. }
    unfold thread_lock_inv at 2; unfold thread_lock_R, selflock; Intros.
    forward.
    unfold thread_lock_inv.
    forward_call freelock_self ((1/2)%Qp, (1/2)%Qp, Znth i ll, thread_lock_R (Znth i shs) N_frac g (gv _c) h).
    { rewrite -> Znth_map by (simpl in *; lia); entailer!. }
    { unfold selflock; cancel. }
    { apply Qp.half_half. }
    erewrite <- sublist_same with (al := shs) in Hshs by eauto.
    rewrite -> sublist_split with (mid := i) in Hshs by lia.
    rewrite -> sublist_next with (i := i) in Hshs by lia.
    rewrite app_cons_assoc in Hshs.
    apply sepalg_list.list_join_unapp in Hshs as (sh' & Hshs1 & ?).
    apply sepalg_list.list_join_unapp in Hshs1 as (? & J & J1).
    apply sepalg_list.list_join_eq with (c := sh) in J; auto; subst.
    rewrite <- sepalg_list.list_join_1 in J1.
    rewrite -> !(sublist_split 0 i (i + 1)), !sublist_len_1 by lia.
    Exists sh'; entailer!.
    { eapply sepalg_list.list_join_app; eauto; econstructor; eauto; constructor. }
    unfold thread_lock_R.
    rewrite -(field_at_share_join _ _ sh') //.
    replace (pos_to_Qp (Z.to_pos (i + 1 + 1))) with (pos_to_Qp (Z.to_pos (i + 1)) + 1)%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l -frac_op Z2Nat.inj_add; [|lia..].
    rewrite -ctr_handle_share_join Nat.add_comm /=.
    replace (Z.to_nat N - S (Z.to_nat i))%nat with n by lia.
    cancel; apply derives_refl.
    { rewrite pos_to_Qp_add; f_equal; lia. } }
  Intros sh'.
  eapply sepalg_list.list_join_eq in Hshs; [|erewrite <- (sublist_same 0 N shs) by auto; eauto].
  subst.
  rewrite Nat.sub_diag Qp.mul_inv_r.
  forward_call (h, g, Z.to_nat N, gv).
  forward.
  rewrite -> Z2Nat.id by auto.
  (* We've proved that t is N! *)
  forward.
  { repeat sep_apply data_at_data_at_; cancel. }
Qed.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl.
  destruct x.
  unfold PROPx, LOCALx, SEPx, local, lift1; monPred.unseal; simpl; unfold_lift; Intros h.
  destruct ret; unfold eval_id in H0; simpl in H0; subst; simpl; [|contradiction].
  saturate_local; apply bi.pure_intro; auto. }
do 4 semax_func_cons_ext.
semax_func_cons body_init_ctr.
semax_func_cons body_dest_ctr.
semax_func_cons body_incr.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.

End proofs.
