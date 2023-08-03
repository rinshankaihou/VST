(* Additional Axioms about the helper functions for int64 operations
   in ia32 backend. *)

(** The ia32 compiler backend introduces 
    helper functions / builtin functions for int64 operations. 
    Here we collect these builtin/helper functions in order to restrict external behaviours.
 *)
Require Import Coqlib AST Values Memory Globalenvs Events SplitLong ValRels.

Inductive i64ext : external_function -> Prop :=
| I64_negl: i64ext (EF_builtin "__builtin_negl" sig_l_l)
| I64_addl: i64ext (EF_builtin "__builtin_addl" sig_ll_l)
| I64_subl: i64ext (EF_builtin "__builtin_subl" sig_ll_l)
| I64_mull: i64ext (EF_builtin "__builtin_mull" sig_ii_l)                   
| I64_dtos: i64ext (EF_runtime "__i64_dtos" sig_f_l)
| I64_dtou: i64ext (EF_runtime "__i64_dtou" sig_f_l)
| I64_stod: i64ext (EF_runtime "__i64_stod" sig_l_f)
| I64_utod: i64ext (EF_runtime "__i64_utod" sig_l_f)
| I64_stof: i64ext (EF_runtime "__i64_stof" sig_l_s)
| I64_utof: i64ext (EF_runtime "__i64_utof" sig_l_s)
| I64_sdiv: i64ext (EF_runtime "__i64_sdiv" sig_ll_l)
| I64_udiv: i64ext (EF_runtime "__i64_udiv" sig_ll_l)
| I64_smod: i64ext (EF_runtime "__i64_smod" sig_ll_l)
| I64_umod: i64ext (EF_runtime "__i64_umod" sig_ll_l)
| I64_shl: i64ext (EF_runtime "__i64_shl" sig_li_l)
| I64_shr: i64ext (EF_runtime "__i64_shr" sig_li_l)
| I64_sar: i64ext (EF_runtime "__i64_sar" sig_li_l)
| I64_umulh: i64ext (EF_runtime "__i64_umulh" sig_ll_l)
| I64_smulh: i64ext (EF_runtime "__i64_smulh" sig_ll_l).

Axiom i64ext_effects:
  forall ef ge vargs m tr vres m',
    i64ext ef ->
    external_call ef ge vargs m tr vres m' ->
    m' = m /\ tr = E0.

Axiom i64ext_irr:
  forall ef ge vargs m vres ge' m',
    i64ext ef ->
    external_call ef ge vargs m E0 vres m ->
    external_call ef ge' vargs m' E0 vres m'.

Axiom i64ext_inject:
  forall F V ef (ge: Genv.t F V) vargs m vres j vargs' m',
    i64ext ef ->
    meminj_preserves_globals ge j ->
    external_call ef ge vargs m E0 vres m ->
    Mem.inject j m m' ->
    Val.inject_list j vargs vargs' ->
    exists vres',
      external_call ef ge vargs' m' E0 vres' m' /\
      Val.inject j vres vres'.


(** for defining AsmLang *)
Parameter i64ext_sem: external_function -> list val -> val -> Prop.

Axiom i64ext_extcall:
  forall ef args res,
    i64ext_sem ef args res <-> (i64ext ef /\ forall ge m, external_call ef ge args m E0 res m).

Axiom i64ext_args_related:
  forall ef j args res args',
    list_forall2 (val_related j) args args' ->
    i64ext_sem ef args res ->
    exists res', i64ext_sem ef args' res' /\ val_related j res res'.

Axiom i64ext_args_related':
  forall ef j args args' res',
    list_forall2 (val_related j) args args' ->
    i64ext_sem ef args' res' ->
    exists res, i64ext_sem ef args res /\ val_related j res res'.


Lemma i64ext_extcall_forall:
  forall ge m ef args res,
    i64ext ef ->
    external_call ef ge args m E0 res m ->
    (forall ge' m', external_call ef ge' args m' E0 res m').
Proof. intros. eapply i64ext_irr; eauto. Qed.

Lemma extcall_i64ext_sem:
  forall ge m ef args res,
    i64ext ef ->
    external_call ef ge args m E0 res m ->
    i64ext_sem ef args res.
Proof. intros. apply i64ext_extcall. split; auto. eapply i64ext_extcall_forall; eauto. Qed.

Lemma i64ext_det:
  forall ef ge args E0 res m E' res' m',
    i64ext ef ->
    external_call ef ge args m E0 res m ->
    external_call ef ge args m E' res' m' ->
    E0 = E' /\ m' = m /\ res = res'.
Proof.
  intros. exploit i64ext_effects; eauto. intros [ []]. subst.
  exploit i64ext_effects; try exact H0; eauto. intros [ []]. subst.
  split; auto. split; auto.
  pose proof (external_call_spec ef).
  destruct H2. exploit ec_determ. exact H0. exact H1.
  intros. tauto.
Qed.
