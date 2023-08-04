Require Import Values Footprint.


(** * Event and Trace *)

(** This file contains general definitions of event traces,
    with parameterized step relation *)

(** The labels of labelled transition system:
    - [tau]: silent steps
    - [sw]: thread switching steps, for the convenience of proof development
    - [evt]: event steps 
 *)

Inductive glabel : Type :=
| tau : glabel
| sw : glabel
| evt : val -> glabel.

Definition is_tau' (l: glabel) : Prop :=
  match l with
  | tau => True
  | _ => False
  end.
Lemma is_tau'_dec:
  forall l, {is_tau' l} + {~is_tau' l}.
Proof. intros; destruct l; simpl; auto. Qed.

(** Definition of event trace (bahavior) *)
CoInductive behav : Type :=
| Behav_done : behav
| Behav_abort : behav
| Behav_diverge : behav (* silently diverge *)
| Behav_cons : val -> behav -> behav.

Section Etrace.
  
  Context {State: Type}.
  Variable step: State -> glabel -> FP.t -> State -> Prop.
  Variable abort: State -> Prop.
  Variable final_state : State -> Prop.
  Variable thread_halt : State -> Prop.

  (** 0 or multiple steps *)
  Inductive star : State -> list glabel -> FP.t -> State -> Prop :=
  | star_refl: forall s, star s nil FP.emp s
  | star_step: forall s1 e fp1 s2 l fp2 s3,
      step s1 e fp1 s2 ->
      star s2 l fp2 s3 ->
      star s1 (e::l) (FP.union fp1 fp2) s3.
  
  (* Star step for non-evt steps *)
  Inductive non_evt_star : State -> FP.t -> State -> Prop :=
  | ne_star_refl: forall s,
      non_evt_star s FP.emp s
  | ne_star_step: forall s1 fp1 s2 fp2 s3,
      step s1 tau fp1 s2 \/ step s1 sw fp1 s2 ->
      non_evt_star s2 fp2 s3 ->
      non_evt_star s1 (FP.union fp1 fp2) s3
  .

  Inductive tau_plus: State -> FP.t -> State -> Prop :=
  | tau_plus_1: forall s fp s',
      step s tau fp s' ->
      tau_plus s fp s'
  | tau_plus_cons: forall s fp s' fp' s'',
      step s tau fp s' ->
      tau_plus s' fp' s'' ->
      tau_plus s (FP.union fp fp') s''.

  Inductive tau_N : nat -> State -> FP.t -> State -> Prop :=
  | tau_N_O: forall s, tau_N O s FP.emp s
  | tau_N_S: forall s fp s' n fp' s'',
      step s tau fp s' ->
      tau_N n s' fp' s'' ->
      tau_N (S n) s (FP.union fp fp') s''.

  Inductive tau_star: State -> FP.t -> State -> Prop :=
  | tau_star_0: forall s, tau_star s FP.emp s
  | tau_star_cons: forall s fp s' fp' s'',
      step s tau fp s' ->
      tau_star s' fp' s'' ->
      tau_star s (FP.union fp fp') s''.

  Lemma tau_star_tau_N_equiv:
    forall s fp s',
      (exists n, tau_N n s fp s') <-> tau_star s fp s'.
  Proof.
    split; intros.
    - destruct H as (n & HtauN).
      induction HtauN. constructor.
      econstructor; eauto.
    - induction H.
      exists O. constructor.
      destruct IHtau_star as (n & HtauN).
      exists (S n). econstructor; eauto.
  Qed.

  Lemma tau_N_cons : forall m n pc pc' pc'' fp fp',
      tau_N m pc fp pc' ->
      tau_N n pc' fp' pc'' ->
      tau_N (m+n) pc (FP.union fp fp') pc''.
  Proof.
    {
      intro m.
      induction m.
      + intros.
        inversion H;subst.
        rewrite FP.emp_union_fp.
        simpl;auto.
      + intros.
        inversion H;subst.
        eapply IHm  in H0;eauto.
        rewrite <- FP.fp_union_assoc.
        eapply tau_N_S;eauto.
    }
  Qed.
  Lemma tau_N_sub1: forall m pc pc1 fpu,
      tau_N (S m) pc fpu pc1 ->
      exists pc' fp fp',
        step pc tau fp pc' /\
        tau_N m pc' fp' pc1/\
        FP.union fp fp'=fpu.
  Proof.
    intros.
    inversion H;subst.
    exists s',fp,fp'.
    auto.
  Qed.
  Lemma tau_N_split:forall m n pc pc'' fpu,
      tau_N  (m+n) pc fpu pc'' ->
      exists pc' fp fp',
        tau_N m pc fp pc' /\ tau_N n pc' fp' pc'' /\ FP.union fp fp' = fpu.
  Proof.
      induction m,n.
      {
        intros.
        inversion H;clear H;subst.
        exists pc'',FP.emp,FP.emp.
        split;constructor;try apply fp_union_emp;constructor.
      }
      {
        intros.
        compute in H.
        exists pc,FP.emp,fpu.
        split;constructor;auto;try apply FP.emp_union_fp.
      }
      {
        intros.
        assert(L:S m = S m + 0);auto.
        destruct L.
        exists pc'',fpu,FP.emp.
        split;auto;split;try constructor;try apply FP.fp_union_emp.
      }
      {
        intros.
        specialize (IHm (S n)).
        assert(L:S (m + S n)= S m + S n). auto.
        destruct L.
        apply tau_N_sub1 in H.
        destruct H as[pc'[fp[fp'[N1[N2 union]]]]].
        apply IHm in N2.
        destruct N2 as[pc2[fp2[fp3[N3[N4 union2]]]]].
        eapply tau_N_S in N3;eauto.
        exists pc2,(FP.union fp fp2),fp3.
        split;auto.
        split;auto.
        rewrite <- union.
        rewrite <- union2.
        rewrite FP.fp_union_assoc.
        auto.
      }
    Qed.
    Lemma tau_star_cons': forall pc pc' pc'' fp fp',
        tau_star pc fp pc' ->
        tau_star pc' fp' pc'' ->
        tau_star pc (FP.union fp fp') pc''.
    Proof.
      {
        intros.
        rewrite <- tau_star_tau_N_equiv.
        rewrite <- tau_star_tau_N_equiv in H. rewrite <- tau_star_tau_N_equiv in H0.
        destruct H. destruct H0.
        eapply tau_N_cons in H0;eauto.
      }
    Qed.  
    Lemma tau_plus_tau_N_equiv:
      forall s s' fp,
        tau_plus s fp s' <-> (exists n, tau_N (S n) s fp s') .
    Proof.
      {
        split.
        +
          intro.
          induction H.
          -  exists 0. rewrite <- FP.fp_union_emp with(fp:=fp). econstructor 2;eauto. constructor.
          -  destruct IHtau_plus.
           exists (S x). econstructor 2;eauto.
        +
          intros. destruct H.
          generalize dependent s. generalize dependent s'. generalize dependent fp.
          induction x.
          -
            intros.
            assert(L:step s tau fp s').  inversion H. inversion H2. rewrite FP.fp_union_emp.   congruence.
            constructor;auto.
          -
            intros.
            inversion H. eapply IHx in H2. constructor 2 with(s':=s'0);auto.
      }
    Qed.    
    
    Lemma tau_star_plus : forall fp1 fp2 pc pc' pc'',
        tau_star pc fp1 pc' ->
        tau_plus pc' fp2 pc'' ->
        tau_plus pc (FP.union fp1 fp2) pc''.
    Proof.
      {
        intros.
        rewrite tau_plus_tau_N_equiv.
        rewrite tau_plus_tau_N_equiv  in H0.
        rewrite <- tau_star_tau_N_equiv in H.
        destruct H. destruct H0. exists (x+x0).
        assert(L:S(x + x0) = x + (S x0)). Omega.omega.
        rewrite L.
        eapply tau_N_cons;eauto.
      }
    Qed.
    Lemma tau_plus2star :forall fp1 pc pc',
      tau_plus pc fp1 pc'->
      tau_star pc fp1 pc'.
    Proof.
      {
        intros.
        rewrite tau_plus_tau_N_equiv in H.
        rewrite <- tau_star_tau_N_equiv.
        destruct H.
        exists (S x). auto.
      }
    Qed.
    Lemma tau_star_star : forall fp1 fp2 pc pc' pc'',
        tau_star pc fp1 pc' ->
        tau_star pc' fp2 pc'' ->
        tau_star pc (FP.union fp1 fp2) pc''.
    Proof.
      {
        intros.
        rewrite <- tau_star_tau_N_equiv in H.
        rewrite <- tau_star_tau_N_equiv.
        rewrite <- tau_star_tau_N_equiv in H0.
        destruct H. destruct H0.
        exists (x+ x0). eapply tau_N_cons;eauto.
      }
    Qed.

  
  (* Star sw step *)
  Inductive sw_star : State -> State -> Prop :=
  | sw_star_refl: forall s,
      sw_star s s
  | sw_star_cons: forall s1 s2 s3,
      step s1 sw FP.emp s2 ->
      sw_star s2 s3 ->
      sw_star s1 s3.
      

  (** Silent diverge is when there are infinite steps without event.
   We rule out the case of infinite switching by inserting a [tau] step in the definition. *)

  CoInductive silent_diverge : State -> Prop :=
  | Diverge : forall s s' fp' s'',
      sw_star s s' ->
      step s' tau fp' s'' ->
      silent_diverge s'' ->
      silent_diverge s.


  (** The event trace is constructed by these constructors
      - [Etr_done] : program terminates
      - [Etr_abort] : program abort
      - [Etr_diverge] : program silent diverge
      - [Etr_cons] : or a event step followed by other behaviors
   *)
  CoInductive Etr (state: State) : behav -> Prop :=
  | Etr_done :
      forall fp state',
        non_evt_star state fp state' ->
        final_state state' -> Etr state Behav_done
  | Etr_abort :
      forall fp state',
        non_evt_star state fp state' ->
        abort state' ->
        Etr state Behav_abort
  | Etr_diverge :
      silent_diverge state ->
      Etr state Behav_diverge
  | Etr_cons :
      forall fp state' v state'' B',
        non_evt_star state fp state' ->
        step state' (evt v) FP.emp state'' -> 
        Etr state'' B' ->
        Etr state (Behav_cons v B').

  Definition safe_state (s: State) : Prop :=
    forall l fp s',
      star s l fp s' -> ~ abort s'.
  
End Etrace.