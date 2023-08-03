Require Import BoolEqual Coqlib AST Integers Floats Values Memory Globalenvs Events.
Set Implicit Arguments.

Require Import Op.

Require Import Footprint Memory MemOpFP ValFP VundefInj.

Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.

(** * Evaluation functions footprint *)

(** Evaluation of conditions, operators and addressing modes applied
  to lists of values.  Return [None] when the computation can trigger an
  error, e.g. integer division by zero.  [eval_condition] returns a boolean,
  [eval_operation] and [eval_addressing] return a value. *)
Definition eval_condition_fp (cond: condition) (vl: list val) (m: mem): option footprint :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => if Val.cmp_bool c v1 v2 then Some empfp else None
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool_fp m c v1 v2
  | Ccompimm c n, v1 :: nil => if Val.cmp_bool c v1 (Vint n) then Some empfp else None
  | Ccompuimm c n, v1 :: nil => cmpu_bool_fp m c v1 (Vint n)
  | Ccompl c, v1 :: v2 :: nil => if Val.cmpl_bool c v1 v2 then Some empfp else None
  | Ccomplu c, v1 :: v2 :: nil => cmplu_bool_fp m c v1 v2
  | Ccomplimm c n, v1 :: nil => if Val.cmpl_bool c v1 (Vlong n) then Some empfp else None
  | Ccompluimm c n, v1 :: nil => cmplu_bool_fp m c v1 (Vlong n)
  | Ccompf c, v1 :: v2 :: nil => if Val.cmpf_bool c v1 v2 then Some empfp else None
  | Cnotcompf c, v1 :: v2 :: nil =>
    if option_map negb (Val.cmpf_bool c v1 v2) then Some empfp else None
  | Ccompfs c, v1 :: v2 :: nil => if Val.cmpfs_bool c v1 v2 then Some empfp else None
  | Cnotcompfs c, v1 :: v2 :: nil =>
    if option_map negb (Val.cmpfs_bool c v1 v2) then Some empfp else None
  | Cmaskzero n, v1 :: nil => if Val.maskzero_bool v1 n then Some empfp else None
  | Cmasknotzero n, v1 :: nil => if option_map negb (Val.maskzero_bool v1 n) then Some empfp else None
  | _, _ => None
  end.

Lemma eval_condition_eval_condition_fp:
  forall cond vl m v,
    eval_condition cond vl m = Some v ->
    exists fp, eval_condition_fp cond vl m = Some fp.
Proof.
  destruct cond; intros; inv H; FuncInv; simpl;
    try match goal with H: _ = Some _ |- _ => rewrite H; eauto end.
  eapply cmpu_bool_cmpu_bool_fp; eauto.
  eapply cmpu_bool_cmpu_bool_fp; eauto.
  eapply cmplu_bool_cmplu_bool_fp; eauto.
  eapply cmplu_bool_cmplu_bool_fp; eauto.
Qed.

(** TODO: move to Op_fp *)
Lemma eval_condition_fp_negate:
  forall cond vl m fp,
    eval_condition_fp cond vl m = Some fp ->
    eval_condition_fp (negate_condition cond) vl m = Some fp.
Proof.
  clear. destruct cond; simpl; do 2 (destruct vl; auto); try (destruct vl; auto); intro m.
  destruct c, v, v0; auto.
  destruct c, v, v0; auto.
  destruct c, v; auto.
  destruct c, v; auto.
  destruct c, v, v0; auto.
  destruct c, v; auto.
  destruct c, v, v0; auto.
  destruct c, v, v0; auto.
  destruct c, v, v0; auto.
  destruct c, v, v0; auto.
  destruct (Val.maskzero_bool v n); auto.
  destruct (Val.maskzero_bool v n); auto.
Qed.

  
Definition eval_operation_fp
           (F V: Type) (genv: Genv.t F V) (sp: val)
           (op: operation) (vl: list val) (m: mem): option footprint :=
  match op, vl with
  | Omove, v1::nil => Some empfp
  | Ointconst n, nil => Some empfp
  | Olongconst n, nil => Some empfp
  | Ofloatconst n, nil => Some empfp
  | Osingleconst n, nil => Some empfp
  | Oindirectsymbol id, nil => Some empfp
  | Ocast8signed, v1 :: nil => Some empfp
  | Ocast8unsigned, v1 :: nil => Some empfp
  | Ocast16signed, v1 :: nil => Some empfp
  | Ocast16unsigned, v1 :: nil => Some empfp
  | Oneg, v1::nil => Some empfp
  | Osub, v1::v2::nil => Some empfp
  | Omul, v1::v2::nil => Some empfp
  | Omulimm n, v1::nil => Some empfp
  | Omulhs, v1::v2::nil => Some empfp
  | Omulhu, v1::v2::nil => Some empfp
  | Odiv, v1::v2::nil => if Val.divs v1 v2 then Some empfp else None
  | Odivu, v1::v2::nil => if Val.divu v1 v2 then Some empfp else None
  | Omod, v1::v2::nil => if Val.mods v1 v2 then Some empfp else None
  | Omodu, v1::v2::nil => if Val.modu v1 v2 then Some empfp else None
  | Oand, v1::v2::nil => Some empfp
  | Oandimm n, v1::nil => Some empfp
  | Oor, v1::v2::nil => Some empfp
  | Oorimm n, v1::nil => Some empfp
  | Oxor, v1::v2::nil => Some empfp
  | Oxorimm n, v1::nil => Some empfp
  | Onot, v1::nil => Some empfp
  | Oshl, v1::v2::nil => Some empfp
  | Oshlimm n, v1::nil => Some empfp
  | Oshr, v1::v2::nil => Some empfp
  | Oshrimm n, v1::nil => Some empfp
  | Oshrximm n, v1::nil => if Val.shrx v1 (Vint n) then Some empfp else None
  | Oshru, v1::v2::nil => Some empfp
  | Oshruimm n, v1::nil => Some empfp
  | Ororimm n, v1::nil => Some empfp
  | Oshldimm n, v1::v2::nil => Some empfp
  | Olea addr, _ => if eval_addressing32 genv sp addr vl then Some empfp else None
  | Omakelong, v1::v2::nil => Some empfp
  | Olowlong, v1::nil => Some empfp
  | Ohighlong, v1::nil => Some empfp
  | Ocast32signed, v1 :: nil => Some empfp
  | Ocast32unsigned, v1 :: nil => Some empfp
  | Onegl, v1::nil => Some empfp
  | Oaddlimm n, v1::nil => Some empfp
  | Osubl, v1::v2::nil => Some empfp
  | Omull, v1::v2::nil => Some empfp
  | Omullimm n, v1::nil => Some empfp
  | Omullhs, v1::v2::nil => Some empfp
  | Omullhu, v1::v2::nil => Some empfp
  | Odivl, v1::v2::nil => if Val.divls v1 v2 then Some empfp else None
  | Odivlu, v1::v2::nil => if Val.divlu v1 v2 then Some empfp else None
  | Omodl, v1::v2::nil => if Val.modls v1 v2 then Some empfp else None
  | Omodlu, v1::v2::nil => if Val.modlu v1 v2 then Some empfp else None
  | Oandl, v1::v2::nil => Some empfp
  | Oandlimm n, v1::nil => Some empfp
  | Oorl, v1::v2::nil => Some empfp
  | Oorlimm n, v1::nil => Some empfp 
  | Oxorl, v1::v2::nil => Some empfp
  | Oxorlimm n, v1::nil => Some empfp
  | Onotl, v1::nil => Some empfp
  | Oshll, v1::v2::nil => Some empfp
  | Oshllimm n, v1::nil => Some empfp
  | Oshrl, v1::v2::nil => Some empfp
  | Oshrlimm n, v1::nil => Some empfp
  | Oshrxlimm n, v1::nil => if Val.shrxl v1 (Vint n) then Some empfp else None
  | Oshrlu, v1::v2::nil => Some empfp
  | Oshrluimm n, v1::nil => Some empfp
  | Ororlimm n, v1::nil => Some empfp
  | Oleal addr, _ => if eval_addressing64 genv sp addr vl then Some empfp else None
  | Onegf, v1::nil => Some empfp
  | Oabsf, v1::nil => Some empfp
  | Oaddf, v1::v2::nil => Some empfp
  | Osubf, v1::v2::nil => Some empfp
  | Omulf, v1::v2::nil => Some empfp
  | Odivf, v1::v2::nil => Some empfp
  | Onegfs, v1::nil => Some empfp
  | Oabsfs, v1::nil => Some empfp
  | Oaddfs, v1::v2::nil => Some empfp
  | Osubfs, v1::v2::nil => Some empfp
  | Omulfs, v1::v2::nil => Some empfp
  | Odivfs, v1::v2::nil => Some empfp
  | Osingleoffloat, v1::nil => Some empfp
  | Ofloatofsingle, v1::nil => Some empfp
  | Ointoffloat, v1::nil => if Val.intoffloat v1 then Some empfp else None
  | Ofloatofint, v1::nil => if Val.floatofint v1 then Some empfp else None
  | Ointofsingle, v1::nil => if Val.intofsingle v1 then Some empfp else None
  | Osingleofint, v1::nil => if Val.singleofint v1 then Some empfp else None
  | Olongoffloat, v1::nil => if Val.longoffloat v1 then Some empfp else None
  | Ofloatoflong, v1::nil => if Val.floatoflong v1 then Some empfp else None
  | Olongofsingle, v1::nil => if Val.longofsingle v1 then Some empfp else None
  | Osingleoflong, v1::nil => if Val.singleoflong v1 then Some empfp else None
  | Ocmp c, _ => eval_condition_fp c vl m
  | _, _ => None
  end.


Lemma op_depends_on_memory_footprint_emp:
  forall (F V: Type) (ge: Genv.t F V) sp op args m fp,
    op_depends_on_memory op = false ->
    eval_operation_fp ge sp op args m = Some fp ->
    fp = empfp.
Proof.
  intros until fp.
  destruct op; simpl; FuncInv; intros SF H; FuncInv; auto;
    try (match goal with
         | H: context[match ?x with _ => _ end] |- _ =>
           destruct x eqn:?; inv H; auto
         end; fail).
  destruct cond; simpl in H; FuncInv;
      try (match goal with
         | H: context[match ?x with _ => _ end] |- _ =>
           destruct x eqn:?; inv H; auto
           end; fail).
  unfold cmpu_bool_fp in H. rewrite negb_false_iff in SF. rewrite SF in H. destruct v, v0; inv H; auto.
  unfold cmpu_bool_fp in H. rewrite negb_false_iff in SF. rewrite SF in H. destruct v; inv H; auto.
  unfold cmplu_bool_fp in H. rewrite SF in H. simpl in H. destruct v, v0; inv H; auto.
  unfold cmplu_bool_fp in H. rewrite SF in H. simpl in H. destruct v; inv H; auto.  
Qed.

Lemma op_depends_on_memory_footprint_correct:
    forall (F V: Type) (ge: Genv.t F V) sp op args m1 m2,
    op_depends_on_memory op = false ->
    eval_operation_fp ge sp op args m1 = eval_operation_fp ge sp op args m2.
Proof.
  intros until m2. destruct op; simpl; try congruence.
  destruct cond; simpl; intros SF; auto; rewrite ? negb_false_iff in SF;
    unfold eval_condition_fp, cmplu_bool_fp, cmpu_bool_fp; rewrite SF; reflexivity.
Qed.

(** Global variables mentioned in an operation or addressing mode *)


(** * Invariance and compatibility properties. *)

(** [eval_operation] and [eval_addressing] depend on a global environment
  for resolving references to global symbols.  We show that they give
  the same results if a global environment is replaced by another that
  assigns the same addresses to the same symbols. *)

Section GENV_TRANSF.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Hypothesis agree_on_symbols:
  forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.

Lemma eval_operation_fp_preserved:
  forall sp op vl m,
  eval_operation_fp ge2 sp op vl m = eval_operation_fp ge1 sp op vl m.
Proof.
  intros.
  unfold eval_operation_fp; destruct op; auto using eval_addressing32_preserved, eval_addressing64_preserved.
  erewrite eval_addressing32_preserved; eauto.
Qed.

End GENV_TRANSF.

(** Compatibility of the evaluation functions with value injections. *)

Section EVAL_COMPAT.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable f: meminj.

Variable m1: mem.
Variable m2: mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Ltac InvInject :=
  match goal with
  | [ H: Val.inject _ (Vint _) _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject _ (Vfloat _) _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject _ (Vptr _ _) _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject_list _ nil _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject_list _ (_ :: _) _ |- _ ] =>
      inv H; InvInject
  | _ => idtac
  end.

Ltac TrivialReduce :=
  match goal with
  | H: context[match ?x with _ => _ end] |- _ =>
    destruct x eqn:?; inv H
  | H: ?x = _ |- context[match ?x with _ => _ end] => rewrite H
  end.

(******** this point *)
(** We need a definition describing footprint "inject" *)
Require Import Blockset Injections FMemOpFP MemOpFP InjRels.

(* ls' subset of f(ls) *)

Inductive loc_inject (f: meminj) (ls ls': locset) : Prop :=
  Loc_inject:
    (forall b ofs,
        Locs.belongsto ls' b ofs ->
        exists b0 ptrofs0 delta,
          f b0 = Some (b, delta) /\
          (** restrict ofs to be Int32 representable..., or a -1 offset generated by weak_valid_pointer... *)
          ((ofs = Ptrofs.unsigned (Ptrofs.add ptrofs0 (Ptrofs.repr delta)) /\
           Locs.belongsto ls b0 (Ptrofs.unsigned ptrofs0))
           \/
           (ofs = Ptrofs.unsigned (Ptrofs.add ptrofs0 (Ptrofs.repr delta)) - 1 /\
            Locs.belongsto ls b0 (Ptrofs.unsigned ptrofs0 - 1))
          ))
    -> loc_inject f ls ls'.

Record fp_inject (f: meminj) (fp fp': footprint) :=
  {
    cmp_inject: loc_inject f (FP.cmps fp) (FP.cmps fp');
    read_inject: loc_inject f (FP.reads fp) (FP.reads fp');
    write_inject: loc_inject f (FP.writes fp) (FP.writes fp');
    free_match: loc_inject f (FP.frees fp) (FP.frees fp');
  }.

Lemma loc_inject_emp:
  forall f ls, loc_inject f ls Locs.emp.
Proof.
  clear. intros. constructor. intros. inv H.
Qed.

Lemma fp_inject_emp:
  forall f fp, fp_inject f fp empfp.
Proof.
  clear. intros. constructor; eapply loc_inject_emp.
Qed.

Lemma loc_inject_union_s:
  forall f ls1 ls1' ls2,
    loc_inject f ls1 ls1' -> loc_inject f (Locs.union ls1 ls2) ls1'.
Proof.
  clear; intros. inv H. constructor.
  intros. apply H0 in H. destruct H as (? & ? & ? & ? & [[? ?]|[? ?]]); exists x, x0, x1; split; auto.
  left. split; auto. Locs.unfolds. rewrite H2. auto.
  right. split; auto. Locs.unfolds. rewrite H2. auto.  
Qed.

Lemma loc_inject_union_t:
  forall f ls ls1' ls2',
    loc_inject f ls ls1' -> loc_inject f ls ls2' -> loc_inject f ls (Locs.union ls1' ls2').
Proof.
  clear; intros. constructor; intros.
  Locs.unfolds. rewrite orb_true_iff in H1. destruct H1; [apply H|apply H0]; auto.
Qed.

Lemma fp_inject_union_s:
  forall f fp1 fp1' fp2,
    fp_inject f fp1 fp1' -> fp_inject f (FP.union fp1 fp2) fp1'.
Proof.
  clear; intros.
  inv H; constructor; destruct fp1, fp2, fp1'; simpl;
    apply loc_inject_union_s; auto.
Qed.

Lemma fp_inject_union_t:
  forall f fp fp1' fp2',
    fp_inject f fp fp1' -> fp_inject f fp fp2' -> fp_inject f fp (FP.union fp1' fp2').
Proof.
  clear;intros.
  inv H; inv H0. constructor; apply loc_inject_union_t; auto.
Qed.
  
Lemma fp_inject_union:
  forall f fp1 fp1' fp2 fp2',
    fp_inject f fp1 fp1' -> fp_inject f fp2 fp2' -> fp_inject f (FP.union fp1 fp2) (FP.union fp1' fp2').
Proof.
  clear. intros.
  apply fp_inject_union_t; [|rewrite FP.union_comm_eq]; apply fp_inject_union_s; auto.
Qed.

Lemma loc_inject_id_loc_subset:
  forall ls ls', loc_inject inject_id ls ls' -> Locs.subset ls' ls.
Proof.
  clear; simpl. Locs.unfolds. intros. apply H in H0. destruct H0 as (?&?&?&?&?).
  inv H0. rewrite Ptrofs.add_zero in *. destruct H1 as [H1|H1]; destruct H1; subst; auto.
Qed.

Lemma fp_inject_id_fp_subset:
  forall fp fp', fp_inject inject_id fp fp' -> FP.subset fp' fp.
Proof.
  clear; destruct fp; constructor; inv H; simpl in *;
    apply loc_inject_id_loc_subset; auto.
Qed.

Lemma loc_inject_loc_match:
  forall mu f ls ls',
    loc_inject f ls ls' ->
    inject_incr (Bset.inj_to_meminj (inj mu)) f ->
    sep_inject (Bset.inj_to_meminj (inj mu)) f ->
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    LocMatch mu ls ls'.
Proof.
  clear. intros.
  inv H. constructor. intros b ofs HShared HLoc.
  specialize (H3 b ofs HLoc). destruct H3 as (b0 & ofs0 & delta & INJ & [[Hofs HLoc']|[Hofs HLoc']]).
  eapply Bset.inj_range in HShared; [|inv H2; eauto].
  destruct HShared as (b0' & INJ').
  cut (b0' = b0 /\ delta = 0). 
  intros [? ?]. subst. 
  exists b0. split; auto. rewrite Ptrofs.add_zero. auto.
  exploit H1. unfold Bset.inj_to_meminj. rewrite INJ'. eauto. eauto. intro.
  unfold Bset.inj_to_meminj in H. destruct (inj mu b0) eqn:C; [inv H| try discriminate].
  exploit Bset.inj_injective. inv H2; eauto. exact INJ'. exact C. 
  split; auto. 

  eapply Bset.inj_range in HShared; [|inv H2; eauto].
  destruct HShared as (b0' & INJ').
  cut (b0' = b0 /\ delta = 0). 
  intros [? ?]. subst. 
  exists b0. split; auto. rewrite Ptrofs.add_zero. auto.
  exploit H1. unfold Bset.inj_to_meminj. rewrite INJ'. eauto. eauto. intro.
  unfold Bset.inj_to_meminj in H. destruct (inj mu b0) eqn:C; [inv H| try discriminate].
  exploit Bset.inj_injective. inv H2; eauto. exact INJ'. exact C. 
  split; auto.
Qed.
  
Lemma fp_inject_fp_match:
  forall mu f fp fp',
    fp_inject f fp fp' ->
    inject_incr (Bset.inj_to_meminj (inj mu)) f ->
    sep_inject (Bset.inj_to_meminj (inj mu)) f ->
    Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu) ->
    FPMatch' mu fp fp'.
Proof.
  clear. intros. inv H.
  constructor; eapply loc_inject_loc_match; eauto;
    eapply loc_inject_union_s; auto.
Qed.

Lemma valid_pointer_fp_inject:
  forall b b' delta ofs,
    f b = Some (b', delta) ->
    fp_inject f (valid_pointer_fp b (Ptrofs.unsigned ofs))
              (valid_pointer_fp b' (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  clear; intros. unfold MemOpFP.valid_pointer_fp; simpl.
  constructor; try apply loc_inject_emp.
  simpl. unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes. simpl. repeat rewrite Locs.locs_union_emp.
  generalize H. clear. unfold range_locset. constructor.
  Locs.unfolds. intros. destruct eq_block;[|discriminate].
  destruct zle;[|discriminate].
  destruct zlt;[|discriminate].
  subst. exists b, ofs, delta. split;[auto|left;split;[omega|]].
  destruct eq_block; [|contradiction].
  destruct zle, zlt; try omega; auto.
Qed.

Lemma weak_valid_pointer_fp_inject:
  forall b b' delta ofs,
    f b = Some (b', delta) ->
    Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
    fp_inject f (weak_valid_pointer_fp m1 b (Ptrofs.unsigned ofs))
              (weak_valid_pointer_fp m2 b' (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)))).
Proof.
  unfold Mem.weak_valid_pointer. intros.
  destruct (Mem.valid_pointer m1 b (Ptrofs.unsigned ofs)) eqn:VALID;
    [clear H0| simpl in H0]; unfold weak_valid_pointer_fp; rewrite VALID.
  erewrite valid_pointer_inj; eauto. apply valid_pointer_fp_inject; auto.
  destruct (Mem.valid_pointer m2 b' (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)))) eqn:? .
  - unfold MemOpFP.valid_pointer_fp; simpl.
    constructor; try apply loc_inject_emp.
    generalize H. clear. constructor; unfold range_locset; Locs.unfolds; simpl.
    unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes. simpl. repeat rewrite Locs.locs_union_emp.
    intros. destruct eq_block;[|discriminate].
    destruct zle, zlt; try discriminate.
    subst. exists b, ofs, delta. split; auto. left; split. omega.
    destruct eq_block; try contradiction.
    destruct zle, zlt; try omega; auto.
  - constructor; try apply loc_inject_emp.
    generalize H. clear. constructor; unfold range_locset; Locs.unfolds; simpl.
    unfold FP.ge_cmps, FP.ge_reads, FP.ge_writes. simpl. repeat rewrite Locs.locs_union_emp.
    intros. destruct eq_block;[|discriminate].
    destruct zle, zlt; try discriminate.
    subst. exists b, ofs, delta. split; auto.
    assert (ofs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) \/
            ofs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) - 1) as HOFS by omega.
    destruct HOFS as [HOFS|HOFS];[left|right];(split; [omega|]).
    destruct eq_block; try contradiction.
    destruct zle, zlt; try omega; auto.
    destruct eq_block; try contradiction.
    destruct zle, zlt; try omega; auto.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ Val.inject _ _ v2 ] =>
    exists v1; split; auto
  | _ => idtac
  end.

Ltac TrivialExists_fp :=
  match goal with
  | [ |- exists fp2, Some empfp = Some fp2 /\ fp_inject _ _ fp2 ] =>
    exists empfp; split; [auto|eapply fp_inject_emp]
  | H: None = Some _ |- _ => discriminate
  | _ => idtac
  end.


Lemma cmpu_bool_fp_fp_inject:
  forall c v1 v2 v1' v2' v fp,
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.cmpu_bool (Mem.valid_pointer m1) c v1 v2 = Some v ->
    cmpu_bool_fp m1 c v1 v2 = Some fp ->
    exists fp', cmpu_bool_fp m2 c v1' v2' = Some fp' /\ fp_inject f fp fp'.
Proof.
  intros c v1 v2 v1' v2' v fp INJ1 INJ2 EVAL EVALFP.
  inv INJ1; inv INJ2; try (simpl in EVAL, EVALFP; inv EVAL; simpl; TrivialExists_fp; fail).
  + simpl in *. destruct Archi.ptr64; [|destruct Int.eq;[destruct Val.cmp_different_blocks|]]; try discriminate.
    destruct (Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1)) eqn:WEAKVALID;
      unfold Mem.weak_valid_pointer in WEAKVALID; rewrite WEAKVALID in EVAL; [inv EVAL|discriminate].
    eexists; split; [eauto|inv EVALFP]. 
    eapply weak_valid_pointer_fp_inject; eauto.
  + simpl in *. destruct Archi.ptr64; [|destruct Int.eq;[destruct Val.cmp_different_blocks|]]; try discriminate.
    destruct (Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1)) eqn:WEAKVALID;
      unfold Mem.weak_valid_pointer in WEAKVALID; rewrite WEAKVALID in EVAL; [inv EVAL|discriminate].
    eexists; split; [eauto|inv EVALFP]. 
    eapply weak_valid_pointer_fp_inject; eauto.
  + simpl in *. destruct Archi.ptr64; [|destruct eq_block;[subst|destruct Val.cmp_different_blocks]]; try discriminate.
    * rewrite H in H0; inv H0. destruct eq_block; [|contradiction]. 
      eexists; split; [eauto|simpl in EVALFP; inv EVALFP].
      apply fp_inject_union.
      destruct (Mem.weak_valid_pointer m1 b0 (Ptrofs.unsigned ofs1)) eqn:C;
        [eapply weak_valid_pointer_fp_inject; eauto|unfold Mem.weak_valid_pointer in C; rewrite C in EVAL; inv EVAL].
      destruct (Mem.weak_valid_pointer m1 b0 (Ptrofs.unsigned ofs0)) eqn:C;
        [eapply weak_valid_pointer_fp_inject; eauto|unfold Mem.weak_valid_pointer in C; rewrite C in EVAL].
      rewrite andb_false_r in EVAL. discriminate.
    * match goal with
      | H : context[match ?x && ?y with _ => _ end] |- _ =>
        let Hx:= fresh Valid in
        let Hy:= fresh Valid in
        destruct x eqn:Hx; destruct y eqn:Hy; simpl in H; try rewrite andb_false_r in H; try discriminate
      end.
      exploit valid_different_pointers_inj; eauto. 
      destruct eq_block; [intros [NEQ|NEQ]; try congruence|].
      ** inv EVAL. inv EVALFP. eexists; split; [eauto|].
         exploit (@valid_pointer_inj b1); eauto. intro Valid1'.
         exploit (@valid_pointer_inj b0); eauto. intro Valid0'.             
         unfold weak_valid_pointer_fp. rewrite Valid1', Valid0'.
         apply fp_inject_union; apply valid_pointer_fp_inject; auto.
      ** intros _. inv EVAL. inv EVALFP. eexists; split; [eauto|].
         apply fp_inject_union; apply valid_pointer_fp_inject; auto.
Qed.

Lemma cmplu_bool_fp_fp_inject:
  forall c v1 v2 v1' v2' v fp,
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.cmplu_bool (Mem.valid_pointer m1) c v1 v2 = Some v ->
    cmplu_bool_fp m1 c v1 v2 = Some fp ->
    exists fp', cmplu_bool_fp m2 c v1' v2' = Some fp' /\ fp_inject f fp fp'.
Proof.
  intros c v1 v2 v1' v2' v fp INJ1 INJ2 EVAL EVALFP.
  inv INJ1; inv INJ2; simpl in EVAL, EVALFP; inv EVAL. simpl. TrivialExists_fp.
Qed.

Lemma eval_condition_fp_inj:
  forall cond vl1 vl2 v1 fp1,
    Val.inject_list f vl1 vl2 ->
    eval_condition cond vl1 m1 = Some v1 ->
    eval_condition_fp cond vl1 m1 = Some fp1 ->
    exists fp2, eval_condition_fp cond vl2 m2 = Some fp2 /\
           fp_inject f fp1 fp2.
Proof.
  intros cond vl1 vl2 v1 fp1 INJVALS EVALCOND EVALFP.
  destruct cond; simpl in EVALCOND, EVALFP; FuncInv; InvInject; simpl; auto;
    try (repeat match goal with
                | H: context[match ?x with _ => _ end] |- context[match ?x with _ => _ end] => destruct x
                | H: Val.inject _ _ _ |- _ => inv H; try discriminate
                end; TrivialExists_fp; fail).
  -     eapply cmpu_bool_fp_fp_inject; eauto.
  - eapply cmpu_bool_fp_fp_inject with (v2:= Vint n); eauto.
  - eapply cmplu_bool_fp_fp_inject; eauto.
  - eapply cmplu_bool_fp_fp_inject with (v2:=Vlong n); eauto.
Qed.



Lemma block_weak_valid_pointer:
  forall m b ofs (Local: Bset.t),
    Local b -> Bset.subset (FP.blocks (weak_valid_pointer_fp m b ofs)) Local.
Proof.
  clear. intros. unfold Bset.subset, FP.blocks, weak_valid_pointer_fp, valid_pointer_fp, FP.locs. intros b' [? C].
  Locs.unfolds. red_boolean_true.
  edestruct weak_valid_pointer_fp_loc. exploit H1; eauto. intros [? _]. subst; auto.
  destruct Mem.valid_pointer; inv H1.
  destruct Mem.valid_pointer; inv H0.
  destruct Mem.valid_pointer; inv H0.
Qed.

Lemma block_weak_valid_pointer_union:
  forall m b1 ofs1 b2 ofs2 (Local: Bset.t),
    Local b1 -> Local b2 ->
    Bset.subset (FP.blocks (
                     FP.union (weak_valid_pointer_fp m b1 ofs1)
                              (weak_valid_pointer_fp m b2 ofs2))) Local.
Proof.
  clear. intros. unfold Bset.subset, FP.union, FP.blocks, weak_valid_pointer_fp, valid_pointer_fp, FP.locs. intros b' [? C].
  Locs.unfolds.
  do 2 destruct Mem.valid_pointer; simpl in C; try discriminate; red_boolean_true; try discriminate;
    try (edestruct FMemOpFP.range_locset_loc as [D _]; exploit D; eauto; intros [? _]; subst; auto).
Qed.

Lemma eval_operation_fp_inj:
  forall op sp1 vl1 sp2 vl2 v1 fp1,
  (forall id ofs,
      In id (globals_operation op) ->
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) ->

    Val.inject f sp1 sp2 ->
    Val.inject_list f vl1 vl2 ->
    eval_operation ge1 sp1 op vl1 m1 = Some v1 ->    
    eval_operation_fp ge1 sp1 op vl1 m1 = Some fp1 ->
    exists fp2, eval_operation_fp ge2 sp2 op vl2 m2 = Some fp2 /\
           fp_inject f fp1 fp2.
Proof.
  intros until fp1; intros GL INJSP INJVALS EVAL1 EVALFP1.
  destruct op; simpl in EVAL1, EVALFP1; simpl; FuncInv; InvInject; TrivialExists_fp;
    try (repeat match goal with
                | H: context[match ?x with _ => _ end] |- context[match ?x with _ => _ end] => destruct x
                | H: Val.inject _ _ _ |- _ => inv H; try discriminate
                end; TrivialExists_fp; fail).
  TrivialReduce. exploit eval_addressing32_inj; eauto. intros [v' [R INJR]]. rewrite R. TrivialExists_fp.
  TrivialReduce. exploit eval_addressing64_inj; eauto. intros [v' [R INJR]]. rewrite R. TrivialExists_fp.
  destruct eval_condition eqn:?;[|discriminate].
  exploit eval_condition_fp_inj; eauto. 
Qed.


End EVAL_COMPAT.

(** Compatibility of the evaluation functions with the ``is less defined'' relation over values. *)
Lemma eval_shift_stack_operation_fp:
  forall F V (ge: Genv.t F V) sp op vl m delta,
    eval_operation_fp ge (Vptr sp Ptrofs.zero) (shift_stack_operation delta op) vl m =
    eval_operation_fp ge (Vptr sp (Ptrofs.repr delta)) op vl m.
Proof.
  clear; unfold eval_operation_fp; destruct op; simpl; auto.
  intros. rewrite eval_shift_stack_addressing32; auto.
  intros. rewrite eval_shift_stack_addressing64; auto.
Qed.
  
Section EVAL_LESSDEF.

Variable F V: Type.
Variable genv: Genv.t F V.

Lemma eval_condition_lessdef_fp:
  forall cond vl1 vl2 v fp m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_condition cond vl1 m1 = Some v ->  
  eval_condition_fp cond vl1 m1 = Some fp ->
  exists fp', eval_condition_fp cond vl2 m2 = Some fp' /\ fp_inject inject_id fp fp'.
Proof.
  intros.
  exploit (@eval_condition_fp_inj inject_id m1 m2).
  intros. inv H3. eapply valid_pointer_extends; eauto.
  intros. inv H6; inv H7; auto.
  eapply val_inject_list_lessdef. eauto.
  eauto. eauto.
  intros (fp' & H1' & FPINJ).
  exists fp'. split; auto.
Qed.

Lemma eval_operation_lessdef_fp:
  forall sp op vl1 vl2 v1 fp1 m1 m2,
    Val.lessdef_list vl1 vl2 ->
    Mem.extends m1 m2 ->
    eval_operation genv sp op vl1 m1 = Some v1 ->
    eval_operation_fp genv sp op vl1 m1 = Some fp1 ->
    exists fp2, eval_operation_fp genv sp op vl2 m2 = Some fp2
           /\ fp_inject inject_id fp1 fp2.
Proof.
  intros. eapply eval_operation_fp_inj with (m1 := m1) (sp1 := sp).
  apply valid_pointer_extends; auto.
  intros. inv H6. inv H7. auto.
  intros. apply val_inject_lessdef. auto.
  apply val_inject_lessdef; auto.
  apply val_inject_list_lessdef; eauto.
  eauto.
  auto.  
Qed.


End EVAL_LESSDEF.

(** Compatibility of the evaluation functions with memory injections. *)

Section EVAL_INJECT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp1: block.
Variable sp2: block.
Variable delta: Z.
Hypothesis sp_inj: f sp1 = Some(sp2, delta).

Lemma eval_condition_fp_inject:
  forall cond vl1 vl2 v1 fp1 m1 m2,
  Val.inject_list f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_condition cond vl1 m1 = Some v1 ->  
  eval_condition_fp cond vl1 m1 = Some fp1 ->
  exists fp2, eval_condition_fp cond vl2 m2 = Some fp2 /\ fp_inject f fp1 fp2.
Proof.
  intros.
  exploit (@eval_condition_fp_inj f m1 m2).
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  eauto. eauto. eauto.
  intros (fp2 & EVALCONDFP & FPINJ).
  eexists; split; eauto.
Qed.


Lemma eval_operation_fp_inject:
  forall op vl1 vl2 v1 fp1 m1 m2,
    Val.inject_list f vl1 vl2 ->
    Mem.inject f m1 m2 ->
    eval_operation genv (Vptr sp1 Ptrofs.zero) op vl1 m1 = Some v1 ->
    eval_operation_fp genv (Vptr sp1 Ptrofs.zero) op vl1 m1 = Some fp1 ->
    exists fp2,
      eval_operation_fp genv (Vptr sp2 Ptrofs.zero) (shift_stack_operation delta op) vl2 m2 = Some fp2
      /\ fp_inject f fp1 fp2.
Proof.
  intros.
  rewrite eval_shift_stack_operation_fp. 
  eapply eval_operation_fp_inj with (sp1 := Vptr sp1 Ptrofs.zero) (m1 := m1); eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  intros. apply symbol_address_inject. auto.
  econstructor; eauto.
  rewrite Ptrofs.add_zero_l; auto. 
Qed.

End EVAL_INJECT.
