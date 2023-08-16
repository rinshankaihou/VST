(* Contents related to [val_casted] in this file are mostly copied from [val_casted.v] of Compositional CompCert.  *)

Require Import Coqlib Integers Values AST Ctypes Cop FCop Locations.

(** A function version of [val_casted] *)
Definition val_casted_func (v : val) (ty: type) : bool :=
  match v, ty with
  (** val_casted_int *)
  | Vint n, Tint sz si attr => 
    if Int.eq_dec (cast_int_int sz si n) n then true
    else false
  (** val_casted_float *)
  | Vfloat n, Tfloat F64 attr =>
    true
  (** val_casted_single *)
  | Vsingle n, Tfloat F32 attr =>
    true
  (** val_casted_long *)
  | Vlong n, Tlong si attr =>
    true
  (** val_casted_ptr_ptr *)
  | Vptr b ofs, Tpointer ty attr =>
    true
  (** val_casted_int_ptr *)
  | Vint n, Tpointer ty attr =>
    negb Archi.ptr64
  (** val_casted_ptr_int *)
  | Vptr b ofs, Tint I32 si attr =>
    negb Archi.ptr64
  (** val_casted_long_ptr *)
  | Vlong n, Tpointer ty attr =>
    Archi.ptr64
  (** val_casted_ptr_long *)
  | Vptr b ofs, Tlong si attr =>
    Archi.ptr64
  (** val_casted_struct *)
  | Vptr b ofs, Tstruct id attr =>
    true
  (** val_casted_union *)
  | Vptr b ofs, Tunion id attr =>
    true
  (** val_casted_void *)
  | _,  Tvoid =>
    true
  (** OTHERS *)
  | _, _ => false
  end.

Lemma val_casted_funcP:
  forall v ty,
    val_casted v ty <-> val_casted_func v ty = true.
Proof.
  destruct v, ty;
    (simpl; split; intro H;
     [ try match goal with
           | [|- true = true] => reflexivity
           | [|- _ = true] => inv H
           end
     | inversion H; try constructor; auto ]).
  rewrite H2. destruct Int.eq_dec; auto.
  destruct Int.eq_dec; auto. discriminate.
  auto with bool.
  auto with bool.
  auto.
  destruct f0. discriminate. constructor.
  auto.
  destruct f0. constructor. discriminate.
  auto with bool.
  destruct i0; try discriminate. constructor; auto with bool.
  auto.
Qed.

(** val_casted for value list *)
Inductive val_casted_list: list val -> typelist -> Prop :=
  | vcl_nil:
      val_casted_list nil Tnil
  | vcl_cons: forall v1 vl ty1 tyl,
      val_casted v1 ty1 -> val_casted_list vl tyl ->
      val_casted_list (v1 :: vl) (Tcons  ty1 tyl).

Lemma val_casted_list_params:
  forall params vl,
  val_casted_list vl (type_of_params params) ->
  list_forall2 val_casted vl (List.map snd params).
Proof.
  induction params; simpl; intros. 
  inv H. constructor.
  destruct a as [id ty]. inv H. constructor; auto. 
Qed.

Fixpoint val_casted_list_func (vs : list val) (ts : typelist) : bool :=
  match vs, ts with
    | nil, Tnil => true
    | v1 :: vl, Tcons ty1 tyl => 
      val_casted_func v1 ty1 && val_casted_list_func vl tyl
    | _, _ => false
  end.


Lemma val_casted_list_funcP vs ts : 
  val_casted_list_func vs ts = true <-> val_casted_list vs ts.
Proof.
  revert ts; induction vs. destruct ts; simpl; auto.
  split; auto. intros _. constructor.
  split; auto. inversion 1. inversion 1.
  split; auto. destruct ts; simpl; auto.
  inversion 1. rewrite andb_true_iff. intros [H1 H2]. constructor.
  rewrite <- val_casted_funcP in H1; auto. rewrite <-IHvs; auto.
  inversion 1; subst. simpl. rewrite andb_true_iff; split.
  rewrite <- val_casted_funcP; auto. rewrite IHvs; auto.
Qed.

Lemma val_casted_inj (j : meminj) v1 v2 tv : 
  Val.inject j v1 v2 -> 
  val_casted v1 tv -> 
  val_casted v2 tv.
Proof.
inversion 1; subst; auto.
inversion 1; subst; auto; try solve[constructor; auto].
inversion 1; constructor.
Qed.

Lemma val_casted_list_inj (j : meminj) vs1 vs2 ts :
  Val.inject_list j vs1 vs2 ->
  val_casted_list vs1 ts ->
  val_casted_list vs2 ts.
Proof.
intros H1; revert vs1 vs2 H1; induction ts; simpl; intros vs1 vs2 H1 H2.
revert H2 H1; inversion 1; subst. inversion 1; subst. constructor.
revert H2 H1; inversion 1; subst. inversion 1; subst. constructor.
eapply val_casted_inj; eauto.
eapply IHts; eauto.
Qed.

Definition val_has_type_func (v : val) (t : typ) : bool :=
  match v with
    | Vundef => true
    | Vint _ => match t with
                | AST.Tint => true
                | AST.Tany32 => true
                | AST.Tany64 => true
                | _ => false
                end
    | Vlong _ => match t with 
                 | AST.Tlong => true
                 | AST.Tany64 => true
                 | _ => false
               end
    | Vfloat _ => match t with 
                  | AST.Tfloat => true
                  | AST.Tany64 => true
                  | _ => false
                  end
    | Vsingle _ => match t with
                   | AST.Tsingle => true
                   | AST.Tany32 => true
                   | AST.Tany64 => true
                   | _ => false
                   end
    | Vptr _ _ => match t with
                  | AST.Tint => negb Archi.ptr64
                  | AST.Tany32 => negb Archi.ptr64
                  | AST.Tlong => Archi.ptr64
                  | AST.Tany64 => true
                  | _ => false
                  end
  end.

Lemma val_has_type_funcP v t : 
  Val.has_type v t <-> (val_has_type_func v t=true).
Proof.
split.
induction v; auto.
simpl. destruct t; auto.
simpl. destruct t; auto.
simpl. destruct t; auto. 
simpl. destruct t; auto.
simpl. destruct t; auto.
induction v; simpl; auto.
destruct t; auto; try inversion 1.
destruct t; auto; try inversion 1.
destruct t; auto; try solve[inversion 1].
destruct t; auto. inversion 1. inversion 1. inversion 1.
destruct t; auto; inversion 1.
Qed.

Fixpoint val_has_type_list_func (vl : list val) (tyl : list typ) : bool :=
  match vl, tyl with
    | nil, nil => true
    | v :: vl', ty :: tyl' => val_has_type_func v ty 
                              && val_has_type_list_func vl' tyl' 
    | nil, _ :: _ => false
    | _ :: _, nil => false
  end.

Lemma val_has_type_list_func_charact vl tyl : 
  Val.has_type_list vl tyl <-> (val_has_type_list_func vl tyl=true).
Proof.
revert tyl; induction vl.
destruct tyl. simpl. split; auto. simpl. split; auto. inversion 1.
intros. destruct tyl. simpl. split; auto. inversion 1.
simpl. split. intros [H H2]. 
+ rewrite andb_true_iff. split. 
  rewrite <-val_has_type_funcP; auto.
  rewrite <-IHvl; auto.
+ rewrite andb_true_iff. intros [H H2]. split.
  rewrite val_has_type_funcP; auto.
  rewrite IHvl; auto.
Qed.


Fixpoint tys_nonvoid (tyl : typelist) :=
  match tyl with
    | Tnil => true
    | Tcons Tvoid tyl' => false
    | Tcons _ tyl' => tys_nonvoid tyl'
  end.

Fixpoint vals_defined (vl : list val) :=
  match vl with
    | nil => true
    | Vundef :: _ => false
    | _ :: vl' => vals_defined vl'
  end.

Lemma vals_inject_defined (vl1 vl2 : list val) (j : meminj) :
  Val.inject_list j vl1 vl2 -> 
  vals_defined vl1=true -> 
  vals_defined vl2=true.
Proof.
revert vl2; induction vl1; simpl. destruct vl2; try solve[inversion 1|auto].
intros vl2; inversion 1; subst. destruct a; try solve[inversion 1].
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
Qed.

Lemma valinject_hastype':
  forall (j : meminj) (v v' : val),
    Val.inject j v v' -> 
    v <> Vundef -> 
    forall T : typ, Val.has_type v T -> Val.has_type v' T.
Proof.
  intros.
  induction H; auto.
  elim H0; auto.
Qed.

Lemma val_list_inject_hastype j vl1 vl2 tys :
  Val.inject_list j vl1 vl2 -> 
  vals_defined vl1=true -> 
  val_has_type_list_func vl1 tys=true ->
  val_has_type_list_func vl2 tys=true.
Proof.
revert vl2 tys. induction vl1. inversion 1. solve[destruct tys; simpl; auto].
intros H tys H1 H2 H3. inv H1. 
assert (def: vals_defined vl1=true). 
{ inv H2. revert H0. destruct a; auto. congruence. }
simpl. destruct tys. simpl in H3; congruence. 
rewrite andb_true_iff. split. 
rewrite <-val_has_type_funcP. eapply valinject_hastype'; eauto.
simpl in H2. intros contra. rewrite contra in H2. congruence.
inv H3. rewrite andb_true_iff in H0. 
  destruct H0 as [H0 _]. solve[rewrite val_has_type_funcP; auto].
eapply (IHvl1 vl'); eauto.
inv H3. rewrite H0. rewrite andb_true_iff in H0. 
  solve[destruct H0 as [_ ->]; auto].
Qed.

Lemma val_list_inject_defined j vl1 vl2 : 
  Val.inject_list j vl1 vl2 -> 
  vals_defined vl1=true -> 
  vals_defined vl2=true.
Proof.
revert vl2. induction vl1; simpl. 
+ intros vl2; inversion 1; auto.
+ intros vl2; inversion 1; subst. inv H. 
simpl. intros H8.
assert (def1: vals_defined vl1=true).
{ destruct a; try solve[congruence]. }
revert H2 H8. inversion 1; auto. subst. congruence.
Qed.


(** TODO: properties about these fixpoints remains to be proved *)

Fixpoint encode_longs (tyl : list typ) (vl : list val) :=
  match tyl with
    | nil => nil
    | AST.Tlong :: tyl' => 
      match vl with 
        | nil => nil
        | Vlong n :: vl' => Vint (Int64.hiword n) :: Vint (Int64.loword n) 
                            :: encode_longs tyl' vl'
        | Vundef :: vl' => Vundef :: Vundef :: encode_longs tyl' vl'
        | _ :: vl' => Vundef :: Vundef :: encode_longs tyl' vl'
      end
    | t :: tyl' => 
      match vl with
        | nil => nil
        | v :: vl' => v :: encode_longs tyl' vl'
      end
  end.

Fixpoint encode_typs (tyl : list typ) : list typ :=
  match tyl with
    | nil => nil
    | AST.Tlong :: tyl' => AST.Tint :: AST.Tint :: encode_typs tyl'
    | t :: tyl' => t :: encode_typs tyl'
  end.

Fixpoint getBlocks' (vl : list val) (b0 : block) := 
  match vl with
    | nil => false
    | Vptr b _ :: vl' => eq_block b b0 || getBlocks' vl' b0
    | _ :: vl' => getBlocks' vl' b0
  end.














(** should val_casted.v renamed into arguments_welldefined.v? *)
(** is this definition is too conservative? Zlength * 8 instead of actuall size of arguments *)

Definition wd_args (args: list val) (tyl: list typ) : bool :=
  val_has_type_list_func args tyl && vals_defined args && zlt (4 * (2 * (Zlength args))) Int.max_unsigned.

Fixpoint set_arguments (ll: list (rpair loc)) (vl: list val) (ls: Locmap.t) : Locmap.t :=
  match ll, vl with
  | lp :: ll' , v :: vl' =>
    match lp with
    | AST.One l => Locmap.set l v (set_arguments ll' vl' ls)
    | AST.Twolong hi lo => Locmap.set hi (Val.hiword v) (Locmap.set lo (Val.loword v) (set_arguments ll' vl' ls))
    end
  | _, _ => ls
  end.

(** dual to Locmap.getpair *)
Definition get_result (rp: rpair mreg) (lm: Locmap.t) : val :=
  match rp with
  | AST.One r => lm (R r)
  | AST.Twolong r1 r2 => Val.longofwords (lm (R r1)) (lm (R r2))
  end.








Lemma has_type_list_tail:
  forall vl vl' tyl tyl', Val.has_type_list (vl ++ vl') (tyl ++ tyl') ->
                     length vl = length tyl ->
                     Val.has_type_list vl' tyl'.
Proof.
  clear. induction vl; intros.
  destruct tyl; inv H0. auto.
  destruct tyl; inv H0. eapply IHvl in H2; eauto.
  simpl in H. tauto.
Qed.

Lemma vals_defined_tail:
  forall vl vl', vals_defined (vl ++ vl') = true -> vals_defined vl' = true.
Proof.
  clear. induction vl; simpl; auto.
  intros. destruct a; try congruence; auto.
Qed.

Lemma wd_args_inject:
  forall j args args' tyl,
    Val.inject_list j args args' ->
    wd_args args tyl = true ->
    wd_args args' tyl = true.
Proof.
  induction args; intros; inv H; auto.
  assert (EQLEN: length args = length vl').
  { generalize vl' H5; clear; induction args; intros; inv H5; auto.
    simpl. erewrite IHargs; eauto. }
  destruct tyl. discriminate.
  assert (wd_args args tyl = true).
  { unfold wd_args in *. InvBooleans. simpl in H2, H0. InvBooleans.
    rewrite H4. assert (vals_defined args = true) by (destruct a; auto; discriminate). rewrite H0.
    rewrite Zlength_cons in H. destruct zlt; auto. Lia.lia. }
  eapply IHargs in H5; try eassumption. 
  unfold wd_args in *. InvBooleans. rewrite andb_true_iff; split.
  simpl in H0, H9|- * . InvBooleans. rewrite H4.
  destruct a, t; simpl in H8; try discriminate; inv H3; simpl; auto.
  rewrite Zlength_cons, Zlength_correct, <- EQLEN, <- Zlength_correct, <- (Zlength_cons a).
  generalize H1. clear. destruct zlt. auto. contradiction.
Qed.


Require Import Conventions1.
Lemma wd_args_set_arguments_get_agree:
  forall sg args locs ls,
    wd_args args (sig_args sg) = true ->
    locs = loc_arguments sg ->
    set_arguments locs args (Locmap.init Vundef) = ls ->
    forall n l, nth_error locs n = Some l ->
           exists v, nth_error args n = Some v /\
                match l with
                | AST.One l0 => ls l0 = v
                | AST.Twolong lhi llo =>
                  ls lhi = Val.hiword v /\
                  ls llo = Val.loword v
                end.
Proof.
  clear. unfold loc_arguments.
  destruct Archi.ptr64 eqn:C; inv C. destruct sg. simpl. clear. intros args locs ls.
  unfold wd_args. repeat rewrite andb_true_iff. intros ((? & ?) & _) Hlocs Hls. subst.
  generalize 0. generalize dependent args.
  induction sig_args; simpl; intros.
  destruct n; inversion H1.
  destruct args as [|v args]; [inversion H| specialize (IHsig_args args)].
  simpl in H. rewrite andb_true_iff in H. destruct H as [vTyp argsTyp]. 
  assert (v <> Vundef /\ vals_defined args = true) as [vDef argsDef] by (destruct v; inversion H0; split; congruence).
  destruct n.
  (* n = 0 *)
  clear IHsig_args. simpl in H1|-* . inv H1. exists v; split;[auto|].
  unfold Locmap.getpair; destruct a; simpl;
    try (destruct v; inv vTyp; try congruence; rewrite Locmap.gss; auto; fail).
  rewrite Locmap.gss. rewrite Locmap.gso, Locmap.gss. simpl.
  destruct v; inversion vTyp; try contradiction. simpl. auto.
  right. simpl; Lia.lia.
  (* n > 0 *)
  destruct (IHsig_args argsTyp argsDef (z + typesize a) n _ H1) as [v' [Hnth Hagree]].
  exists v'. split; [auto|]. simpl in H1|-* . 
  apply nth_error_in, loc_arguments_32_charact in H1.  
  destruct l; unfold Locmap.getpair; simpl in H1. 
  { destruct a; rewrite Locmap.gso; auto; 
      try (destruct r; simpl in *; [auto| right; destruct sl; try tauto; Lia.lia; fail]).
    simpl. rewrite Locmap.gso; auto. simpl. destruct r; auto; destruct sl; auto. simpl in H1. right. Lia.lia. }
  { destruct H1 as [Hhi Hlo].
    destruct a; repeat rewrite Locmap.gso; auto;
      repeat match goal with
             | |- Loc.diff _ ?x => destruct x; simpl in *; auto
             | |- ?x <> ?x \/ _ => right; Lia.lia
             | |- _ <> ?x \/ _  => destruct x; auto
             end.
  }
Qed.

Lemma wd_args_set_arguments_eq:
  forall args sg,
    wd_args args (sig_args sg) = true ->
    args = (map (fun p => Locmap.getpair p (set_arguments (loc_arguments sg) args (Locmap.init Vundef))) (loc_arguments sg)).
Proof.
  clear. unfold loc_arguments.
  destruct Archi.ptr64 eqn:C; inv C. destruct sg. simpl. clear. 
  unfold wd_args. repeat rewrite andb_true_iff. intros ((? & ?) & _). 
  generalize 0. generalize dependent args.
  induction sig_args; simpl; intros.
  destruct args; auto. inversion H.
  destruct args as [|v args]; [inversion H| specialize (IHsig_args args)].
  simpl in H. rewrite andb_true_iff in H. destruct H as [vTyp argsTyp]. 
  assert (v <> Vundef /\ vals_defined args = true) as [vDef argsDef] by (destruct v; inversion H0; split; congruence).
  f_equal.
  clear IHsig_args argsTyp argsDef H0.
  apply val_has_type_funcP in vTyp.
  destruct v, a; try contradiction; simpl in *; try (rewrite Locmap.gss; simpl; auto; fail).
  rewrite Locmap.gss. rewrite Locmap.gso, Locmap.gss. simpl. rewrite Int64.ofwords_recompose; auto.
  red; simpl; right; Lia.lia. inversion vTyp.
  specialize (IHsig_args argsTyp argsDef (z + typesize a)).
  rewrite IHsig_args at 1. clear. apply map_ext_in; intros.
  apply loc_arguments_32_charact in H. destruct a0; simpl in *.
  destruct r; simpl in *; try contradiction. destruct sl; try contradiction.
  destruct a; simpl; repeat (rewrite Locmap.gso; [auto| red; right; simpl in *; Lia.lia]).
  destruct rhi, rlo; simpl in *; try intuition.
  destruct sl, sl0; simpl in *; try intuition.
  destruct a; simpl; repeat (rewrite Locmap.gso; [auto| red; right; simpl in *; Lia.lia]).
Qed.

(** TODO: move to val_casted *)
Lemma locmap_set_reorder:
  forall l1 l2 v1 v2 rs, Loc.diff l1 l2 ->
                    Locmap.set l1 v1 (Locmap.set l2 v2 rs) =
                    Locmap.set l2 v2 (Locmap.set l1 v1 rs).
Proof.
  clear. intros. apply Axioms.functional_extensionality. intro.
  unfold Locmap.set. pose proof Loc.diff_not_eq.
  destruct (Loc.diff_dec l1 x) eqn:? ;
    destruct (Loc.diff_dec l2 x) eqn:? ;
    repeat destruct Loc.eq; subst; auto;
      try match goal with
          | H: Loc.diff ?x ?x |- _ =>  exfalso; eapply Loc.same_not_diff; eauto
          end.
  apply Loc.diff_sym in H; congruence. congruence.
Qed.

Lemma set_arguments_reorder:
  forall t a tyl args z0 z rs,
    z0 <= z ->
    set_arguments (loc_arguments_32 (t::nil) z0) (a::nil)
                  (set_arguments (loc_arguments_32 tyl (z + typesize t)) args rs) =
    set_arguments (loc_arguments_32 tyl (z + typesize t)) args
                  (set_arguments (loc_arguments_32 (t::nil) z0) (a::nil) rs).
Proof.
  clear. induction tyl. simpl; auto.
  intros. unfold loc_arguments_32 at 2, set_arguments at 2.
  
  destruct a0.
  1,2,4,5,6:
    destruct args; [auto|]; fold set_arguments loc_arguments_32;
    unfold set_arguments at 1, loc_arguments_32 at 1 in IHtyl;
    unfold set_arguments at 1, loc_arguments_32 at 1;
    destruct t;
    try match goal with
        | |- Locmap.set ?hi ?vhi
                       (Locmap.set ?lo ?vlo
                                   (Locmap.set ?head ?vhead _)) = _ =>
          rewrite (locmap_set_reorder lo head); 
            [rewrite (locmap_set_reorder hi head);[|simpl;right;Lia.lia]
            |simpl;right;Lia.lia]
        | |- Locmap.set ?x ?v (Locmap.set ?head ?vhead _) = _ =>
          rewrite (locmap_set_reorder x head);[|simpl;right;Lia.lia]
        end;
    try
      match goal with
      | |- context[?x + ?y + ?z] =>
        replace (x + y + z) with (x + z + y) by Lia.lia;
          rewrite IHtyl;
          [replace (x + z + y) with (x + y + z) by Lia.lia; auto|
           simpl; Lia.lia]
      end.

  destruct args; [auto|]; fold set_arguments loc_arguments_32.
  unfold set_arguments at 1, loc_arguments_32 at 1 in IHtyl;
    unfold set_arguments at 1, loc_arguments_32 at 1.
  destruct t;
    match goal with
    | |- Locmap.set ?hi ?vhi
                   (Locmap.set ?lo ?vlo
                               (Locmap.set ?headhi ?vheadhi
                                           (Locmap.set ?headlo ?vheadlo _))) = _ =>
      rewrite (locmap_set_reorder lo headhi); 
        [rewrite (locmap_set_reorder hi headhi);
         [rewrite (locmap_set_reorder lo headlo);
          [rewrite (locmap_set_reorder hi headlo);
           [|simpl;right;Lia.lia]
          |simpl;right;Lia.lia]
         |simpl;right;Lia.lia]
        |simpl;right;Lia.lia]
    | |- Locmap.set ?l ?v
                   (Locmap.set ?headhi ?vhi
                               (Locmap.set ?headlo ?vlo _)) = _ =>
      rewrite (locmap_set_reorder l headhi); 
        [rewrite (locmap_set_reorder l headlo);[|simpl;right;Lia.lia]
        |simpl;right;Lia.lia]
    end;
    match goal with
    | |- context[set_arguments (loc_arguments_32 _ (?x + ?y + ?z))] =>
      replace (x + y + z) with (x + z + y) by Lia.lia;
        rewrite IHtyl;
        [replace (x + z + y) with (x + y + z) by Lia.lia; auto|
         simpl; Lia.lia]
    end.
Qed.