Require Import Coqlib Maps Integers Values Memdata AST Globalenvs.
Require Import Blockset Footprint FMemOpFP GMemory FMemory FMemPerm FMemLemmas MemAux CUAST LDSimDefs Localize ValRels MemInterpolant val_casted Ctypes Floats.

Require Import AsmLocalize Clight ClightLang Clight_local ClightWD.

Lemma init_genv_iff: forall cu ge G,
    ClightLang.init_genv cu ge G <->
    G =  {| Clight.genv_genv := ge; Clight.genv_cenv := cu_comp_env cu |} /\ ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).
Proof. intros. unfold ClightLang.init_genv. tauto. Qed.
Hint Resolve FPlocalize_emp FPlocalize_union : fplocalize.
Lemma init_mem_valid_block:
  forall ge m,
    ClightLang.init_gmem ge m ->
    (forall b, Bset.belongsto (valid_block_bset m) b <-> Plt b (Genv.genv_next ge)).
Proof.
  intros. inv H. destruct H0. inv H0.
  destruct x; simpl in *.
  unfold valid_block_bset, strip, Mem.valid_block, GMem.valid_block in *; simpl in *.
  rewrite dom_match_fm. tauto.
Qed.

Definition env_rel (j:Bset.inj)(a b:block*type):=
  let (la,tya):=a in
  let (lb,tyb):=b in
  val_related j (Vptr la Ptrofs.zero)(Vptr lb Ptrofs.zero) /\ tya = tyb.
                 

Definition env_related (j:Bset.inj)(e e':env):Prop:=
  forall id,
  option_rel (fun (a b:block*type)=> let (la,tya):=a in  let (lb,tyb):=b in    val_related j (Vptr la Ptrofs.zero)(Vptr lb Ptrofs.zero) /\ tya = tyb) (e!id)(e'!id).
Definition tenv_related (j:Bset.inj)(e e':temp_env):Prop:=
  forall id, option_rel (val_related j)(e ! id)(e' ! id).
Ltac det :=
  match goal with
  | [H1: eval_expr ?ge ?sp ?e ?m ?a ?v1,
         H2: eval_expr ?ge ?sp ?e ?m ?a ?v2
     |- _ ] => pose proof (eval_expr_det _ _ _ _ _ _ H1 _ H2);
             subst v1; clear H1
  | [H1: eval_expr_fp ?ge ?sp ?e ?m ?a ?v1,
         H2: eval_expr_fp ?ge ?sp ?e ?m ?a ?v2
     |- _ ] => pose proof (eval_expr_fp_det _ _ _ _ _ _ H1 _ H2);
             subst v1; clear H1
  | [H1: ?x = ?y1, H2: ?x = ?y2 |- _] => rewrite H1 in H2; inv H2
  end.
Ltac inv_eq:=
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; inversion H ;subst
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H
         | H:Some ?P = Some ?Q |- _ => inv H
         end;
  simpl in *;subst;try contradiction;try discriminate.



Definition trans_c_fundef_ast (f:fundef): (AST.fundef function):=
  match f with
    Ctypes.Internal x => AST.Internal x
  | Ctypes.External x _ _ _ => AST.External x
  end.

Fixpoint trans_cu_defs_ast_defs (l:list (ident * globdef fundef Ctypes.type)) : list (ident * globdef (AST.fundef function) Ctypes.type):=
  match l with
    nil => nil
  | (id,x)::ls => cons (match x with
                         Gfun y => (id, Gfun (trans_c_fundef_ast y))
                       | Gvar y => (id,Gvar y)
                       end) (trans_cu_defs_ast_defs ls)
  end.
Fixpoint ef_name_notin (name:String.string)(ids:list (ident* globdef fundef type)) : bool :=
  match ids with
  | nil => true
  | (id, gd) :: ids' =>
    match gd_ef_fun_name gd with
    | Some name' => if String.string_dec name name' then false
                   else ef_name_notin name ids'
    | _ => ef_name_notin name ids'
    end
  end.
Lemma ef_name_notin_correct:
  forall name defs,
    ef_name_notin  name defs = true ->
    forall id gd name',
      In (id,gd) defs ->
      gd_ef_fun_name gd = Some name' ->
      name <> name'.
Proof.
  induction defs; simpl; intros. contradiction.
  destruct a. destruct g. destruct f. simpl in *. inv H0. inv H2. discriminate.
  eapply IHdefs; eauto.
  destruct gd_ef_fun_name eqn:NAME. destruct String.string_dec. discriminate.
  inv H0. inv H2. rewrite NAME in H1. inv H1. auto. eapply IHdefs; eauto.
  inv H0. inv H2. congruence. eapply IHdefs; eauto.
  destruct gd_ef_fun_name eqn:NAME. destruct String.string_dec; try congruence.
  inv H0. inv H2. congruence. eapply IHdefs; eauto.
  inv H0. inv H2. congruence. eapply IHdefs; eauto.
Qed.
Fixpoint nodup_ef ids : bool :=
  match ids with
  | nil => true
  | (id, gd) :: ids' =>
    match gd_ef_fun_name gd with
    | Some name => ef_name_notin name ids' && nodup_ef ids'
    | None => nodup_ef ids'
    end
  end.

Lemma nodup_ef_correct:
  forall ids,
    nodup_ef ids = true ->
    forall n1 n2 id1 gd1 id2 gd2 name1 name2,
      n1 <> n2 ->
      nth_error ids n1 = Some (id1, gd1) ->
      nth_error ids n2 = Some (id2, gd2) ->
      gd_ef_fun_name gd1 = Some name1 ->
      gd_ef_fun_name gd2 = Some name2 ->
      name1 <> name2.
Proof.
  induction ids; simpl; intros.
  rewrite nth_error_nil in H1; discriminate.
  destruct n1, n2; simpl in *; auto. 
  { inv H1. apply nth_error_in in H2.
    rewrite H3 in H.
    intro. inv H1. apply andb_true_iff in H. destruct H.
    eapply ef_name_notin_correct in H2; try exact H; eauto. }
  { inv H2. apply nth_error_in in H1.
    rewrite H4 in H.
    intro. inv H2. apply andb_true_iff in H. destruct H.
    eapply ef_name_notin_correct in H1; try exact H; eauto. }
  rewrite Nat.succ_inj_wd_neg in H0.
  destruct a; eauto. destruct gd_ef_fun_name. apply andb_true_iff in H. destruct H.
  eauto. eauto.
Qed.

Definition wdcu (cu: clight_comp_unit) : Prop :=
  nodup_ef (cu_defs cu) = true /\ nodup_gd_ident (cu_defs cu) = true.

Definition transge cu :=  (Genv.globalenv {|AST.prog_defs := cu_defs cu; AST.prog_public := cu_public cu; AST.prog_main := 1%positive |}).
Lemma norepet_defs_gd_ident_exists:
  forall cu,
    list_norepet (map fst (cu_defs cu)) ->
    forall b gd,
      PTree.get b (Genv.genv_defs (transge cu)) = Some gd ->
      exists id, PTree.get id (Genv.genv_symb (transge cu)) = Some b.
Proof.
  intros until cu. destruct cu; simpl. intro NOREPET.
  unfold transge.
  unfold Genv.globalenv. simpl. revert NOREPET.
  replace cu_defs with (rev (rev cu_defs)); try apply rev_involutive.
  generalize (rev cu_defs). clear cu_defs. intro rcu_defs.
  induction (rcu_defs); intros; simpl in H.
  rewrite PTree.gempty in H. discriminate.
  rewrite map_rev in NOREPET. simpl in NOREPET.
  apply list_norepet_append_commut in NOREPET. simpl in NOREPET. inv NOREPET.
  rewrite <-map_rev in H3. specialize (IHl H3). simpl.
  rewrite Genv.add_globals_app in H. 
  rewrite Genv.add_globals_app. simpl in *.
  destruct (peq b (Genv.genv_next (Genv.add_globals (Genv.empty_genv fundef type cu_public) (rev l)))).
  subst. exists (fst a). rewrite PTree.gss. auto.
  rewrite PTree.gso in H; auto. pose proof H. apply IHl in H. destruct H.
  exists x. rewrite PTree.gso; auto. intro. subst.
  exploit (Genv.find_symbol_inversion (Build_comp_unit_generic _ _ (rev l) cu_public)).
  unfold Genv.globalenv. simpl. eauto.
  unfold prog_defs_names. simpl. rewrite map_rev. auto.
Qed.

Lemma nodup_gd_ident_exists:
  forall cu,
    nodup_gd_ident (cu_defs cu) = true ->
    forall b gd,
      PTree.get b (Genv.genv_defs (transge cu)) = Some gd ->
      exists id, PTree.get id (Genv.genv_symb (transge cu)) = Some b.
Proof. intros until 1. apply norepet_defs_gd_ident_exists. apply nodup_gd_ident_no_repet. auto. Qed.

Lemma nodup_gd_ident_exists':
  forall cu,
    nodup_gd_ident (cu_defs cu) = true ->
    forall b gd,
      PTree.get b (Genv.genv_defs (transge cu)) = Some gd ->
      exists id, In (id, gd) (cu_defs cu) /\  PTree.get id (Genv.genv_symb (transge cu)) = Some b.
Proof.
  intros. exploit nodup_gd_ident_exists;eauto. intros [id FIND].
  exists id;split;auto.
  unfold transge in *.
  assert ((prog_defmap (mkprogram (cu_defs cu) (cu_public cu) 1%positive))! id = Some gd).
  apply Genv.find_def_symbol;eauto.
  eapply in_prog_defmap in H1;eauto.
Qed.
Lemma wdcu_goodge:
  forall cu (R:wdcu cu) b gd, (Genv.genv_defs (transge cu)) ! b = Some gd -> exists id, (Genv.genv_symb (transge cu)) ! id = Some b.
Proof.
  intros.
  destruct R.
  eapply nodup_gd_ident_exists in H1;eauto.
Qed.

Lemma nodup_ef_ge_norep_ef_name:
  forall cu,
    wdcu cu->
    norep_ef_name (transge cu).
Proof.
  destruct 1.
  unfold transge.
  unfold norep_ef_name.
  intros.

  exploit nodup_gd_ident_exists';try eexact H1;eauto.
  intros [id1 [IN1 FIND1]].
  exploit nodup_gd_ident_exists';try eexact H2;eauto.
  intros [id2 [IN2 FIND2]].
  unfold Genv.find_def,transge in *.
  unfold Genv.globalenv in *. simpl in *.
  assert(id1 <> id2).
  { intro. apply H1. congruence. }
  apply In_nth_error in IN1 as [n1 IN1].
  apply In_nth_error in IN2 as [n2 IN2].
  assert(n2 <> n1). intro;subst. apply H1;congruence.
  eapply nodup_ef_correct;try eassumption.
Qed.  
Lemma weak_valid_pointer_related:
  forall (j : Bset.inj) (bound : block) (fl : freelist) 
    (m : Memory.Mem.mem) (m' : mem) (b b' : block) (ofs : Z),
    mem_related j bound fl (strip m') m ->
    construct_inj j bound fl b = Some b' ->
    Memory.Mem.weak_valid_pointer m b ofs = Mem.weak_valid_pointer m' b' ofs.
Proof.
  unfold Memory.Mem.weak_valid_pointer,Mem.weak_valid_pointer.
  intros.
  do 2 (erewrite valid_pointer_related;eauto).
Qed.
Lemma env_related_set:
  forall j e e',
    env_related j e e'->
    forall id b b' ty,
      val_related j (Vptr b Ptrofs.zero)(Vptr b' Ptrofs.zero)->
      env_related j (PTree.set id (b,ty) e)(PTree.set id (b',ty) e').
Proof.
  unfold env_related.
  intros.
  do 2 rewrite PTree.gsspec.
  destruct peq;auto. constructor. auto.
Qed.     
Section EXPR.
  Variable sge tge:Clight.genv.
  Variable j:Bset.inj.
  Hypothesis GEMATCH: ge_match_strict j (genv_genv sge)(genv_genv tge).
  Hypothesis GEQ: genv_cenv sge = genv_cenv tge.
  Definition bound:=(Genv.genv_next(genv_genv sge)).
  Hypothesis INJECT : Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound).
Section SEM_EXPR.  
  Variable e e':env.
  Variable le le':temp_env.
  Variable fm:FMemory.mem.
  Variable m:Memory.mem.
  Definition fl:=FMemory.Mem.freelist fm.
  Hypothesis MEMREL: mem_related j bound fl (strip fm) m.
  Definition j' := construct_inj j bound fl.
  Hypothesis ENVREL: env_related j' e' e.
  Hypothesis TENVREL: tenv_related j' le' le.
  Hypothesis NOREP: norep fl.
  Hypothesis NOOVERLAP: no_overlap fl (fun b=>Plt b bound).

  
  Lemma injective_j':
    forall b b0 b',
      j' b = Some b' ->
      j' b0 = Some b' ->
      b = b0.
  Proof.
    unfold j',construct_inj.
    intros.
    destruct plt,plt.

    inv GEMATCH;eauto.
    inversion H0. eapply NOOVERLAP in H2.
    unfold Bset.belongsto in H2.
    inv INJECT.
    inv inj_weak.
    apply inj_range' in H. unfold Bset.belongsto in H.
    contradiction.

    rename H into H1;rename H0 into H;rename H1 into H0.
    inversion H0. eapply NOOVERLAP in H2.
    unfold Bset.belongsto in H2.
    inv INJECT.
    inv inj_weak.
    apply inj_range' in H. unfold Bset.belongsto in H.
    contradiction.

    unfold get_block in *.
    inv_eq.
    destruct (peq b b0);auto.
    inv NOREP.
    assert((Pos.to_nat b - Pos.to_nat bound)%nat <> (Pos.to_nat b0 - Pos.to_nat bound)%nat).
    xomega.
    apply H in H0. contradiction.
  Qed.
  
  Lemma bool_val_related:
    forall v ty b v',
      val_related j' v' v->
      FCop.bool_val v ty fm = Some b->
      Cop.bool_val v' ty m = Some b .
  Proof.
    unfold FCop.bool_val,Cop.bool_val.
    intros.
    destruct (Cop.classify_bool ty);simpl;intros;try discriminate.
    all:inv H;try discriminate;try congruence.
    destruct Archi.ptr64;try discriminate.
    destruct Mem.weak_valid_pointer eqn:?;try discriminate.
    inv H0.
    
    unfold j' in H1.
    erewrite weak_valid_pointer_related,Heqb1;eauto.
  Qed.
  Lemma bool_val_fp_related:
    forall v ty b v',
      val_related j' v' v->
      Cop_fp.bool_val_fp v ty fm = Some b->
      exists b',
        Cop_fp_local.bool_val_fp v' ty m = Some b'/\FPlocalize j' b b'.
  Proof.
    unfold Cop_fp.bool_val_fp,Cop_fp_local.bool_val_fp.
    intros.
    destruct (Cop.classify_bool ty);simpl;intros;try discriminate.
    all:inv H;try discriminate;inv_eq;Esimpl;eauto with fplocalize.
    eapply weak_valid_pointer_fp_localize;eauto.
  Qed.
  Lemma sem_unary_operation_localize:
    forall v v',
      val_related j' v' v->
      forall op ty resv,
        FCop.sem_unary_operation op v ty fm = Some resv->
        exists resv',
          Cop.sem_unary_operation op v' ty m = Some resv' /\
          val_related j' resv' resv.
  Proof.
    destruct op;simpl.
    {
      unfold FCop.sem_notbool,Cop.sem_notbool,option_map.
      intros.
      destruct (FCop.bool_val) eqn:?;try discriminate.
      inv H0.
      erewrite bool_val_related;eauto.
    }
    {
      unfold Cop.sem_notint;intros.
      destruct (Cop.classify_notint);try discriminate; inv H;try discriminate;Esimpl;eauto.
      all: inv H0; constructor.
    }
    {
      unfold Cop.sem_neg;intros.
      destruct (Cop.classify_neg);try discriminate; inv H;try discriminate;Esimpl;eauto;inv H0;try constructor.
    }
    {
      unfold Cop.sem_absfloat;intros.
      destruct (Cop.classify_neg);try discriminate; inv H;try discriminate;Esimpl;eauto;inv H0;try constructor.
    }
  Qed.
  Lemma sem_unary_operation_fp_localize:
    forall v v',
      val_related j' v' v->
      forall op ty,
        option_rel (FPlocalize j') (Cop_fp.sem_unary_operation_fp op v ty fm)(Cop_fp_local.sem_unary_operation_fp op v' ty m).
  Proof.
    unfold Cop_fp.sem_unary_operation_fp,Cop_fp_local.sem_unary_operation_fp.
    intros v v' REL [] ty.
    {
      unfold Cop_fp.sem_notbool_fp,Cop_fp_local.sem_notbool_fp.
      unfold Cop_fp.bool_val_fp,Cop_fp_local.bool_val_fp.
      destruct Cop.classify_bool ;try discriminate;try constructor.
      all: inv REL;try discriminate;try constructor.
      all: try apply FPlocalize_emp.
      apply weak_valid_pointer_fp_localize;auto.
    }
    {
      unfold Cop.sem_notint.
      destruct Cop.classify_notint ;try discriminate;try constructor.
      all: inv REL;try discriminate;try constructor;try apply FPlocalize_emp.
    }
    {
      unfold Cop.sem_neg.
      destruct Cop.classify_neg ;try discriminate;try constructor.
      all: inv REL;try discriminate;try constructor;try apply FPlocalize_emp.
    }
    {
      unfold Cop.sem_absfloat.
      destruct Cop.classify_neg ;try discriminate;try constructor.
      all: inv REL;try discriminate;try constructor;try apply FPlocalize_emp.
    }
  Qed.
  Lemma sizeof_eq:
    forall ty,
      Ctypes.sizeof sge ty = Ctypes.sizeof tge ty.
  Proof.
    induction ty;simpl;auto;try congruence.
    all: rewrite GEQ;auto.
  Qed.
  Lemma alignof_eq:
    forall ty,
      Ctypes.alignof sge ty = Ctypes.alignof tge ty.
  Proof.
    induction ty;simpl;auto;try congruence.
    all:rewrite GEQ;auto.
  Qed.
  Definition binary_related_correct
             (sem: val->type->val->type->mem->option val)
             (sem2: val->type->val->type->Memory.Mem.mem->option val) :Prop:=
    forall va tya vb tyb v,
      sem va tya vb tyb fm = Some v->
      forall va' vb',
        val_related j' va' va ->
        val_related j' vb' vb ->
        exists v',
          sem2 va' tya vb' tyb m = Some v' /\ val_related j' v' v.
  Definition binary_fp_related_correct
             (semfp: val->type->val->type->mem->option FP.t)
             (semfp2: val->type->val->type->Memory.Mem.mem->option FP.t) :Prop:=
    forall va tya vb tyb fp,
      semfp va tya vb tyb fm = Some fp->
      forall va' vb',
        val_related j' va' va->
        val_related j' vb' vb->
        exists fp',semfp2 va' tya vb' tyb m = Some fp' /\ FPlocalize j' fp fp'.
  Section MAKE_BIN.
    Variable sem_int: signedness -> int -> int -> option val.
    Variable sem_long: signedness -> int64 -> int64 -> option val.
    Variable sem_float: float -> float -> option val.
    Variable sem_single: float32 -> float32 -> option val.
    Definition notptr v:=
      match v with
      | Vptr _ _ => false
      | _ => true
      end = true.
    Hypothesis sem_int_rel:
      forall sg a b i, sem_int sg a b = Some i-> notptr i.
    Hypothesis sem_long_rel:
      forall sg a b i, sem_long sg a b = Some i-> notptr i.
    Hypothesis sem_float_rel:
      forall a b i, sem_float a b = Some i-> notptr i.
    Hypothesis sem_single_rel:
      forall a b i, sem_single a b = Some i-> notptr i.
    Lemma sem_cast_related:
      forall va va',
        val_related j' va' va->
        forall tya ty res,
          FCop.sem_cast va tya ty fm = Some res ->
          exists res',
            Cop.sem_cast va' tya ty m = Some res' /\ val_related j' res' res.
    Proof.
      unfold FCop.sem_cast,Cop.sem_cast.
      intros.
      destruct Cop.classify_cast;inv H;try discriminate;try (inv_eq;Esimpl;eauto;econstructor;fail).
      erewrite weak_valid_pointer_related;eauto.
      inv_eq. Esimpl;eauto. constructor.
    Qed.
    Lemma sem_cast_fp_related:
      forall va va',
        val_related j' va' va->
        forall tya ty fp,
          Cop_fp.sem_cast_fp va tya ty fm = Some fp ->
          exists fp', Cop_fp_local.sem_cast_fp va' tya ty m = Some fp' /\ FPlocalize j' fp fp'.
    Proof.
      unfold Cop_fp.sem_cast_fp,Cop_fp_local.sem_cast_fp.
      intros.
      destruct Cop.classify_cast;inv H;try discriminate;try (inv_eq;Esimpl;eauto;try apply FPlocalize_emp;fail).
      inv_eq.
      exploit weak_valid_pointer_fp_localize;eauto.
    Qed.
    Lemma sem_cast_related2:
      forall va va',
        val_related j' va' va->
        forall tya ty,
          FCop.sem_cast va tya ty fm =None->
          Cop.sem_cast va' tya ty m = None.
    Proof.
      unfold FCop.sem_cast,Cop.sem_cast.
      intros.
      destruct Cop.classify_cast;inv H;try discriminate;try (inv_eq;Esimpl;eauto;econstructor;fail).
      inv_eq. erewrite weak_valid_pointer_related;eauto. rewrite Heqb1. auto.
    Qed.
    Lemma sem_binarith_correct:
      binary_related_correct (FCop.sem_binarith sem_int sem_long sem_float sem_single)(Cop.sem_binarith sem_int sem_long sem_float sem_single).
    Proof.
      red. unfold FCop.sem_binarith,Cop.sem_binarith;intros until v;intros SEM ? ? REL1 REL2.
      set (cls := Cop.classify_binarith tya tyb) in *.
      set (ty := Cop.binarith_type cls) in *.
      destruct (FCop.sem_cast va tya ty fm) as [va2|] eqn:Ca;try discriminate.
      destruct (FCop.sem_cast vb tyb ty fm) as [vb2|] eqn:Cb;try discriminate.
      eapply sem_cast_related in Ca as Ca';eauto.
      eapply sem_cast_related in Cb as Cb';eauto.
      destruct Ca' as [va2'[Ca' REL3]],Cb' as [vb2'[Cb' REL4]].
      rewrite Ca',Cb'.
      destruct cls;try discriminate.
      all: inv REL3;inv REL4;try discriminate.
      all: Esimpl;eauto.
      eapply sem_int_rel in SEM;inv SEM;inv_eq;constructor.
      eapply sem_long_rel in SEM;inv SEM;inv_eq;constructor.
      eapply sem_float_rel in SEM;inv SEM;inv_eq;constructor.
      eapply sem_single_rel in SEM;inv SEM;inv_eq;constructor.
    Qed.

    Lemma sem_binarith_fp_correct:
      binary_fp_related_correct (Cop_fp.sem_binarith_fp sem_int sem_long sem_float sem_single)(Cop_fp_local.sem_binarith_fp sem_int sem_long sem_float sem_single).
    Proof.
      red. unfold Cop_fp.sem_binarith_fp,Cop_fp_local.sem_binarith_fp;intros until vb';intros REL1 REL2.
      set (cls := Cop.classify_binarith tya tyb) in *.
      set (ty := Cop.binarith_type cls) in *.
            
      destruct (FCop.sem_cast va tya ty fm) as [va2|] eqn:Ca;try discriminate.
      eapply sem_cast_related in Ca as Ca';eauto.
      destruct Ca' as [va2'[Ca' REL3]].
      rewrite Ca'.

      destruct (Cop_fp.sem_cast_fp va tya ty fm) as [fpa|] eqn:FPA;try discriminate.
      eapply sem_cast_fp_related in FPA as FPA';eauto.
      destruct FPA' as [fpa'[FPA' FPREL1]].
      rewrite FPA'.
      
      destruct (FCop.sem_cast vb tyb ty fm) as [vb2|] eqn:Cb;try discriminate.
      eapply sem_cast_related in Cb as Cb';eauto.
      destruct Cb' as [vb2'[Cb' REL4]].
      rewrite Cb'.
      
      destruct (Cop_fp.sem_cast_fp vb tyb ty fm) as [fpb|] eqn:FPB;try discriminate.
      eapply sem_cast_fp_related in FPB as FPB';eauto.
      destruct FPB' as [fpb'[FPB' FPREL2]].
      rewrite FPB'.
      
      destruct cls;try discriminate.
      all: inv REL3;inv REL4;try discriminate;inv_eq.
      all: Esimpl;eauto;eapply FPlocalize_union;eauto.
    Qed.
  End MAKE_BIN.


  
  Lemma sem_add_correct:
    binary_related_correct (FCop.sem_add sge)(Cop.sem_add tge).
  Proof.
    red. unfold Cop.sem_add,FCop.sem_add.
    intros until v. intros SEM ? ? REL1 REL2.
    destruct (Cop.classify_add tya tyb);eauto.
    1-4: unfold Cop.sem_add_ptr_int,Cop.sem_add_ptr_long in *;inv REL1;inv REL2;try discriminate;
      [destruct Archi.ptr64;try discriminate;inv SEM;Esimpl;eauto;rewrite sizeof_eq;constructor|inv SEM;rewrite <-sizeof_eq;econstructor;eauto].
    eapply sem_binarith_correct in SEM;eauto.
    all: intros;inv_eq;eauto;unfold notptr;auto.
  Qed.
  Lemma sem_add_fp_correct:
    binary_fp_related_correct (Cop_fp.sem_add_fp sge)(Cop_fp_local.sem_add_fp tge).
  Proof.
    red;unfold Cop_fp.sem_add_fp,Cop_fp_local.sem_add_fp.
    intros until fp;intros SEM ? ? REL1 REL2.
    destruct (Cop.classify_add tya tyb);eauto.
    1-4: unfold Cop.sem_add_ptr_int,Cop.sem_add_ptr_long in *;inv REL1;inv REL2;try discriminate;inv_eq;Esimpl;eauto;try apply FPlocalize_emp.
    eapply sem_binarith_fp_correct;eauto.
  Qed.
  Lemma sem_sub_correct:
    binary_related_correct (FCop.sem_sub sge)(Cop.sem_sub tge).
  Proof.
    red. unfold Cop.sem_sub,FCop.sem_sub.
    intros until v. intros SEM ? ? REL1 REL2.
    destruct (Cop.classify_sub tya tyb);eauto.
    {
      inv REL1;inv REL2;try discriminate.
      destruct Archi.ptr64;try discriminate;inv SEM;Esimpl;eauto;rewrite sizeof_eq;constructor.
      inv SEM. Esimpl;eauto. rewrite sizeof_eq;constructor;auto.
    }
    {
      inv REL1;inv REL2;try discriminate.
      inv_eq. eapply injective_j' in H;eauto;subst b0.
      destruct (eq_block b b);try contradiction.
      Esimpl;eauto. constructor.
    }
    {
      inv REL1;inv REL2;try discriminate;inv_eq; Esimpl;eauto.
    }
    eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr;eauto.
  Qed.

  Lemma sem_sub_fp_correct:
    binary_fp_related_correct (Cop_fp.sem_sub_fp sge)(Cop_fp_local.sem_sub_fp tge).
  Proof.
    red. unfold Cop_fp.sem_sub_fp,Cop_fp_local.sem_sub_fp.
    intros until fp. intros SEM ? ? REL1 REL2.
    destruct (Cop.classify_sub tya tyb);eauto.
    {
      inv REL1;inv REL2;try discriminate.
      destruct Archi.ptr64;try discriminate;inv SEM;Esimpl;eauto with fplocalize.
      inv SEM;Esimpl;eauto with fplocalize.
    }
    {
      inv REL1;inv REL2;try discriminate.
      inv_eq. eapply injective_j' in H;eauto;subst b0.
      destruct (eq_block b b);try contradiction.
      Esimpl;eauto with fplocalize.
    }
    {
      inv REL1;inv REL2;try discriminate;inv_eq; Esimpl;eauto with fplocalize.
    }
    eapply sem_binarith_fp_correct;eauto with fplocalize.
  Qed.
  Lemma sem_mul_correct:
    binary_related_correct FCop.sem_mul Cop.sem_mul .
  Proof. red; eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr;eauto.
  Qed.
  Lemma sem_mul_fp_correct:
    binary_fp_related_correct Cop_fp.sem_mul_fp Cop_fp_local.sem_mul_fp .
  Proof. red; eapply sem_binarith_fp_correct;eauto with fplocalize.
  Qed.
  Lemma sem_div_correct:
    binary_related_correct FCop.sem_div Cop.sem_div.
  Proof.  red ;eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr;eauto.  Qed.
  Lemma sem_div_fp_correct:
    binary_fp_related_correct Cop_fp.sem_div_fp Cop_fp_local.sem_div_fp .
  Proof. red; eapply sem_binarith_fp_correct;eauto with fplocalize.
  Qed.
  Lemma sem_mod_correct:
    binary_related_correct FCop.sem_mod Cop.sem_mod.
  Proof. eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr;eauto. Qed.
  Lemma sem_mod_fp_correct:
    binary_fp_related_correct Cop_fp.sem_mod_fp Cop_fp_local.sem_mod_fp .
  Proof. red; eapply sem_binarith_fp_correct;eauto with fplocalize.
  Qed.
  Lemma sem_and_correct:
    binary_related_correct FCop.sem_and Cop.sem_and.
  Proof. eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr;eauto. Qed.
  Lemma sem_and_fp_correct:
    binary_fp_related_correct Cop_fp.sem_and_fp Cop_fp_local.sem_and_fp .
  Proof. red; eapply sem_binarith_fp_correct;eauto with fplocalize.
  Qed.
  Lemma sem_or_correct:
    binary_related_correct FCop.sem_or Cop.sem_or.
  Proof. eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr;eauto. Qed.
  Lemma sem_or_fp_correct:
    binary_fp_related_correct Cop_fp.sem_or_fp Cop_fp_local.sem_or_fp .
  Proof. red; eapply sem_binarith_fp_correct;eauto with fplocalize.
  Qed.
  Lemma sem_xor_correct:
    binary_related_correct FCop.sem_xor Cop.sem_xor.
  Proof. eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr;eauto. Qed.
  Lemma sem_xor_fp_correct:
    binary_fp_related_correct Cop_fp.sem_xor_fp Cop_fp_local.sem_xor_fp .
  Proof. red; eapply sem_binarith_fp_correct;eauto with fplocalize.
  Qed.
  Lemma cmp_ptr_correct:
    forall v1 v1' v2 v2',
      val_related j' v1' v1->
      val_related j' v2' v2->
      forall op res,
        FCop.cmp_ptr fm op v1 v2 = Some res->
        exists res', Cop.cmp_ptr m op v1' v2' = Some res' /\ val_related j' res' res.
  Proof.
    unfold FCop.cmp_ptr,Cop.cmp_ptr in *.
    destruct Archi.ptr64 eqn:?;try discriminate.
    unfold option_map in *.
    intros.
    inv_eq.
    eapply cmpu_bool_related with(c:=op) in H0 as ?;try apply H;eauto.
    inv H1;inv_eq.
    Esimpl;eauto.
  Qed.
  Lemma cmp_ptr_fp_correct:
    forall v1 v1' v2 v2',
      val_related j' v1' v1->
      val_related j' v2' v2->
      forall op res,
        Cop_fp.cmp_ptr_fp fm op v1 v2 = Some res->
        exists res', Cop_fp_local.cmp_ptr_fp m op v1' v2' = Some res' /\ FPlocalize j' res res'.
  Proof.
    unfold Cop_fp.cmp_ptr_fp,Cop_fp_local.cmp_ptr_fp.
    destruct Archi.ptr64 eqn:?;try discriminate.
    intros.
    eapply cmpu_fp_localize with(c:=op) in H0 as ?;try apply H;eauto.
    unfold ASM_local.of_optfp in H2.
    rewrite H1 in H2.
    Esimpl;eauto.
    unfold ValFP.cmpu_bool_fp,ValFP.cmpu_bool_fp_total,Cop_fp.cmpu_bool_fp in *.
    inv H;inv H0;try discriminate;auto.
    all: destruct Archi.ptr64 eqn:?;try discriminate.
    all: try(inv_eq;auto).
    eapply injective_j' in H3;eauto. congruence.
  Qed.
  Ltac inv_val_rel:=
    match goal with
    | H: val_related _ _ _ |- _ => inv H;try discriminate
    end.
  Ltac goal_destruct:=
    match goal with
    | H:_ |- context[if ?x then Vtrue else Vfalse] => destruct x
    end.
  Ltac solv_cmp:=
    unfold FCop.sem_cmp,Cop.sem_cmp in *;
    destruct Cop.classify_cmp eqn:?;try discriminate;
    try(eapply sem_binarith_correct;eauto;intros;inv_eq;unfold notptr,Val.of_bool;
        goal_destruct;auto;fail);
    try(inv_val_rel;inv_val_rel;inv_eq;try(eapply cmp_ptr_correct;eauto;constructor);fail).
  Lemma sem_binary_operation_localize:
    forall v1 v2 v1' v2',
      val_related j' v1' v1 ->
      val_related j' v2' v2 ->
      forall op res t1 t2,
        FCop.sem_binary_operation sge op v1 t1 v2 t2 fm = Some res ->
        exists res',
          Cop.sem_binary_operation tge op v1' t1 v2' t2 m = Some res' /\
          val_related j' res' res.
  Proof.
    destruct op;simpl;intros.
    eapply sem_add_correct;eauto.
    eapply sem_sub_correct;eauto.
    eapply sem_mul_correct;eauto.
    eapply sem_div_correct;eauto.
    eapply sem_mod_correct;eauto.
    eapply sem_and_correct;eauto.
    eapply sem_or_correct;eauto.
    eapply sem_xor_correct;eauto.
    {
      unfold Cop.sem_shl,Cop.sem_shift in *.
      destruct ( Cop.classify_shift t1 t2 ) eqn:?;try discriminate;
        inv H;inv H0;try discriminate.
      all: inv_eq;Esimpl;eauto.
    }
    {
      unfold Cop.sem_shr,Cop.sem_shift in *.
      destruct Cop.classify_shift eqn:?;try discriminate;
        inv H;inv H0;try discriminate;
          inv_eq;Esimpl;eauto.
    }
    all: solv_cmp.
  Qed.
  Lemma deref_loc_related:
    forall ty loc ofs v,
      deref_loc ty fm loc ofs v ->
      forall loc' ofs',
        val_related j' (Vptr loc' ofs')(Vptr loc ofs) ->
        exists v', Clight.deref_loc ty m loc' ofs' v' /\ val_related j' v' v.
  Proof.
    inversion 1;subst;intros.
    exploit loadv_related;eauto;intro;simpl in *.
    rewrite H1 in H3. inv H3.
    Esimpl;eauto. econstructor;eauto.
    Esimpl;eauto. econstructor 2;eauto.
    Esimpl;eauto. econstructor 3;eauto.
  Qed.
  Lemma sem_binary_operation_fp_localize:
    forall v1 v2 v1' v2',
      val_related j' v1' v1 ->
      val_related j' v2' v2 ->
      forall op res t1 t2,
        Cop_fp.sem_binary_operation_fp sge op v1 t1 v2 t2 fm = Some res ->
        exists res',
          Cop_fp_local.sem_binary_operation_fp tge op v1' t1 v2' t2 m = Some res' /\
          FPlocalize j' res res'.
  Proof.
    destruct op;simpl;intros.
    eapply sem_add_fp_correct;eauto.
    eapply sem_sub_fp_correct;eauto.
    eapply sem_mul_fp_correct;eauto.
    eapply sem_div_fp_correct;eauto.
    eapply sem_mod_fp_correct;eauto.
    eapply sem_and_fp_correct;eauto.
    eapply sem_or_fp_correct;eauto.
    eapply sem_xor_fp_correct;eauto.
    {
      unfold Cop.sem_shl,Cop.sem_shift in *.
      destruct ( Cop.classify_shift t1 t2 ) eqn:?;try discriminate;
        inv H;inv H0;try discriminate.
      all: inv_eq;Esimpl;eauto with fplocalize.
    }
    {
      unfold Cop.sem_shr,Cop.sem_shift in *.
      destruct Cop.classify_shift eqn:?;try discriminate;
        inv H;inv H0;try discriminate;
          inv_eq;Esimpl;eauto with fplocalize.
    }
    Ltac solv_cmp_fp:=
    unfold Cop_fp.sem_cmp_fp,Cop_fp_local.sem_cmp_fp in *;
    destruct Cop.classify_cmp eqn:?;try discriminate;
    try(eapply sem_binarith_fp_correct;eauto;fail);
    try(inv_val_rel;inv_val_rel;inv_eq;try(eapply cmp_ptr_fp_correct;eauto;try constructor);fail).
    all: solv_cmp_fp.
  Qed.
  Lemma eval_expr_lvalue_localize:
    (forall a v,
        ClightLang.eval_expr sge e le fm a v ->
        exists v',
          Clight.eval_expr tge e' le' m a v' /\
          val_related j' v' v) /\
    (forall a b ofs,
        ClightLang.eval_lvalue sge e le fm a b ofs ->
        exists b' ofs',
          Clight.eval_lvalue tge e' le' m a b' ofs' /\
          val_related j' (Vptr b' ofs')(Vptr b ofs)).
  Proof.
    apply eval_expr_lvalue_ind;intros.
    all: Hsimpl;try (Esimpl;eauto;try econstructor;eauto;fail).
    {
      specialize (TENVREL id).
      inv TENVREL;try congruence.
      rewrite H in H1;inv H1.
      Esimpl;eauto. econstructor;eauto.
    }
    {
      eapply sem_unary_operation_localize in H1;eauto.
      Hsimpl;Esimpl;eauto. econstructor;eauto.
    }
    {
      Hsimpl.
      eapply sem_binary_operation_localize in H3;eauto.
      Hsimpl;Esimpl;eauto. econstructor;eauto.
    }
    {
      eapply sem_cast_related in H1;eauto.
      Hsimpl;Esimpl;eauto. econstructor;eauto.
    }
    {
      Esimpl. econstructor;eauto.
      unfold Vptrofs. destruct Archi.ptr64 eqn:?;try discriminate.
      rewrite sizeof_eq. constructor.
    }
    {
      Esimpl;eauto. econstructor;eauto.
      rewrite alignof_eq. constructor.
    }
    {
      
     
      eapply deref_loc_related in H1 as ?;eauto.
      Hsimpl;Esimpl;eauto. econstructor;eauto.
    }
    {
      unfold env_related in ENVREL.
      specialize (ENVREL id).
      rewrite H in *.
      inv ENVREL. destruct x.
      destruct H2.
      subst.
      Esimpl;eauto. econstructor;eauto.
    }
    {
      unfold env_related in ENVREL.
      specialize (ENVREL id).
      rewrite H in *.
      inv ENVREL.
      eapply Localize.ge_match_strict_senv with(id0:=id) in GEMATCH as ?.
      inv H1;inv_eq.
      
      
      
      Esimpl;eauto. econstructor 2;eauto.
      econstructor;eauto.

      unfold j'.
      unfold construct_inj.
      destruct plt;auto.

      eapply INJECT in H6. unfold Bset.belongsto in H6. contradiction.
    }
    {
      inv H1. 
      Esimpl;eauto. econstructor;eauto.
    }
    {
      inv H4.
      rewrite GEQ in *.
      Esimpl;eauto. econstructor;eauto.
    }
    {
      inv H3.
      rewrite GEQ in *.
      Esimpl;econstructor;eauto.
    }
  Qed.

  Lemma eval_expr_localize:
    forall a v,
      ClightLang.eval_expr sge e le fm a v ->
      exists v',
        Clight.eval_expr tge e' le' m a v' /\
        val_related j' v' v.
  Proof. pose (proj1 eval_expr_lvalue_localize). auto. Qed.

  
  Lemma eval_lvalue_localize:
    forall a b ofs,
      ClightLang.eval_lvalue sge e le fm a b ofs ->
      exists b' ofs',
        Clight.eval_lvalue tge e' le' m a b' ofs' /\
        val_related j' (Vptr b' ofs')(Vptr b ofs).
  Proof. pose (proj2 eval_expr_lvalue_localize). auto. Qed.

  Lemma deref_loc_fp_related:
    forall ty loc ofs fp,
      ClightLang.deref_loc_fp ty loc ofs fp->
      forall loc' ofs',
        val_related j' (Vptr loc' ofs')(Vptr loc ofs)->
        exists fp', Clight_local.deref_loc_fp ty loc' ofs' fp' /\ FPlocalize j' fp fp'.
  Proof.
    assert(INJ:Bset.inj_inject j').
    unfold Bset.inj_inject. apply injective_j'.
    inversion 1;subst;intros.
    {
      Esimpl;eauto. econstructor;eauto.
      eapply loadv_fp_localize;eauto.
    }
    {
      Esimpl;eauto with fplocalize. econstructor 2;eauto with fplocalize.
    }
    {
      Esimpl;eauto with fplocalize.
      econstructor 3;eauto.
    }
  Qed.
  Lemma eval_expr_lvalue_fp_localize:
    (forall a fp,
        ClightLang.eval_expr_fp sge e le fm a fp ->
        forall v (EX:ClightLang.eval_expr sge e le fm a v),
          exists fp',
            Clight_local.eval_expr_fp tge e' le' m a fp'/\  FPlocalize j' fp fp') /\
    (forall a v,
        ClightLang.eval_lvalue_fp sge e le fm a v ->
         forall b ofs (EX:ClightLang.eval_lvalue sge e le fm a b ofs),
           exists v',
             Clight_local.eval_lvalue_fp tge e' le' m a v' /\
             FPlocalize j' v v').
  Proof.
    apply ClightLang.eval_expr_lvalue_fp_ind;intros.
    all: try( eapply eval_expr_localize in EX as EX';eauto;destruct EX' as [v'[EX' REL]];eauto).
    all: try(Hsimpl;Esimpl;eauto with fplocalize;constructor;auto;fail).
    {
      inv EX.
      specialize (H0 _ _ H4).
      Hsimpl; Esimpl;eauto. econstructor;eauto.

      inv H1.
    }
    {
      specialize (H1 _ H).

      eapply eval_expr_localize in H as ?;eauto.
      Hsimpl.

      eapply sem_unary_operation_fp_localize in H6 as ?;eauto.
      rewrite H3 in H8. inv H8.
      eapply sem_unary_operation_localize in H6 as ?;eauto.
      Hsimpl.
      Esimpl;eauto with fplocalize.
      econstructor;eauto.
    }
    {
      specialize (H1 _ H).
      specialize (H4 _ H2).
      Hsimpl.
      eapply eval_expr_localize in H as ?;eauto.
      eapply eval_expr_localize in H2 as ?;eauto.
      eapply eval_expr_localize in EX as ?;eauto.
      Hsimpl.
      eapply sem_binary_operation_localize in H5 as ? ;eauto.
      Hsimpl.
      eapply sem_binary_operation_fp_localize in H6 as ?;eauto.
      Hsimpl.
      rewrite <- H7.
      Esimpl;eauto with fplocalize. econstructor;eauto. 
    }
    {
      specialize (H1 _ H).
      eapply eval_expr_localize in H as ?;eauto.
      Hsimpl.
      eapply sem_cast_related in H2 as ?;eauto.
      eapply sem_cast_fp_related in H3 as ?;eauto.
      Hsimpl.
      rewrite <- H4.
      Esimpl;eauto with fplocalize. econstructor;eauto.
    }
    {
      specialize (H1 _ _ H).
      eapply eval_lvalue_localize in H as ?;eauto;Hsimpl.
      eapply deref_loc_related in H2 as ?;eauto;Hsimpl.


      eapply deref_loc_fp_related in H3 as ?;eauto.
      Hsimpl.
      rewrite <- H4.
      Esimpl;eauto with fplocalize.
      econstructor;eauto.
    }
    {
      specialize (H1 _ H).
      Hsimpl.
      eapply eval_expr_localize in H as ?;eauto.
      Hsimpl.
      Esimpl;eauto. econstructor;eauto.
    }
    {
      specialize (H1 _ H).
      Hsimpl. eapply eval_expr_localize in H as ?;eauto.
      Hsimpl. Esimpl;eauto. econstructor;eauto.
    }
  Qed.
  Lemma eval_expr_fp_localize:
    forall a fp,
      ClightLang.eval_expr_fp sge e le fm a fp ->
      forall v (EX:ClightLang.eval_expr sge e le fm a v),
      exists fp',
        Clight_local.eval_expr_fp tge e' le' m a fp'/\  FPlocalize j' fp fp'.
  Proof. pose (proj1 eval_expr_lvalue_fp_localize). auto. Qed.

  
  Lemma eval_lvalue_fp_localize:
    forall a v,
      ClightLang.eval_lvalue_fp sge e le fm a v ->
      forall b ofs (EX:ClightLang.eval_lvalue sge e le fm a b ofs),
      exists v',
        Clight_local.eval_lvalue_fp tge e' le' m a v' /\
        FPlocalize j' v v'.
  Proof. pose (proj2 eval_expr_lvalue_fp_localize). auto. Qed.

  Lemma eval_exprlist_localize:
    forall la tyl lv,
      ClightLang.eval_exprlist sge e le fm la tyl lv ->
      exists lv', Clight.eval_exprlist tge e' le' m la tyl lv' /\  list_forall2 (val_related j') lv' lv.
  Proof.
    induction 1;intros. Esimpl;eauto;econstructor.
    Hsimpl.
    
    eapply eval_expr_localize in H as ?;eauto.
    Hsimpl.
    eapply sem_cast_related in H0;eauto.
    Hsimpl.
    Esimpl;eauto;econstructor;eauto.
  Qed.

  Lemma eval_exprlist_fp_localize:
    forall la tyl fp,
      ClightLang.eval_exprlist_fp sge e le fm la tyl fp->
      exists fp', Clight_local.eval_exprlist_fp tge e' le' m la tyl fp' /\  FPlocalize j' fp fp'.
  Proof.
    induction 1;intros.
    Esimpl;eauto with fplocalize. constructor.

    eapply eval_expr_localize in H as ?;eauto.
    Hsimpl.
    eapply eval_expr_fp_localize in H0;eauto.
    Hsimpl.
    eapply sem_cast_related in H1 as ?;eauto.
    Hsimpl.
    eapply sem_cast_fp_related in H2 as ?;eauto.
    Hsimpl.
    rewrite <- H4.
    Esimpl;eauto with fplocalize. econstructor;eauto.
  Qed.

  Lemma assign_loc_related:
    forall loc ofs loc' ofs' v v',
      val_related j' v' v->
      val_related j' (Vptr loc' ofs')(Vptr loc ofs)->
      forall ty fm',
        ClightLang.assign_loc sge ty fm loc ofs v fm'->
        exists m',
          Clight.assign_loc tge ty m loc' ofs' v' m' /\ mem_related j bound fl (strip fm') m'.
  Proof.
    intros.
    inv H1. 
    eapply storev_related in H as ?;eauto.
    rewrite H3 in H1.
    inv H1.
    Esimpl;eauto. econstructor;eauto.
  Qed.

  Lemma assign_loc_fp_related:
    forall loc ofs loc' ofs' v v',
      val_related j' (Vptr loc' ofs')(Vptr loc ofs)->
      forall ty fp,
        ClightLang.assign_loc_fp sge ty loc ofs v fp ->
        exists fp', Clight_local.assign_loc_fp tge ty loc' ofs' v' fp' /\ FPlocalize j' fp fp'.
  Proof.
    intros.
    inv H0.
    Esimpl. econstructor;eauto.
    eapply storev_fp_localize;eauto.
    unfold Bset.inj_inject;apply injective_j'.
  Qed.
End SEM_EXPR.
 
  Definition binj_to_bofsinj (f:block->option block)(x y:block*Z*Z):Prop:=
    let (tx,hi):=x in
    let (b,lo):=tx in 
    let (ty,hi'):=y in
    let (b',lo'):=ty in
    f b = Some b' /\ lo = lo' /\ hi = hi'.

  Lemma env_related_l:
    forall f e e',
      env_related f e e'->
       list_forall2
         (fun i_x i_y : positive * (block * type) =>
          fst i_x = fst i_y /\
          (let (la, tya) := snd i_x in
           let (lb, tyb) := snd i_y in
           val_related f (Vptr la Ptrofs.zero) (Vptr lb Ptrofs.zero) /\ tya = tyb))
         (PTree.elements e) (PTree.elements e').
  Proof.
    unfold blocks_of_env,env_related. intros.
    apply PTree.elements_canonical_order' in H as ?;auto.
  Qed.

  Lemma block_of_binding_mapping:
    forall f (x y:positive *(block*type)),
      fst x = fst y ->
      let (la, tya) := snd x in
      let (lb, tyb) := snd y in
      val_related f (Vptr la Ptrofs.zero) (Vptr lb Ptrofs.zero) /\ tya = tyb->
      binj_to_bofsinj f (block_of_binding tge x)(block_of_binding sge y).
  Proof.      
    intros f [?[]] [?[]];simpl;intros ? [];subst.
    inv H0. Esimpl;eauto. rewrite sizeof_eq;eauto.
  Qed.

  Lemma env_related_l2:
    forall f e e',
      env_related f e e'->
      list_forall2 (binj_to_bofsinj f)(blocks_of_env tge e)(blocks_of_env sge e').
  Proof.
    intros.
    apply env_related_l in H.
    unfold blocks_of_env.
    
    induction H;simpl.
    constructor.

    constructor.
    Hsimpl.

    pose proof block_of_binding_mapping f a1 b1 H.
    destruct a1 as (?,(?,?)),b1 as (?,(?,?)).

    simpl in *.
    specialize (H2 H1).
    auto.

    auto.
  Qed.



  Lemma freelist_related:
    forall fm e fm' (NOREP':norep (Mem.freelist fm))(NOOVERLAP': no_overlap (Mem.freelist fm) (fun b=>Plt b bound)),
      FMemory.Mem.free_list fm (blocks_of_env sge e) = Some fm'->
      forall e' m,
        mem_related j bound (Mem.freelist fm)(strip fm) m->
        env_related (j' fm) e' e ->
        exists m',
          Memory.Mem.free_list m (blocks_of_env tge e') = Some m' /\ mem_related j bound (Mem.freelist fm)(strip fm') m'.
  Proof.
    intros.
    pose proof env_related_l2 _ _ _ H1.
    clear H1.
    revert H H2.
    generalize dependent fm;
      generalize dependent fm';
      generalize dependent m.
    generalize (blocks_of_env sge e)(blocks_of_env tge e').
    clear e e'.
    induction l;intros.
    {
      assert(l=nil).
      destruct l;auto.
      simpl in *.
      inv H2. subst.
      simpl in *.
      inv H.
      Esimpl;eauto.
    }
    {
      simpl in H.
      destruct a as ((b,lo),hi),Mem.free eqn:?;try discriminate.
      inv H2.

      simpl.
      unfold binj_to_bofsinj in H5.
      destruct a1 as ((b__a,lo__a),hi__a).
      simpl in *.
      Hsimpl;subst.
      exploit free_related;eauto.
      rewrite Heqo. intros R;inv R.

      apply Mem.free_freelist in Heqo as ?.
      unfold j',fl in *.
      rewrite <- H3 in *.
      exploit IHl;eauto.
    }
  Qed.

  Lemma freelist_fp_related:
    forall m e1 e2 (NOREP':norep (Mem.freelist m))(NOOVERLAP': no_overlap (Mem.freelist m) (fun b=>Plt b bound)),
      env_related (j' m) e1 e2 ->
      FPlocalize (j' m) (free_list_fp (blocks_of_env sge e2)) (free_list_fp (blocks_of_env tge e1)).
  Proof.
    intros.
    pose proof env_related_l2 _ _ _ H.
    clear H.
    revert H0.
    generalize dependent m.
    generalize (blocks_of_env sge e2)(blocks_of_env tge e1).
    clear e1 e2.
    induction l;intros;inv H0.
    auto with fplocalize.
    simpl.
    apply IHl in H4;auto.
    destruct a as ((?,?),?),a1 as ((?,?),?).
    apply FPlocalize_union;auto.

    inv H3. Hsimpl;subst.
    unfold free_fp.
    constructor;simpl;try apply Loclocalize_emp.
    constructor.
    unfold range_locset,Locs.belongsto.
    intros.
    destruct eq_block,eq_block;split;auto;intro;subst.
    eapply injective_j' in H0;try apply H;eauto.
    congruence.
  Qed.
  Lemma alloc_variables_related:
    forall v fm e e' fm' (NOREP':norep (Mem.freelist fm)),
      alloc_variables sge e fm v e' fm'->
      forall m e2,
        mem_related j bound (Mem.freelist fm) (strip fm) m->
        env_related (j' fm) e2 e-> 
        exists e2' m', Clight.alloc_variables tge e2 m v e2' m' /\
                  mem_related j bound (Mem.freelist fm)  (strip fm') m' /\
                  env_related (j' fm) e2' e'.
  Proof.
    induction v;intros.
    inv H.  Esimpl;eauto. econstructor;eauto.

    inv H.
    assert(exists m' b', Memory.Mem.alloc m 0 (sizeof sge ty) = (m',b')).
    Transparent Memory.Mem.alloc.
    unfold Memory.Mem.alloc.
    Esimpl;eauto.
    Hsimpl.
    eapply alloc_result_related in H6 as ?;eauto.
    eapply alloc_related in H6 as ?;eauto.
    apply mem_alloc_fleq in H6 as ?.
    assert(j' fm = j' m1).
    unfold j',fl. congruence.
    rewrite H5 in *. 
    eapply IHv in H9 as ?;eauto;try rewrite <-H4;eauto.

    Hsimpl.
    2: eapply env_related_set;eauto;econstructor;rewrite <- H5;eauto.

    Esimpl;eauto. econstructor;eauto.
    rewrite<- sizeof_eq;auto.

    congruence.
  Qed.
  Lemma alloc_variables_fp_related:
    forall v fm fp (NOREP':norep (Mem.freelist fm))(NOOVERLAP': no_overlap (Mem.freelist fm) (fun b=>Plt b bound)),
      ClightLang.alloc_variables_fp sge fm v fp->
      forall m,
        mem_related j bound (Mem.freelist fm) (strip fm) m->
        exists fp', Clight_local.alloc_variables_fp tge m v fp' /\
               FPlocalize (j' fm) fp fp'.
  Proof.
    induction v;intros.
    inv H. Esimpl;eauto with fplocalize. constructor.

    inv H.
    assert(exists m' b', Memory.Mem.alloc m 0 (sizeof sge ty) = (m',b')).
    Transparent Memory.Mem.alloc.
    unfold Memory.Mem.alloc.
    Esimpl;eauto.
    Hsimpl.
    eapply alloc_result_related in H3 as ?;eauto.
    eapply alloc_related in H3 as ?;eauto.
    apply mem_alloc_fleq in H3 as ?.
    assert(j' fm = j' m1).
    unfold j',fl. congruence.
    rewrite H5 in *. 
    eapply IHv in H7 as ?;eauto;try rewrite <-H4;eauto.
    Hsimpl.
    Esimpl;eauto. econstructor;eauto.
    rewrite<- sizeof_eq;eauto.
    apply FPlocalize_union;auto.
    constructor;constructor;unfold MemOpFP.alloc_fp,alloc_fp,uncheck_alloc_fp,FMemOpFP.uncheck_alloc_fp;simpl;intros.
    all: split;intro R;try (inv R;fail); unfold Locs.belongsto in *.
    {
      unfold Locs.belongsto.
      destruct peq;try discriminate.
      rewrite <- H5 in H9.
      destruct peq;auto.

      apply Mem.alloc_result in H3.
      apply Memory.Mem.alloc_result in H.
      subst b1 x0.
      unfold j' in H9.
      exploit injective_j'.
      eauto.
      eauto.
      eexact H1.
      rewrite e.
      eexact H9.
      intros.
      contradiction.
    }
    {
      unfold Locs.belongsto.
      destruct peq;try discriminate.
      rewrite <- H5 in H9.
      destruct peq;auto.

      apply Mem.alloc_result in H3.
      apply Memory.Mem.alloc_result in H.
      subst.
      unfold j',fl in H9.
      rewrite H1 in H9. inv H9.
      congruence.
    }
  Qed.
  Opaque Memory.Mem.alloc.
  Lemma tenv_related_setid:
    forall j te1 te2,
      tenv_related j te1 te2->
      forall id v v',
        val_related j v v'->
        tenv_related j (PTree.set id v te1)(PTree.set id v' te2).
  Proof.
    unfold tenv_related.
    intros.
    do 2 rewrite PTree.gsspec.
    destruct peq;auto.
    subst. econstructor;eauto.
  Qed.
  Lemma bind_parameter_temps_related:
    forall p vargs t le,
      bind_parameter_temps p vargs t = Some le ->
      forall j vargs' t',
        list_forall2 (val_related j) vargs' vargs ->
        tenv_related j t' t->
        exists le', bind_parameter_temps p vargs' t' = Some le' /\ tenv_related j le' le.
  Proof.
    induction p;intros.
    inv H.
    inv_eq. inv H0. Esimpl;eauto.
    simpl in *.
    destruct a.
    inv_eq.
    inv H0.
    exploit IHp;eauto.
    eapply tenv_related_setid;eauto.
  Qed.
  Lemma env_related_empty_env:
    forall j,
      env_related j empty_env empty_env.
  Proof.
    unfold env_related,empty_env.
    intros.
    rewrite PTree.gempty.
    constructor.
  Qed.
  Lemma tenv_related_temps:
    forall j t,
      tenv_related j (create_undef_temps t) (create_undef_temps t).
  Proof.
    unfold tenv_related.
    intros.
    induction t;simpl. rewrite PTree.gempty. constructor.
    destruct a. rewrite PTree.gsspec. destruct peq;auto.
    constructor;auto.
  Qed.
  Lemma function_entry2_related:
    forall fm f vargs e le fm'  (NOREP':norep (Mem.freelist fm)),
      ClightLang.function_entry2 sge f vargs fm e le fm'->
      forall vargs' m,
        list_forall2 (val_related (j' fm)) vargs' vargs->
        mem_related j bound (fl fm) (strip fm) m -> 
        exists e' m' le', Clight_local.function_entry2 tge f vargs' m e' le' m' /\
                     env_related (j' fm) e' e /\
                     tenv_related (j' fm) le' le /\
                     mem_related j bound (fl fm) (strip fm') m'.
  Proof.
    intros.
    inv H.
    eapply alloc_variables_related in H5 as ?;eauto.
    

    2: eapply env_related_empty_env;eauto.
    Hsimpl.
    eapply bind_parameter_temps_related in H6 as ?;eauto.
    2: apply tenv_related_temps.
    Hsimpl.
    Esimpl;eauto. econstructor;eauto.
  Qed.
  Lemma function_entry2_fp_related:
    forall fm f vargs e fp  (NOREP':norep (Mem.freelist fm))(NOOVERLAP': no_overlap (Mem.freelist fm) (fun b=>Plt b bound)),
      ClightLang.function_entry2_fp sge f vargs fm e fp->
      forall e' vargs' m,
        list_forall2 (val_related (j' fm)) vargs' vargs->
        mem_related j bound (fl fm) (strip fm) m -> 
        exists fp', Clight_local.function_entry2_fp tge f vargs' m e' fp' /\
               FPlocalize (j' fm) fp fp'.
  Proof.
    intros.
    inv H.
    eapply alloc_variables_fp_related in H2;eauto.
    Hsimpl;Esimpl;eauto with fplocalize.
    econstructor;eauto.
  Qed.
End EXPR.

Inductive match_cont (j: Bset.inj):cont->cont->Prop:=
| match_stop: match_cont j Kstop Kstop
| match_seq:
    forall k1 k1'  s,
      match_cont j k1 k1'->
      match_cont j (Kseq s k1)(Kseq s k1')
| match_loop1:
    forall k k' s1 s2,
      match_cont j k k'->
      match_cont j (Kloop1 s1 s2 k)(Kloop1 s1 s2 k')
| match_loop2:
    forall k k' s1 s2,
      match_cont j k k'->
      match_cont j (Kloop2 s1 s2 k)(Kloop2 s1 s2 k')
| match_switch:
    forall k k',
      match_cont j k k'->
      match_cont j (Kswitch k)(Kswitch k')
| match_call:
    forall id f v v' e e' k k',
      match_cont j k k'->
      env_related j v v'->
      tenv_related j e e'->
      match_cont j (Kcall id f v e k)(Kcall id f v' e' k').

Lemma find_label_match_cont_case1:
  forall j s t k k',
      match_cont j k k'->
      find_label s t k' = None ->
      find_label s t k= None
with find_label_ls_match_cont_case1:
       forall j s t k k',
         match_cont j k k'->
         find_label_ls s t k' = None ->
         find_label_ls s t k = None.
Proof.
  induction t;intros;auto.
  all : simpl in *;ex_match.
  all : try (eapply IHt1 in Hx;eauto;try econstructor;eauto;eapply IHt2 in H0;try econstructor;eauto;simpl;rewrite Hx;auto;fail).

  eapply find_label_ls_match_cont_case1;eauto. constructor;eauto.
  eapply IHt;eauto.

  induction t;intros;auto.
  all : simpl in *;ex_match.
  eapply find_label_match_cont_case1 in Hx;eauto;try econstructor;eauto.
  rewrite Hx;eauto.
Qed.

Lemma find_label_match_cont_case2:
  forall t j s k k' ,
    match_cont j k k'->
    match find_label s t k with
    | None => find_label s t k' = None
    | Some (s2,k2) =>
      exists k3,
      find_label s t k' = Some (s2,k3) /\ match_cont j k2 k3
    end
      
with find_label_ls_match_cont_case2:
       forall t j s k k' ,
         match_cont j k k'->
         match find_label_ls s t k with
         | None => find_label_ls s t k' = None
         | Some (s2,k2) =>
           exists k3,
           find_label_ls s t k' = Some (s2,k3) /\ match_cont j k2 k3
         end.
Proof.
  {
    intros t;case_eq t;intros.
    all: simpl in *;eauto.
    {
      assert(match_cont j (Kseq s0 k)(Kseq s0 k')). constructor;auto.
      eapply find_label_match_cont_case2 with(s:=s1)(t:=s) in H1 as ?.
      destruct (find_label). 
      destruct p. Hsimpl.
      rewrite H2. Esimpl;eauto.
      eapply find_label_match_cont_case2 with(s:=s1)(t:=s0) in H0.
      destruct (find_label s1 s0 k).
      destruct p;Hsimpl. rewrite H2. Esimpl;eauto.
      rewrite H2. auto.
    }
    {
      eapply find_label_match_cont_case2 with(s:=s1)(t:=s) in H0 as ?.
      destruct find_label.
      destruct p.
      Hsimpl. rewrite H1. Esimpl;eauto.
      rewrite H1. eapply find_label_match_cont_case2;eauto.
    }
    {
      assert(match_cont j (Kloop1 s s0 k)(Kloop1 s s0 k')).
      econstructor;auto.
      eapply find_label_match_cont_case2 with(s:=s1)(t:=s) in H1 as ?.
      destruct (find_label).
      destruct p. Hsimpl.
      rewrite H2. Esimpl;eauto.
      rewrite H2.
      eapply find_label_match_cont_case2. econstructor;eauto.
    }
    {
      eapply find_label_ls_match_cont_case2;eauto. econstructor;eauto.
    }
    {
      destruct ident_eq.
      {
        Esimpl;eauto.
      }
      {
        eapply find_label_match_cont_case2;eauto.
      }
    }
  }
  {
    intros t;case_eq t;intros.
    all: simpl in *;eauto.
    destruct find_label eqn:?. destruct p.
    assert(match_cont j (Kseq (seq_of_labeled_statement l) k)(Kseq (seq_of_labeled_statement l) k')).
    econstructor;eauto.
    eapply find_label_match_cont_case2 in H1;eauto.
    rewrite Heqo0 in H1. Hsimpl. rewrite H1. Esimpl;eauto.

    assert(match_cont j (Kseq (seq_of_labeled_statement l) k)(Kseq (seq_of_labeled_statement l) k')).
    econstructor;eauto.
    eapply find_label_match_cont_case2 in H1;eauto.
    rewrite Heqo0 in H1. rewrite H1.
    eapply find_label_ls_match_cont_case2;eauto.
  }
Qed.      
      
Lemma call_cont_match:
  forall k k' j,
    match_cont j k k'->
    match_cont j (call_cont k)(call_cont k').
Proof.
  induction k;intros;simpl.
  inv H;constructor.
  inv H. eapply IHk in H3. eauto.
  inv H. eapply IHk in H4;eauto.
  inv H. eapply IHk in H4;eauto.
  inv H. eapply IHk in H1;eauto.
  inv H. constructor;auto.
Qed.
Inductive match_core (j: Bset.inj) : core -> core -> Prop :=
| match_state_intro:
    forall f s k1 k2 e1 e2 te1 te2,
      match_cont j k1 k2 ->
      env_related j e1 e2->
      tenv_related j te1 te2->
      match_core j (Core_State f s k1 e1 te1)
                 (Core_State f s k2 e2 te2)
| match_state_call:
    forall fd args1 args2 k1 k2,
      match_cont j k1 k2 ->
      list_forall2 (val_related j) args1 args2 ->
      match_core j (Core_Callstate fd args1 k1)
                 (Core_Callstate fd args2 k2)
| match_state_return:
    forall res1 res2 k1 k2,
      match_cont j k1 k2 ->
      val_related j res1 res2 ->
      match_core j (Core_Returnstate res1 k1)
                 (Core_Returnstate res2 k2).
Lemma freelist_fleq:
  forall l m m',
    Mem.free_list m l = Some m'->
    Mem.freelist m' = Mem.freelist m.
Proof.
  induction l;intros;simpl in *;inv_eq;eauto.
  apply mem_free_fleq in Heqo. apply IHl in H1.
  congruence.
Qed.
Theorem clight_localize: LangLocalize clight_comp_unit wdcu Clight_IS_2 Clight_IS_2_local.
Proof.
  constructor; simpl in *.
  intros cu WDCU ge G INITGE.
  pose proof INITGE as GEBOUND.
  rewrite init_genv_iff in GEBOUND.
  destruct GEBOUND as [_ [_ _ _ _ _ _ _ _ GEBOUND]].
  remember (Genv.genv_next ge) as bound eqn:HBOUND.
  remember (ge_extend (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)) bound GEBOUND) as ge_local eqn:HGE.
  assert (INITGE_local: init_genv cu ge_local {|genv_genv:=ge_local;genv_cenv:=cu_comp_env cu|}).
  { split; [auto|econstructor; eauto]. }
  remember  {|genv_genv:=ge_local;genv_cenv:=cu_comp_env cu|} as ge_real eqn:HGE2.

  rewrite init_genv_iff in INITGE. destruct INITGE as [X INITGE]. subst G.
  pose proof INITGE as INITG.
  destruct INITGE as [j DOM INJECTIVE PUBLICEQ SYMBREL DEFSDOM DEFSRANGE DEFSREL _].
  exists j, ge_local, ge_real.
  assert (GEMATCH: ge_match_strict j ge ge_local).
  { constructor; try (subst; auto; fail).
    intros. apply DEFSREL in H. rewrite <- H. subst ge_local; unfold ge_extend in H; simpl.
    match goal with |- option_rel _ ?x ?x => destruct x eqn:? end.
    constructor. destruct g; constructor. destruct v; constructor. constructor.
    rewrite PUBLICEQ. subst ge_local; unfold ge_extend; simpl. tauto. }
  exists (fun jfull fl c' m' c m =>
            exists fm', strip fm' = m' /\ (FMemory.Mem.freelist fm' = fl) /\
                        inject_incr (Bset.inj_to_meminj j) (Bset.inj_to_meminj jfull) /\
                        Bset.inject jfull (fun b => Plt b bound) (fun b => Plt b bound) /\
                        let cj := construct_inj jfull bound fl in
                        match_core cj c c' /\ mem_related jfull bound fl m' m /\
                        norep fl /\ no_overlap fl (fun b => Plt b bound)).
  do 3 (split; auto). subst. unfold ge_extend, Genv.find_def. simpl. eauto.
  intros jfull INCRJ INJECT. pose proof GEMATCH as GEMATCH'.
  eapply ge_match_strict_incr in GEMATCH; try exact INCRJ. 2:inv INJECT; inv inj_weak; auto.
  constructor; simpl in *.
  (** ge match & inj wd *)
  split; auto. rewrite <- HBOUND. auto.
  (** norep freelist *)
  intros. destruct H. tauto.
  (** no overlap *)
  intros. destruct H. rewrite <- HBOUND. tauto.
  (** memrel *)
  intros. destruct H. rewrite <- HBOUND. tauto.
  (** init *)
  {
    intros. exploit G_args_exists_args_related'. eauto. subst ge_local; simpl in *. rewrite <- HBOUND. eauto.
    
    intros [args_local INJARGS]. exists args_local.
    unfold init_core,ClightLang.init_core,type_of_fundef in *.
    destruct (Genv.find_symbol ge id) eqn:FINDSYMB;[|discriminate].
    destruct (Genv.find_funct_ptr ge b) eqn:FINDDEF;[|discriminate].
    exploit (SYMBREL). instantiate (1:=id).
    rewrite FINDSYMB. intro. inv H1. symmetry in H2.
    unfold Genv.find_symbol in H2 |- * . simpl.  rewrite H2. clear H2.
    exploit DEFSREL. exact H5. unfold Genv.find_funct_ptr, Genv.find_def in *.
    destruct ((Genv.genv_defs ge)!b) eqn:FINDDEF'; try discriminate. intro.
    simpl. rewrite H1. clear H1. rewrite FINDDEF. 
    destruct g; [|discriminate]. inversion FINDDEF; subst f0; clear FINDDEF. destruct f; [|discriminate].
    destruct (type_of_function f) eqn: TYPF;try discriminate.
    destruct ( val_casted_list_func args t && tys_nonvoid t && vals_defined args &&
                                    zlt (4 * (2 * Zlength args)) Int.max_unsigned) eqn:WDARGS;try discriminate.
    assert(  val_casted_list_func args_local t && tys_nonvoid t && vals_defined args_local &&
                                  zlt (4 * (2 * Zlength args_local)) Int.max_unsigned = true).
    {
      generalize t INJARGS WDARGS. clear.
      intros until 1.
      intro. apply andb_true_iff in WDARGS. destruct WDARGS.
      apply andb_true_iff in H. destruct H.
      apply andb_true_iff in H as [].
      repeat (apply andb_true_iff;split;auto).
      (* *)
      clear H1 H0 H2.
      revert t H . induction INJARGS; intros. 
      destruct t. auto. inversion H. destruct t; simpl in *; auto.
      apply andb_true_iff in H0. destruct H0.
      apply andb_true_iff; split; auto. inv H; destruct t; auto.
      (* *)
      clear H H0. induction INJARGS; auto. simpl. inv H; auto.
      (* *)
      apply list_forall2_length in INJARGS. rewrite Zlength_correct in H0 |- * .
      rewrite INJARGS. auto.
    }
    pose proof H1 as H2.
    simpl in H2.  rewrite H2. clear H2.
    Esimpl.
    apply list_forall2_imply with (val_related jfull); auto. intros. apply val_related_val_inject_strict; auto.
    eauto.

    intros m fl INITMEM NOREP NOOVERLAP RC.
    exploit lmem_construction; eauto. 
    intros [lm [INITMEM_local MEMREL]]. exists lm.
    unfold init_mem. split. auto.
    destruct NOREP as [NOREP].
    assert (VALIDWD: forall n b, get_block fl n = b -> In b (GMem.validblocks m) <-> (n < 0)%nat).
    { intros. split; intro C; [| inversion C]. exfalso. eapply NOOVERLAP; eauto. }
    repeat (split; auto).
    eexists (FMemory.Mem.mkmem
               (GMem.mem_contents m) (GMem.mem_access m) (GMem.validblocks m) fl 0 NOREP VALIDWD
               (GMem.access_max m) (GMem.invalid_noaccess m) (GMem.contents_default m)).
    unfold strip. simpl. split. destruct m; auto.
    repeat (split; auto).
    (* match core *)
    inv H0. constructor. unfold construct_inj.
    constructor.
    eapply list_forall2_imply. eauto. intros. apply val_related_incr with jfull; auto.
    apply construct_inj_incr; auto. eapply Bset.inj_dom'. inv INJECT; eauto.
    apply bset_eq_no_overlap with (valid_block_bset m); auto.
    intro. rewrite  <- init_mem_valid_block; eauto. tauto.
  }
  (** step *)
  {
    
    set (ge1:= (Genv.globalenv {|AST.prog_defs := cu_defs cu;AST.prog_public := cu_public cu;AST.prog_main := 1%positive |})) in *.
    intros fl c lc m lm lfp lc' lm' [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] STEP FPG.
    set (sge:=  {| genv_genv := ge; genv_cenv := cu_comp_env cu |} ) in *.
    set (tge:= {|genv_genv := ge_local; genv_cenv := cu_comp_env cu |} ) in *.
    assert(GEMATCH0:ge_match_strict jfull sge tge). auto.
    rewrite HGE in INJECT. simpl in INJECT.
    assert(FINDFEQ:
             forall b b' f,
               construct_inj jfull bound fl b' = Some b->
               (Genv.genv_defs ge)! b = Some f->
               (Genv.genv_defs ge1)! b' = Some f).
    {
      intros.
      apply DEFSRANGE in H0 as ?.
      Hsimpl.
      unfold construct_inj in H.
      destruct plt.
      
      exploit INCRJ;unfold Bset.inj_to_meminj. rewrite H1. eauto.
      intros. destruct (jfull x) eqn:?;inv H2.
      inv INJECT.
      inv inj_weak.
      eapply inj_injective in H;try apply Heqo;subst x.

      eapply DEFSREL in H1;eauto.
      congruence.
      {
        inversion H.
        apply NOOVERLAP in H3. unfold Bset.belongsto in H3.
        
        apply Genv.genv_defs_range in H0.
        rewrite  HBOUND in H3. contradiction.
      }
    }
    Ltac triv:=
      Esimpl;eauto with fplocalize;try econstructor;eauto;try econstructor;eauto.
    inv MS; inv STEP.
    all: match goal with
    | H: embed (strip ?fm) (Mem.freelist ?fm) ?m |- _ =>
      apply embed_eq in H; subst fm
         end.
    {  (*NEED FREELIST_RELATED*)
      pose proof H3 as STEPBK.
      inv H3.
      {
        eapply eval_lvalue_localize in H8 as ?;eauto.
        Hsimpl.
        eapply eval_expr_localize in H9 as ?;eauto.
        Hsimpl.
        eapply sem_cast_related in H10 as ?;eauto;unfold bound,fl;eauto.
        Hsimpl.
        eapply assign_loc_related with(tge:=tge) in H11 as ?;eauto.
        Hsimpl.

        eapply eval_lvalue_fp_localize in H12 as ?;eauto.
        Hsimpl.
        eapply eval_expr_fp_localize in H17 as ?;eauto.
        Hsimpl.
        eapply sem_cast_fp_related in H18 as ?;eauto;unfold bound,fl;eauto.
        Hsimpl.
        eapply assign_loc_fp_related with(v':=x2) in H19 as ?;eauto.
        Hsimpl.

        triv.
        inv H11. 
        eapply mem_storev_fleq in H27;eauto.
      }
      {
        eapply eval_expr_localize in H12 as ?;eauto.
        Hsimpl.
        eapply eval_expr_fp_localize in H13 as ?;eauto.
        Hsimpl.
        triv.
        eapply tenv_related_setid;eauto.
      }
      {
        eapply eval_expr_localize in H9 as ?;eauto;Hsimpl.
        eapply eval_exprlist_localize in H10 as ?;eauto;Hsimpl.
        eapply eval_expr_fp_localize in H17 as ?;eauto;Hsimpl.
        eapply eval_exprlist_fp_localize in H18 as ?;eauto;Hsimpl.
        triv.

        unfold Genv.find_funct in *.
        inv H3;auto.
        inv_eq. unfold Genv.find_funct_ptr,Genv.find_def in *.
        unfold ge_extend;simpl.
        inv_eq.
        exploit FINDFEQ;eauto.
        intro R;rewrite R;auto.
      }
      {
        triv.
      }
      {
        inv H;triv.
      }
      {
        inv H;triv.
      }
      {
        inv H;triv.
      }
      {
        eapply eval_expr_localize in H8 as ?;eauto;Hsimpl.
        eapply bool_val_related in H13 as ?;eauto;Hsimpl;unfold bound,fl;eauto.
        eapply eval_expr_fp_localize in H14 as ?;eauto;Hsimpl.
        eapply bool_val_fp_related in H15 as ?;unfold bound,fl;eauto;eauto;Hsimpl.
        triv.
      }
      {
        triv.
      }
      {
        inv H;triv.
      }
      {
        inv H.
        Esimpl;eauto with fplocalize.
        eapply Clight_local.step_break_loop1;eauto with fplocalize.
        econstructor;eauto.
      }
      {
        inv H. triv.
      }
      {
        inv H. triv.
      }
      
      { (*NEED FREELIST_RELATED*)
        eapply freelist_related in H12 as ?;eauto.
        Hsimpl.
        Esimpl;eauto with fplocalize.
        econstructor;eauto.
        exploit freelist_fp_related;eauto.
       
        eapply freelist_fleq;eauto.
        econstructor;eauto.
        apply call_cont_match;auto.
      }
      {
        eapply eval_expr_localize in H8 as ?;eauto;Hsimpl.
        eapply sem_cast_related in H9 as ?;eauto;unfold bound,fl;eauto;Hsimpl.
        eapply freelist_related in H10 as ?;eauto;Hsimpl.
        eapply eval_expr_fp_localize in H15 as ?;eauto;Hsimpl.
        eapply sem_cast_fp_related in H16 as ?;eauto;unfold bound,fl;eauto;Hsimpl.
        exploit freelist_fp_related;eauto;intro.
        
        
        triv.
        eapply freelist_fleq;eauto.
        apply call_cont_match;auto.
      }
      {
        eapply freelist_related in H13 as ?;eauto;Hsimpl.
        exploit freelist_fp_related;eauto;intro.
        triv.
        inv H;inv H12;constructor.
        eapply freelist_fleq;eauto.
      }
      {
        eapply eval_expr_localize in H12 as ?;eauto;Hsimpl.
        eapply eval_expr_fp_localize in H13 as ?;eauto;Hsimpl.
        triv.
        inv H3;simpl in *;inv_eq;auto.
      }
      {
        inv H. triv.
      }
      {
        inv H.
        Esimpl;eauto with fplocalize.
        eapply  step_continue_switch;eauto.
        econstructor;eauto.
      }
      {
        triv.
      }
      {
        exploit call_cont_match;eauto.
        intro.
        exploit find_label_match_cont_case2;eauto.
        rewrite H12.
        intro.
        destruct (find_label lbl (fn_body f)(call_cont k1)) eqn:?;try discriminate.
        destruct p as (s4,k4).
        Hsimpl. inv H3.
        triv.
      }
    }
    {
      inv H2.
      assert(genv_cenv sge = genv_cenv tge).
      unfold sge,tge;auto.
      eapply function_entry2_related in H9 as ?;eauto.
      Hsimpl.
      eapply function_entry2_fp_related with(e':=x) in H10 as ?;eauto.
      Hsimpl.
      Esimpl;eauto with fplocalize.
      econstructor;eauto.
      inv H9.
      eapply alloc_variables_fleq in H13;eauto.
      econstructor;eauto.
    }
    {
      inv H2.
      inv H.
      triv.
      unfold set_opttemp.
      destruct optid eqn:?.
      eapply tenv_related_setid;eauto.
      auto.
    }
  }
    
  { (*at_ext*)
    intros fl c lc m lm f sg args_local [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] ATEXT GARGS.
    unfold ClightLang.at_external,at_external in *. inv MS; try discriminate.
    (** ef *)
    destruct fd;try discriminate.
    destruct e;try discriminate.
    destruct (vals_defined args2) eqn:?;try discriminate.
    assert(vals_defined args1=true).
    {
      revert Heqb H0. clear.
      induction 2;auto.
      simpl in *.
      assert(vals_defined bl = true).
      destruct b1;try discriminate;auto.
      specialize (IHlist_forall2 H1).
      rewrite IHlist_forall2.
      inv H;try discriminate;auto.
    }
    rewrite H1.
    destruct (ClightLang.invert_symbol_from_string _ name) eqn:NAME;try discriminate.
    enough( invert_symbol_from_string
              {|
                genv_genv := ge_extend
                               (Genv.globalenv
                                  {|
                                    AST.prog_defs := cu_defs cu;
                                    AST.prog_public := cu_public cu;
                                    AST.prog_main := 1%positive |}) (Genv.genv_next ge) GEBOUND;
                genv_cenv := cu_comp_env cu |} name = Some i).
    rewrite H2.
    destruct peq; try discriminate.
    destruct peq; try discriminate.
    simpl in *. inv ATEXT.
    Esimpl;eauto.
    unfold args_related.
    { generalize args_local args1 H0 GARGS NOOVERLAP; clear.
      induction args_local; intros; inv H0; inv GARGS; constructor; auto.
      inv H3; econstructor. unfold Bset.inj_to_meminj, construct_inj in *. 
      destruct plt; try contradiction. rewrite H. eauto.
      inv H. exfalso. eapply NOOVERLAP; eauto. 
      rewrite Ptrofs.add_zero. auto. }
    clear GARGS args1 k1 k2 H H0 H1.
    set (ggee:= (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive))) in *.
    set (ge_local:= (ge_extend ggee (Genv.genv_next ge) GEBOUND)) in *.

    unfold invert_symbol_from_string,ClightLang.invert_symbol_from_string in *.
    simpl in *.
    destruct (ClightLang.invert_block_from_string) eqn:?;inv NAME.

    apply Genv.invert_find_symbol in H0 as ?.
    destruct peq; try discriminate.
    destruct peq; try discriminate. simpl in *. inv ATEXT.
    specialize (SYMBREL f) as R.
    rewrite H in R.
    inv R.
    symmetry in H1.
    apply Genv.find_invert_symbol in H1 as ?.

    Lemma ge_extend_invert_symbol_eq:
      forall F V ge  a b x,
        Genv.invert_symbol ge x= @Genv.invert_symbol F V (ge_extend ge a b) x.
    Proof.
      unfold Genv.invert_symbol;intros.
      unfold ge_extend. simpl. auto.
    Qed.
    Lemma ge_extend_invert_block_from_string_eq:
      forall ge  a b x,
        invert_block_from_string ge x= invert_block_from_string (ge_extend ge a b) x.
    Proof.
      unfold invert_block_from_string;intros.
      unfold ge_extend. simpl. auto.
    Qed.
    unfold ge_local;rewrite<- ge_extend_invert_block_from_string_eq.

    enough(invert_block_from_string ggee name = Some b0).
    rewrite H3,<-ge_extend_invert_symbol_eq;try congruence.

    pose proof invert_block_from_string_eq.
    exploit H3;eauto.
    eapply nodup_ef_ge_norep_ef_name;eauto.
    inv WDCU.
    eapply nodup_gd_ident_exists;eauto.
    instantiate(1:= name). intro.
    rewrite Heqo in H5.
    inv H5. Hsimpl.
    unfold Genv.find_symbol in *.
    specialize (SYMBREL x) as ?.
    rewrite H5,H6 in H8. inv H8.
    f_equal.
    eapply INJECTIVE;eauto.
  }
  { (*aft_ext*)
    intros fl c lc m lm ores lc' lores [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] RESREL AFTEXT.
    unfold ClightLang.after_external,after_external in *. inv MS; try discriminate.
    (** ef *)
    destruct fd; try discriminate.
    destruct e; try discriminate.
    destruct lores, ores; simpl in *; try contradiction.
    { destruct (sig_res sg) as [ty|];
        [destruct (val_has_type_func v ty) eqn:TYPE, (val_has_type_func v0 ty) eqn:TYPE'
        |]; try discriminate.
      eexists. split. eauto. exists fm. repeat (split; auto). inv AFTEXT. constructor; auto.
      inv RESREL;auto.
      unfold Bset.inj_to_meminj in H1.
      ex_match. inv H1.
      rewrite Ptrofs.add_zero. econstructor;eauto.
      eapply mem_related_inj_construct_inj;eauto.
      
      exfalso. inv RESREL;unfold val_has_type_func in *; ex_match.
    }
    { destruct (sig_res sg) as [ty|]; try discriminate.
      eexists. split. eauto. exists fm. repeat (split; auto). inv AFTEXT. constructor; auto.
    }
  }
  {
    intros fl c lc m lm [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] m' lm' UNCHG RELY.
    (** TODO: RELY condition too weak. unchg_freelist required *)
    assert (MEMREL': mem_related jfull bound fl m' lm').
    { subst. auto. }
    assert (VALIDWD: forall n b, get_block fl n = b -> In b (GMem.validblocks m') <-> (n < (FMemory.Mem.nextblockid fm))%nat).
    { intros. fold (GMem.valid_block m' b). rewrite <- GMem.unchanged_on_validity; eauto; simpl.
      unfold GMem.valid_block. replace (GMem.validblocks m) with (Mem.validblocks fm).
      apply (FMemory.Mem.valid_wd fm); subst; auto. subst m. unfold strip. auto. eexists. eauto. }
    destruct fm. unfold strip in *. simpl in *. subst.
    exists (FMemory.Mem.mkmem
              (GMem.mem_contents m') (GMem.mem_access m') (GMem.validblocks m')
              fl (nextblockid) (freelist_wd) VALIDWD
              (GMem.access_max m') (GMem.invalid_noaccess m') (GMem.contents_default m')).
    destruct m'. subst. unfold ge_extend in *. simpl in *. 
    split; auto. split; auto. split; auto.
  }
  
  { (** halt *)
    unfold ClightLang.halted,halted, Vzero; intros fl c lc m lm lres [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] HALT GRES.
    inv MS; try discriminate.
    destruct k2 ;try discriminate.
    inv H.
    inv HALT.
    Esimpl;eauto.

    unfold G_arg in GRES.
    inv H0;auto;try discriminate;try constructor.
    unfold arg_related.
    destruct res2 eqn:?;inv H1;inv H0;try econstructor;eauto.
    
    unfold Bset.belongsto in GRES.
    Focus 2.
    instantiate(1:=0). rewrite Ptrofs.add_zero. auto.
    apply MEMREL in GRES as [].
    assert(construct_inj jfull (Genv.genv_next ge)(Mem.freelist fm) x = Some b).
    eapply mem_related_inj_construct_inj in H;eauto.
    eapply construct_inj_injective in H2;try apply H0;eauto.
    specialize (H2 H0). subst.
    unfold Bset.inj_to_meminj. rewrite H. auto.
  }
  Unshelve.
  apply 0.
Qed.



