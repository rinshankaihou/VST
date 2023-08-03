Require Import Coqlib Maps Integers Values Memdata AST Globalenvs.
Require Import Blockset Footprint FMemOpFP GMemory FMemory FMemPerm FMemLemmas MemAux CUAST LDSimDefs Localize ValRels MemInterpolant val_casted.

Require Import AsmLocalize Cminor CminorLang Cminor_local CminorWD.

Lemma init_genv_iff: forall cu ge G,
    CminorLang.init_genv cu ge G <->
    G = ge /\ ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).
Proof. intros. unfold CminorLang.init_genv. tauto. Qed.

Lemma init_mem_valid_block:
  forall ge m,
    CminorLang.init_mem ge m ->
    (forall b, Bset.belongsto (valid_block_bset m) b <-> Plt b (Genv.genv_next ge)).
Proof.
  intros. inv H. destruct H0. inv H0.
  destruct x; simpl in *.
  unfold valid_block_bset, strip, Mem.valid_block, GMem.valid_block in *; simpl in *.
  rewrite dom_match_fm. tauto.
Qed.

Lemma eval_uop_related:
  forall op j v v',
    val_related j v v' ->
    option_rel (val_related j) (eval_unop op v) (eval_unop op v').
Proof.
  intros.
  inv H; destruct op; simpl; try constructor; auto;
    match goal with
    | |- option_rel _ (option_map _ ?x) (option_map _ ?x) =>
      destruct x; simpl; constructor; auto
    end.
Qed.

Local Hint Resolve construct_inj_injective  FPlocalize_emp
      FPlocalize_union weak_valid_pointer_fp_localize
      range_locset_localize Loclocalize_emp Build_FPlocalize.
Lemma eval_binop_related:
  forall op j bound fl v1 v1' v2 v2' m m',
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) ->
    val_related (construct_inj j bound fl) v1 v1' ->
    val_related (construct_inj j bound fl) v2 v2' ->
    mem_related j bound fl (strip m') m ->
    option_rel (val_related (construct_inj j bound fl))
               (Cminor.eval_binop op v1 v2 m)
               (CminorLang.eval_binop op v1' v2' m') /\
    option_rel (FPlocalize (construct_inj j bound fl))
               (CminorLang.eval_binop_fp op v1' v2' m')
               (Cminor_op_footprint.eval_binop_fp op v1 v2 m).
Proof.
  intros. destruct op; simpl.
  all: try (split; constructor; auto).
  1-9,11-13:inv H2; inv H3; simpl;
    try (split; repeat constructor; auto;
         repeat match goal with
                | |- option_rel _ (match ?x with _ => _ end)
                               (match ?x with _ => _ end)
                  => destruct x
                end; try constructor; auto).
  split. exploit cmpu_bool_related. 1-4:eauto. exact H2. exact H3.
  intro. inv H5. rewrite <- H7, <- H8. constructor.
  rewrite <- H6, <- H7. constructor. auto.
  constructor.
  inv H3; inv H2; simpl; auto;
    repeat match goal with
           | |- option_rel _ (match ?x with _ => _ end)
                          (match ?x with _ => _ end)
             => destruct x
           | |- FPlocalize _ (match ?x with _ => _ end)
                          (match ?x with _ => _ end)
             => destruct x
           end; auto using weak_valid_pointer_fp_localize.
  destruct eq_block; destruct eq_block;
    subst; auto.
  exfalso. apply n. eapply construct_inj_injective; eauto.
  congruence.
  destruct Val.cmp_different_blocks; auto.
  apply FPlocalize_union; constructor; simpl; auto.

  inv H2; inv H3; simpl; repeat constructor; auto.
Qed.

Ltac det :=
  match goal with
  | [H1: eval_expr ?ge ?sp ?e ?m ?a ?v1,
         H2: eval_expr ?ge ?sp ?e ?m ?a ?v2
     |- _ ] => pose proof (eval_expr_det _ _ _ _ _ _ H1 _ H2);
             subst v1; clear H1
  | [H1: CminorLang.eval_expr_fp ?ge ?sp ?e ?m ?a ?v1,
         H2: CminorLang.eval_expr_fp ?ge ?sp ?e ?m ?a ?v2
     |- _ ] => pose proof (eval_expr_fp_det _ _ _ _ _ _ H1 _ H2);
             subst v1; clear H1
  | [H1: ?x = ?y1, H2: ?x = ?y2 |- _] => rewrite H1 in H2; inv H2
  end.

Definition match_env (j: Bset.inj) (e1 e2 : env) : Prop :=
  forall id, option_rel (val_related j) (e1 ! id) (e2 ! id).

Lemma eval_expr_localize:
  forall ge ge_local j m m' v1 v2 e1 e2 a v' fp',
    let bound := (Genv.genv_next ge) in
    let fl := (Mem.freelist m') in
    ge_match_strict j ge ge_local ->
    norep fl ->
    no_overlap fl (fun b => Plt b bound) ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) v1 v2 ->
    match_env (construct_inj j bound fl) e1 e2 ->
    eval_expr ge v2 e2 m' a v' ->
    CminorLang.eval_expr_fp ge v2 e2 m' a fp' ->
    exists v fp,
      Cminor.eval_expr ge_local v1 e1 m a v /\
      Cminor_local.eval_expr_fp ge_local v1 e1 m a fp /\
      val_related (construct_inj j bound fl) v v' /\
      FPlocalize (construct_inj j bound fl) fp' fp.
Proof.
  intros until 7. revert fp'. induction H5; intros.
  { inv H6. specialize (H4 id). rewrite H5 in H4.
    destruct (e1 ! id) eqn:ENV; inv H4; try discriminate.
    exists v0, FP.emp. split. constructor. auto.
    split. constructor. auto using FPlocalize_emp. }
  { inv H6. clear v0 H8.
    destruct cst; simpl in *; inv H5.
    all: try (eexists; exists FP.emp; repeat (econstructor; eauto); fail).
    exists (Genv.symbol_address ge_local i i0), FP.emp.
    split. econstructor; eauto.
    split. econstructor; simpl; eauto.
    split. unfold Genv.symbol_address. inv H.
    unfold Senv.find_symbol in *; simpl in *.
    destruct (ge_match_strict_senv i); auto.
    constructor. eapply mem_related_inj_construct_inj; eauto.
    auto using FPlocalize_emp.
    exists (Val.offset_ptr v1 i), FP.emp.
    split. econstructor; eauto.
    split. econstructor; simpl; eauto.
    split. unfold Val.offset_ptr. inv H3; auto.
    auto using FPlocalize_emp. }
  { inv H7. repeat det.
    apply IHeval_expr in H11. destruct H11 as [v [fp [A [B [C D]]]]].
    exploit eval_uop_related; eauto.
    rewrite H6. intro. inv H5; auto. 
    exists x, fp. split.
    econstructor; eauto.
    split. econstructor; eauto.
    split; auto.
  }
  {
    inv H6. repeat det.
    eapply IHeval_expr1 in H11 as ?;eauto.
    eapply IHeval_expr2 in H13 as ?;eauto.
    Hsimpl.
    eapply eval_binop_related in H9 as ?;try apply H17;eauto;try eapply mem_related_inj_j;eauto.
    
    rewrite H16 in H19.
    destruct H19.
    inv H19;auto. rewrite H5 in H23;inv H23.
    rewrite H5 in H22;inv H22.
    symmetry in H21.
    assert(exists fp, Cminor_op_footprint.eval_binop_fp op x1 x m = Some fp).
    unfold Cminor_op_footprint.eval_binop_fp,Cminor.eval_binop in *.
    ex_match;eauto;try rewrite H21;eauto.
    unfold option_map in H21. ex_match. inv H21.
    apply ValFP.cmplu_bool_cmplu_bool_fp in Hx0;eauto.
    Hsimpl.
    Esimpl;eauto. econstructor;eauto.
    econstructor;eauto.
    eapply FPlocalize_union;eauto.
    inv H20. rewrite H19 in H24;inv H24. auto.
  }
  {
    inv H7.
    specialize (IHeval_expr _ H11).
    Hsimpl.
    repeat det.
    exploit (loadv_related);eauto.
    rewrite H6;intro.
    inv H5.
    Esimpl;eauto. econstructor;eauto.
    econstructor;eauto.
    eapply FPlocalize_union;eauto.
    eapply loadv_fp_localize;eauto.
    apply construct_inj_injective;auto.
    inv H2;auto.
  }
Qed.
Lemma eval_exprlist_localize:
  forall ge ge_local j m m' v1 v2 e1 e2 a v' fp',
    let bound := (Genv.genv_next ge) in
    let fl := (Mem.freelist m') in
    ge_match_strict j ge ge_local ->
    norep fl ->
    no_overlap fl (fun b => Plt b bound) ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) v1 v2 ->
    match_env (construct_inj j bound fl) e1 e2 ->
    eval_exprlist ge v2 e2 m' a v' ->
    CminorLang.eval_exprlist_fp ge v2 e2 m' a fp' ->
    exists v fp,
      Cminor.eval_exprlist ge_local v1 e1 m a v /\
      Cminor_local.eval_exprlist_fp ge_local v1 e1 m a fp /\
      list_forall2 (val_related (construct_inj j bound fl)) v v' /\
      FPlocalize (construct_inj j bound fl) fp' fp.
Proof.
  induction a;intros.
  inv H5. inv H6. Esimpl;eauto. constructor. constructor. constructor.

  inv H5;inv H6.
  det.
  eapply eval_exprlist_det in H11;eauto;subst.
  exploit eval_expr_localize;eauto;intro;Hsimpl.
  eapply IHa in H13;eauto.
  Hsimpl. Esimpl;eauto.
  econstructor. eauto. eauto.
  econstructor;eauto. econstructor;eauto.
Qed.
Lemma set_val_related_match_env_preserve:
  forall u v1 v2 e1 e2 id,
    val_related u v1 v2 ->
    match_env u e1 e2 ->
    match_env u (PTree.set id v1 e1)(PTree.set id v2 e2).
Proof.
  intros.
  unfold match_env in *.
  intros.
  specialize (H0 id0).
  do 2 rewrite PTree.gsspec.
  ex_match2.
  constructor;auto.
Qed.          
Definition wdcu (cu: cminor_comp_unit) : Prop :=
  nodup_ef (cu_defs cu) = true /\ nodup_gd_ident (cu_defs cu) = true.

Inductive match_cont (j: Bset.inj):cont->cont->Prop:=
| match_stop: match_cont j Kstop Kstop
| match_seq:
    forall k1 k1'  s,
      match_cont j k1 k1'->
      match_cont j (Kseq s k1)(Kseq s k1')
| match_block:
    forall k k',
      match_cont j k k'->
      match_cont j (Kblock k)(Kblock k')
| match_call:
    forall id f v v' e e' k k',
      match_cont j k k'->
      val_related j v v'->
      match_env j e e'->
      match_cont j (Kcall id f v e k)(Kcall id f v' e' k').

Inductive match_core (j: Bset.inj) : core -> core -> Prop :=
| match_state_intro:
    forall f s k1 k2 v1 e1 v2 e2,
      match_cont j k1 k2 ->
      val_related j v1 v2 ->
      match_env j e1 e2 ->
      match_core j (Core_State f s k1 v1 e1)
                 (Core_State f s k2 v2 e2)
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
Lemma find_label_match_cont_case1:
  forall j s t k k',
    match_cont j k k'->
    find_label s t k' = None ->
    find_label s t k= None.
Proof.
  induction t;intros;auto.
  all : simpl in H0;ex_match.
  all : try (eapply IHt1 in Hx;eauto;try econstructor;eauto;eapply IHt2 in H0;eauto;simpl;rewrite Hx;auto;fail).
  eapply IHt in H0;eauto;constructor;auto.
  eapply IHt in H0;eauto. econstructor;eauto.
  eapply IHt in H0;eauto. simpl. rewrite Hx. auto.
Qed.

Lemma find_label_match_cont_case2:
  forall t j s k k' k1  s',
    match_cont j k k'->
    find_label s t k' = Some (s',k1) ->
    exists k2,find_label s t k= Some (s',k2) /\ match_cont j k2 k1.
Proof.
  induction t;intros;eauto.
  all: simpl in *;inv H0;ex_match;try match goal with H:Some _ = Some _ |- _ => inv H end.
  all: try (eapply IHt1 in Hx;eauto;Hsimpl;try rewrite H0;eauto;try constructor;auto;fail).
  all: try (eapply find_label_match_cont_case1 in Hx;eauto;try rewrite Hx;eauto;try constructor;eauto;fail).
  all: try(eapply IHt in H2;eauto;constructor;eauto).
  Esimpl;eauto.
Qed.
Lemma call_cont_match:
  forall k k' j,
    match_cont j k k'->
    match_cont j (call_cont k)(call_cont k').
Proof.
  induction k;intros;simpl.
  inv H;constructor.
  inv H. eapply IHk in H3. eauto.
  inv H. eapply IHk in H1;eauto.
  inv H. constructor;auto.
Qed.
Lemma set_params_match_env:
  forall b args1 args2 j ,
    list_forall2 (val_related j) args1 args2->
    forall id, option_rel (val_related j) (set_params args1 b)!id
                     (set_params args2 b)!id.
Proof.
  induction b.
  intros.
  simpl. rewrite PTree.gempty. constructor.
  
  intros. simpl.
  ex_match2;try inversion H;subst.
  
  rewrite PTree.gsspec.
  destruct peq. constructor. constructor.
  eapply IHb in H;eauto.
  
  do 2 rewrite PTree.gsspec.
  destruct peq. constructor. auto.
  apply IHb;auto.
Qed.
Lemma set_locals_related_cons:
  forall j e1 e2 a,
    match_env j e1 e2->
    match_env j (set_locals a e1)(set_locals a e2).
Proof.
  induction a.
  intros. simpl. auto.
  intros. Hsimpl. simpl.
  unfold match_env;intro;do 2 rewrite PTree.gsspec.
  ex_match2. constructor;constructor.
  eapply IHa;eauto.
Qed.
Theorem cminor_localize: LangLocalize cminor_comp_unit wdcu CminorLang Cminor_IS.
Proof.
  constructor; simpl in *. intros cu WDCU ge G INITGE.
  pose proof INITGE as GEBOUND.
  rewrite init_genv_iff in GEBOUND. destruct GEBOUND as [_ [_ _ _ _ _ _ _ _ GEBOUND]].
  remember (Genv.genv_next ge) as bound eqn:HBOUND.
  remember (ge_extend (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)) bound GEBOUND) as ge_local eqn:HGE.
  assert (INITGE_local: init_genv cu ge_local ge_local).
  { split; [auto|econstructor; eauto]. }
  rewrite init_genv_iff in INITGE. destruct INITGE as [X INITGE]. subst G.
  destruct INITGE as [j DOM INJECTIVE PUBLICEQ SYMBREL DEFSDOM DEFSRANGE DEFSREL _]. 
  exists j, ge_local, ge_local.
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
  { intros. exploit G_args_exists_args_related'. eauto. subst ge_local; simpl in *. rewrite <- HBOUND. eauto.
    intros [args_local INJARGS]. exists args_local.
    intros. unfold 
              CminorLang.init_core, init_core,
            generic_init_core, CminorLang.fundef_init, fundef_init in *.
    destruct (Genv.find_symbol ge id) eqn:FINDSYMB;[|discriminate].
    destruct (Genv.find_funct_ptr ge b) eqn:FINDDEF;[|discriminate].
    exploit (SYMBREL). instantiate (1:=id). unfold Senv.find_symbol; simpl.
    rewrite FINDSYMB. intro. inv H1. symmetry in H2.
    unfold Genv.find_symbol in H2 |- * .  simpl. rewrite H2. clear H2.
    exploit DEFSREL. exact H5. unfold Genv.find_funct_ptr, Genv.find_def in *.
    destruct ((Genv.genv_defs ge)!b) eqn:FINDDEF'; try discriminate. intro.
    simpl. rewrite H1. clear H1. rewrite FINDDEF. 
    destruct g; [|discriminate]. inversion FINDDEF; subst f0; clear FINDDEF. destruct f; [|discriminate].
    unfold funsig in *.
    destruct (wd_args args) eqn:WDARGS; [|discriminate].
    assert (wd_args args_local (sig_args (fn_sig f)) = true).
    { generalize (sig_args (fn_sig f)) INJARGS WDARGS. clear. intros until 1. unfold wd_args.
      intro. apply andb_true_iff in WDARGS. destruct WDARGS.
      apply andb_true_iff in H. destruct H.
      apply andb_true_iff. split. apply andb_true_iff. split.
      (* *)
      clear H1 H0. revert l H. induction INJARGS; intros. 
      destruct l. auto. inversion H. destruct l; simpl in *; auto.
      apply andb_true_iff in H0. destruct H0.
      apply andb_true_iff; split; auto. inv H; destruct t; auto.
      (* *)
      clear H H0. induction INJARGS; auto. simpl. inv H; auto.
      (* *)
      apply list_forall2_length in INJARGS. rewrite Zlength_correct in H0 |- * .
      rewrite INJARGS. auto.
    }
     rewrite H1. eexists; split. 
    apply list_forall2_imply with (val_related jfull); auto. intros. apply val_related_val_inject_strict; auto.
    split. eauto.

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
    intro. rewrite  <- init_mem_valid_block; eauto. tauto. }
  (** step *)
  {
    
    set (ge1:= (Genv.globalenv {|prog_defs := cu_defs cu;prog_public := cu_public cu;prog_main := 1%positive |})) in *.
    intros fl c lc m lm lfp lc' lm' [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] STEP FPG.    
   
    inv MS; inv STEP.
    all: match goal with
         | H: embed (strip ?fm) (Mem.freelist ?fm) ?m |- _ =>
           apply embed_eq in H; subst fm
         end.
    {
      pose proof H3 as STEP0.
      inv H3.
      Ltac triv :=
        match goal with H:match_cont _ _ _ |- _ => inversion H;subst end;do 3 eexists; split;
        [econstructor |
         split; auto using FPlocalize_emp;
         eexists; repeat (split; eauto); try constructor; auto].
      all : try (triv;auto;fail).
      all: try (Esimpl;eauto;econstructor;eauto;econstructor;eauto;fail).
      { (* skip call *)
        inv H0. exploit free_related; eauto.
        rewrite H13. intro. inv H0. symmetry in H2.
        do 3 eexists. split. econstructor; eauto.
        unfold is_call_cont in *;ex_match2;inv H.
        split. 
        constructor; simpl; auto using Loclocalize_emp.
        eexists; repeat (split; eauto).
        eapply Mem.free_freelist; eauto.
        econstructor; eauto. }
      { (* assign *)
        edestruct eval_expr_localize as (?&?&Expr1&Fp1&Vl1&Fpl1);try apply GEMATCH;eauto.
        Esimpl;eauto.
        econstructor;eauto.
        constructor; simpl; auto.
        eapply set_val_related_match_env_preserve;eauto.
      }
      { (*Sstore*)
        edestruct eval_expr_localize as (?&?&Expr1&Fp1&Vl1&Fpl1);try apply GEMATCH;try apply H7;eauto.
        edestruct eval_expr_localize as (?&?&Expr2&Fp2&Vl2&Fpl2);try apply GEMATCH;try apply H9;eauto.
        
        eapply storev_related in Vl1 as Sl1;try apply Vl2;eauto.
        erewrite H16 in Sl1.
        inv Sl1.
        Esimpl;eauto.
        econstructor;eauto.
        apply FPlocalize_union. apply FPlocalize_union;auto.
        eapply storev_fp_localize;eauto.
        eapply mem_storev_fleq in H16;eauto.
        econstructor;eauto.
      }
      { (*Scall *)
        edestruct eval_expr_localize as (?&?&Expr1&Fp1&Vl1&Fpl1);try apply GEMATCH;try apply H8;eauto.
        edestruct eval_exprlist_localize as (?&?&ExprList1&Fp2&Vl2&Fpl2);try apply GEMATCH;try apply H10;eauto.
        
        Esimpl;eauto.
        econstructor;eauto.
        Focus 2. econstructor;eauto. constructor;auto.

        set(ge':= (ge_extend ge1 (Genv.genv_next ge) GEBOUND)) in *.
        unfold Genv.find_funct in *.
        inv Vl1;auto. ex_match.
        
        unfold Genv.find_funct_ptr in *.
        ex_match.
        inv H16.
        enough(Genv.find_def ge' b = Some (Gfun fd)).
        rewrite H3. auto.

        destruct (Genv.find_def ge b') eqn:FIND; try discriminate.
        destruct g eqn:GD; try discriminate. inv Hx0.
        exploit Genv.genv_defs_range. eauto. intro.
        unfold construct_inj in H2. destruct plt.
        exploit DEFSRANGE. eauto. intros [b'' INJ]. pose proof INJ.
        eapply inject_incr_bset_inj_incr in H4; eauto.
        assert (b = b''). eapply Bset.inj_injective; eauto using Bset.inj_weak.
        subst. exploit DEFSREL. exact INJ. intro. subst ge'.
        unfold ge_extend, Genv.find_def; simpl. rewrite H5. eauto.

        exfalso. inv H2. eapply NOOVERLAP; eauto.
      }
      { (*tailcall *)
        edestruct eval_expr_localize as (?&?&Expr1&Fp1&Vl1&Fpl1);try apply GEMATCH;try apply H8;eauto.
        edestruct eval_exprlist_localize as (?&?&ExprList1&Fp2&Vl2&Fpl2);try apply GEMATCH;try apply H10;eauto.
        inv H0.
        exploit free_related;try rewrite H18;eauto.
        intro. inv H0.
        Esimpl;eauto.
        econstructor;eauto.

        {
          set(ge':= (ge_extend ge1 (Genv.genv_next ge) GEBOUND)) in *.
          unfold Genv.find_funct in *.
          inv Vl1;auto. ex_match.
          unfold Genv.find_funct_ptr in *.
          ex_match. inv H12.
          assert(Genv.find_def ge' b0 = Some (Gfun fd)).
          
          destruct (Genv.find_def ge b') eqn:FIND; try discriminate.
          destruct g eqn:GD; try discriminate. inv Hx0.
          exploit Genv.genv_defs_range. eauto. intro.
          unfold construct_inj in H0. destruct plt.
          exploit DEFSRANGE. eauto. intros [b'' INJ]. pose proof INJ.
          eapply inject_incr_bset_inj_incr in H6; eauto. auto.
          
          assert (b0 = b''). eapply Bset.inj_injective; eauto using Bset.inj_weak.
          subst. exploit DEFSREL. exact INJ. intro. subst ge'.
          unfold ge_extend, Genv.find_def; simpl.  rewrite H7. eauto. 
          exfalso. inv H0. eapply NOOVERLAP; eauto.

          rewrite H3. auto.
        }
        apply FPlocalize_union;auto.
        unfold free_fp;constructor;simpl;auto.
        eapply Mem.free_freelist;eauto.
        econstructor;eauto. eapply call_cont_match;eauto.
      }
      { (*ifelse*)
        edestruct eval_expr_localize as (?&?&Expr1&Fp1&Vl1&Fpl1);try apply GEMATCH;eauto.
        Esimpl;eauto.
        econstructor;eauto.
        instantiate(1:=b).
        inv H14. inv Vl1. constructor.
        econstructor;eauto.
      }
      { (*switch*)
        edestruct eval_expr_localize as (?&?&Expr1&Fp1&Vl1&Fpl1);try apply GEMATCH;eauto.
        Esimpl;eauto. econstructor;eauto.
        instantiate(1:=n). inv H14;inv Vl1;try constructor.
        econstructor;eauto.
      }
      { (*return *)
        inv H0.
        exploit free_related;try rewrite H12;eauto.
        intros. 
        inv H0.
        Esimpl;eauto.
        econstructor;eauto.
        unfold free_fp.
        constructor;auto.
        simpl. auto.
        eapply Mem.free_freelist; eauto.
        econstructor;eauto.
        eapply call_cont_match;eauto.
      }
      { (*return with val*)
        edestruct eval_expr_localize as (?&?&Expr1&Fp1&Vl1&Fpl1);try apply GEMATCH;eauto.
        inv H0.
        exploit free_related;try rewrite H14;eauto.
        intro.
        inv H0.
        Esimpl;eauto. econstructor;eauto.
        eapply FPlocalize_union;eauto.
        unfold free_fp;constructor;auto;simpl;auto.
        eapply Mem.free_freelist;eauto.
        econstructor;eauto.
        eapply call_cont_match;eauto.
      }
      { (*goto*)
        assert(match_cont (construct_inj jfull (Genv.genv_next ge) (Mem.freelist m')) (call_cont k1)(call_cont k2)).
        revert H;clear.
        revert k1 k2.
        induction k1;intros.
        inv H;constructor.
        inv H. eapply IHk1 in H3;eauto.
        inv H. eapply IHk1 in H1;eauto.
        inv H;econstructor;eauto.
        eapply find_label_match_cont_case2 in H12;eauto.
        Hsimpl.
        Esimpl;eauto. econstructor;eauto.
        constructor;auto.
      } 
    }
    { (*Call State *)
      inv H2.
      remember (  Memory.Mem.alloc lm 0 (fn_stackspace f)).
      destruct p.
      exploit alloc_related;try apply GEMATCH;eauto.
      exploit alloc_result_related;try apply GEMATCH;eauto.
      intros.
      Esimpl;eauto.
      econstructor;eauto.
      
      unfold alloc_fp, MemOpFP.alloc_fp, uncheck_alloc_fp.
      erewrite <- Memory.Mem.alloc_result, <- FMemory.Mem.alloc_result; eauto.
      constructor; simpl; try (constructor; tauto); auto using range_locset_localize.
      constructor; intros. Locs.unfolds. do 2 destruct peq; try tauto.
      subst. exploit construct_inj_injective. eauto. eauto. eauto.
      eapply H3. eapply H1. congruence. congruence.
      eapply Mem.alloc_freelist;eauto.
      econstructor;eauto.
      eapply set_locals_related_cons.
      unfold match_env.
      eapply set_params_match_env;eauto.
    }
    { (*Return State*)
      inv H2. inv H.
      Esimpl;eauto. econstructor;eauto.
      constructor;auto.
      destruct optid;auto.
      unfold set_optvar.
      eapply set_val_related_match_env_preserve;eauto.
    }
  }
  (** At_ext *)
  {  intros fl c lc m lm f sg args_local [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] ATEXT GARGS.
     unfold CminorLang.at_external,at_external in *. inv MS; try discriminate.
     (** ef *)
     destruct fd ;try discriminate.
     destruct e; try discriminate.
     destruct (invert_symbol_from_string _ name) eqn:NAME; try discriminate.
     erewrite <-invert_symbol_from_string_eq. rewrite NAME.
     destruct peq; simpl in *. discriminate.
     destruct peq; simpl in *. discriminate.
     inv ATEXT.
     eexists. split. eauto. unfold args_related.
     { generalize args_local args1 H0 GARGS NOOVERLAP; clear. induction args_local; intros; inv H0; inv GARGS; constructor; auto.
       inv H3; econstructor. unfold Bset.inj_to_meminj, construct_inj in *. 
       destruct plt; try contradiction. rewrite H. eauto.
       inv H. exfalso. eapply NOOVERLAP; eauto. 
       rewrite Ptrofs.add_zero. auto. }
     (** TODO: missing norep gd in Localize/Lift *)
     { destruct WDCU. eapply nodup_ef_ge_norep_ef_name; try eassumption.
       econstructor. eauto. eauto. }
     { destruct WDCU. eapply nodup_gd_init_genv_ident_exists; eauto.
       econstructor. eauto. eauto. }
     econstructor; eauto. unfold ge_extend; simpl. auto with coqlib.
  }
  (** after_ext *)
  { intros fl c lc m lm ores lc' lores [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] RESREL AFTEXT.
    unfold CminorLang.after_external,after_external in *. inv MS; try discriminate.
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
  (** rely *)
  { intros fl c lc m lm [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] m' lm' UNCHG RELY.
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
    unfold CminorLang.halted,halted, Vzero; intros fl c lc m lm lres [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] HALT GRES.
    inv MS; try discriminate.
    destruct k2 ;try discriminate.
    inv H. inv HALT.
    Esimpl;eauto.

    unfold G_arg in GRES.
    inv H0;auto;try discriminate;try constructor.
    unfold arg_related.
    econstructor;eauto.
    
    unfold Bset.belongsto in GRES.
    Focus 2.
    instantiate(1:=0). rewrite Ptrofs.add_zero. auto.
    apply MEMREL in GRES as [].
    assert(construct_inj jfull (Genv.genv_next ge)(Mem.freelist fm) x = Some b').
    eapply mem_related_inj_construct_inj in H0;eauto.
    eapply construct_inj_injective in H;try apply H1;eauto.
    specialize (H H1). subst.
    unfold Bset.inj_to_meminj. rewrite H0. auto.
  }
  Unshelve.
  apply 0.
Qed.